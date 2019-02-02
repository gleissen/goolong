{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}

module Language.IceT.VCGen2 (verifyFile, verifyProgram) where

import           Language.IceT.Parse (parseFile, parseString, ParsedProgram)
import           Language.IceT.SMT
import           Language.IceT.Types hiding (CFG, Action(..))

import           Control.Monad.State
import qualified Data.Graph.Inductive.Graph        as G
import           Data.Graph.Inductive.PatriciaTree
import qualified Data.HashMap.Strict               as HM
import qualified Data.HashSet                      as HS
import qualified Data.IntMap.Strict                as IM
import qualified Data.IntSet                       as IS
import           Data.List (nub, isInfixOf, foldl')
import           GHC.IO.Handle
import           System.Exit
import           System.IO
import           System.Process
import           Text.Printf

import Language.IceT.Pretty
import Debug.Trace





-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- VCGEN
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

type TypeEnv = HM.HashMap Id Sort
data VCState a = VCState { freshCounter       :: Int              -- used to create fresh variables
                         , typeEnv            :: TypeEnv          -- map from variables to their types
                         , unfoldedProcesses  :: UF               -- p -> ps
                         , parallelProcesses  :: HS.HashSet Id    -- symmetric sets we have seen so far

                         -- atomic action related stuff
                         , actionMap          :: ActionMap a    -- map from action labels to actions
                         , actionStatePath    :: ActionPath a   -- path conditions of the actions
                         , actionForLoop      :: Maybe (Stmt a) -- used to check whether in for loop or not
                         , actionProp         :: Prop a         -- used for integrating loop invariants actions
                         }

type VCGen a r = State (VCState a) r
type UF = HM.HashMap Id Id

verifyProgram :: String -> IO Bool
verifyProgram = verify . parseString

verifyFile :: FilePath -> IO Bool
verifyFile fp = do
  program <- parseFile fp
  verify program

-------------------------------------------------------------------------------
writeSMT :: ParsedProgram -> IO ()
-------------------------------------------------------------------------------
writeSMT (Program{..}) = do
  writeFile filename vcstr
  printf "Wrote smt2 file to %s\n" filename

  where
    filename = ".query.smt2" 
    vcstr = createSMTQuery decls' pss vc'

    vc' = simplifyProp vc
    -- vc' = trace (pretty _vc') _vc'
    -- vc' = vc

    (vc, lastState) = runState action initialState
    initialState = VCState { freshCounter       = 0
                           , typeEnv            = tenv
                           , unfoldedProcesses  = HM.empty
                           , parallelProcesses  = HS.empty
                           , actionMap          = IM.empty
                           , actionStatePath    = []
                           , actionProp         = TT
                           , actionForLoop      = Nothing
                           }
    tenv       = makeTypeEnv decls
    decls'     = fmap (uncurry Bind) . HM.toList $ typeEnv lastState
    action     = wlp prog' ensures
    preprocess = fixAtomicPost . updateTypes tenv
    prog'     = preprocess prog
    -- prog'      = trace (pretty _prog') _prog'
    pss        = HS.toList $ parallelProcesses lastState

-------------------------------------------------------------------------------
verify :: ParsedProgram -> IO Bool
-------------------------------------------------------------------------------
verify p = do
  writeSMT p

  (inp, out, err, pid) <- runInteractiveProcess "z3" ["-smt2", ".query.smt2"] Nothing Nothing
  ec   <- waitForProcess pid
  outp <- hGetContents out
  errp <- hGetContents err

  putStrLn outp
  hPutStr stderr errp

  case ec of
    ExitSuccess   -> return ("unsat" `isInfixOf` outp)
    ExitFailure _ -> return False


-------------------------------------------------------------------------------
wlp :: VCAnnot a => Stmt a -> Prop a -> VCGen a (Prop a)
-------------------------------------------------------------------------------
wlp (Skip {..}) q = return q

wlp (Assign {assignExpr = NonDetValue, ..}) q = do
  v' <- freshBinder assignVar -- create a fresh variable to replace the expression
  wlp (Assign { assignExpr = Var (bvar v'), ..}) q

-- p.v <- p'.e where v has type t
wlp (Assign {..}) q = do
  e' <- case e of
          -- if the rhs is a variable, and it's a map
          -- (i.e. from processes to values)
          -- replace it with a Select
          -- (this is probably due to parsing of pairs ...)
          Var x -> do
            t' <- getType x
            case t' of
              Map _ _ -> return $ Select e (Var p')
              _       -> return e
          _ -> return e
  -- if the lhs is a map, update the map
  -- otherwise, just replace it with the expression
  t <- getType v
  let e'' = case t of
              Map _ _ -> Store (Var v) (Var p) e'
              _       -> e'

  insertType v' t

  return $
    Atom Eq (Var v') e''
    :=>:
    subst v (Var v') q

  where
    p  = stmtProcess
    p' = assignFromProcess
    e  = assignExpr
    v  = bvar assignVar
    v' = v ++ "!1"

wlp (Assume {..}) q = return $ stmtProperty :=>: q

wlp (Assert {..}) q = return $ And [stmtProperty, q]

wlp (Atomic {..}) q = do
  p1 <- wlp atomicStmt atomicPost
  p2 <- wlp atomicStmt q
  return $ And [ p1, p2 ]

wlp (Seq {..}) q = foldM (flip wlp) q (reverse seqStmts)

wlp (Cases {casesExpr = NonDetValue, ..}) q =
  And <$> (sequence $ (flip wlp q . caseStmt) <$> caseList)

wlp (Cases {..}) q = And <$> (sequence $ go <$> caseList)
  where
    go c = do
      wp <- wlp (caseStmt c) q
      return (Atom Eq casesExpr (caseGuard c) :=>: wp)

wlp (If {..}) q = do
  q1 <- wlp thenStmt q
  q2 <- wlp elseStmt q
  let g p1 p2 = case ifCondition of
                  NonDetProp -> And [p1, p2]
                  _          -> And [ ifCondition :=>: p1
                                    , Not ifCondition :=>: p2
                                    ]
  return (g q1 q2)

wlp stmt@(ForEach {..}) q = do
  withElem x xs $ do
    pre <- wlp forStmt q'
    let invInit = subst done EmptySet inv -- invariant holds when done = empty
        -- if invariant holds for done, then it holds for done U {x} after executing the loop
        invStep = Forall y $              
                  And [ inv
                      , Atom SetMem ex exs
                      , Not $ Atom SetMem ex edone
                      , Atom SetSub edone exs
                      ] :=>:
                  pre
        invExit = Forall y $ (subst done exs inv) :=>: q -- invariant holds when done = xs
        result = And [ invInit
                     , invStep
                     , invExit
                     ]
    -- traceM (smtS result)
    return result

  where
    q'          = subst done (Bin SetAdd edone ex) inv
    edone       = Var done
    x           = bvar forElement
    xs          = bvar forList
    ex          = Var x
    exs         = Var xs
    (done,_inv) = forInvariant
    y           = updatedVars stmt
    inv         = case forStmt of
                    Atomic { stmtData = a2
                           , ..
                           } -> And [ _inv
                                    , atomicPost
                                    ]
                    _ -> _inv

wlp (Par {..}) q = do
  withElem stmtProcess stmtProcessSet $ do
    VCState{..} <- get
    ActionResult{ arMap    = m
                , arCFG    = g
                , arPC0s   = pc0s
                , arPCExit = pcExit
                , arStmt   = atomizedStmt
                } <- extractCFG stmtProcessSet parStmt
    put VCState { parallelProcesses = HS.insert stmtProcessSet parallelProcesses
                , ..
                }
    traceM (pretty atomizedStmt)
    --forM_ (IM.toList m) $ \(n, la) -> traceM (pretty $ actionStmt la)
      
    let _i = Forall [Bind stmtProcess Int] $
            And [ And [ Atom SetMem varP varPs
                      , Atom Eq (pc ps p) (Const l)
                      ]
                  :=>:
                  let posts = [ if   l' == pcExit
                                then TT
                                else let la' = m IM.! l'
                                     in atomicPost $ actionStmt la'
                              | l' <- G.pre g l
                              ]
                  in case posts of
                       [] -> TT
                       _  -> Or posts
                | l <- pcExit : IM.keys m
                ]
        i = trace (printf "I: %s\n\n" (pretty $ simplifyProp _i)) _i
        invInit = ( Forall [Bind stmtProcess Int] $
                    And [ Atom SetMem varP varPs
                        , Or [ Atom Eq (Select varPC varP) (Const pc0)
                             | pc0 <- pc0s 
                             ]
                        ]
                  ) :=>: i
        invExit = Forall y $
                  And [ Forall [Bind stmtProcess Int] $
                        And [ Atom SetMem varP varPs
                            , Atom Eq (Select varPC varP) (Const pcExit)
                            ]
                      , i
                      ] :=>: q
        cf l = And [ Atom Eq (pc ps p) (Const l)
                   , Or [ Atom Eq varPC' (Store varPC varP (Const l'))
                        |  l' <- G.suc g l
                        ]
                   ]
    conjunts <- sequence $
                (\(la_pc,la) -> do
                    let stmt' = subst p varP0 (atomicStmt $ actionStmt la)
                        q'     = subst (pcName ps) varPC' i
                        uf     = actionUnfolding la
                    withElem p ps $ withElem p0 ps $ do
                      prop <- withActionState la (wlp stmt' q')
                      return (la_pc, la, prop)
                ) <$> (IM.toList m)
    let idxs = HS.fromList [ pp
                           | (_,la) <- IM.toList m
                           , (pp,_) <- HM.toList $ actionUnfolding la
                           ]
    let invStep = Forall (Bind p0 Int : y ++ [ Bind pp Int | pp <- HS.toList idxs]) $
                  Atom SetMem varP0 varPs
                  :=>:
                  And [ And ([ i
                             , cf l
                             , Atom SetMem varP0 varPs
                             , Atom SetMem varP  varPs
                             ] ++ actionPath la)  :=>: w
                      | (l, la, w) <- conjunts
                      ]
    return $ And [ invInit
                 , invStep
                 , invExit
                 ]

  where
    y = Bind (pcName stmtProcessSet) pcType :
        Bind (pcName' stmtProcessSet) pcType :
        updatedVars parStmt
    p0 = stmtProcess ++ "!0"
    p  = stmtProcess
    ps = stmtProcessSet
    varP   = Var p
    varPs  = Var ps
    varP0  = Var p0
    varPC  = Var $ pcName ps
    varPC' = Var $ pcName' ps

    withActionState :: Action a -> VCGen a r -> VCGen a r
    withActionState la act = do
      let uf = actionUnfolding la
          te = actionTypeEnv la
      oldUnfoldings <- gets unfoldedProcesses
      oldTypeEnv    <- gets typeEnv
      modify $ \VCState{..} -> VCState{ unfoldedProcesses = HM.union oldUnfoldings uf
                                      , typeEnv           = HM.union oldTypeEnv
                                                            (HM.union (HM.map (const Int) uf) te)
                                      , ..
                                      }
      result <- act
      -- keep the new type environment !
      modify $ \VCState{..} -> VCState{ unfoldedProcesses = oldUnfoldings
                                      , ..
                                      }
      return result

wlp (While {..}) q = undefined








-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- ACTIONS
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

data Action a = Action { actionStmt        :: Stmt a        -- this is the atomic action
                       , actionPath        :: ActionPath a  -- path condition (i.e. if stmt conditions)
                       , actionUnfolding   :: HM.HashMap Id Id
                       , actionTypeEnv     :: TypeEnv
                       }

data ActionResult a = ActionResult { arMap    :: ActionMap a
                                   , arPC0s   :: [Int]
                                   , arPCExit :: Int
                                   , arCFG    :: CFG
                                   , arStmt   :: Stmt a -- stmt after atomization
                                   }

type ActionPath a  = [ Prop a ]
type ActionTypeEnv = HM.HashMap Id Sort
type ActionMap a   = IM.IntMap (Action a)
type CFG           = UGr

--------------------------------------------------------------------------------
-- Merge local statements together to create a program consists of only atomic
-- actions to be used for generating the verification conditions for the
-- parallel case.
-- This stateful computation only increments the fresh counter variable.
--------------------------------------------------------------------------------
atomize :: Stmt a -> VCGen a (Stmt a)
--------------------------------------------------------------------------------
atomize = go
  where
    ------------------------------------------------------------
    go :: Stmt a -> VCGen a (Stmt a)
    ------------------------------------------------------------
    go stmt@(Atomic s p _ a) = do
      l' <- incrCounter
      let ss = case s of
                 Seq {..} -> seqStmts
                 _        -> [s]
          (p', s') = atomicMerge ss
      return $ Atomic { atomicPost = And (p:p')
                      , atomicStmt = case s' of
                                       [s0] -> s0
                                       _ -> Seq { seqStmts = s'
                                                , stmtData = a
                                                }
                      , atomicLabel = l'
                      , stmtData = a
                      }
    go (Seq {..}) = do
      ss  <- goHelper seqStmts
      return $ Seq { seqStmts = ss
                   , ..
                   }
    go (ForEach {..}) = do
      s' <- go forStmt
      return $ ForEach { forStmt = s'
                       , ..
                       }
    go (If {..}) = do
      t' <- go thenStmt
      e' <- go elseStmt
      return $ If { thenStmt = t'
                  , elseStmt = e'
                  , ..
                  }
    go (While {..}) = do
      s' <- go whileStmt
      return $ While { whileStmt = s'
                     , ..
                     }
    go (Cases {..}) = do
      cs' <- mapM (\Case{..} -> do
                      s' <- go caseStmt
                      return $ Case { caseStmt = s'
                                    , ..
                                    }
                  ) caseList
      return $ Cases { caseList = cs'
                     , ..
                     }
    go s@(Skip {..})   = mergeStmts [s]
    go s@(Assign {..}) = mergeStmts [s]
    go s@(Assume {..}) = mergeStmts [s]
    go s@(Assert {..}) = mergeStmts [s]
    go s@(Par {..})    = error "atomize.go is called with a parallel composition"

    ------------------------------------------------------------
    goHelper :: [Stmt a] -> VCGen a [Stmt a]
    ------------------------------------------------------------
    goHelper ss = do
      sss <- partitionStmts ss
      mapM mergeStmts sss

    ------------------------------------------------------------
    -- given a sequence of statements, partition them such that
    -- we can create atomic blocks
    ------------------------------------------------------------
    partitionStmts :: [Stmt a] -> VCGen a [[Stmt a]]
    ------------------------------------------------------------
    partitionStmts []     = return []
    partitionStmts (s:ss) = do
      -- invariant: s is not a sequence, or another parallel process
      s'  <- if   canMerge s
             then return s
             else go s
      ss' <- partitionStmts ss
      return $ case ss' of
                 []    -> [[s']]
                 []:ls -> error "partitionStmts returned an empty list"
                 (l@(lh:_)):ls ->
                   if   canMerge lh
                   then (s':l):ls
                   else [[s']] ++ ss'

    ------------------------------------------------------------
    mergeStmts :: [Stmt a] -> VCGen a (Stmt a)
    ------------------------------------------------------------
    mergeStmts [] = error "mergeStmts is called with an empty list"
    mergeStmts [s]
      | isSimple s = do
          l <- incrCounter
          let (ps, ss') = atomicMerge [s]
              a         = stmtData s
              s'        = case ss' of
                            []   -> Skip a
                            [_s] -> _s
                            _    -> error "atomize.mergeStmts : impossible !"
              result    = Atomic { atomicStmt  = s'
                                 , atomicPost  = And ps
                                 , atomicLabel = l
                                 , stmtData    = a
                                 }
          return result
      | otherwise  = return s

    mergeStmts ss@(ss1:_) = do
      l <- incrCounter
      let (ps, ss') = atomicMerge ss
          a         = stmtData ss1
          seq'      = Seq { seqStmts = ss'
                          , stmtData = a
                          }
          result    = Atomic { atomicStmt  = seq'
                             , atomicPost  = And ps
                             , atomicLabel = l
                             , stmtData    = a
                             }
      return result

    ------------------------------------------------------------
    -- can the statement merge with the following statement
    -- (to create an atomic block) if it was inside a sequence ?
    ------------------------------------------------------------
    canMerge :: Stmt a -> Bool
    ------------------------------------------------------------
    canMerge = \case
      Seq     {..} -> error "canMerge is called with a sequence of stmts"
      s            -> isSimple s

    isSimple = \case
      Skip    {..} -> True
      Assign  {..} -> True
      Assume  {..} -> True
      Assert  {..} -> True
      Par     {..} -> False
      Atomic  {..} -> False
      If      {..} -> False
      Cases   {..} -> False
      ForEach {..} -> False
      While   {..} -> False
      Seq     {..} -> False

fixAtomicPost :: Stmt a -> Stmt a
fixAtomicPost = go
  where
    go (Atomic {..})  = let ss = case atomicStmt of
                                   Seq { stmtData = a2
                                       , ..
                                       } -> seqStmts
                                   s -> [s]
                            (ps, ss') = atomicMerge ss
                            s' = case ss' of
                                   [stmt1] -> stmt1
                                   _       -> Seq { seqStmts = ss'
                                                  , ..
                                                  }
                        in  Atomic { atomicStmt = s'
                                   , atomicPost = simplifyProp $ And $ atomicPost:ps
                                   , ..
                                   }
    go (Skip {..})    = Skip {..}
    go (Par {..})     = Par {..}
    go (Assign {..})  = Assign {..}
    go (Seq {..})     = Seq { seqStmts = go <$> seqStmts
                            , ..
                            }
    go (Assume {..})  = Assume {..}
    go (Assert {..})  = Assert {..}
    go (If {..})      = If { thenStmt = go thenStmt
                           , elseStmt = go elseStmt
                           , ..
                           }
    go (Cases {..})   = Cases { caseList = h <$> caseList
                              , ..
                              }
      where
        h (Case {..}) = Case { caseStmt = go caseStmt
                             , ..
                             }
    go (ForEach {..}) = ForEach { forStmt = go forStmt
                                , ..
                                }
    go (While {..})   = While { whileStmt = go whileStmt
                              , ..
                              }

atomicMerge :: [Stmt a] -> ([Prop a], [Stmt a])
atomicMerge = go
  where
    go []     = ([],[])
    go (s:ss) = case s of
                  Assert {..} -> if   assertBool
                                 then (stmtProperty:ps', ss')
                                 else (ps', s:ss')
                  _ -> (ps', s:ss')
      where
        (ps', ss') = go ss


--------------------------------------------------------------------------------
-- given a symmetric set, a counter and a statement, returns the following:
-- 1. A map from program counters to statements
-- 2. initial program location (l_0)
-- 3. last program location (l_exit)
-- 4. control flow graph
--------------------------------------------------------------------------------
extractCFG :: (Show a, VCAnnot a) => Id -> Stmt a -> VCGen a (ActionResult a)
--------------------------------------------------------------------------------
extractCFG ps stmt = do
  atomizedStmt0 <- atomize stmt
  pcExit <- incrCounter
  let atomizedStmt = replaceHere ps atomizedStmt0
      g = G.mkUGraph nodes edges :: CFG
      nodes = IS.toList $
              foldl' (\s (n1,n2) -> IS.insert n1 (IS.insert n2 s)) IS.empty edges
      edges = go atomizedStmt ++
              [ (stmtPC p,pcExit) | p <- lastStmt atomizedStmt ]
  m <- createActionMap atomizedStmt
  return $ ActionResult { arMap    = m
                        , arPC0s   = stmtPC <$> firstStmt atomizedStmt
                        , arPCExit = pcExit
                        , arCFG    = g
                        , arStmt   = atomizedStmt
                        }
  where
    -- returns the CF edges within a statement
    go :: (Show a, VCAnnot a) => Stmt a -> [(Int, Int)]
    go (Seq {..}) = case seqStmts of
                      []       -> []
                      [s]      -> go s
                      s1:s2:ss ->
                        let s' = Seq { seqStmts = s2:ss, ..}
                        in go s1 ++
                           go s' ++
                           [ (stmtPC p1, stmtPC p2)
                           | p1 <- lastStmt s1
                           , p2 <- firstStmt s'
                           ]
    go (ForEach {..}) = go forStmt ++
                        [ (stmtPC p1, stmtPC p2)
                        | p1 <- lastStmt forStmt
                        , p2 <- firstStmt forStmt
                        ]
    go (While {..}) = go whileStmt ++
                      [ (stmtPC p1, stmtPC p2)
                      | p1 <- lastStmt whileStmt
                      , p2 <- firstStmt whileStmt
                      ]
    go (If {..})      = go thenStmt ++ go elseStmt
    go (Cases {..})   = (caseStmt <$> caseList) >>= go
    go (Atomic  {..}) = []
    go s@(Par     {..}) = error $ printf "extractCFG.go is called with a parallel composition !\n%s" (pretty s)
    go s@(Skip    {..}) = error $ printf "extractCFG.go is called with a skip !\n%s" (pretty s)
    go s@(Assert  {..}) = error $ printf "extractCFG.go is called with a assert !\n%s" (pretty s)
    go s@(Assume  {..}) = error $ printf "extractCFG.go is called with a assume !\n%s" (pretty s)
    go s@(Assign  {..}) = error $ printf "extractCFG.go is called with a assign !\n%s" (pretty s)

-- Returns the first statement(s) of a langugage construct, or the statement itself
firstStmt :: Show a => Stmt a -> [Stmt a]
firstStmt s@(Atomic  {..}) = [s]
firstStmt s@(ForEach {..}) = firstStmt forStmt
firstStmt s@(While   {..}) = firstStmt whileStmt
firstStmt s@(If      {..}) = firstStmt thenStmt ++ firstStmt elseStmt
firstStmt s@(Cases   {..}) = firstStmt =<< (caseStmt <$> caseList)
firstStmt s@(Seq     {..}) = case seqStmts of
                               []   -> error "firstStmt is called with an empty sequence"
                               s1:_ -> firstStmt s1
firstStmt s                = error $ printf "firstStmt called with %s" (show s)

-- Returns the last statement(s) of a langugage construct, or the statement itself
lastStmt :: Show a => Stmt a -> [Stmt a]
lastStmt s@(Atomic  {..}) = [s]
lastStmt s@(ForEach {..}) = lastStmt forStmt
lastStmt s@(While   {..}) = lastStmt whileStmt
lastStmt s@(If      {..}) = lastStmt thenStmt ++ lastStmt elseStmt
lastStmt s@(Cases   {..}) = lastStmt =<< (caseStmt <$> caseList)
lastStmt s@(Seq     {..}) = case seqStmts of
                              [] -> error "lastStmt is called with an empty sequence"
                              _  -> lastStmt $ last seqStmts
lastStmt s                = error $ printf "firstStmt called with %s" (show s)

-- creates a map from labeled statements
createActionMap :: VCAnnot a => Stmt a -> VCGen a (ActionMap a)
createActionMap rootStmt = do
  cleanup
  go rootStmt
  m <- gets actionMap
  cleanup
  return m

  where
    cleanup :: VCAnnot a => VCGen a ()
    cleanup = modify $
      \VCState {..} -> VCState { actionMap       = IM.empty
                               , actionStatePath = []
                               , actionForLoop   = Nothing
                               , actionProp      = TT
                               , ..
                               }

    go :: VCAnnot a => Stmt a -> VCGen a ()
    go (Atomic{..}) = do
      maybeLoop <- gets actionForLoop
      case maybeLoop of
        Just forLoop -> do
          let x  = forElement forLoop
              xs = forList forLoop
              d  = fst $ forInvariant forLoop
              w  = updatedVars $ forStmt forLoop
              y  = x : Bind d Set : [] -- : w
          oldProp <- gets actionProp
          -- FIXME: enable annot stuff ?
          -- newProp <- wlp atomicStmt oldProp
          modify $
            \VCState{..} ->
              -- FIXME: enable annot stuff ?
              -- let newProp' = And [ Atom SetMem (Var p) (Var ps)
              --                    | (p,ps) <- HM.toList unfoldedProcesses
              --                    ] :=>: newProp
              --     atomicPost' = Forall y $ And [atomicPost, newProp']
              let newProp' = oldProp
                  atomicPost' = atomicPost
                  a = Action { actionStmt      = Atomic { atomicPost = simplifyProp atomicPost'
                                                        , ..
                                                        }
                             , actionPath      = actionStatePath
                             , actionUnfolding = unfoldedProcesses
                             , actionTypeEnv   = typeEnv
                             }
                  -- a = trace (printf "action[%d] ::: %s" atomicLabel (show unfoldedProcesses)) _a
              in VCState{ actionMap = IM.insert atomicLabel a actionMap
                        , actionProp = newProp'
                        , ..
                        }
        Nothing -> do
          modify $
            \VCState{..} ->
              let a = Action { actionStmt      = Atomic { atomicPost = simplifyProp atomicPost
                                                        , ..
                                                        }
                             , actionPath      = actionStatePath
                             , actionUnfolding = unfoldedProcesses
                             , actionTypeEnv   = typeEnv
                             }
                  -- a = trace (printf "action[%d] ::: %s" atomicLabel (show unfoldedProcesses)) _a
              in VCState{ actionMap = IM.insert atomicLabel a actionMap
                        , ..
                        }

    go forLoop@(ForEach{..}) = do
      let x  = bvar forElement
          xs = bvar forList
      modify $ \VCState{..} -> VCState{ actionForLoop = Just forLoop
                                      , actionProp    = snd $ forInvariant
                                      , ..
                                      }
      withElem x xs $ withType (fst forInvariant) Set $
        go forStmt
      modify $ \VCState{..} -> VCState{ actionForLoop = Nothing
                                      , actionProp    = TT
                                      , ..
                                      }
        where
          y = updatedVars forLoop

    go (Seq {..}) = sequence_ $ go <$> reverse seqStmts

    go (If {..}) = do
      oldPath <- gets actionStatePath
      modify $ \VCState{..} -> VCState{ actionStatePath = ifCondition : oldPath , .. }
      go thenStmt
      modify $ \VCState{..} -> VCState{ actionStatePath = (Not ifCondition) : oldPath , .. }
      go elseStmt
      modify $ \VCState{..} -> VCState{ actionStatePath = oldPath , .. }

    go _ = error $ printf "createActionMap.go called with sth other than expected !"

-- merge stmt sequences
-- e.g. : (s1;s2);(s3;s4) becomes (s1;s2;s3;s4)
flattenSeq :: Stmt a -> Stmt a
flattenSeq s = case go s of
                 []   -> error "flattenSeq returned empty list"
                 [s'] -> s'
                 ss   -> Seq { seqStmts = ss
                             , stmtData = stmtData s
                             }
  where
    go :: Stmt a -> [Stmt a]
    go (Skip    {..}) = Skip {..} : []
    go (Assign  {..}) = Assign {..} : []
    go (Assume  {..}) = Assume {..} : []
    go (Assert  {..}) = Assert {..} : []
    go (Seq     {..}) = go =<< seqStmts
    go (Par     {..}) = Par { parStmt = flattenSeq parStmt
                            , ..
                            } : []
    go (Atomic  {..}) = Atomic { atomicStmt = flattenSeq atomicStmt
                               , ..
                               } : []
    go (If      {..}) = If { thenStmt = flattenSeq thenStmt
                           , elseStmt = flattenSeq elseStmt
                           , ..
                           } : []
    go (Cases   {..}) = Cases { caseList = (\Case{..} -> Case { caseStmt = flattenSeq caseStmt
                                                              , ..
                                                              }
                                           ) <$> caseList
                              , ..
                              } : []
    go (ForEach {..}) = ForEach { forStmt = flattenSeq forStmt
                                , ..
                                } : []
    go (While   {..}) = While { whileStmt = flattenSeq whileStmt
                              , ..
                              } : []

stmtPC :: Show a => Stmt a -> Int
stmtPC (Atomic {..}) = atomicLabel
stmtPC s             = error $ printf "stmtPC called with non-atomic value [[[%s]]] !" (pretty s)

replaceHere :: Id -> Stmt a -> Stmt a
replaceHere ps stmt = go undefined stmt
  where
    go :: Int -> Stmt a -> Stmt a
    go n (Seq {..}) =
      Seq { seqStmts = (go n) <$> seqStmts
          , ..
          }
    go n (ForEach {..}) =
      ForEach { forStmt      = go n forStmt
              , forInvariant = (d, goProp n i)
              , ..
              }
      where
        (d,i) = forInvariant
    go n (While {..}) =
      While { whileStmt = go n whileStmt
            , ..
            }
    go n (If {..}) =
      If { thenStmt = go n thenStmt
         , elseStmt = go n elseStmt
         , ..
         }
    go n (Cases {..}) =
      Cases { caseList = (
                \Case{..} -> Case { caseStmt = go n caseStmt
                                  , ..
                                  }
                ) <$> caseList
            , ..
            }
    go n (Atomic {..}) =
      Atomic { atomicStmt = go atomicLabel atomicStmt
             , atomicPost = goProp atomicLabel atomicPost
             , ..
             }
    go n (Assume {..}) =
      Assume { stmtProperty = goProp n stmtProperty
             , ..
             }
    go n (Assert {..}) =
      Assert { stmtProperty = goProp n stmtProperty
             , ..
             }
    go _ (Assign {..}) = Assign {..}
    go _ (Skip {..}) = Skip {..}
    go _ s = error $ printf "replaceHere.go is called with an unsupported stmt:\n%s" (pretty s)

    goProp n (Here e)      = Atom Eq (Select (Var (pcName ps)) e) (Const n)
    goProp n (Forall xs a) = Forall xs $ goProp n a
    goProp n (a :=>: b)    = goProp n a :=>: goProp n b
    goProp n (And as)      = And (goProp n <$> as)
    goProp n (Or as)       = Or (goProp n <$> as)
    goProp n (Not a)       = Not $ goProp n a
    goProp n a             = a





-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- HELPER FUNCTIONS
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

freshBinder :: Binder -> VCGen a Binder
freshBinder (Bind x _) = do
  i <- incrCounter
  t <- getType x
  let var = (x ++ "!" ++ show i)
  let b' = Bind var t
  return b'

incrCounter :: VCGen a Int
incrCounter = do
  n <- gets freshCounter
  modify $
    \VCState{..} -> VCState { freshCounter = n + 1
                            , ..
                            }
  return n

getType :: Id -> VCGen a Sort
getType x = do
  te <- gets typeEnv
  case HM.lookup x te of
    Just t  -> return t
    Nothing -> error (printf "Unknown id: %s" x)

insertType :: Id -> Sort -> VCGen a Bool
insertType v t =
  if v /= "_"
    then do
    VCState{..} <- get
    case HM.lookup v typeEnv of
      Nothing -> do put VCState { typeEnv = HM.insert v t typeEnv
                                , ..
                                }
                    return True
      Just s -> if s == t
                then return False 
                else error "insertType: Trying to update a var with a different type"
    else
    return False

withType :: Id -> Sort -> VCGen a r -> VCGen a r 
withType v t act = do
  c <- insertType v t
  r <- act
  when c removeType
  return r
  where
    removeType :: VCGen a ()
    removeType = do
      VCState{..} <- get
      case HM.lookup v typeEnv of
        Just s -> if s == t
                  then put VCState { typeEnv = HM.delete v typeEnv
                                   , ..
                                   }
                  else error "insertType: Trying to delete a var with a different existing type"
        Nothing -> error "insertType: Trying to delete missing var"

isSet :: Id -> VCGen a Bool
isSet i = do
  m <- gets unfoldedProcesses
  return $ HM.member i m

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM mb t e = do
  b <- mb
  if b then t else e

isIndex :: Sort -> Id -> VCGen a Bool
isIndex (Map (SetIdx ps) _) p = isElem p ps
isIndex _ _                   = return False

isElem :: Id -> Id -> VCGen a Bool
isElem p ps = do
  g <- gets unfoldedProcesses
  return $ maybe False (== ps) $ HM.lookup p g

withElem :: Id -> Id -> VCGen a r ->  VCGen a r
withElem p ps act = withType p Int $ do
  c <- addElem
  r <- act
  when c removeElem
  return r

  where
    -- returns whether the addition was successful or not
    addElem :: VCGen a Bool
    addElem = do
      VCState{..} <- get
      if (p /= "_")
        then
        case HM.lookup p unfoldedProcesses of
          Nothing -> do
            put $ VCState { unfoldedProcesses = HM.insert p ps unfoldedProcesses
                          , ..
                          }
            -- return $ trace msg True
            return True
          Just ps' ->
            if   ps' == ps
            then return False
            else error $ printf "adding %s \\in %s is weird !!!" p ps
        else
        return False
      where
        msg :: String
        msg = printf "adding %s \\in %s" p ps
    
    removeElem :: VCGen a ()
    removeElem = do
      VCState {..} <- get
      case HM.lookup p unfoldedProcesses of
        Just _ -> do
          let st' = VCState { unfoldedProcesses = HM.delete p unfoldedProcesses
                            , ..
                            }
          -- put $ trace msg st'
          put st'
        _ -> error $ printf "%s does not exist in unfoldedProcesses or typeEnv !!!" p
      where
        msg :: String
        msg = printf "removing %s \\in %s" p ps

updatedVars :: Stmt a -> [Binder]
updatedVars = filter (\(Bind v _) -> v /= "_") . nub . go
  where
    go (Skip {..})    = []
    go (If {..})      = go thenStmt ++ go elseStmt
    go (Atomic {..})  = go atomicStmt
    go (Assign {..})  = [assignVar]
    go (Seq {..})     = seqStmts >>= go
    go (ForEach {..}) = forElement : Bind (fst forInvariant) Set : go forStmt
    go (While {..})   = go whileStmt
    go (Cases {..})   = caseList >>= go . caseStmt
    go (Par {..})     = go parStmt
    go (Assert {..})  = []
    go (Assume {..})  = []

makeTypeEnv :: [Binder] -> HM.HashMap Id Sort
makeTypeEnv bs = HM.fromList [ (x,t) | Bind x t <- bs ]

-- some variables are parsed with the default type (i.e. Int)
-- update the binds with the correct ones from the type environment
updateTypes :: TypeEnv -> Stmt a -> Stmt a
updateTypes tenv s = go s
  where
    go (Skip {..})    = Skip {..}
    go (If {..})      = If { thenStmt = go thenStmt
                           , elseStmt = go elseStmt
                           , ..
                           }
    go (Atomic {..})  = Atomic { atomicStmt = go atomicStmt
                               , ..
                               }
    go (Assign {..})  = Assign { assignVar = updateVar assignVar
                               , ..
                               }
    go (Seq {..})     = Seq { seqStmts = go <$> seqStmts
                            , ..
                            }
    go (ForEach {..}) = ForEach { forStmt = go forStmt
                                , ..
                                }
    go (While {..})   = While { whileStmt = go whileStmt
                              ,  ..
                              }
    go (Cases {..})   = Cases { caseList = (
                                  \Case{..} -> Case { caseStmt = go caseStmt
                                                    , ..
                                                    }
                                  ) <$> caseList
                              , ..
                              }
    go (Par {..})     = Par { parStmt = go parStmt
                            , ..
                            }
    go (Assert {..})  = Assert {..}
    go (Assume {..})  = Assume {..}

    updateVar b@(Bind v t) =
      case HM.lookup v tenv of
        Nothing   -> b
        Just sort -> Bind v sort


simplifyProp :: Prop a -> Prop a
simplifyProp (And ps) = if   elem FF ps''
                        then FF
                        else case ps'' of
                               []  -> TT
                               [p] -> p
                               _   -> And ps''
  where
    ps'  = simplifyProp <$> ps
    ps'' = filter (/= TT) ps'
simplifyProp (Or ps) = if   elem TT ps''
                       then TT
                       else case ps'' of
                              []  -> FF
                              [p] -> p
                              _   -> Or ps''
  where
    ps'  = simplifyProp <$> ps
    ps'' = filter (/= FF) ps'
simplifyProp (Not p) = case p' of
                         TT     -> FF
                         FF     -> TT
                         Not p2 -> p2
                         _      -> Not p'
  where
    p' = simplifyProp p
simplifyProp (a :=>: b) = case (a', b') of
                            (TT, _) -> b'
                            (FF, _) -> TT
                            (_, TT) -> TT
                            (_, FF) -> Not a'
                            _       -> a' :=>: b'
  where
    a' = simplifyProp a
    b' = simplifyProp b
simplifyProp p0@(Forall bs p) = case p'' of
                                  TT -> TT
                                  FF -> FF
                                  _  -> Forall bs' p''
  where
    (bs', p'') = case p' of
                   Forall bs2 p2 -> (nub $ bs ++ bs2, p2) 
                   _             -> (bs, p')
    p' = simplifyProp p
simplifyProp (Exists bs p)  = Exists bs $ simplifyProp p
simplifyProp (Let bs p)     = Let bs $ simplifyProp p
simplifyProp (Atom r e1 e2) = Atom r (simplifyExpr e1) (simplifyExpr e2)
simplifyProp (Here e)       = Here (simplifyExpr e)
simplifyProp (Prop e)       = case e' of
                                PExpr p -> p
                                _       -> Prop e'
  where
    e' = simplifyExpr e
simplifyProp TT = TT
simplifyProp FF = FF
simplifyProp (PVar v) = PVar v
simplifyProp NonDetProp = NonDetProp


simplifyExpr :: Expr a -> Expr a
simplifyExpr = go
  where
    go (PExpr p)     = case p' of
                         Prop e -> e
                         _      -> PExpr p'
      where
        p' = simplifyProp p
    go (Select a i)  = Select (go a) (go i)
    go (Store a i e) = Store (go a) (go i) (go e)
    go (Size e)      = Size (go e)
    go (Ite p th el) = case p' of
                         TT -> (go th)
                         FF -> (go el)
                         _  -> Ite p' (go th) (go el)
      where
        p' = simplifyProp p
    go (Bin o e1 e2) = Bin o (go e1) (go e2)
    go (Const i)     = Const i
    go EmptySet      = EmptySet
    go NonDetValue   = NonDetValue
    go (Var v)       = Var v
