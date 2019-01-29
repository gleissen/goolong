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

type TypeEnv a = HM.HashMap Id Sort
data VCState a = VCState { freshCounter       :: Int
                         , typeEnv            :: TypeEnv a
                         , unfoldedProcesses  :: HM.HashMap Id Id -- p -> ps
                         , parallelProcesses  :: HS.HashSet Id    -- symmetric sets we have seen so far

                         , actionMap          :: ActionMap a   -- map from action labels to actions
                         , actionStatePath    :: ActionPath a  -- path conditions of the actions

                         , actionInForLoop    :: Bool          -- used to check whether in for loop or not
                         , actionProp         :: Prop a        -- used for integrating loop invariants actions
                         }

type VCGen a r = State (VCState a) r

verifyProgram :: String -> IO Bool
verifyProgram = verify . parseString

verifyFile :: FilePath -> IO Bool
verifyFile fp = do
  program <- parseFile fp
  verify program

-------------------------------------------------------------------------------
verify :: ParsedProgram -> IO Bool
-------------------------------------------------------------------------------
verify (Program{..}) = do
  writeFile ".query.smt2" vcstr

  (inp, out, err, pid) <- runInteractiveProcess "z3" ["-smt2", ".query.smt2"] Nothing Nothing
  ec   <- waitForProcess pid
  outp <- hGetContents out
  errp <- hGetContents err

  putStrLn outp
  hPutStr stderr errp

  case ec of
    ExitSuccess   -> return ("unsat" `isInfixOf` outp)
    ExitFailure _ -> return False

  where
    vcstr = createSMTQuery decls' pss vc

    (vc, lastState) = runState action initialState
    initialState = VCState { freshCounter       = 0
                           , typeEnv            = tenv
                           , unfoldedProcesses  = HM.empty
                           , parallelProcesses  = HS.empty
                           , actionMap          = IM.empty
                           , actionStatePath    = []
                           , actionProp         = TT
                           , actionInForLoop    = False
                           }
    tenv   = makeTypeEnv decls
    decls' = fmap (uncurry Bind) . HM.toList $ typeEnv lastState
    action = wlp prog' ensures
    prog'  = updateTypes tenv prog
    pss    = HS.toList $ parallelProcesses lastState

-------------------------------------------------------------------------------
wlp :: VCAnnot a => Stmt a -> Prop a -> VCGen a (Prop a)
-------------------------------------------------------------------------------
wlp (Skip {..}) q = return q

wlp (Assign {assignExpr = NonDetValue, ..}) q = do
  v' <- freshBinder assignVar
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
  return $
    case t of
      Map _ _ -> subst v (Store (Var v) (Var p) e') q
      _       -> subst v e' q
  where
    p  = stmtProcess
    p' = assignFromProcess
    e  = assignExpr
    v  = bvar assignVar

wlp (Assume {..}) q = return $ stmtProperty :=>: q

wlp (Assert {..}) q = return $ And [stmtProperty, q]

wlp (Atomic {..}) q = do
  p <- wlp atomicStmt q
  return $ And [ atomicPost, p ]

wlp (Seq {..}) q = foldM f q (reverse seqStmts)
  where
    f q' s = wlp s q'

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

wlp (ForEach {..}) q = do
  addSuccess <- addElem x xs
  pre <- wlp forStmt q'
  let inv1 = subst done EmptySet inv
      inv2 = Forall y $
             And [ inv
                 , Atom SetMem ex exs
                 , Not $ Atom SetMem ex edone
                 ] :=>:
             pre
      inv3 = Forall y $ (subst done exs inv) :=>: q
  when addSuccess $ removeElem x xs
  return $ And [inv1, inv2, inv3]
  where
    q'          = subst done (Bin SetAdd edone ex) inv
    edone       = Var done
    x           = bvar forElement
    xs          = bvar forList
    ex          = Var x
    exs         = Var xs
    (done, inv) = forInvariant
    y           = forElement : Bind done Set : updatedVars forStmt

wlp (While {..}) q = undefined

wlp (Par {..}) q = do
  addSuccess <- addElem stmtProcess stmtProcessSet
  VCState{..} <- get
  ActionResult{ arMap    = m
              , arCFG    = g
              , arPC0    = pc0
              , arPCExit = pcExit
              , arStmt   = atomizedStmt
              } <- extractCFG stmtProcessSet parStmt
  put VCState { parallelProcesses = HS.insert stmtProcessSet parallelProcesses
              , ..
              }
  traceM (pretty atomizedStmt)
  let i = Forall [Bind stmtProcess Int] $
          And [ And [ Atom SetMem varP varPs
                    , Atom Eq (pc ps p) (Const l)
                    ]
                :=>:
                let posts = [ let la' = m IM.! l'
                              in atomicPost $ actionStmt la'
                            | l' <- G.pre g l
                            , l' /= pc0 && l' /= pcExit
                            ]
                in case posts of
                     [] -> TT
                     _  -> Or posts
              | (l, la) <- IM.toList m
              ]
      invInit = ( Forall [Bind stmtProcess Int] $
                  And [ Atom SetMem varP varPs
                      , Atom Eq (Select varPC varP) (Const pc0)
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
                  let _stmt' = subst p varP0 (atomicStmt $ actionStmt la)
                      q'    = subst (pcName ps) varPC' i
                      stmt' = trace (printf "[[[action %d\n%s]]]" la_pc (pretty _stmt')) _stmt'
                  c <- addElem p ps
                  c0 <- addElem p0 ps
                  prop <- wlp stmt' q'
                  when c $ removeElem p ps
                  when c0 $ removeElem p0 ps
                  return (la_pc, la, prop)
              ) <$> (IM.toList m)
  let invStep = Forall (Bind p0 Int : y) $
                Atom SetMem varP0 varPs
                :=>:
                And [ And [i, cf l] :=>: w
                    | (l, _, w) <- conjunts
                    ]
  when addSuccess $ removeElem stmtProcess stmtProcessSet
  return $ And [ invInit
               , invStep
               , invExit
               ]

  where
    y = Bind (pcName stmtProcessSet) pcType :
        Bind (pcName' stmtProcessSet) pcType :
        updatedVars parStmt
    p0 = stmtProcess ++ "0"
    p  = stmtProcess
    ps = stmtProcessSet
    varP   = Var p
    varPs  = Var ps
    varP0  = Var p0
    varPC  = Var $ pcName ps
    varPC' = Var $ pcName' ps





-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- ACTIONS
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

data Action a = Action { actionStmt      :: Stmt a        -- this is the atomic action
                       , actionPath      :: ActionPath a  -- path condition (i.e. if stmt conditions)
                       , actionUnfolding :: HM.HashMap Id Id
                       }

data ActionResult a = ActionResult { arMap    :: ActionMap a
                                   , arPC0    :: Int
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
          (p', s') = mergeHelper ss
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
          let (ps, ss') = mergeHelper [s]
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
      let (ps, ss') = mergeHelper ss
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
    mergeHelper :: [Stmt a] -> ([Prop a], [Stmt a])
    ------------------------------------------------------------
    mergeHelper ss = (ps', ss')
      where
        ps' = case ps of
                [] -> [TT]
                _  -> ps
        (ps, ss') = _mergeHelper ss

    _mergeHelper []     = ([],[])
    _mergeHelper (s:ss) = case s of
                          Assert {..} -> if   assertBool
                                         then (stmtProperty:ps', ss')
                                         else (ps', s:ss')
                          _ -> (ps', s:ss')
      where
        (ps', ss') = mergeHelper ss

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
  pc0 <- incrCounter
  atomizedStmt0 <- atomize stmt
  pcExit <- incrCounter
  let atomizedStmt = replaceHere ps atomizedStmt0
      g :: CFG
      g = G.mkUGraph nodes edges
      nodes = IS.toList $
              foldl' (\s (n1,n2) -> IS.insert n1 (IS.insert n2 s)) IS.empty edges
      edges = go atomizedStmt ++
              [ (pc0, stmtPC p)   | p <- firstStmt atomizedStmt ] ++
              [ (stmtPC p,pcExit) | p <- lastStmt atomizedStmt ]
  m <- createActionMap atomizedStmt
  return $ ActionResult { arMap    = m
                        , arPC0    = pc0
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
      \VCState {..} -> VCState { actionMap          = IM.empty
                               , actionStatePath    = []
                               , actionProp         = TT
                               , ..
                               }

    go :: VCAnnot a => Stmt a -> VCGen a ()
    go (Atomic{..}) = do
      inLoop <- gets actionInForLoop
      if inLoop
        then do oldProp <- gets actionProp
                newProp <- wlp atomicStmt oldProp
                modify $
                  \VCState{..} ->
                    let a = Action { actionStmt      = Atomic { atomicPost = And [atomicPost, oldProp]
                                                              , ..
                                                              }
                                   , actionPath      = actionStatePath
                                   , actionUnfolding = unfoldedProcesses
                                   }
                    in VCState{ actionMap = IM.insert atomicLabel a actionMap
                              , actionProp = newProp
                              , ..
                              }
        else do modify $
                  \VCState{..} ->
                    let a = Action { actionStmt      = Atomic {..}
                                   , actionPath      = actionStatePath
                                   , actionUnfolding = unfoldedProcesses
                                   }
                    in VCState{ actionMap = IM.insert atomicLabel a actionMap
                              , ..
                              }

    go (ForEach{..}) = do
      let x  = bvar forElement
          xs = bvar forList
      modify $ \VCState{..} -> VCState{ actionInForLoop = True
                                      , actionProp      = snd $ forInvariant
                                      , ..
                                      }
      c <- addElem x xs
      go forStmt
      when c $ removeElem x xs
      modify $ \VCState{..} -> VCState{ actionInForLoop = False
                                      , actionProp      = TT
                                      , ..
                                      }

    go (Seq {..}) = sequence_ $ go <$> reverse seqStmts

    go (If {..}) = do
      oldPath <- gets actionStatePath
      modify $ \VCState{..} -> VCState{ actionStatePath = ifCondition : oldPath , .. }
      go thenStmt
      modify $ \VCState{..} -> VCState{ actionStatePath = (Not ifCondition) : oldPath , .. }
      go elseStmt
      modify $ \VCState{..} -> VCState{ actionStatePath = oldPath , .. }

    go _ = error $ printf "createActionMap.go called with sth other than expected !"

    -- go s =
    --   case s of
        -- While   {..} -> go whileStmt
        -- Cases   {..} -> gos $ caseStmt <$> caseList
      -- where
      --   gos ss = foldl' go m ss

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

-- inserts the type and returns the previous state
insertType :: Id -> Sort -> VCGen a (VCState a)
insertType v t = do
  currentState@VCState{..} <- get
  put VCState { typeEnv = HM.insert v t typeEnv
              , ..
              }
  return currentState

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

-- returns whether the addition was successful or not
addElem :: Id -> Id -> VCGen a Bool
addElem p ps = do
  VCState{..} <- get
  case (HM.lookup p unfoldedProcesses, HM.lookup p typeEnv) of
    (Nothing, Nothing) -> do
      put $ VCState { unfoldedProcesses = HM.insert p ps unfoldedProcesses
                    , typeEnv           = HM.insert p Int typeEnv
                    , ..
                    }
      return $ trace msg True
    (Just ps', Just sort) ->
      if   ps' == ps && sort == Int
      then return False
      else error $ printf "adding %s \\in %s is weird !!!" p ps
    _ -> error $ printf "adding %s \\in %s is weird !!!" p ps
  where
    msg :: String
    msg = printf "adding %s \\in %s" p ps

removeElem :: Id -> Id -> VCGen a ()
removeElem p ps = do
  VCState {..} <- get
  case (HM.lookup p unfoldedProcesses, HM.lookup p typeEnv) of
    (Just _, Just _) -> do
      let st' = VCState { unfoldedProcesses = HM.delete p unfoldedProcesses
                        , typeEnv           = HM.delete p typeEnv
                        , ..
                        }
      put $ trace msg st'
    _ -> error $ printf "%s does not exist in unfoldedProcesses or typeEnv !!!" p
  where
    msg :: String
    msg = printf "removing %s \\in %s" p ps

updatedVars :: Stmt a -> [Binder]
updatedVars = nub . go
  where
    go (Skip {..})    = []
    go (If {..})      = go thenStmt ++ go elseStmt
    go (Atomic {..})  = go atomicStmt
    go (Assign {..})  = [assignVar]
    go (Seq {..})     = seqStmts >>= go
    go (ForEach {..}) = forElement : go forStmt
    go (While {..})   = go whileStmt
    go (Cases {..})   = caseList >>= go . caseStmt
    go (Par {..})     = go parStmt
    go (Assert {..})  = []
    go (Assume {..})  = []

makeTypeEnv :: [Binder] -> HM.HashMap Id Sort
makeTypeEnv bs = HM.fromList [ (x,t) | Bind x t <- bs ]

-- some variables are parsed with the default type (i.e. Int)
-- update the binds with the correct ones from the type environment
updateTypes :: TypeEnv a -> Stmt a -> Stmt a
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
