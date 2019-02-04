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
import           System.Process
import           Text.Printf

import Language.IceT.Pretty
-- import Debug.Trace





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
                         , actionMap     :: ActionMap a    -- map from action labels to actions
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
-- given a program, writes the verification conditions into a file
writeSMT :: ParsedProgram -> IO ()
-------------------------------------------------------------------------------
writeSMT (Program{..}) = do
  writeFile smtFilename vcstr
  debugM $ printf "Wrote smt2 file to %s\n" smtFilename

  where
    vcstr  = createSMTQuery decls' pss vc
    decls' = fmap (uncurry Bind) . HM.toList $ typeEnv lastState -- type declarations
    pss    = HS.toList $ parallelProcesses lastState             -- parallel processes

    (vc, lastState) = runState action initialState
    tenv            = makeTypeEnv decls
    initialState    = VCState { freshCounter       = 0
                              , typeEnv            = tenv
                              , unfoldedProcesses  = HM.empty
                              , parallelProcesses  = HS.empty
                              , actionMap          = IM.empty
                              }

    preProcess  = fixAtomicPost . updateTypes tenv
    postProcess = simplifyProp
    action      = postProcess <$> wlp (preProcess prog) ensures

smtFilename :: String
smtFilename = ".query.smt2"

-------------------------------------------------------------------------------
-- checks the verification conditions using Z3
verify :: ParsedProgram -> IO Bool
-------------------------------------------------------------------------------
verify p = do
  writeSMT p

  (inp, out, err, pid) <- runInteractiveProcess "z3" ["-smt2", smtFilename] Nothing Nothing
  ec   <- waitForProcess pid
  outp <- hGetContents out
  errp <- hGetContents err

  debugM outp
  debugM errp

  case ec of
    ExitSuccess   -> return ("unsat" `isInfixOf` outp)
    ExitFailure _ -> return False


-------------------------------------------------------------------------------
-- computes the weakest liberal precondition of a given statement
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
          -- (this is probably due how we parse assignment between pairs ...)
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
  let result = (Atom Eq (Var v') e'') :=>: (subst v (Var v') q)
  return result

  where
    p  = stmtProcess
    p' = assignFromProcess
    e  = assignExpr
    v  = bvar assignVar
    v' = v ++ "!1"

wlp (Assume {..}) q = return $ stmtProperty :=>: q

wlp (Assert {..}) q = return $ And [stmtProperty, q]

-- strengthen the precondition with the atomic block's post condition
-- i.e. wlp(< stmt :: P >, Q) = wlp(stmt, P) /\ wlp(stmt, Q)
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
                      ] :=>: pre
        invExit = Forall y $ (subst done exs inv) :=>: q -- invariant holds when done = xs
        result = And [ invInit
                     , invStep
                     , invExit
                     ]
    return result

  where
    q'    = subst done (Bin SetAdd edone ex) inv -- I[done U {x}/done]
    edone = Var done
    x     = bvar forElement
    xs    = bvar forList
    ex    = Var x
    exs   = Var xs
    done  = fst forInvariant
    y     = updatedVars stmt
    -- If the for loop contains an atomic statement,
    -- then pull the post condition into the loop invariant
    -- (since that is where the invariant ends up in this case)
    inv   = let rest = case forStmt of
                         Atomic { stmtData = a2, ..} -> [atomicPost]
                         _                           -> []
            in And $ (snd forInvariant):rest

wlp (Par {..}) q = do
  withElem stmtProcess stmtProcessSet $ do
    VCState{..} <- get
    -- compute the atomic actions inside this parallel loop, and
    -- generate the control flow graph
    ActionResult{ arMap    = m
                , arCFG    = g
                , arPC0s   = pc0s
                , arPCExit = pcExit
                , arStmt   = atomizedStmt
                } <- extractCFG stmtProcessSet parStmt
    -- update the state the include the id of the current set of parallel processes
    put VCState { parallelProcesses = HS.insert stmtProcessSet parallelProcesses
                , ..
                }
    debugM (pretty atomizedStmt)

    -- I = forall p \in ps. pc[p] = l -> P1 \/ P2 \/ ...
    -- where P1, P2, .. are the post conditions of the atomic blocks
    -- that are the immediate predecessors of l
    let i = Forall [Bind stmtProcess Int] $
            And [ And [ Atom SetMem varP varPs
                      , Atom Eq (pc ps p) (Const l)
                      ]
                  :=>:
                  let pres = [ let la' = m IM.! l'
                               in  atomicPost $ actionStmt la'
                             | l' <- G.pre g l
                             ]
                  in case pres of
                       [] -> TT
                       _  -> Or pres
                | l <- pcExit : IM.keys m
                ]
    debugM $ printf "I: %s\n\n" (pretty $ simplifyProp i)
    -- initially, I holds
    let invInit = ( Forall [Bind stmtProcess Int] $
                    And [ Atom SetMem varP varPs
                        , Or [ Atom Eq (Select varPC varP) (Const pc0)
                             | pc0 <- pc0s
                             ]
                        ]
                  ) :=>: i
        -- when everyone is at pc_exit and I holds, Q must hold
        invExit = Forall y $
                  And [ Forall [Bind stmtProcess Int] $
                        And [ Atom SetMem varP varPs
                            , Atom Eq (Select varPC varP) (Const pcExit)
                            ]
                      , i
                      ] :=>: q
        -- p0 is the one that is making the transition ...
        -- cf l returns the labels that l can transition into
        cf l = And [ Atom Eq (pc ps p0) (Const l)
                   , Or [ Atom Eq varPC' (Store varPC varP0 (Const l'))
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
    -- if I holds and p0 makes a transition,
    -- (i.e. from < a1 :: P1 > to < a2 :: P2 >)
    -- then the wlp(a1[p0/p], I[pc'/pc]) should hold
    -- pc' is defined in the function "cf" above
    let invStep = Forall (Bind p0 Int : y ++ [ Bind pp Int | pp <- HS.toList idxs]) $
                  And [ And [ i
                            , cf l
                            , Atom SetMem varP0 varPs
                            , Atom SetMem varP  varPs
                            ] :=>: w
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

    -- run an action, in an updated type environment and set of unfolded processes
    -- we keep the new type environment, otherwise we get undefined variable errors !
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
      modify $ \VCState{..} -> VCState{ unfoldedProcesses = oldUnfoldings
                                      , ..
                                      }
      return result

-- while is not implemented :(
wlp (While {..}) q = undefined





-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- ACTIONS
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

data Action a = Action { actionStmt        :: Stmt a           -- this is the atomic action
                       , actionUnfolding   :: HM.HashMap Id Id -- loop unfoldings we have in this action
                       , actionTypeEnv     :: TypeEnv          -- extra type information we have in this action
                       }

data ActionResult a = ActionResult { arMap    :: ActionMap a -- a map from action labels to actions
                                   , arPC0s   :: [Int]       -- set of initial actions (i.e. roots of the graph)
                                   , arPCExit :: Int         -- exit label
                                   , arCFG    :: CFG         -- control flow graph of the actions

                                   -- stmt that was inside parallel loop after atomization
                                   -- this is for debugging purposes
                                   , arStmt   :: Stmt a
                                   }

type ActionPath a  = [ Prop a ]
type ActionTypeEnv = HM.HashMap Id Sort
type ActionMap a   = IM.IntMap (Action a)
type CFG           = UGr

--------------------------------------------------------------------------------
-- Merge local statements together to create a program consists of only atomic
-- actions to be used for generating the verification conditions for the
-- parallel case.
-- This stateful computation only increments the fresh counter variable, that we
-- need for fresh labels.
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
      t' <- go $ appendStmt (Assume ifCondition stmtData) thenStmt
      e' <- go $ appendStmt (Assume (Not ifCondition) stmtData) elseStmt
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
    -- first partition, then merge to create the atomic blocks
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
                   if   canMerge lh && canMerge s'
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

--------------------------------------------------------------------------------
-- pull the formulas inside the "pre" statements inside the atomic blocks into
-- the post condition of the block
fixAtomicPost :: Stmt a -> Stmt a
--------------------------------------------------------------------------------
fixAtomicPost = go
  where
    go (Atomic {..})  = let ss = case atomicStmt of
                                   Seq { stmtData = a2, ..} -> seqStmts
                                   s                        -> [s]
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

--------------------------------------------------------------------------------
-- helper function for atomize and fixAtomicPost
-- partitions a list of statements into formulas that occur in "pre" and the rest
-- of the statements
atomicMerge :: [Stmt a] -> ([Prop a], [Stmt a])
--------------------------------------------------------------------------------
atomicMerge stmts = case go stmts of
                      ([],stmts') -> ([TT], stmts')
                      res         -> res
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
-- 2. initial program locations
-- 3. last program location (l_exit)
-- 4. control flow graph
--------------------------------------------------------------------------------
extractCFG :: (Show a, VCAnnot a) => Id -> Stmt a -> VCGen a (ActionResult a)
--------------------------------------------------------------------------------
extractCFG ps stmt = do
  atomizedStmt <- replaceHere ps <$> atomize stmt
  pcExit <- incrCounter
  let g = G.mkUGraph nodes edges :: CFG
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
    -- returns the control flow edges **within** a statement
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
    -- since our program should only consist of atomic blocks by now, the following throw an error
    go s@(Par     {..}) = error $ printf "extractCFG.go is called with a parallel composition !\n%s" (pretty s)
    go s@(Skip    {..}) = error $ printf "extractCFG.go is called with a skip !\n%s" (pretty s)
    go s@(Assert  {..}) = error $ printf "extractCFG.go is called with a assert !\n%s" (pretty s)
    go s@(Assume  {..}) = error $ printf "extractCFG.go is called with a assume !\n%s" (pretty s)
    go s@(Assign  {..}) = error $ printf "extractCFG.go is called with a assign !\n%s" (pretty s)

--------------------------------------------------------------------------------
-- Returns the first statement(s) of a statement
-- e.g. for a sequence "if(..){s1}else{s2}; s3; ...", the output is [s1, s2]
firstStmt :: Show a => Stmt a -> [Stmt a]
--------------------------------------------------------------------------------
firstStmt s@(Atomic  {..}) = [s]
firstStmt s@(ForEach {..}) = firstStmt forStmt
firstStmt s@(While   {..}) = firstStmt whileStmt
firstStmt s@(If      {..}) = firstStmt thenStmt ++ firstStmt elseStmt
firstStmt s@(Cases   {..}) = firstStmt =<< (caseStmt <$> caseList)
firstStmt s@(Seq     {..}) = case seqStmts of
                               []   -> error "firstStmt is called with an empty sequence"
                               s1:_ -> firstStmt s1
firstStmt s                = error $ printf "firstStmt called with %s" (show s)

--------------------------------------------------------------------------------
-- Returns the last statement(s) of a statement
lastStmt :: Show a => Stmt a -> [Stmt a]
--------------------------------------------------------------------------------
lastStmt s@(Atomic  {..}) = [s]
lastStmt s@(ForEach {..}) = lastStmt forStmt
lastStmt s@(While   {..}) = lastStmt whileStmt
lastStmt s@(If      {..}) = lastStmt thenStmt ++ lastStmt elseStmt
lastStmt s@(Cases   {..}) = lastStmt =<< (caseStmt <$> caseList)
lastStmt s@(Seq     {..}) = case seqStmts of
                              [] -> error "lastStmt is called with an empty sequence"
                              _  -> lastStmt $ last seqStmts
lastStmt s                = error $ printf "firstStmt called with %s" (show s)

--------------------------------------------------------------------------------
-- creates a map from labeled statements
createActionMap :: VCAnnot a => Stmt a -> VCGen a (ActionMap a)
--------------------------------------------------------------------------------
createActionMap rootStmt = do
  cleanup
  go rootStmt
  m <- gets actionMap
  cleanup
  return m

  where
    cleanup :: VCAnnot a => VCGen a ()
    cleanup = modify $
      \VCState {..} -> VCState { actionMap = IM.empty
                               , ..
                               }

    go :: VCAnnot a => Stmt a -> VCGen a ()
    go (Atomic{..}) = do
      modify $
        \VCState{..} ->
          let a = Action { actionStmt      = Atomic { atomicPost = simplifyProp atomicPost
                                                    , ..
                                                    }
                         , actionUnfolding = unfoldedProcesses
                         , actionTypeEnv   = typeEnv
                         }
          in VCState{ actionMap = IM.insert atomicLabel a actionMap
                    , ..
                    }

    go forLoop@(ForEach{..}) = do
      withElem x xs $
        withType (fst forInvariant) Set $
        go forStmt

        where
          y = updatedVars forLoop
          x  = bvar forElement
          xs = bvar forList

    go (Seq {..}) = sequence_ $ go <$> reverse seqStmts

    go (If {..}) = go thenStmt >> go elseStmt

    go _ = error $ printf "createActionMap.go called with sth other than expected !"

stmtPC :: Show a => Stmt a -> Int
stmtPC (Atomic {..}) = atomicLabel
stmtPC s             = error $ printf "stmtPC called with non-atomic statement [[[%s]]] !" (pretty s)

-- replace here(p) with pc[p] = l, if that occurs inside an atomic block with label l
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

-- run an action with a (v:t) variable-type mapping in the state
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

-- check if the id belongs to a symmetric set
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

-- is p \in ps ?
isElem :: Id -> Id -> VCGen a Bool
isElem p ps = do
  g <- gets unfoldedProcesses
  return $ maybe False (== ps) $ HM.lookup p g

-- run an action with (p \in ps) stored in the state
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
            -- return $ debug msg True
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
          -- put $ debug msg st'
          put st'
        _ -> error $ printf "%s does not exist in unfoldedProcesses or typeEnv !!!" p
      where
        msg :: String
        msg = printf "removing %s \\in %s" p ps

-- returns the bindings that might be updated in the given statement
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

-------------------------------------------------------------------------------
-- apply some rewriting to simplify the given formula
simplifyProp :: Prop a -> Prop a
-------------------------------------------------------------------------------
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


-------------------------------------------------------------------------------
simplifyExpr :: Expr a -> Expr a
-------------------------------------------------------------------------------
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

-- append given two statements together
appendStmt :: Stmt a -> Stmt a -> Stmt a
appendStmt s1 s2 = Seq { seqStmts = toSS s1 ++ toSS s2
                       , stmtData = stmtData s1
                       }
  where
    toSS (Seq ss _) = ss
    toSS s          = [s]

debug :: String -> a -> a
-- debug = trace
debug _ a = a

debugM :: Applicative f => String -> f ()
-- debugM = traceM
debugM _ = pure ()
