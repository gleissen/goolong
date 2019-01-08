{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ConstraintKinds #-}

module Language.IceT.VCGen (verifyFile, verifyProgram) where

import           Language.IceT.Parse (parseFile, parseString)
import           Language.IceT.Pretty
import           Language.IceT.SMT
import           Language.IceT.Types

import           Prelude hiding (and, or)
import           Control.Monad.State
import           Data.List (isInfixOf)
import qualified Data.Map.Strict as M
import           GHC.IO.Handle
import           System.IO
import           System.Exit
import           System.Process
import           Text.PrettyPrint.HughesPJ
import           Text.Printf

-- import Debug.Trace

-------------------------------------------------------------------------------
verifyProgram :: String -> IO Bool
-------------------------------------------------------------------------------
verifyProgram = verify . parseString

-------------------------------------------------------------------------------
verifyFile :: FilePath -> IO Bool
-------------------------------------------------------------------------------
verifyFile fp = parseFile fp >>= verify

-------------------------------------------------------------------------------
verify :: VCAnnot a => Program a -> IO Bool
-------------------------------------------------------------------------------
verify (Program{..}) = do
  writeFile ".query.icet" (pretty (coalesceLocal prog))
  writeFile ".query.smt2" vcstr

  (inp, out, err, pid) <- runInteractiveProcess "z3" ["-smt2", ".query.smt2"] Nothing Nothing
  ec   <- waitForProcess pid
  outp <- hGetContents out
  errp <- hGetContents err

  putStrLn outp
  hPutStr stderr errp
  
  case ec of
    ExitSuccess ->   return ("unsat" `isInfixOf` outp)
    ExitFailure _ -> return False

  where
    (binders, vc) = vcgen decls cardDecls prog ensures

    vcstr = render $ vcat (prelude : declBinds binders ++  [checkValid vc])

    prelude = text $ unlines [ "(define-sort Elt () Int)"
                             , "(define-sort Set () (Array Elt Bool))"
                             , "(define-sort IntMap () (Array Elt Elt))"
                             , "(define-fun set_emp () Set ((as const Set) false))"
                             , "(define-fun set_mem ((x Elt) (s Set)) Bool (select s x))"
                             , "(define-fun set_add ((s Set) (x Elt)) Set  (store s x true))"
                             , "(define-fun set_cap ((s1 Set) (s2 Set)) Set ((_ map and) s1 s2))"
                             , "(define-fun set_cup ((s1 Set) (s2 Set)) Set ((_ map or) s1 s2))"
                             , "(define-fun set_com ((s Set)) Set ((_ map not) s))"
                             , "(define-fun set_dif ((s1 Set) (s2 Set)) Set (set_cap s1 (set_com s2)))"
                             , "(define-fun set_sub ((s1 Set) (s2 Set)) Bool (= set_emp (set_dif s1 s2)))"
                             , "(define-fun set_minus ((s1 Set) (x Elt)) Set (set_dif s1 (set_add set_emp x)))"
                             , "(declare-fun set_size (Set) Int)"
                             ]

    declBinds = map declBind
    declBind (Bind x s) = parens (text "declare-const" <+> text x <+> smt s)

    checkValid f = parens (text "assert" <+> smt (Not f)) $+$ text "(check-sat)"

-------------------------------------------------------------------------------
vcgen :: VCAnnot a => [Binder] -> [Card a] -> Stmt a -> Prop a -> ([Binder], Prop a)
-------------------------------------------------------------------------------
vcgen binders cards stmt prop = (binders', vc)
  where
    initialState = VCState { tenv       = tyEnv binders
                           , unfoldings = M.empty
                           , freshed    = []
                           , ictr       = 0
                           , invs       = []
                           , gather     = False
                           , cards      = cards
                           }

    action = do stmt' <- replaceSorts (coalesceLocal stmt)
                wlp stmt' prop

    (vc, st') = runState action initialState
    binders'  = fmap (uncurry Bind) . M.toList $ tenv st'

-------------------------------------------------------------------------------
-- Monads
-------------------------------------------------------------------------------

data VCState a = VCState { tenv       :: M.Map Id Sort -- type environment
                         , unfoldings :: M.Map Id Id   -- contains the unfoldings (e.g. (p, ps) if p \in ps)
                         , ictr       :: Int           -- global counter, used to create unique names
                         , freshed    :: [Binder]      -- TODO: ???
                         , invs       :: [( Int        -- TODO: ???
                                          , [Binder]
                                          , Prop a
                                          )]
                         , cards      :: [Card a]      -- cardinalities
                         , gather     :: Bool          -- TODO: ???
                         }

type VCGen a r = State (VCState a) r

-------------------------------------------------------------------------------
-- | Weakest Liberal Preconditions
wlp :: VCAnnot a => Stmt a -> Prop a -> VCGen a (Prop a)
-------------------------------------------------------------------------------
wlp (Skip _) q = return q

wlp (Assign {..}) q
  -- p.x <- q.*
  | assignExpr == NonDetValue = do
      b' <- freshBinder assignVar
      let stmt' = Assign { assignExpr = Var (bvar b'), .. }
      wlp stmt' q

  -- p.x <- p'.expr
  | otherwise = do
      let p  = stmtProcess
          p' = assignFromProcess
          x  = bvar assignVar
          pr = process stmtData
      select <- isSet p'
      v <- case assignExpr of
             Var y
               | p == p' || select -> do
                   t <- getType y
                   ifM (isIndex t p') (return $ Select assignExpr (Var p')) (return assignExpr)
             _  -> return assignExpr
      ifM (isIndex (bsort assignVar) pr)
            (return $ subst (bvar assignVar) (Store (Var x) (Var pr) v) q)
            (return $ subst (bvar assignVar) v q)

wlp (Seq {..}) q = foldM (flip wlp) q (reverse seqStmts)

wlp (Cases {..}) q
  | casesExpr == NonDetValue = And <$> mapM (flip wlp q . caseStmt) caseList
  | otherwise                = And <$> mapM go caseList
  where
    go (Case{..}) = do wp <- wlp caseStmt q
                       return $ (Atom Eq casesExpr caseGuard) :=>: wp

wlp (ForEach x xs (done, i) stmt _) q = do
  -- add x \in xs to the unfoldings
  addElem (bvar x) (bvar xs)

  let i' = subst done (Bin SetAdd ed ex) i -- I[d U {x} / d]
  i2  <- gathering $ wlp stmt i'           -- wlp(A, I[d U {x} / d])

  removeElem (bvar x)

  return $ And [ subst done EmptySet i -- I[{} / d]
               , Forall va $ And [ subst done exs i        -- I[xs/d]
                                 , Atom SetMem ex exs      -- x \in xs
                                 , Not $ Atom SetMem ex ed -- x  \not\in d
                                 ] :=>: i2
               , Forall va $ subst done (Var (bvar xs)) i :=>: q
               ]
  where
    ex  = Var (bvar x)
    exs = Var (bvar xs)
    ed  = Var done
    va  = x : Bind done Set : writes stmt -- V(A): variables that might be assigned in A

wlp (Par p ps prop stmt _) q = do
  modify $ \s -> s { tenv = M.insert (pcName ps) (Map (SetIdx ps) Int) (tenv s) }
  addElem p ps
  y <- vcBinds -- variables that might be assigned to
  let (ins, acts, outs) = actions p stmt y
      actsWithLoc       = replaceHere p ps <$> acts

  inv <- actionsInvariant p ps actsWithLoc

  let initHead = pcGuardHelper ins -- forall p in ps. pc[p] in ins
      initInv  = initHead :=>: Forall [Bind p Int] inv

      exitHead = pcGuardHelper outs -- forall p in ps. pc[p] in outs
      exitInv  = Forall y $ And [exitHead, inv] :=>: q

  txInvs <- mapM (txInv inv) actsWithLoc

  removeElem p

  return $ And $ initInv : exitInv : txInvs

  where
    ------------------------------------------------------------
    pcGuardHelper :: [Int] -> Prop a
    ------------------------------------------------------------
    pcGuardHelper locations =
      let p0 = p ++ "!"
      in case locations of
           []   -> error "entry point set is empty !"
           [l]  -> Forall [Bind p0 Int] (pcGuard p0 ps l)
           l:ls -> Forall [Bind p0 Int] $ And [ Not (pcGuard p0 ps l') | l' <- ls ] :=>: (pcGuard p0 ps l)

    ------------------------------------------------------------
    vcBinds :: VCGen a [Binder]
    ------------------------------------------------------------
    vcBinds = fmap (uncurry Bind) . M.toList <$> gets tenv

    ------------------------------------------------------------
    cardInits :: [Card a] -> [(Id,Id)] -> [(Binder, Expr a)]
    ------------------------------------------------------------
    cardInits ks us =
      let evalCardFormula k p' q' = subst (cardElem k) (Var q') (subst (cardId k) (Var p') (cardProp k))
          initialBool k p' q' = cardName k ++ "!" ++ p' ++ "!" ++ q'
          bind k p' q' = ( Bind (initialBool k p' q') Bool
                           , PExpr (evalCardFormula k p' q')
                           )
      in [ bind k p' q'
         | k <- ks
         , (p',ps') <- us
         , cardOwner k == ps
         , (q',qs') <- us
         , ps' /= qs'
         ]

    ------------------------------------------------------------
    txInv :: VCAnnot a => Prop a -> Action a -> VCGen a (Prop a)
    ------------------------------------------------------------
    txInv i (Action{..}) = do
      ks <- gets cards
      us <- gets unfoldings
      te <- gets tenv
      let te'     = M.union (tyEnv (Bind p Int : actionScope)) te
          g       = And $ actionPath ++ [ Atom SetMem (Var p) (Var ps)
                                        , pcGuard p ps actionLocation
                                        ]
          invAt l = subst (pcName ps) (Store (Var (pcName ps)) (Var p) (Const l)) i
          post    = case actionExits of
                      [] -> TT
                      l  -> And $ [ invAt o | o <- snd <$> l ]

      modify $ \st -> seq g st { unfoldings = M.union (M.fromList actionProcesses) us
                               , tenv       = te'
                               }
      inductive <- wlp actionStmt post

      -- restore the state
      modify $ \st -> st { unfoldings = us
                         , tenv       = te
                         }

      return $ Forall actionScope $ Let (cardInits ks ((p,ps):actionProcesses)) (g :=>: inductive)

wlp (If {..}) q = do
  p1 <- wlp thenStmt q
  p2 <- wlp elseStmt q
  let result = case ifCondition of
                 NonDetProp -> [p1, p2]
                 _          -> [ ifCondition :=>: p1
                               , Not ifCondition :=>: p2
                               ]
  return $ And result

wlp (Assert p pre _) q = do
  isGather <- gets gather
  return $ if   isGather == pre
           then And [p, q]
           else p

wlp (Assume p _) q = do
  isGather <- gets gather
  return $ if   isGather
           then q
           else p :=>: q

wlp (Atomic {..}) q = wlp atomicStmt q

wlp s _ = error (printf "wlp TBD: %s" (show s))


-------------------------------------------------------------------------------
actionsInvariant :: VCAnnot a => Id -> Id -> [Action a] -> VCGen a (Prop a)
-------------------------------------------------------------------------------
actionsInvariant p ps as = do
  env <- gets tenv
  cs <- gets unfoldings
  prop <- And <$> mapM (oneConj env cs) as
  modify $ \st -> st { tenv = env }
  return prop
  where
    oneConj :: VCAnnot a => M.Map Id Sort -> p -> Action a -> VCGen a (Prop a)
    oneConj env cs (Action {..}) = gathering $ do
      modify $ \st -> st { tenv = M.union (tyEnv actionScope) env }
      forM actionProcesses $ \(q,qs) -> addElem q qs
      prop <- wlp actionStmt TT
      return $ pcGuard p ps actionLocation :=>: prop


--------------------------------------------------------------------------------
replaceSorts :: VCAnnot a => Stmt a -> VCGen a (Stmt a)
--------------------------------------------------------------------------------
replaceSorts (Assign {..}) = do
  t <- getType (bvar assignVar)
  return $ Assign { assignVar = assignVar { bsort = t } , .. }

replaceSorts (Seq {..}) = do
  stmts' <- mapM replaceSorts seqStmts
  return $ Seq { seqStmts = stmts' , .. }

replaceSorts (ForEach {..}) = do
  g <- gets unfoldings
  case M.lookup p g of
    Nothing -> do
      stmt' <- replaceSorts forStmt
      return $ ForEach { forStmt = stmt', .. }
    Just ps -> do
      stmt' <- replaceSorts (subst (bvar forElement) xmap forStmt)
      return $ ForEach { forElement = liftSo forElement ps
                       , forStmt = stmt'
                       , ..
                       }
  where
    p = process stmtData
    liftSo x ps = x { bsort = Map (SetIdx ps) (bsort x) }
    xmap = Select (Var (bvar forElement)) (Var p)

replaceSorts (If {..}) = do
  then' <- replaceSorts thenStmt
  else' <- replaceSorts elseStmt
  return $ If { thenStmt = then', elseStmt = else', .. }

replaceSorts (Par {..}) = do
  s' <- replaceSorts parStmt
  return $ Par { parStmt = s', .. }

replaceSorts (Atomic {..}) = do
  s' <- replaceSorts atomicStmt
  return $ Atomic { atomicStmt = s', .. }

replaceSorts (While {..}) = do
  s' <- replaceSorts whileStmt
  return $ While { whileStmt = s', .. }

replaceSorts (Cases {..}) = do
  l' <- mapM helper caseList
  return $ Cases { caseList = l', .. }
  where
    helper (Case {..}) = do
      s' <- replaceSorts caseStmt
      return $ Case { caseStmt = s', .. }

replaceSorts s@(Assert {..}) = return s

replaceSorts s@(Assume {..}) = return s

replaceSorts s@(Skip {..}) = return s


--------------------------------------------------------------------------------
coalesceLocal :: VCAnnot a => Stmt a -> Stmt a
--------------------------------------------------------------------------------
coalesceLocal (Par {..}) = Par { parStmt = coalesceLocal parStmt, .. }

coalesceLocal (If {..}) = If { thenStmt = coalesceLocal thenStmt
                             , elseStmt = coalesceLocal elseStmt
                             , ..
                             }

coalesceLocal (Seq {..}) =
  case seqStmts of
    -- Empty list of sequence is skip
    []   -> Skip { .. }
    s:ss -> case localPrefix of
              -- if we DO NOT have a prefix with local assignments ...
              [] -> helper stmtData [ coalesceLocal s
                                    , coalesceLocal $ Seq { seqStmts = coalesceLocal <$> ss, .. }
                                    ]
              -- if we have a prefix with local assignments, make that part atomic
              _  -> helper stmtData [ Atomic { atomicStmt = helper stmtData localPrefix, .. }
                                    , coalesceLocal $ helper stmtData $ coalesceLocal <$> restStmts
                                    ]
  where
    (localPrefix, restStmts) = break (not . isLocal) seqStmts

    helper :: a -> [Stmt a] -> Stmt a
    helper a ss = flattenSeq $ Seq { seqStmts = ss
                                   , stmtData = a
                                   }

    flattenSeq :: Stmt  a -> Stmt a
    flattenSeq (Seq ss l) = dropSingleton . simplifySkips $ Seq (foldl go [] ss') l
      where
        ss'                = flattenSeq <$> ss
        go ss1 (Seq ss2 _) = ss1 ++ (foldl go [] ss2)
        go ss1 (Skip _)    = ss1
        go ss1 s           = ss1 ++ [s]

    flattenSeq (ForEach x y inv s l) = ForEach x y inv (flattenSeq s) l
    flattenSeq s = s

    isLocal :: Stmt a -> Bool
    isLocal (Assign p _ q _ _) = p == q
    isLocal (Skip _)           = True
    isLocal (Assert _ _ _)     = True
    isLocal (Assume _ _)       = True
    isLocal _                  = False

    isSkip (Skip _) = True
    isSkip _        = False

    simplifySkips (Seq ss a) = Seq (filter (not . isSkip) ss) a
    simplifySkips s          = error "simplifySkips called with a non sequence"

    dropSingleton (Seq [] l)  = Skip l
    dropSingleton (Seq [s] _) = s
    dropSingleton s           = s

coalesceLocal s = s


-------------------------------------------------------------------------------
-- Helper Functions
-------------------------------------------------------------------------------

freshBinder :: Binder -> VCGen a Binder
freshBinder (Bind x _) = do
  i <- gets ictr
  t <- getType x
  let var = (x ++ "!" ++ show i)
  let b' = Bind var t
  modify $ \s -> s { ictr    = i + 1
                   , freshed = b' : freshed s
                   , tenv    = M.insert var  t (tenv s)
                   }
  return b'

getType :: Id -> VCGen a Sort
getType x = do
  y <- gets tenv
  case M.lookup x y of
    Just t  -> return t
    Nothing -> error (printf "Unknown id: %s" x)

isSet :: Id -> VCGen a Bool
isSet i = do
  g <- gets unfoldings
  return $ M.member i g

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM mb t e = do
  b <- mb
  if b then t else e

isIndex :: Sort -> Id -> VCGen a Bool
isIndex (Map (SetIdx ps) _) p = isElem p ps
isIndex _ _                   = return False

isElem :: Id -> Id -> VCGen a Bool
isElem p ps = do
  g <- gets unfoldings
  return $ maybe False (== ps) $ M.lookup p g

addElem :: Id -> Id -> VCGen a ()
addElem p ps = modify $ \s -> s { unfoldings = M.insert p ps (unfoldings s) }

gathering :: VCGen a b -> VCGen a b
gathering act = do
  modify $ \s -> s { gather = True }
  r <- act
  modify $ \s -> s { gather = False }
  return r

removeElem :: Id -> VCGen a ()
removeElem p = modify $ \s -> s { unfoldings = M.delete p (unfoldings s) }

pcGuard :: Id -> Id -> Int -> Prop a
pcGuard p ps i = Atom Eq (pc ps p) (Const i)

replaceHere :: t -> Id -> Action a -> Action a
replaceHere _ ps (Action {..}) = Action { actionStmt = goStmt actionStmt, .. }
  where
    goStmt (Assert {..})  = Assert { stmtProperty = goProp stmtProperty, .. }
    goStmt (Seq {..})     = Seq { seqStmts = goStmt <$> seqStmts, .. }
    goStmt (If {..})      = If { thenStmt = goStmt thenStmt
                               , elseStmt = goStmt elseStmt
                               , ..
                               }
    goStmt (ForEach {..}) = ForEach { forStmt = goStmt forStmt, .. }
    goStmt s              = s

    goProp (Here e)      = Atom Eq (Select (Var (pcName ps)) e) (Const actionLocation)
    goProp (Forall xs a) = Forall xs (goProp a)
    goProp (a :=>: b)    = goProp a :=>: goProp b
    goProp (And as)      = And (goProp <$> as)
    goProp (Or as)       = Or (goProp <$> as)
    goProp (Not a)       = Not (goProp a)
    goProp a             = a

tyEnv :: [Binder] -> M.Map Id Sort
tyEnv bs = M.fromList [ (x,t) | Bind x t <- bs ]
