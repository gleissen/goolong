{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ConstraintKinds #-}

module Language.IceT.VCGen (verifyFile, verifyProgram) where

import           Prelude hiding (and, or)
import           Language.IceT.Types
import           Language.IceT.Parse (parseFile, parseString)
import           System.Exit
import           Control.Monad.State
import qualified Data.Map.Strict as M
import qualified Language.Fixpoint.Horn.Types   as H
import qualified Language.Fixpoint.Horn.Solve   as H
import qualified Language.Fixpoint.Solver       as Solver
import qualified Language.Fixpoint.Types.Config as F 

import Debug.Trace
import Text.Printf

type HornData = ()
type Query = H.Query HornData

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
  result <- H.solve cfg query
  code <- Solver.resultExitCode result
  return $ code == ExitSuccess

  where
    cfg = F.defConfig
    query = vcgen decls cardDecls prog ensures

-------------------------------------------------------------------------------
vcgen :: VCAnnot a => [Binder] -> [Card a] -> Stmt a -> Prop a -> Query
-------------------------------------------------------------------------------
vcgen binders cards stmt prop = result
  where
    result = trace (printf "%s\n\n%s\n\n%s\n\n%s"
                     (show binders)
                     (show cards)
                     (show stmt)
                     (show prop)
                   ) undefined

-------------------------------------------------------------------------------
-- Monads
-------------------------------------------------------------------------------

data VCState a = VCState { tenv    :: M.Map Id Sort
                         , constrs :: M.Map Id Id
                         , ictr    :: Int
                         , freshed :: [Binder]
                         , invs    :: [(Int, [Binder], Prop a)]
                         , cards   :: [Card a]
                         , gather  :: Bool
                         }

type VCGen a r = State (VCState a) r 

-------------------------------------------------------------------------------
-- Weakest Liberal Preconditions
-------------------------------------------------------------------------------

wlp :: VCAnnot a => Stmt a -> Prop a -> VCGen a (Prop a)   
wlp (Skip _) prop = return prop

-- wlp (Assign a x b NonDetValue c) prop = do
wlp stmt@(Assign {..}) prop
  | assignExpr == NonDetValue = do
      b' <- freshBinder assignBinder
      let stmt' = Assign { assignExpr = Var (bvar b'), .. }
      wlp stmt' prop

  | otherwise = do
      select <- isSet p2
      v <- case assignExpr of
             Var y | stmtProcess == p2 -> do
                       t <- getType y
                       ifM (isIndex t p2)
                         (return $ Select assignExpr (Var p2))
                         (return $ assignExpr)
             Var y | select -> do
                       t <- getType y
                       ifM (isIndex t p2)
                         (return $ Select assignExpr (Var p2))
                         (return assignExpr)
             _  -> return assignExpr
      g <- gets constrs
      
      ifM (isIndex (bsort assignBinder) pr)
            (return $ subst (bvar assignBinder) (Store (Var i) (Var pr) v) prop)
            (return $ subst (bvar assignBinder) v prop)
  where
    p2 = assignFromProcess
    i  = bvar assignBinder
    pr = process stmtData

-- wlp (Seq stmts _) p
--   = foldM (flip wlp) p (reverse stmts)

-- wlp (Cases NonDetValue cs _) p
--   = And <$> mapM (flip wlp p . caseStmt) cs

-- wlp (Cases e cs _) p
--   = And <$> mapM go cs
--   where
--     go c
--       = do wp <- wlp (caseStmt c) p
--            return (Atom Eq e (caseGuard c)  :=>: wp)

-- wlp (ForEach x xs (rest, i) s _) p
--   = do addElem (bvar xs) (bvar x)
--        i'  <- gathering $ wlp s TT
--        let i'' = subst (bvar xs) erest i'
--        let inv = and [i, Forall [x] (and [ Atom SetMem ex erest ] :=>: i'')]
--        pre <- wlp s $ subst rest (Bin SetAdd erest ex) inv
--        removeElem (bvar x)
--        return $ And [ subst rest EmptySet inv
--                     , Forall vs $ and [ inv
--                                       , Atom SetMem ex exs 
--                                       , Not $ Atom SetMem ex erest
--                                       ]
--                                   :=>:
--                                   pre
--                     , Forall vs $ subst rest (Var (bvar xs)) inv :=>: p
--                     ]
--   where
--     ex        = Var (bvar x)
--     exs       = Var (bvar xs)
--     erest     = Var rest
--     vs        = x : Bind rest Set : writes s

-- wlp (Par i is _ s _) p
--   = do modify $ \s -> s { tenv = M.insert (pcName is) (Map (SetIdx is) Int) (tenv s) }
--        addElem is i
--        bs      <- vcBinds
--        let (pc0, acts, outs) = as bs
--            actsLocs     = replaceHere i is <$> acts
--            exitCond     = Or [pcGuard i is x | x <- outs]

--        inv     <- actionsInvariant i is actsLocs

--        let qInv = and [ inv
--                       , (Forall [Bind i0 Int] (pcGuard i0 is (-1)))
--                       ] :=>: p
--            init = Forall [Bind i0 Int] $ and [ Atom SetMem (Var i0) (Var is)
--                                              , or [ pcGuard i0 is pc0i | pc0i <- pc0 ]
--                                              ]
--            initial = init :=>: Forall [Bind i0 Int] (subst i (Var i0) inv)
--        txns    <- mapM (wlpAction i is inv) actsLocs
--        removeElem i
--        return $ and ([initial] ++ txns ++ [Forall bs qInv]) 
--   where
--     as bs = actions i s bs
--     i0    = i ++ "!"

-- wlp (Assert b pre _) p
--   = do g <- gets gather
--        if (g && pre) || (not g && not pre) then
--          return (and [b, p])
--        else
--          return p

-- wlp (Assume b _) p
--   = do g <- gets gather
--        return (if g then p else b :=>: p)

-- wlp (If c s1 s2 _) p
--   = do φ <- wlp s1 p
--        ψ <- wlp s2 p
--        let guard p q = case c of
--                          NonDetProp -> [p, q]
--                          _          -> [c :=>: p, Not c :=>: q]
--        return . and $ guard φ ψ

-- wlp (Atomic s _) p
--   = wlp s p

wlp s _ = error (printf "wlp TBD: %s" (show s))

-------------------------------------------------------------------------------
-- Helper Functions
-------------------------------------------------------------------------------

freshBinder :: Binder -> VCGen a Binder
freshBinder (Bind x _) = do
  i <- gets ictr
  t <- getType x
  let var = (x ++ "!" ++ show i)
  let b' = Bind var t
  modify $ \s -> s { ictr = i + 1, freshed = b' : freshed s, tenv = M.insert var  t (tenv s)}
  return b'

getType :: Id -> VCGen a Sort
getType x = do
  y <- gets tenv
  case M.lookup x y of
    Just t  -> return t
    Nothing -> error (printf "Unknown id: %s" x)

isSet :: Id -> VCGen a Bool
isSet i = do
  g <- gets constrs
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
  g <- gets constrs
  return $ maybe False (== ps) $ M.lookup p g

-- addElem :: Id -> Id -> VCGen a ()  
-- addElem ps p = modify $ \s -> s { constrs = M.insert p ps (constrs s) }

-- removeElem :: Id -> VCGen a ()
-- removeElem p = modify $ \s -> s { constrs = M.delete p (constrs s) }

-- vcBinds :: VCGen a [Binder]
-- vcBinds = fmap (uncurry Bind) . M.toList <$> gets tenv

-- pcGuard :: Id -> Id -> Int -> Prop a
-- pcGuard p ps i = Atom Eq (pc ps p) (Const i)

-- replaceHere :: t -> Id -> Action a -> Action a
-- replaceHere _ ps (Action xs us cond i outs s) = Action xs us cond i outs (goStmt s)
--   where
--     goStmt (Assert φ b l)         = Assert (goProp φ) b l
--     goStmt (Seq stmts l)          = Seq (goStmt <$> stmts) l
--     goStmt (If c s1 s2 l)         = If c (goStmt s1) (goStmt s2) l
--     goStmt (ForEach x xs inv s l) = ForEach x xs inv (goStmt s) l
--     goStmt s                      = s

--     goProp (Here e)      = Atom Eq (Select (Var (pcName ps)) e) (Const i)
--     goProp (Forall xs a) = Forall xs $ goProp a
--     goProp (a :=>: b)    = goProp a :=>: goProp b
--     goProp (And as)      = And (goProp <$> as)
--     goProp (Or as)       = Or (goProp <$> as)
--     goProp (Not a)       = Not $ goProp a
--     goProp a             = a
