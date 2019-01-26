{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ConstraintKinds #-}

module Language.IceT.VCGen2 (verifyFile, verifyProgram) where

import           Language.IceT.Parse (parseFile, parseString, ParsedProgram)
-- import           Language.IceT.Pretty
import           Language.IceT.SMT
import           Language.IceT.Types hiding (CFG)
import           Language.IceT.Action

import           Control.Monad.State
import qualified Data.Graph.Inductive.Graph        as G
import qualified Data.HashMap.Strict               as HM
import qualified Data.IntMap.Strict                as IM
import           Data.List (nub, isInfixOf)
import           GHC.IO.Handle
import           System.Exit
import           System.IO
import           System.Process
import           Text.PrettyPrint.HughesPJ
import           Text.Printf

import Debug.Trace

data VCState a = VCState { freshCounter      :: Int
                         , typeEnv           :: HM.HashMap Id Sort
                         , unfoldedProcesses :: HM.HashMap Id Id -- p -> ps
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
    vcstr = render $ vcat $ prelude : fmap smt decls' ++ [checkValid vc]
                          
    (vc, lastState) = runState action initialState
    initialState = VCState { freshCounter      = 0
                           , typeEnv           = makeTypeEnv decls
                           , unfoldedProcesses = HM.empty
                           }
    decls' = fmap (uncurry Bind) . HM.toList $ typeEnv lastState
    action = wlp prog ensures

-------------------------------------------------------------------------------
wlp :: VCAnnot a => Stmt a -> Prop a -> VCGen a (Prop a)
-------------------------------------------------------------------------------
wlp (Assign {assignExpr = NonDetValue, ..}) q = do
  v' <- freshBinder assignVar
  wlp (Assign { assignExpr = Var (bvar v'), ..}) q

wlp (Assign {..}) q = do
  let p' = assignFromProcess
      e  = assignExpr
  isFromSet <- isSet p'
  let c = stmtProcess == p' || isFromSet
  v <- case e of
         Var y | c -> do t <- getType y
                         check <- isIndex t p'
                         return $ if   check
                                  then Select e (Var p')
                                  else e
         _ -> return e
  let pr = process stmtData 
      i  = bvar assignVar
      s  = bsort assignVar
  ifM (isIndex s pr)
    (return $ subst i (Store (Var i) (Var pr) v) q)
    (return $ subst i v q)

wlp (Assume {..}) q = return $ stmtProperty :=>: q

wlp (Assert {..}) q = return $ And [stmtProperty, q]

wlp (Atomic {..}) q = wlp atomicStmt q  

wlp (Seq {..}) q = foldM f q (reverse seqStmts)
  where
    f q' s = wlp s q'

wlp (Cases {casesExpr = NonDetValue, ..}) q =
  And <$> mapM (flip wlp q . caseStmt) caseList

wlp (Cases {..}) q = And <$> mapM go caseList
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
  addElem x xs
  pre <- wlp forStmt q'
  removeElem x xs
  let inv1 = subst done EmptySet inv
      inv2 = Forall y $
             And [ inv
                 , Atom SetMem ex exs
                 , Not $ Atom SetMem ex edone
                 ] :=>:
             pre
      inv3 = Forall y $ (subst done exs inv) :=>: q
  return $ And [inv1, inv2, inv3]
  where
    q'          = subst done (Bin SetAdd ex edone) inv
    edone       = Var done
    x           = bvar forElement
    xs          = bvar forList
    ex          = Var x
    exs         = Var xs
    (done, inv) = forInvariant
    y           = forElement : Bind done Set : updatedVars forStmt

wlp (Par {..}) q = do
  VCState{..} <- get
  let ActionResult{ arMap    = m
                  , arCFG    = g
                  , arPC0    = pc0
                  , arPCExit = pcExit
                  } = extractCFG freshCounter parStmt
  traceM (show m)
  put VCState { freshCounter = pcExit + 1 , .. }
  let i = Forall [Bind stmtProcess Int] $
          And [ And [ Atom SetMem varP varPs
                    , Atom Eq (pc p ps) (Const l)
                    ] 
                :=>:
                Or [ let la' = m IM.! l'
                     in atomicPost la'
                   | l' <- G.pre g l
                   ]
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
      cf l = And [ Atom Eq (pc p ps) (Const l)
                 , Or [ Atom Eq varPC' (Store varPC varP (Const l'))
                      |  l' <- G.suc g l
                      ]
                 ]
  conjunts <- mapM (\(la_pc,la) -> do
                       let stmt' = subst p varP0 (atomicStmt la)
                           q'    = subst (pcName ps) varPC' i
                       prop <- wlp stmt' q'
                       return (la_pc, la, prop)
                   ) (IM.toList m)
  let invStep = Forall (Bind p0 Int : y) $
                Atom SetMem varP0 varPs
                :=>:
                And [ And [i, cf l] :=>: w
                    | (l, _, w) <- conjunts
                    ]
  return $ trace (show g) q

  where
    y = Bind (pcName stmtProcessSet) Set :
        Bind (pcName' stmtProcessSet) Set :
        updatedVars parStmt
    p0 = stmtProcess ++ "0"
    p  = stmtProcess
    ps = stmtProcessSet
    varP   = Var p
    varPs  = Var ps
    varP0  = Var p0
    varPC  = Var $ pcName ps
    varPC' = Var $ pcName' ps

wlp _ _ = undefined

-------------------------------------------------------------------------------
-- helper functions
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
  modify $ \VCState{..} -> VCState { freshCounter = n + 1
                                   , ..
                                   }
  return n
  
getType :: Id -> VCGen a Sort
getType x = do
  te <- gets typeEnv
  case HM.lookup x te of
    Just t  -> return t
    Nothing -> error (printf "Unknown id: %s" x)

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

addElem :: Id -> Id -> VCGen a ()
addElem p ps =
  modify $ \(VCState {..}) -> VCState { unfoldedProcesses = HM.insert p ps unfoldedProcesses
                                      , ..
                                      }

removeElem :: Id -> Id -> VCGen a ()
removeElem p ps =
  modify $ \(VCState {..}) -> VCState { unfoldedProcesses = HM.delete p unfoldedProcesses
                                      , ..
                                      }

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
