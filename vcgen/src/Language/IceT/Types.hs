{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ConstraintKinds #-}

module Language.IceT.Types where

import Prelude hiding (and, or)
import Control.Monad.State
import Data.Map.Strict as M hiding (foldl')
import Data.List as L hiding (and, or)
import Text.Printf

import Debug.Trace

dbg :: Show a => String -> a -> a
dbg msg x = trace (printf "[%s]: %s\n" msg (show x)) x

-------------------------------------------------------------------------------
-- Programs
-------------------------------------------------------------------------------
type VCAnnot a = (Show a, Process a)

class Process a where
  process :: a -> Id

instance Process Id where
  process = id

type Id = String

instance Process (Id, Int) where
  process = fst

data Program a = Program { decls     :: [Binder]
                         , cardDecls :: [Card a]
                         , prog      :: Stmt a
                         , ensures   :: Prop a
                         }
               deriving (Show)

data Card a = Card { cardName  :: Id
                   , cardOwner :: Id
                   , cardId    :: Id
                   , cardElem  :: Id
                   , cardProp  :: Prop a
                   }
            deriving (Show)

data Stmt a = Skip    { stmtData :: a }
            | Par     { stmtProcess    :: Id
                      , stmtProcessSet :: Id
                      , stmtProperty   :: Prop a
                      , parStmt        :: Stmt a
                      , stmtData       :: a
                      }
            | Assign  { stmtProcess       :: Id
                      , assignVar         :: Binder
                      , assignFromProcess :: Id
                      , assignExpr        :: Expr a
                      , stmtData          :: a
                      }
            | Seq     { seqStmts :: [Stmt a]
                      , stmtData :: a
                      }
            | Atomic  { atomicStmt  :: Stmt a
                      , atomicPost  :: Prop a
                      , atomicLabel :: Int
                      , stmtData    :: a
                      }
            | Assume  { stmtProperty :: Prop a
                      , stmtData     :: a
                      }
            | Assert  { stmtProperty :: Prop a
                      , assertBool   :: Bool
                      , stmtData     :: a
                      }
            | If      { ifCondition :: Prop a
                      , thenStmt    :: Stmt a
                      , elseStmt    :: Stmt a
                      , stmtData    :: a
                      }
            | Cases   { casesExpr :: Expr a
                      , caseList :: [Case a]
                      , stmtData :: a
                      }
            | ForEach { forElement   :: Binder
                      , forList      :: Binder
                      , forInvariant :: (Id, Prop a) -- (d, I)
                      , forStmt      :: Stmt a
                      , stmtData     :: a
                      }
            | While   { stmtProcess :: Id
                      , whileStmt   :: Stmt a
                      , stmtData    :: a
                      }
            deriving (Eq, Show, Functor, Foldable, Traversable)

data Case a = Case { caseGuard :: Expr a
                   , caseStmt  :: Stmt a
                   , caseAnnot :: a
                   }
            deriving (Eq, Show, Functor, Foldable, Traversable)
            
data Expr a = Const Int
            | EmptySet
            | NonDetValue
            | Var Id
            | PExpr (Prop a)
            | Select (Expr a) (Expr a)
            | Store (Expr a) (Expr a) (Expr a)
            | Size (Expr a)
            | Ite (Prop a) (Expr a) (Expr a)
            | Bin Op (Expr a) (Expr a)
            deriving (Eq, Show, Functor, Foldable, Traversable)

data Op = Plus
        | Minus
        | Mul
        | Div
        | SetSubSingle -- Xs - {x}
        | SetAdd
        deriving (Eq, Show)

data Prop a = TT
            | FF
            | Atom Rel (Expr a) (Expr a)
            | Not (Prop a)
            | And [Prop a]
            | Or [Prop a]
            | Prop a :=>: Prop a
            | Forall [Binder] (Prop a)
            | Exists [Binder] (Prop a)
            | Here (Expr a)
            | Prop (Expr a)
            | PVar Id
            | NonDetProp
            | Let [(Binder, Expr a)] (Prop a)
            deriving (Eq, Show, Functor, Foldable, Traversable)

data Binder = Bind { bvar  :: Id
                   , bsort :: Sort
                   }
            deriving (Eq, Show)

data Sort = Int | Set | Map Index Sort | Bool
          deriving (Eq, Show)

data Index = SetIdx Id
           | IntIdx
           deriving (Eq, Show)

data Rel = Eq | Le | Lt | Gt | SetMem
         deriving (Eq, Show)

-------------------------------------------------------------------------------
-- Actions
-------------------------------------------------------------------------------

-- | Atomic action
data Action a = Action { actionScope     :: [Binder]        -- Binders in this scope
                       , actionProcesses :: [(Id, Id)]      -- (p,ps) \in actionProcesses ==> p \in ps
                       , actionPath      :: [Prop a]        -- Path conditions
                       , actionLocation  :: Int             -- The location (i.e. label) of the action
                       , actionExits     :: [(Prop a, Int)] -- Locations of the successors of this atomic action,
                                                            -- and the respective path conditions
                       , actionStmt      :: (Stmt a)        -- Statement that is executed atomically
                       }
              deriving (Show, Eq, Functor)

-- | Local state used while constructing the atomic actions needed by the vcgen
data CFG a = CFG { cfgPath      :: [Prop a]    -- the path conditions
                 , cfgBinds     :: [Binder]    -- set of binders
                 , cfgMap       :: CFGMap a    -- (l, [(p1, m1), ...]) in cfgMap IF m1 is an immediate successor of l,
                                               -- with path condition p1
                 , cfgProcesses :: M.Map Id Id -- Contains (p, ps) if p \in ps. Used for unfolding. 
                 }  

-- Helper type aliases
type CFGMap a = M.Map Int [(Prop a, Int)]
type CfgM s a = State (CFG s) a
type ToActionsReturn a = CfgM (a, Int) ([Int], [Action (a, Int)])

----------------------------------------------------------------------------------------- 
{- |
toAction :: VCAnnot a
         => Stmt (a, Int)     : Statement (with unique identifier Int) to generate
         -> ToActionsReturn a : A stateful monad that returns a pair. First element successor locations,
                                the second is a list of atomic actions.
-}
toActions :: VCAnnot a => Stmt (a, Int) -> ToActionsReturn a
----------------------------------------------------------------------------------------- 
toActions s@(Atomic {..}) = toActionsHelper atomicStmt (getStmtLoc s)

toActions s@(Assign {..}) = toActionsHelper s (getStmtLoc s) 

toActions s@(Skip {..}) = toActionsHelper s (getStmtLoc s)

toActions (ForEach {..}) = pushForLoop $ do
  (outs, as) <- toActions forStmt
  modify $ \st -> st { cfgMap = updCfgMap (cfgMap st) forStmt outs }
  return (outs, as)
  where
    -- | run the given action, after updating the path and bindings
    pushForLoop :: CfgM s a -> CfgM s a 
    pushForLoop act = withUnfold (bvar forElement) (bvar forList) $ do
      vs0 <- gets cfgBinds
      p0  <- gets cfgPath
      let grd = Atom SetMem (Var $ bvar forElement) (Var $ bvar forList) 

      modify $ \s -> s { cfgBinds = forElement : vs0
                       , cfgPath  = grd : p0
                       }
      result <- act
      modify $ \s -> s { cfgBinds = vs0
                       , cfgPath  = p0
                       }
      return result

    -- | run the given action, after updating the 
    withUnfold :: Id -> Id -> CfgM s a -> CfgM s a
    withUnfold p ps act = do
      us0 <- gets cfgProcesses
      modify $ \s -> s { cfgProcesses = M.insert p ps (cfgProcesses s)  }
      result <- act
      modify $ \s -> s { cfgProcesses = us0}
      return result
  
toActions (Seq {..}) = do
  (lastOut, as) <- foldM go ([], []) seqStmts
  return (lastOut, concat as)
  where
    go (prevOut, s0) s = do (out, s') <- toActions s
                            modify $ \st -> st { cfgMap = updCfgMap (cfgMap st) s prevOut }
                            return (out, s':s0)

toActions (If {..}) = do
  p0 <- gets cfgPath
  -- handle the then branch
  modify $ \s -> s { cfgPath = ifCondition : p0 }
  (last1, a1)  <- toActions thenStmt
  -- handle the else branch
  modify $ \s -> s { cfgPath = Not ifCondition : p0 }
  (last2, a2) <- toActions elseStmt
  -- reset the path variable, and return the result
  modify $ \s -> s { cfgPath = p0 }
  return (last1 ++ last2, a1 ++ a2)

toActions stmt = error $ printf "called toActions with %s %s" (show stmt)

{-|
Given a statement that is executed atomically and the location of the statement,
returns a pair that contains the location and the atomic action
-}
toActionsHelper :: Stmt (a, Int) -> Int -> ToActionsReturn a
toActionsHelper stmt loc = do
  p  <- gets cfgPath                   -- get the current path variable
  bs <- gets cfgBinds                  -- get the current set of binders
  us <- M.toList <$> gets cfgProcesses -- get the list of unfolded processes
  let action = Action { actionScope     = bs
                      , actionProcesses = us
                      , actionPath      = p
                      , actionLocation  = loc
                      , actionExits     = [] -- This will be updated later ...
                      , actionStmt      = stmt
                      }
  return ([loc], [action])

{-|
Given an immediate successor map, a statement and a list of successors, update
the map with entries (o, (True, i)) where
* o is a successor location
* i is a predecessor location
-}
updCfgMap :: CFGMap (a, Int) -> Stmt (a, Int) -> [Int] -> CFGMap (a, Int)
updCfgMap m stmt outs = foldl' (\m' o ->
                                  foldl' (\m'' i ->
                                            M.alter (ins TT i) o m''
                                         ) m' (firstOf stmt)
                               ) m outs
  where
    ins prop v Nothing   = Just [(prop,v)]
    ins prop v (Just vs) = Just ((prop,v):vs)
  
----------------------------------------------------------------------------------------- 
{-|
actions :: VCAnnot a
        => Id           : TODO: ???
        -> Stmt a       : Statement to generate atomic actions from
        -> [Binder]     : TODO: ???
        -> ( [Int]      : Entry points to the statement
           , [Action a] : List of atomic actions found
           , [Int]      : Exit points
           )
-}
actions :: VCAnnot a => Id -> Stmt a -> [Binder] -> ([Int], [Action a], [Int])
----------------------------------------------------------------------------------------- 
actions w stmt bs = ( firstOf labeledStmt
                    , [ a { actionExits = getOuts (actionLocation a) } | a <- as0 ]
                    , outs
                    )
  where
    labeledStmt      = label stmt
    ((outs, as), st) = runState (toActions labeledStmt) st0  
    getOuts loc      = [ (fst <$> p, i') | (p, i') <- M.findWithDefault [] loc cfg ]

    cfg  = cfgMap st
    bind = Bind { bvar = w , bsort = Int }
    st0  = CFG [] (bind : bs) M.empty M.empty
    as0  = fmap (fmap fst) as

-------------------------------------------------------------------------------
-- Substitution
-------------------------------------------------------------------------------

class Subst b where
  subst :: Id -> (Expr a) -> b a -> b a

instance Subst Stmt where
  subst v e (Assign {..})  = Assign { assignExpr = subst v e assignExpr, .. }
  subst v e (Seq {..})     = Seq { seqStmts = subst v e <$> seqStmts, .. }
  subst v e (ForEach {..})
    | v /= bvar forElement = ForEach { forInvariant = subst v e <$> forInvariant
                                     , forStmt = subst v e forStmt
                                     , ..
                                     }
    | otherwise            = ForEach {..}
  subst v e (Atomic {..})  = Atomic { atomicStmt = subst v e atomicStmt, .. }
  subst v e (If {..})      = If { ifCondition = subst v e ifCondition
                                , thenStmt = subst v e thenStmt
                                , elseStmt = subst v e elseStmt
                                , ..
                                }
  subst v e (Assert {..})  = Assert { stmtProperty = subst v e stmtProperty, .. }
  subst v e (Assume {..})  = Assume { stmtProperty = subst v e stmtProperty, .. }
  subst v e (Par {..})     = Par { parStmt = subst v e parStmt, .. }
  subst _ _ (Skip {..})    = Skip {..}
  subst _ _ _              = error "subst stmt"

instance Subst Expr where
  subst _ _ (Const i)        = Const i
  subst v e var@(Var x)      = if v == x then e else var
  subst v e (Bin o e1 e2)    = Bin o (subst v e e1) (subst v e e2)
  subst v e (Select e1 e2)   = Select (subst v e e1) (subst v e e2)
  subst v e (Store e1 e2 e3) = Store (subst v e e1) (subst v e e2) (subst v e e3)
  subst _ _ EmptySet         = EmptySet
  subst v e (Size a)         = Size (subst v e a)
  subst _ _ NonDetValue      = NonDetValue
  subst v e (PExpr a)        = PExpr (subst v e a)
  subst v e (Ite prop e1 e2) = Ite (subst v e prop) (subst v e e1) (subst v e e2)

instance Subst Prop where
  subst v e = go
    where go (Atom r e1 e2)          = Atom r (subst v e e1) (subst v e e2)
          go (Not p)                 = Not (subst v e p)
          go (And ps)                = And (go <$> ps)
          go (Or ps)                 = Or (go <$> ps)
          go (p :=>: q)              = go p :=>: go q
          go (Forall xs p)
            | v `elem` (bvar <$> xs) = Forall xs p
            | otherwise              = Forall xs (go p)
          go (Exists xs p)
            | v `elem` (bvar <$> xs) = Exists xs p
            | otherwise              = Exists xs (go p)
          go TT                      = TT
          go FF                      = FF
          go (Prop e')               = Prop (subst v e e')
          go (Here e')               = Here $ subst v e e'
          go (NonDetProp)            = NonDetProp
          go (Let xs p)
            | v `elem` (bvar . fst <$> xs) = Let xs p
            | otherwise                    = Let xs (go p)
          go p@(PVar _)              = p

-------------------------------------------------------------------------------
-- Helper Functions
-------------------------------------------------------------------------------

-- | Gives an unique identifier to every statement
label      :: Stmt a -> Stmt (a, Int)
label stmt = evalState (mapM go stmt) 0
  where
    go   :: s -> State Int (s, Int)
    go s = do i <- get :: State Int Int
              put (i + 1)
              return (s, i)

getStmtLoc :: Stmt (a, Int) -> Int
getStmtLoc = snd . stmtData

firstOf :: Stmt (a, Int) -> [Int]
firstOf (If _ s1 s2 _) = firstOf s1 ++ firstOf s2
firstOf stmt           = [ getStmtLoc stmt ]

pc :: Id -> Id -> Expr a
pc ps p = Select (Var (pcName ps)) (Var p)

pc' :: Id -> Id -> Expr a
pc' ps p = Select (Var (pcName' ps)) (Var p)

pcName :: Id -> Id
pcName ps = "pc!" ++ ps

pcName' :: Id -> Id
pcName' ps = "pc'!" ++ ps

writes :: Stmt a -> [Binder]
writes = nub . go
  where
    go                :: Stmt a -> [Binder]
    go (Skip {..})    = []
    go (Assert {..})  = []
    go (Assume {..})  = []
    go (If {..})      = go thenStmt ++ go elseStmt
    go (Atomic {..})  = go atomicStmt
    go (Assign {..})  = [assignVar]
    go (Seq {..})     = seqStmts >>= go
    go (ForEach {..}) = forElement : go forStmt
    go (While {..})   = go whileStmt
    go (Cases {..})   = caseList >>= go . caseStmt
    go (Par {..})     = go parStmt
