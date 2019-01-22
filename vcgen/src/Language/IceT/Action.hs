{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ConstraintKinds #-}

module Language.IceT.Action ( extractCFG
                            , LabeledAction(..)
                            , ActionResult(..)
                            ) where

-- import           Language.IceT.SMT
import           Language.IceT.Types hiding (CFG, actions)

import           Control.Monad.State
import qualified Data.Graph.Inductive.Graph        as G
import           Data.Graph.Inductive.PatriciaTree
-- import qualified Data.HashMap.Strict               as HM
import qualified Data.IntMap.Strict                as IM
import qualified Data.IntSet                       as IS
import           Data.List (foldl')
import           Text.Printf

data LabeledAction a = LA { laLabel :: Expr a
                          , laStmt  :: Stmt a
                          , laPC    :: Int
                          }

data ActionResult a = ActionResult { arMap    :: ActionMap a
                                   , arPC0    :: Int
                                   , arPCExit :: Int
                                   , arCFG    :: CFG
                                   }

data ActionState a = ActionState { freshCounter :: Int }

type ActionGen a r = State (ActionState a) r 
type ActionMap a = IM.IntMap (LabeledAction a)
type CFG = UGr  

-- given a statement, returns the following:
-- 1. A map from program counters to statements
-- 2. initial program location (l_0)
-- 3. last program location (l_exit)
-- 4. control flow graph
extractCFG :: VCAnnot a => Int -> Stmt a -> ActionResult a
extractCFG initCounter stmt = result
  where
    (result, _) = runState action (ActionState { freshCounter = initCounter })

    action = do
      pc0 <- incrCounter
      stmt' <- labelStmts stmt
      pcExit <- incrCounter
      let g = actions (pc0, pcExit) stmt'
      return ActionResult { arMap = createActionMap stmt'
                          , arPC0 = pc0
                          , arPCExit = pcExit
                          , arCFG = g
                          }

    labelStmts :: VCAnnot a => Stmt a -> ActionGen a (Stmt (a, Int))
    labelStmts s = mapM (\a -> do ActionState{..} <- get
                                  put ActionState{ freshCounter = freshCounter + 1, .. }
                                  return (a, freshCounter)) s

-- Given the l_0 and l_exit labels, and a statement, creates a control flow graph
-- of atomic actions
actions :: VCAnnot a => (Int, Int) -> Stmt (a, Int) -> CFG
actions (pc0, pcExit) stmt = G.mkUGraph nodes edges
  where
    nodes = IS.toList $
            foldl' (\s (n1,n2) -> IS.insert n1 (IS.insert n2 s)) IS.empty edges
    edges = go stmt ++
            [ (pc0, stmtPc p)   | p <- firstStmt stmt ] ++
            [ (stmtPc p,pcExit) | p <- lastStmt stmt ]

    stmtPc = snd . stmtData

    go (Seq {..}) = case seqStmts of
                      []   -> []
                      s:ss -> let s' = Seq { seqStmts = ss, ..}
                              in go s ++
                                 go s' ++
                                 [ (stmtPc p1, stmtPc p2)
                                 | p1 <- lastStmt s
                                 , p2 <- firstStmt s'
                                 ]
    go (ForEach {..}) = go forStmt ++
                        [ (stmtPc p1, stmtPc p2)
                        | p1 <- lastStmt forStmt
                        , p2 <- firstStmt forStmt
                        ]
    go (While {..}) = go whileStmt ++
                      [ (stmtPc p1, stmtPc p2)
                      | p1 <- lastStmt whileStmt
                      , p2 <- firstStmt whileStmt
                      ]
    go (If {..})      = go thenStmt ++ go elseStmt
    go (Cases {..})   = caseStmt <$> caseList >>= go
    go (Skip    {..}) = []
    go (Assert  {..}) = []
    go (Assume  {..}) = []
    go (Assign  {..}) = []
    go (Atomic  {..}) = []
    go (Par {..})     = error "actions called with a parallel composition !"

-- Returns the first statement(s) of a langugage construct, or the statement itself
firstStmt :: Show a => Stmt a -> [Stmt a]
firstStmt s@(Skip    {..}) = [s]
firstStmt s@(Assert  {..}) = [s]
firstStmt s@(Assume  {..}) = [s]
firstStmt s@(Assign  {..}) = [s]
firstStmt s@(Atomic  {..}) = [s]
firstStmt s@(ForEach {..}) = firstStmt forStmt
firstStmt s@(While   {..}) = firstStmt whileStmt
firstStmt s@(If      {..}) = firstStmt thenStmt ++ firstStmt elseStmt
firstStmt s@(Cases   {..}) = firstStmt =<< (caseStmt <$> caseList)
firstStmt s@(Seq     {..}) = go seqStmts
  where
    go []      = []
    go (s2:ss) = case firstStmt s2 of
                   [] -> go ss
                   l  -> l
firstStmt s = error $ printf "firstStmt called with %s" (show s)

-- Returns the last statement(s) of a langugage construct, or the statement itself
lastStmt :: Show a => Stmt a -> [Stmt a]
lastStmt s@(Skip    {..}) = [s]
lastStmt s@(Assert  {..}) = [s]
lastStmt s@(Assume  {..}) = [s]
lastStmt s@(Assign  {..}) = [s]
lastStmt s@(Atomic  {..}) = [s]
lastStmt s@(ForEach {..}) = lastStmt forStmt
lastStmt s@(While   {..}) = lastStmt whileStmt
lastStmt s@(If      {..}) = lastStmt thenStmt ++ lastStmt elseStmt
lastStmt s@(Cases   {..}) = lastStmt =<< (caseStmt <$> caseList)
lastStmt s@(Seq     {..}) = go (reverse seqStmts)
  where
    go []      = []
    go (s2:ss) = case lastStmt s2 of
                   [] -> go ss
                   l  -> l
lastStmt s = error $ printf "firstStmt called with %s" (show s)

-- creates a map from labeled statements
createActionMap :: Stmt (a, Int) -> ActionMap a
createActionMap = go IM.empty
  where
    n = snd . stmtData
    go m s =
      case s of
        Skip    {..} -> m'
        Assert  {..} -> m'
        Assume  {..} -> m'
        Assign  {..} -> m'
        Par     {..} -> go m' parStmt
        Atomic  {..} -> go m' atomicStmt
        ForEach {..} -> go m' forStmt
        While   {..} -> go m' whileStmt
        If      {..} -> gos [thenStmt, elseStmt]
        Cases   {..} -> gos $ caseStmt <$> caseList
        Seq     {..} -> gos seqStmts
      where
        s_pc   = n s
        la     = LA { laLabel = undefined
                    , laStmt  = fmap fst s
                    , laPC    = s_pc
                    }
        m'     = IM.insert s_pc la m
        gos ss = foldl' go m' ss

incrCounter :: ActionGen a Int
incrCounter = do
  n <- gets freshCounter
  modify $ \ActionState{..} -> ActionState { freshCounter = n + 1 , .. }
  return n
