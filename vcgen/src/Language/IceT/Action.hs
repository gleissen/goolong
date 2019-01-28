{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}

module Language.IceT.Action ( extractCFG
                            , ActionResult(..)
                            ) where

import           Language.IceT.Types hiding (CFG, actions)
import           Language.IceT.Pretty

import           Control.Monad.State
import qualified Data.Graph.Inductive.Graph        as G
import           Data.Graph.Inductive.PatriciaTree
import qualified Data.IntMap.Strict                as IM
import qualified Data.IntSet                       as IS
import           Data.List (foldl')
import           Text.Printf

-- import Debug.Trace

data ActionResult a = ActionResult { arMap    :: ActionMap a
                                   , arPC0    :: Int
                                   , arPCExit :: Int
                                   , arCFG    :: CFG
                                   }

data ActionState a = ActionState { freshCounter :: Int }

type ActionGen a r = State (ActionState a) r 
type ActionMap a = IM.IntMap (Stmt a)
type CFG = UGr  

--------------------------------------------------------------------------------
-- Merge local statements together to create a program consists of only atomic
-- actions to be used for generating the verification conditions for the
-- parallel case.
-- First argument is used as the fresh counter to give labels, and returns the
-- counter value afterwards.
--------------------------------------------------------------------------------
atomize :: Int -> Stmt a -> (Stmt a, Int)
--------------------------------------------------------------------------------
atomize c parStatement = (atomizeResult, freshCounter st')
  where
    (atomizeResult, st') = runState (go parStatement) $ ActionState { freshCounter = c }
      
    ------------------------------------------------------------
    go :: Stmt a -> ActionGen a (Stmt a)
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
    goHelper :: [Stmt a] -> ActionGen a [Stmt a]
    ------------------------------------------------------------
    goHelper ss = do
      sss <- partitionStmts ss 
      mapM mergeStmts sss

    ------------------------------------------------------------
    -- given a sequence of statements, partition them such that
    -- we can create atomic blocks
    ------------------------------------------------------------
    partitionStmts :: [Stmt a] -> ActionGen a [[Stmt a]]
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
    mergeStmts :: [Stmt a] -> ActionGen a (Stmt a)
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
extractCFG :: (Show a, VCAnnot a) => Id -> Int -> Stmt a -> ActionResult a
--------------------------------------------------------------------------------
extractCFG ps initCounter stmt =
  ActionResult { arMap    = createActionMap atomizedStmt
               , arPC0    = pc0
               , arPCExit = pcExit
               , arCFG    = g
               }
  where
    pc0 = initCounter
    (atomizedStmt0, pcExit) = atomize (pc0 + 1) stmt
    atomizedStmt = replaceHere ps atomizedStmt0
    -- atomizedStmt = trace (pretty _atomizedStmt) _atomizedStmt

    g :: CFG
    g = G.mkUGraph nodes edges

    nodes = IS.toList $
            foldl' (\s (n1,n2) -> IS.insert n1 (IS.insert n2 s)) IS.empty edges
    edges = go atomizedStmt ++
            [ (pc0, stmtPC p)   | p <- firstStmt atomizedStmt ] ++
            [ (stmtPC p,pcExit) | p <- lastStmt atomizedStmt ]

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
createActionMap :: Show a => Stmt a -> ActionMap a
createActionMap = go IM.empty
  where
    go m s =
      case s of
        Atomic  {..} -> IM.insert atomicLabel s m
        ForEach {..} -> go m forStmt
        While   {..} -> go m whileStmt
        If      {..} -> gos [thenStmt, elseStmt]
        Cases   {..} -> gos $ caseStmt <$> caseList
        Seq     {..} -> gos seqStmts
        _            -> error $ printf "createActionMap.go called with sth other than expected !"
      where
        gos ss = foldl' go m ss

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

incrCounter :: ActionGen a Int
incrCounter = do
  n <- gets freshCounter
  modify $ \ActionState{..} -> ActionState { freshCounter = n + 1 , .. }
  return n

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
