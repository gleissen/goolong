{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ConstraintKinds #-}

module Language.IceT.VCGen (verifyFile, verifyProgram) where

import Prelude hiding (and, or)
import Language.IceT.Types
import Language.IceT.Parse (parseFile, parseString)
import System.Exit

import qualified Language.Fixpoint.Horn.Types   as H
import qualified Language.Fixpoint.Horn.Solve   as H
import qualified Language.Fixpoint.Solver       as Solver
import qualified Language.Fixpoint.Types.Config as F 

type HornData = ()
type Query = H.Query HornData

verifyProgram :: String -> IO Bool
verifyProgram = verify . parseString
  
verifyFile :: FilePath -> IO Bool
verifyFile fp = parseFile fp >>= verify

verify :: VCAnnot a => Program a -> IO Bool
verify (Program{..}) = do
  result <- H.solve cfg query
  code <- Solver.resultExitCode result
  return $ code == ExitSuccess

  where
    cfg = F.defConfig
    query = vcgen decls cardDecls prog ensures

vcgen :: VCAnnot a => [Binder] -> [Card a] -> Stmt a -> Prop a -> Query
vcgen = undefined
