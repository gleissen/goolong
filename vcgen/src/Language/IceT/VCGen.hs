{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ConstraintKinds #-}

module Language.IceT.VCGen (verifyFile, verifyProgram) where

import Prelude hiding (and, or)
import Language.IceT.Types
import Language.IceT.Parse (parseFile, parseString)


-------------------------------------------------------------------------------
-- IO one-stop-shop
-------------------------------------------------------------------------------
verifyProgram :: String -> IO Bool
verifyProgram = verify . parseString
  
verifyFile :: FilePath -> IO Bool
verifyFile fp = parseFile fp >>= verify

verify :: VCAnnot a => Program a -> IO Bool
verify _ = undefined
