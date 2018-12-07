module Main where

import System.Environment
import System.Exit
import Language.IceT.VCGen

main :: IO ()
main = do args <- getArgs
          case args of
            []  -> getContents >>= verifyProgram >>= exit
            [f] -> verifyFile f >>= exit
            _   -> exitFailure
  where exit True = do putStrLn (green ++ "✓ SAFE")
                       exitSuccess
        exit _    = do putStrLn (red ++ "✗ UNSAFE")
                       exitFailure

        green = "\x1b[32m"
        red   = "\x1b[31m"
