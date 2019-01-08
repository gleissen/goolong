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
  where exit True = do putStrLn (green "✓ SAFE")
                       exitSuccess
        exit _    = do putStrLn (red "✗ UNSAFE")
                       exitFailure

        green s = "\x1b[32m \x1b[1m" ++ s ++ defaultColor
        red s   = "\x1b[31m \x1b[1m" ++ s ++ defaultColor
        defaultColor = "\x1b[0m"
