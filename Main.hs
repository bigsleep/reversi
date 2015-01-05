module Main where

import Cui (runReversi)

main :: IO ()
main = do
    r <- runReversi
    print r
