module Cui
( runReversi
) where

import Reversi (Reversi(..), ReversiResult, Player(..), Cell(..), reversi, reversiStateBoard, reversiStateMoves, enumerateMoves)

import Control.Monad (unless)
import Control.Monad.Free (Free(..))
import Data.Maybe (listToMaybe)
import Data.Array.Repa ((!), ix2)

boardSize :: Int
boardSize = 8

runReversi :: IO ReversiResult
runReversi = run reversi

run :: Free Reversi a -> IO a
run (Pure r) = return r

run (Free (LoadBoardSize f)) = run (f boardSize)

run (Free (InputMove _ ms Black f)) = print ms >> inputMove
    where
    inputMove = do
        putStrLn "x y で入力して下さい。"
        input <- fmap (map maybeRead . words) getLine
        case input of
             [Just x, Just y] | (x, y) `elem` ms -> run (f (x, y))
             _ -> inputMove

    maybeRead = fmap fst . listToMaybe . reads

run (Free (InputMove _ ms _ f)) = run . f . head $ ms

run (Free (OutputState s cont)) = do
    unless (null ms) $ print (head ms)
    putStrLn $ ' ' : concat (map show [0..7])
    sequence_ [showCell' x y (board ! ix2 x y) |y <- [0..size - 1], x <- [0..size - 1]]
    run cont
    where
    size = boardSize
    showCell Empty = '_'
    showCell (Disc Black) = 'B'
    showCell (Disc White) = 'W'
    showCell' i j c | i == 0 = putStr (show j ++ [showCell c])
    showCell' i _ c | i == boardSize - 1 = putStr (showCell c : "\n")
    showCell' _ _ c = putStr [showCell c]
    board = reversiStateBoard s
    ms = reversiStateMoves s

run (Free (PutError s)) = putStrLn s >> error s
