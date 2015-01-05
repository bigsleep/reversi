{-# LANGUAGE MultiParamTypeClasses, DeriveDataTypeable, DeriveFunctor, TypeFamilies, TemplateHaskell, QuasiQuotes #-}
module Reversi
( Reversi(..)
, ReversiM
, Board
, Player(..)
, Cell(..)
, ReversiResult
, reversiStateBoard
, reversiStateMoves
, emptyBoard
, judge
, move
, enumerateMoves
, reversi
) where

import Data.Typeable (Typeable)
import Control.Monad.Identity (runIdentity)
import Control.Monad.State (StateT, get, modify, evalStateT)
import Control.Monad.Trans (lift)
import Control.Monad.Free (Free(..))
import Control.Monad (when, liftM)
import qualified Data.Array.Repa as Repa (Array, U, DIM2, Z(..), (:.)(..), (!), extent, fromListUnboxed, map, computeP, foldAllP, fromFunction)
import qualified Data.Array.Repa.Shape as Repa (Shape(..))
import Data.Vector.Unboxed.Deriving (derivingUnbox)
import Data.Word (Word8)

data Player = Black | White deriving (Show, Eq, Enum)

data Cell = Empty | Disc Player  deriving (Show, Eq)

cellToWord8 :: Cell -> Word8
cellToWord8 Empty = 0
cellToWord8 (Disc Black) = 1
cellToWord8 (Disc White) = 2

word8ToCell :: Word8 -> Cell
word8ToCell 0 = Empty
word8ToCell 1 = Disc Black
word8ToCell 2 = Disc White
word8ToCell _ = undefined

derivingUnbox "Cell" [t|Cell -> Word8|] [|cellToWord8|] [|word8ToCell|]

type Matrix = Repa.Array Repa.U Repa.DIM2

type Board = Matrix Cell

data ReversiResult = BlackWin | WhiteWin | Even deriving (Show, Eq, Enum)

data Move = Move Player (Int, Int) | NoMove Player deriving (Show, Eq)

data ReversiState = ReversiState
    { reversiStateBoard :: Board
    , reversiStateMoves :: [Move]
    } deriving (Show, Eq)

emptyBoard :: Int -> Board
emptyBoard size = Repa.fromListUnboxed (Repa.Z Repa.:. size Repa.:. size) (replicate (size * size) Empty)

initialState :: ReversiState
initialState = ReversiState (emptyBoard 0) []

judge :: Board -> ReversiResult
judge = judge' . runIdentity . Repa.foldAllP add (0, 0) . Repa.map f
    where
    judge' (a, b) | a == b = Even
    judge' (a, b) | a > b = BlackWin
    judge' _ = WhiteWin

    add (a, b) (c, d) = (a + c, b + d)

    f :: Cell -> (Int, Int)
    f Empty = (0, 0)
    f (Disc Black) = (1, 0)
    f (Disc White) = (0, 1)

move :: Move -> Board -> [(Int, Int)]
move (NoMove _) _ = []
move (Move _ q) board
    | not (Repa.inShapeRange (toDIM2 (0, 0)) (Repa.extent board) (toDIM2 q))
    || board Repa.! toDIM2 q /= Empty
        = []
move (Move p (qx, qy)) board =
    concat [ move' (qx + x, qy + y) (x, y) [] | x <- [-1..1], y <- [-1..1], (x, y) /= (0, 0)]

    where
    start = toDIM2 (0, 0)
    end = Repa.extent board
    color = Disc p
    move' z _ _
        | not (Repa.inShapeRange start end (toDIM2 z))
        || board Repa.! toDIM2 z == Empty
            = []
    move' z _ zs
        | board Repa.! toDIM2 z == color
            = zs
    move' z @ (a, b) (dx, dy) zs = move' (a + dx, b + dy) (dx, dy) (z : zs)

enumerateMoves :: Player -> Board -> [(Int, Int)]
enumerateMoves p board = [(x, y) | x <- [0..(w-1)], y <- [0..(h-1)], not . null $ move (Move p (x, y)) board]
    where
    Repa.Z Repa.:. w Repa.:. h = Repa.extent board

updateBoard :: Cell -> [(Int, Int)] -> Board -> Board
updateBoard c ps board = runIdentity . Repa.computeP $ Repa.fromFunction ex f
    where
    ex = Repa.extent board
    f sh | toP sh `elem` ps = c
    f sh = board Repa.! sh

data Reversi a =
    LoadBoardSize (Int -> a) |
    InputMove Board [(Int, Int)] Player ((Int, Int) -> a) |
    OutputState ReversiState a |
    PutError String
    deriving (Typeable, Functor)

type ReversiM = Free Reversi

loadBoardSize :: StateT ReversiState ReversiM Int
loadBoardSize = lift . Free . LoadBoardSize $ Pure

inputMove :: Board -> [(Int, Int)] -> Player -> StateT ReversiState ReversiM (Int, Int)
inputMove board ms player = lift . Free . InputMove board ms player $ Pure

outputState :: ReversiState -> StateT ReversiState ReversiM ()
outputState s = lift . Free . OutputState s $ Pure ()

putError :: String -> StateT ReversiState ReversiM a
putError = lift . Free . PutError

pushMove :: Move -> StateT ReversiState ReversiM ()
pushMove m = modify $ \s -> s { reversiStateMoves = m : reversiStateMoves s }

getMoves :: StateT ReversiState ReversiM [Move]
getMoves = liftM reversiStateMoves get

getBoard :: StateT ReversiState ReversiM Board
getBoard = liftM reversiStateBoard get

putBoard :: Board -> StateT ReversiState ReversiM ()
putBoard board = modify $ \s -> s { reversiStateBoard = board }

reversi :: ReversiM ReversiResult
reversi = flip evalStateT initialState $ do
    size <- loadBoardSize

    putBoard $ emptyBoard size

    initialMoves $ size `div` 2

    outputState =<< get

    takeWhileM_ (const isNotEnd) $ cycle [turn Black, turn White]

    return . judge =<< getBoard

    where
    initialMoves half =
        putBoard . updateBoard (Disc Black) [(half - 1, half), (half, half - 1)]
                 . updateBoard (Disc White) [(half - 1, half - 1), (half, half)] =<< getBoard

    turn player = do
        board <- getBoard
        let ms = enumerateMoves player board
        if null ms
            then pushMove (NoMove player)
            else do
                q <- inputMove board ms player
                let ps = move (Move player q) board
                when (null ps) $ putError "impossible move"
                putBoard $ updateBoard (Disc player) (q : ps) board
                pushMove (Move player q)
        outputState =<< get

    isNotEnd = liftM isNotEnd' getMoves

    isNotEnd' (NoMove _ : NoMove _ : _) = False
    isNotEnd' _ = True

    takeWhileM_ _ [] = return ()
    takeWhileM_ a (b : bs) = a b >>= flip when (b >> takeWhileM_ a bs)

toDIM2 :: (Int, Int) -> Repa.DIM2
toDIM2 (a, b) = Repa.Z Repa.:. a Repa.:. b
toP :: Repa.DIM2 -> (Int, Int)
toP sh = (a, b)
    where
    Repa.Z Repa.:. a Repa.:. b = sh
