{-# LANGUAGE MultiParamTypeClasses, DeriveDataTypeable, DeriveFunctor, TypeFamilies, TemplateHaskell, QuasiQuotes #-}
module Reversi
( Reversi
, Board
, InnerBoard
, Player
, Cell
, ReversiResult
, black
, white
, getInnerBoard
, emptyBoard
, judge
, move
, enumerateMoves
, reversi
) where

import Data.Typeable (Typeable)
import Control.Monad.Identity (runIdentity)
import Control.Monad.State (StateT, get, modify)
import Control.Monad.Trans (lift)
import Control.Monad.Free (Free(..))
import Control.Monad (when, liftM)
import qualified Data.Array.Repa as Repa (Array, U, DIM2, Z(..), (:.)(..), (!), extent, fromListUnboxed, map, computeP, foldAllP, fromFunction)
import qualified Data.Array.Repa.Shape as Repa (Shape(..))
import Data.Vector.Unboxed.Deriving (derivingUnbox)
import Data.Word (Word8)

data Player = Black | White deriving (Show, Eq, Enum)

black, white :: Player
black = Black
white = White

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

type InnerBoard = Matrix Cell

newtype Board = Board { unBoard :: InnerBoard } deriving (Show, Eq)

data ReversiResult = BlackWin | WhiteWin | Even deriving (Show, Eq, Enum)

data Move = Move Player (Int, Int) | NoMove Player deriving (Show, Eq)

data ReversiState = ReversiState
    { reversiStateBoard :: Board
    , reversiStateMoves :: [Move]
    } deriving (Show, Eq)

getInnerBoard :: Board -> InnerBoard
getInnerBoard = unBoard

emptyBoard :: Int -> Board
emptyBoard size = Board $ Repa.fromListUnboxed (Repa.Z Repa.:. size Repa.:. size) (replicate (size * size) Empty)

disc :: Player -> Cell
disc = Disc

judge :: InnerBoard -> ReversiResult
judge = judge' . runIdentity . Repa.foldAllP add (0, 0) . Repa.map f
    where
    judge' (a, b) | a == b = Even
    judge' (a, b) | a > b = BlackWin
    judge' _ = WhiteWin

    add (a, b) (c, d) = (a + b, c + d)

    f :: Cell -> (Int, Int)
    f Empty = (0, 0)
    f (Disc Black) = (1, 0)
    f (Disc White) = (0, 1)

move :: Move -> InnerBoard -> [(Int, Int)]
move (NoMove _) _ = []
move (Move _ q) board
    | not (Repa.inShapeRange (toDIM2 (0, 0)) (Repa.extent board) (toDIM2 q))
    || board Repa.! toDIM2 q /= Empty
        = []
move (Move p (qx, qy)) board =
    concat [ move' (qx + x, qy + y) (x, y) [(qx, qy)] | x <- [-1..1], y <- [-1..1], (x, y) /= (0, 0)]

    where
    start = toDIM2 (0, 0)
    end = Repa.extent board
    color = disc p
    move' z _ _
        | not (Repa.inShapeRange start end (toDIM2 z))
        || board Repa.! toDIM2 z == Empty
            = []
    move' z _ zs
        | board Repa.! toDIM2 z == color
            = zs
    move' z @ (a, b) (dx, dy) zs = move' (a + dx, b + dy) (dx, dy) (z : zs)

enumerateMoves :: Player -> InnerBoard -> [(Int, Int)]
enumerateMoves p board = [(x, y) | x <- [0..(w-1)], y <- [0..(h-1)], not . null $ move (Move p (x, y)) board]
    where
    Repa.Z Repa.:. w Repa.:. h = Repa.extent board

updateBoard :: Cell -> [(Int, Int)] -> InnerBoard -> InnerBoard
updateBoard c ps board = runIdentity . Repa.computeP $ Repa.fromFunction ex f
    where
    ex = Repa.extent board
    f sh | toP sh `elem` ps = c
    f sh = board Repa.! sh

data Reversi a =
    LoadBoardSize (Int -> a) |
    InputMove Player ((Int, Int) -> a) |
    OutputState ReversiState a |
    PutError String
    deriving (Typeable, Functor)

type ReversiM = StateT ReversiState (Free Reversi)

loadBoardSize :: ReversiM Int
loadBoardSize = lift . Free . LoadBoardSize $ Pure

inputMove :: Player -> ReversiM (Int, Int)
inputMove player = lift . Free . InputMove player $ Pure

outputState :: ReversiState -> ReversiM ()
outputState s = lift . Free . OutputState s $ Pure ()

putError :: String -> ReversiM a
putError = lift . Free . PutError

pushMove :: Move -> ReversiM ()
pushMove m = modify $ \s -> s { reversiStateMoves = m : reversiStateMoves s }

getMoves :: ReversiM [Move]
getMoves = liftM reversiStateMoves get

getBoard :: ReversiM Board
getBoard = liftM reversiStateBoard get

putBoard :: Board -> ReversiM ()
putBoard board = modify $ \s -> s { reversiStateBoard = board }

reversi :: ReversiM ReversiResult
reversi = do
    size <- loadBoardSize

    putBoard $ emptyBoard size

    initialMoves $ size `div` 2

    takeWhileM_ (const isNotEnd) . take (turnLimit size) $ cycle [turn Black, turn White]

    return . judge . unBoard =<< getBoard

    where
    turnLimit size = size * size - 4

    initialMoves half = do
        pushMove $ Move Black (half - 1, half)
        pushMove $ Move White (half - 1, half - 1)
        pushMove $ Move Black (half, half - 1)
        pushMove $ Move White (half, half)
        putBoard . Board
                 . updateBoard (Disc Black) [(half - 1, half), (half, half - 1)]
                 . updateBoard (Disc Black) [(half - 1, half - 1), (half, half)]
                 . unBoard =<< getBoard

    turn player = do
        board <- fmap unBoard getBoard
        if null (enumerateMoves player board)
            then pushMove (NoMove player)
            else do
                q <- inputMove player
                let ps = move (Move player q) board
                when (null ps) $ putError "impossible move"
                putBoard . Board $ updateBoard (disc player) ps board
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
