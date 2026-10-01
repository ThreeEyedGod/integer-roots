{-# LANGUAGE MagicHash #-}

module Main (main) where

import Data.Time.Clock
  ( NominalDiffTime,
    diffUTCTime,
    getCurrentTime,
  )
import GHC.Exts (Int#)
import GHC.Environment (getFullArgs)
import qualified Math.NumberTheory.Roots as Old (integerSquareRoot)
import qualified Math.NumberTheory.Roots_ as New (integerSquareRoot)
import System.Random.Stateful (globalStdGen, uniformRM)
import Weigh

one, two :: String
one = "one"
two = "two"

-- data Itr__ = Itr__ {lv__# :: {-# UNPACK #-} !Int#, yCumulative___ :: !Integer, iRem___ :: {-# UNPACK #-} !Integer, tb__# :: {-# UNPACK #-} !FloatingX#} deriving (Generic, NFData, Eq)

iRange :: Integer -> (Integer, Integer)
iRange x = (2 ^ x, 2 ^ (x + 1))

main :: IO ()
main = do
  iIntInteger <- getRndMInt (iRange 31)
  iHugeWord <- getRndMInt (iRange 63)
  iHumongous <- getRndMInt (iRange 129)
  iGargantuan <- getRndMInt (iRange 257)
  iGoogolplex <- getRndMInt (iRange 511)
  iFZeight <- getRndMInt (iRange 1023)
  iBoogol <- getRndMInt (iRange 2046)
  mainWith $ do
    setColumns [Case, Allocated, Max, Live, GCs, MaxOS, WallTime] -- new
    value "()" ()
    value "1" (1 :: Int)
    value "True" True
    value "[0..3]" ([0 .. 3] :: [Int])
    value "[0,1,2,3]" ([0, 1, 2, 3] :: [Int])
    value "one" one
    -- value "Itr__" Itr__
    func "Old Int Integer" Old.integerSquareRoot (fromIntegral iIntInteger :: Int)
    func "New Int Integer" New.integerSquareRoot (fromIntegral iIntInteger :: Int)
    func "Old Huge Integer" Old.integerSquareRoot (fromIntegral iHugeWord :: Word)
    func "New Huge Integer" New.integerSquareRoot (fromIntegral iHugeWord :: Word)
    func "Old Humoungous Integer " Old.integerSquareRoot iHumongous
    func "New Humoungous Integer " New.integerSquareRoot iHumongous
    func "Old Gargantuan Integer" Old.integerSquareRoot iGargantuan
    func "New Gargantuan Integer" New.integerSquareRoot iGargantuan
    func "Old Googolplex Integer " Old.integerSquareRoot iGoogolplex
    func "New Googolplex Integer " New.integerSquareRoot iGoogolplex
    func "Old FZeight Integer " Old.integerSquareRoot iFZeight
    func "New FZeight Integer " New.integerSquareRoot iFZeight
    func "Old Boogol Integer " Old.integerSquareRoot iBoogol
    func "New Boogol Integer " New.integerSquareRoot iBoogol

-- | Helper function
timeit :: IO a -> IO (Maybe a, NominalDiffTime)
timeit action = do
  start <- getCurrentTime
  value <- action
  end <- getCurrentTime
  pure (Just value, diffUTCTime end start)

-- | Get a Random Integer with uniform probability in the range (l,u)
getRndMInt :: (Integer, Integer) -> IO Integer
getRndMInt (l, u) = max l . min u <$> uniformRM (l, u) globalStdGen -- uniformRM (a, b) = uniformRM (b, a) holds as per fn defn
