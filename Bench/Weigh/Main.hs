module Main (main) where

import Data.Time.Clock
  ( NominalDiffTime,
    diffUTCTime,
    getCurrentTime,
  )
import qualified Math.NumberTheory.Roots as Old (integerSquareRoot)
import qualified Math.NumberTheory.Roots_ as New (integerSquareRoot)
import System.Random.Stateful (globalStdGen, uniformRM)
import Weigh
import GHC.Environment (getFullArgs)

one,two :: String
one = "one"
two = "two"

main :: IO ()
main = do 
  iIntInteger <- getRndMInt (2^31, 2^32) 
  iHugeWord <- getRndMInt (2^63, 2^64)  
  iHumongous <- getRndMInt (2^129, 2^130) 
  iGargantuan <- getRndMInt (2^257, 2^258) 
  iGoogolplex <- getRndMInt (2^511, 2^512) 
  iFZeight <- getRndMInt (2^1023, 2^1024) 
  iBoogol <- getRndMInt (2^2046, 2^2047) 
  mainWith $ do
    setColumns [Case, Allocated, Max, Live, GCs, MaxOS, WallTime] -- new
    value "()"         ()
    value "1"          (1 :: Int)
    value "True"       True
    value "[0..3]"     ([0..3] :: [Int])
    value "[0,1,2,3]"  ([0,1,2,3] :: [Int])
    value "one"        one
    func "Old Int Integer" Old.integerSquareRoot (fromIntegral iIntInteger :: Int)
    func "New Int Integer"  New.integerSquareRoot (fromIntegral iIntInteger :: Int)
    func "Old Huge Integer" Old.integerSquareRoot (fromIntegral iHugeWord :: Word)
    func "New Huge Integer" New.integerSquareRoot (fromIntegral iHugeWord :: Word)
    func "Old Humoungous Integer " Old.integerSquareRoot iHumongous
    func "New Humoungous Integer " New.integerSquareRoot iHumongous
    func "Old Gargantuan Integer" Old.integerSquareRoot iGargantuan
    func "New Gargantuan Integer"  New.integerSquareRoot iGargantuan
    func  "Old Googolplex Integer " Old.integerSquareRoot iGoogolplex
    func "New Googolplex Integer " New.integerSquareRoot iGoogolplex
    func "Old FZeight Integer "  Old.integerSquareRoot iFZeight
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

