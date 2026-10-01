{-# LANGUAGE BangPatterns  #-}
{-# LANGUAGE MagicHash     #-}
{-# LANGUAGE UnboxedTuples #-}
module Main (main) where

import Data.Time.Clock
  ( NominalDiffTime,
    diffUTCTime,
    getCurrentTime,
  )
import GHC.Environment (getFullArgs)
import qualified Math.NumberTheory.Roots as Old (integerSquareRoot)
import qualified Math.NumberTheory.Roots_ as New (integerSquareRoot)
import System.Random.Stateful (globalStdGen, uniformRM)
import GHC.Num.BigNat (BigNat(..), bigNatSize#)
import GHC.Exts (Word#, Word(..), Int(..))
import GHC.Natural (Natural(..))


iRange :: Integer -> (Integer, Integer)
iRange x = (2 ^ x, 2 ^ (x + 1))

main :: IO ()
main = do
  -- putStrLn "Searching args..."
  -- args <- getFullArgs
  -- print args
  iIntInteger <- getRndMInt (iRange 31)
  iHugeWord <- getRndMInt (iRange 63)
  iHumongous <- getRndMInt (iRange 129)
  iGargantuan <- getRndMInt (iRange 257)
  iGoogolplex <- getRndMInt (iRange 511)
  iFZeight <- getRndMInt (iRange 1023)
  iBoogol <- getRndMInt (iRange 2046)
  printNatSize (fromInteger iBoogol)
  -- putStrLn "iHumongous Old"
  x2 <- timeit (pure $ Old.integerSquareRoot iHumongous)
  print x2
  -- putStrLn "iHumongous New"
  x3 <- timeit (pure $ New.integerSquareRoot iHumongous)
  print x3
  -- putStrLn "iBoogol Old"
  x4 <- timeit (pure $ Old.integerSquareRoot iBoogol)
  print x4
  -- putStrLn "iBoogol New"
  x5 <- timeit (pure $ New.integerSquareRoot iBoogol)
  print x5
  -- putStrLn "------------"

-- -- | Helper function
timeit :: IO a -> IO (Maybe a, NominalDiffTime)
timeit action = do
  start <- getCurrentTime
  value <- action
  end <- getCurrentTime
  pure (Just value, diffUTCTime end start)

-- | Get a Random Integer with uniform probability in the range (l,u)
getRndMInt :: (Integer, Integer) -> IO Integer
getRndMInt (l, u) = max l . min u <$> uniformRM (l, u) globalStdGen -- uniformRM (a, b) = uniformRM (b, a) holds as per fn defn

printNatSize :: Natural -> IO ()
printNatSize (NatS# n#) = putStrLn $ "Natural size in words: " ++ show (W# (1##))
printNatSize (NatJ# n@(BN# n#)) = do 
  let fullSize = bigNatSize# n# 
  putStrLn $ "Natural size in words: " ++ show (I# fullSize)

--  cabal run integer-roots-exe "+RTS -I0 -K256m -A16m -N8 -H24m -T -w -RTS --output=integer-roots.html" -p
