module Main (main) where

-- import Data.Time.Clock
--   ( NominalDiffTime,
--     diffUTCTime,
--     getCurrentTime,
--   )
-- import qualified Math.NumberTheory.Roots as Old (integerSquareRoot)
import qualified Math.NumberTheory.Roots_ as New (integerSquareRoot)
import System.Random.Stateful (globalStdGen, uniformRM)
import GHC.Environment (getFullArgs)

iRange :: Integer -> (Integer, Integer) 
iRange x = (2 ^ x, 2 ^ (x+1))

main :: IO ()
main = do
  putStrLn "Searching args..."
  args <- getFullArgs
  print args
  iIntInteger <- getRndMInt (iRange 31)
  iHugeWord <- getRndMInt  (iRange 63)
  iHumongous <- getRndMInt  (iRange 129) 
  iGargantuan <- getRndMInt (iRange 257)
  iGoogolplex <- getRndMInt (iRange 511) 
  iFZeight <- getRndMInt (iRange 1023) 
  iBoogol <- getRndMInt (iRange 2046)  
  _ <- pure $ New.integerSquareRoot iHumongous 
  putStrLn "------------"

-- -- | Helper function
-- timeit :: IO a -> IO (Maybe a, NominalDiffTime)
-- timeit action = do
--   start <- getCurrentTime
--   value <- action
--   end <- getCurrentTime
--   pure (Just value, diffUTCTime end start)

-- | Get a Random Integer with uniform probability in the range (l,u)
getRndMInt :: (Integer, Integer) -> IO Integer
getRndMInt (l, u) = max l . min u <$> uniformRM (l, u) globalStdGen -- uniformRM (a, b) = uniformRM (b, a) holds as per fn defn
