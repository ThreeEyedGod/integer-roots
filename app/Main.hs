module Main (main) where

-- import Data.Time.Clock
--   ( NominalDiffTime,
--     diffUTCTime,
--     getCurrentTime,
--   )
import qualified Math.NumberTheory.Roots as Old (integerSquareRoot)
import qualified Math.NumberTheory.Roots_ as New (integerSquareRoot)
import System.Random.Stateful (globalStdGen, uniformRM)
import GHC.Environment (getFullArgs)

main :: IO ()
main = do
  putStrLn "Searching args..."
  args <- getFullArgs
  print args
  iIntInteger <- getRndMInt (2^31, 2^32) 
  iHugeWord <- getRndMInt (2^63, 2^64)  
  iHumongous <- getRndMInt (2^129, 2^130) 
  iGargantuan <- getRndMInt (2^257, 2^258) 
  iGoogolplex <- getRndMInt (2^511, 2^512) 
  iFZeight <- getRndMInt (2^1023, 2^1024) 
  iBoogol <- getRndMInt (2^2046, 2^2047)  
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
