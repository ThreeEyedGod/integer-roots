import qualified Math.NumberTheory.Roots as Old (integerSquareRoot)
import qualified Math.NumberTheory.Roots_ as New (integerSquareRoot)
import Criterion.Main
import System.Random.Stateful (globalStdGen, uniformRM)

main :: IO ()
main = do 
  iIntInteger <- getRndMInt (2^31, 2^32) 
  iHugeWord <- getRndMInt (2^63, 2^64)  
  iHumongous <- getRndMInt (2^129, 2^130) 
  iGargantuan <- getRndMInt (2^257, 2^258) 
  iGoogolplex <- getRndMInt (2^511, 2^512) 
  iFZeight <- getRndMInt (2^1023, 2^1024) 
  iBoogol <- getRndMInt (2^2046, 2^2047) 
  defaultMain
    [ bgroup
        "IntegerSquare Roots"
        [ 
            bench "Old Int Integer" $ whnf Old.integerSquareRoot (fromIntegral iIntInteger :: Int)
          , bench "New Int Integer" $ whnf New.integerSquareRoot (fromIntegral iIntInteger :: Int)
          , bench "Old Huge Integer" $ whnf Old.integerSquareRoot (fromIntegral iHugeWord :: Word)
          , bench "New Huge Integer" $ whnf New.integerSquareRoot (fromIntegral iHugeWord :: Word)
          , bench "Old Humoungous Integer " $ whnf Old.integerSquareRoot iHumongous
          , bench "New Humoungous Integer " $ whnf New.integerSquareRoot iHumongous
          , bench "Old Gargantuan Integer" $ whnf Old.integerSquareRoot iGargantuan
          , bench "New Gargantuan Integer" $ whnf New.integerSquareRoot iGargantuan
          , bench "Old Googolplex Integer " $ whnf Old.integerSquareRoot iGoogolplex
          , bench "New Googolplex Integer " $ whnf New.integerSquareRoot iGoogolplex
          , bench "Old FZeight Integer " $ whnf Old.integerSquareRoot iFZeight
          , bench "New FZeight Integer " $ whnf New.integerSquareRoot iFZeight
          , bench "Old Boogol Integer " $ whnf Old.integerSquareRoot iBoogol
          , bench "New Boogol Integer " $ whnf New.integerSquareRoot iBoogol
        ]
    ]

-- | Get a Random Integer with uniform probability in the range (l,u)
getRndMInt :: (Integer, Integer) -> IO Integer
getRndMInt (l, u) = max l . min u <$> uniformRM (l, u) globalStdGen -- uniformRM (a, b) = uniformRM (b, a) holds as per fn defn

-- cabal bench --benchmark -options "+RTS -I0 -K256m -A16m -N8 -H24m -T -w -RTS --output=integer-roots.html"
