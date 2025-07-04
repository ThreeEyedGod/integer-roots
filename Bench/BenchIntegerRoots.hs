import Math.NumberTheory.Roots
import Test.Tasty.Bench

main :: IO ()
main =
  Test.Tasty.Bench.defaultMain
    [ bgroup
        "IntegerSquare Roots"
        [ 
          bench "Int Integer" $ whnf integerSquareRoot (2^31+1013),
          bench "Huge Integer" $ whnf integerSquareRoot (2^63+1013),
          bench "Humoungous Integer " $ whnf integerSquareRoot (2^129+1013),
          bench "Gargantuan Integer" $ whnf integerSquareRoot (2^257+1013),
          bench "Googolplex Integer " $ whnf integerSquareRoot (2^1027+1013)
        ]
    ]
