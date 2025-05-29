import Math.NumberTheory.Roots
import Test.Tasty.Bench

main :: IO ()
main =
  Test.Tasty.Bench.defaultMain
    [ bgroup
        "IntegerSquare Roots"
        [ bench "Huge Integer" $ whnf integerSquareRoot (2^63+1000),
          bench "Humoungous Integer " $ whnf integerSquareRoot (2^127+1000)
        ]
    ]
