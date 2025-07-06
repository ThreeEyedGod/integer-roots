import Math.NumberTheory.Roots  
import Criterion.Main

main :: IO ()
main =
  defaultMain
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
