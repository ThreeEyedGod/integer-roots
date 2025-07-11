import qualified Math.NumberTheory.Roots as Old (integerSquareRoot)
import qualified Math.NumberTheory.Roots_ as New (integerSquareRoot)
import Criterion.Main

main :: IO ()
main =
  defaultMain
    [ bgroup
        "IntegerSquare Roots"
        [ 
            bench "Old Int Integer" $ whnf Old.integerSquareRoot (2^31+1013 :: Int)
          , bench "New Int Integer" $ whnf New.integerSquareRoot (2^31+1013 :: Int)
          , bench "Old Huge Integer" $ whnf Old.integerSquareRoot (2^63+1013 :: Word)
          , bench "New Huge Integer" $ whnf New.integerSquareRoot (2^63+1013 :: Word)
          , bench "Old Humoungous Integer " $ whnf Old.integerSquareRoot (2^129+1013)
          , bench "New Humoungous Integer " $ whnf New.integerSquareRoot (2^129+1013)
          , bench "Old Gargantuan Integer" $ whnf Old.integerSquareRoot (2^257+1013)
          , bench "New Gargantuan Integer" $ whnf New.integerSquareRoot (2^257+1013)
          , bench "Old Googolplex Integer " $ whnf Old.integerSquareRoot (2^1027+1013)
          , bench "New Googolplex Integer " $ whnf New.integerSquareRoot (2^1027+1013)
        ]
    ]

