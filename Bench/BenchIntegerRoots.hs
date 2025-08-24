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
          , bench "Old Googolplex Integer " $ whnf Old.integerSquareRoot (2^511+1013)
          , bench "New Googolplex Integer " $ whnf New.integerSquareRoot (2^511+1013)
          , bench "Old FZeight Integer " $ whnf Old.integerSquareRoot (2^1023+1013)
          , bench "New FZeight Integer " $ whnf New.integerSquareRoot (2^1023+1013)
          , bench "Old Boogol Integer " $ whnf Old.integerSquareRoot (2^2046+1013)
          , bench "New Boogol Integer " $ whnf New.integerSquareRoot (2^2046+1013)
        ]
    ]

-- cabal bench --benchmark -options "+RTS -I0 -K256m -A16m -N8 -H24m -T -w -RTS --output=integer-roots.html"
