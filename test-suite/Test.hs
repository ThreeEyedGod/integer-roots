import Control.Monad (unless)
import System.Exit (exitFailure)

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.Runners (parseOptions, tryIngredients)
import Test.Tasty.SmallCheck

import qualified Math.NumberTheory.Roots.CubesTests as Cubes
import qualified Math.NumberTheory.Roots.FourthTests as Fourth
import qualified Math.NumberTheory.Roots.GeneralTests as General
import qualified Math.NumberTheory.Roots.SquaresTests as Squares
import qualified Math.NumberTheory.Roots.GeneralTests as General_
import qualified Math.NumberTheory.Roots.SquaresTests as Squares_

main :: IO ()
main = do
  let ingredients = defaultIngredients
      withTestOptions suite = adjustOption
        (\(QuickCheckTests n) -> QuickCheckTests (max n 10000))
        $ adjustOption
          (\(SmallCheckDepth n) -> SmallCheckDepth (max n 100))
          suite
  options <- parseOptions ingredients (withTestOptions alltests)
  let runSuite suite = case tryIngredients ingredients options (withTestOptions suite) of
        Just run -> run
        Nothing -> pure False
  testsPassed <- runSuite tests
  testsPassed_ <- runSuite tests_
  unless (testsPassed && testsPassed_) exitFailure

tests :: TestTree
tests = testGroup "All"
  [ Squares.testSuite
  , Cubes.testSuite
  , Fourth.testSuite
  , General.testSuite
  ]

alltests :: TestTree 
alltests = sequentialTestGroup "BOTH " AllFinish [tests, tests_] 

tests_ :: TestTree
tests_ = testGroup "Root Tests"
  [ 
  testGroup "All_"
    [ Squares_.testSuite
    , Cubes.testSuite
    , Fourth.testSuite
    , General_.testSuite
    ]
  ]
