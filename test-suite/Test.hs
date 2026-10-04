import Control.Monad (unless)
import System.Environment (getArgs, withArgs)
import System.Exit (die, exitFailure)

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
  args <- getArgs
  let selectors = filter (`elem` ["tests", "tests_"]) args
      tastyArgs = filter (`notElem` ["tests", "tests_"]) args
  (suites, optionSuite) <- case selectors of
    [] -> pure ([tests, tests_], alltests)
    ["tests"] -> pure ([tests], tests)
    ["tests_"] -> pure ([tests_], tests_)
    _ -> die "Specify at most one test suite: tests or tests_"
  withArgs tastyArgs $ runSuites suites optionSuite

runSuites :: [TestTree] -> TestTree -> IO ()
runSuites suites optionSuite = do
  let ingredients = defaultIngredients
      withTestOptions suite = adjustOption
        (\(QuickCheckTests n) -> QuickCheckTests (max n 10000))
        $ adjustOption
          (\(SmallCheckDepth n) -> SmallCheckDepth (max n 100))
          suite
  options <- parseOptions ingredients (withTestOptions optionSuite)
  let runSuite suite = case tryIngredients ingredients options (withTestOptions suite) of
        Just run -> run
        Nothing -> pure False
  testsPassed <- mapM runSuite suites
  unless (and testsPassed) exitFailure

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
