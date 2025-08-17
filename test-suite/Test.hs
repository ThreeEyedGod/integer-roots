import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.SmallCheck

import qualified Math.NumberTheory.Roots.CubesTests as Cubes
import qualified Math.NumberTheory.Roots.FourthTests as Fourth
import qualified Math.NumberTheory.Roots.GeneralTests as General
import qualified Math.NumberTheory.Roots.GeneralTests as General_
import qualified Math.NumberTheory.Roots.SquaresTests as Squares
import qualified Math.NumberTheory.Roots.SquaresTests_ as Squares_

main :: IO ()
main
  = defaultMain
  $ adjustOption
    (\(QuickCheckTests n) -> QuickCheckTests (max n 10000))
  $ adjustOption
    (\(SmallCheckDepth n) -> SmallCheckDepth (max n 100))
  $ tests_

alltests :: TestTree 
alltests = sequentialTestGroup "BOTH " AllFinish [tests, tests_] 

tests :: TestTree
tests = testGroup "Root Tests"
  [ 
   testGroup "All"
    [ Squares.testSuite
    , Cubes.testSuite
    , Fourth.testSuite
    , General.testSuite
    ]
  ]

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
