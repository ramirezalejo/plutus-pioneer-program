module Main
    ( main
    ) where

import qualified Spec.ModelWithEnd
import qualified Spec.Trace2
import           Test.Tasty

main :: IO ()
main = defaultMain tests2

tests2 :: TestTree
tests2 = testGroup "token sale"
    [ Spec.Trace2.tests
    , Spec.ModelWithEnd.tests
    ]
