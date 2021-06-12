module Main
    ( main
    ) where

import qualified Spec.ModelWithEnd
import qualified Spec.Trace2
import           Test.Tasty

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "token sale"
    [ Spec.Trace2.tests
    , Spec.ModelWithEnd.tests
    ]
