module Main
    ( main
    ) where

import qualified Spec.Model
import qualified Spec.ModelWithClose
import qualified Spec.ModelWithEnd
import qualified Spec.Trace
import qualified Spec.TraceWithClose
import qualified Spec.Trace2
import           Test.Tasty

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "token sale"
    [ Spec.Trace.tests
    , Spec.TraceWithClose.tests
    , Spec.Trace2.tests
    , Spec.Model.tests
    , Spec.ModelWithClose.tests
    , Spec.ModelWithEnd.tests
    ]
