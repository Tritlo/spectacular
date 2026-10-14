
module Spectacular.Testing where
import Test.QuickCheck.Test hiding (theException)
import Test.QuickCheck.Property
import Test.QuickCheck hiding (theException)
import Test.QuickCheck.State
import Test.QuickCheck.Random
import Test.QuickCheck.Gen
import System.Random (split)


-- | The result of the tests of a property.
data TestResult
  = TestPassed -- ^ Every test passed.
  | TestFailed -- ^ A test was false.
  | Untestable -- ^ A test threw an exception.
  deriving (Eq, Show)

-- A super stripped down version of QuickCheck with only the basic loop, since
-- we don't want any of the other stuff. A test that throws an exception makes
-- the property untestable, as in QuickSpec, not false.
testProperty :: Args -> Property -> IO TestResult
testProperty args prop = withState args loop
  where loop st | numSuccessTests st >= maxSuccess args = return TestPassed
        loop st =
            do MkRose res ts <- protectRose (reduceRose (unProp (unGen (unProperty prop) rnd1 size)))
               case res of
                 MkResult {ok = Just True} ->
                    loop st {randomSeed = rnd2, numSuccessTests = numSuccessTests st + 1}
                 MkResult {ok = Just False, theException = Just _} -> return Untestable
                 MkResult {ok = Just False} -> return TestFailed
                 _ -> error "weird stuff happening in quickcheck shim!!"
          where (rnd1,rnd2) = split (randomSeed st)
                size = computeSize st


