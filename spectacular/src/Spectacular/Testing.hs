
module Spectacular.Testing where
import Test.QuickCheck.Test
import Test.QuickCheck.Property
import Test.QuickCheck
import Test.QuickCheck.State
import Test.QuickCheck.Random
import Test.QuickCheck.Gen
import System.Random (split)


-- A super stripped down version of QuickCheck with only the basic loop, since
-- we don't want any of the other stuff.
quickCheckBoolOnly :: Args -> Property -> IO Bool
quickCheckBoolOnly args prop = withState args loop
  where loop st | numSuccessTests st >= maxSuccess args = return True
        loop st =
            do MkRose res ts <- protectRose (reduceRose (unProp (unGen (unProperty prop) rnd1 size)))
               case res of
                 MkResult {ok = Just True} ->
                    loop st {randomSeed = rnd2, numSuccessTests = numSuccessTests st + 1}
                 MkResult {ok = Just False} -> return False
                 _ -> error "weird stuff happening in quickcheck shim!!"
          where (rnd1,rnd2) = split (randomSeed st)
                size = computeSize st (numSuccessTests st) (numRecentlyDiscardedTests st)


