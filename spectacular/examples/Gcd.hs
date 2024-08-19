-- Some usual list functions.
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, FlexibleInstances, OverloadedStrings #-}
import Spectacular
import Spectacular.Types (genRepFromProxy)
import Application.TermSearch.Type (TypeSkeleton(..))
import Test.QuickCheck
import Data.Proxy
import Data.Typeable

import Test.QuickCheck

newtype PosInt = P Int
  deriving (Eq, Ord, Num, Typeable, Enum, Real, Integral, CoArbitrary, Show)

instance Arbitrary PosInt where
  arbitrary = P <$> arbitrary `suchThat` (>= 0)

extraReps (TCons "PosInt" []) = Just $ genRepFromProxy (Proxy :: Proxy PosInt)
extraReps _ = Nothing

main = tacularSpec' 3 1 extraReps [
  con "0"    (P 0 :: PosInt),
  con "21"   (P 21 :: PosInt),
  con "1029" (P 1029 :: PosInt),
  con "1071" (P 1071 :: PosInt),
  con "gcd" (gcd :: PosInt -> PosInt -> PosInt)
  ]
