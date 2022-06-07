-- Some usual list functions.
{-# LANGUAGE ScopedTypeVariables, ConstraintKinds, RankNTypes, ConstraintKinds,
             FlexibleContexts, OverloadedStrings #-}
import Spectacular

main = tacularSpec' 7 4 [
  con "reverse" (reverse :: [A] -> [A]),
  con "[]" ([] :: [A])
  ]
