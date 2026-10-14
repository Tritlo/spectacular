-- Some usual list functions.
{-# LANGUAGE ScopedTypeVariables, ConstraintKinds, RankNTypes, ConstraintKinds,
             FlexibleContexts, OverloadedStrings #-}
import Spectacular

main = tacularSpec' 7 4 (const Nothing) [
  con "reverse" (reverse :: [A] -> [A]),
  con "[]" ([] :: [A])
  ]
