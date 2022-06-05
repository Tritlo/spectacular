-- Some usual list functions.
{-# LANGUAGE ScopedTypeVariables, ConstraintKinds, RankNTypes, ConstraintKinds,
             FlexibleContexts, OverloadedStrings #-}
import Spectacular

main = tacularSpec [
  con "reverse" (reverse :: [A] -> [A]),
  con "[]" ([] :: [A]),
  con "null" (null :: [A] -> Bool),
  con "True" (True :: Bool),
  con "False" (False :: Bool)
  ]
