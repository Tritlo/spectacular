-- Some usual list functions.
{-# LANGUAGE ScopedTypeVariables, ConstraintKinds, RankNTypes, ConstraintKinds,
             FlexibleContexts, OverloadedStrings #-}
import SynthSpec

main = synthSpec' 6 3 (const Nothing) [
  con "reverse" (reverse :: [A] -> [A]),
  con "++" ((++) :: [A] -> [A] -> [A]),
  con "[]" ([] :: [A]),
  con "map" (map :: (A -> B) -> [A] -> [B]),
  con "length" (length :: [A] -> Int),
  con "concat" (concat :: [[A]] -> [A]),

  -- Add some numeric functions to get more laws about length.
  arith (Proxy :: Proxy Int)
  ]
