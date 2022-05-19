-- Some usual list functions.
{-# LANGUAGE OverloadedStrings #-}
import SynthSpec

main = synthSpec [
  con "head" (head :: [A] -> A),
  con "cons" ((:) :: A -> [A] -> [A]),
  con "++" ((++) :: [A] -> [A] -> [A]),
  con "[]" ([] :: [A]),
  con "map" (map :: (A -> B) -> [A] -> [B]),
  con "length" (length :: [A] -> Int),
  con "concat" (concat :: [[A]] -> [A]),
  
  -- Add some numeric functions to get more laws about length.
  arith (Proxy :: Proxy Int)
  ]
