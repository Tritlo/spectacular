-- Some usual list functions.
{-# LANGUAGE ScopedTypeVariables, ConstraintKinds, RankNTypes, ConstraintKinds,
             FlexibleContexts, OverloadedStrings #-}
import Spectacular
import System.Environment (getArgs)

main = do
  [s,p] <- map read <$> getArgs
  --tacularSpec' 7 3 extraReps [
  res <- tacularSpec' s p (const Nothing) [
    con "reverse" (reverse :: [A] -> [A]),
    con "++" ((++) :: [A] -> [A] -> [A]),
    con "[]" ([] :: [A]),
    con "map" (map :: (A -> B) -> [A] -> [B]),
    con "length" (length :: [A] -> Int),
    con "concat" (concat :: [[A]] -> [A]),

    -- Add some numeric functions to get more laws about length.
    arith (Proxy :: Proxy Int) ]
  mapM print res
  print (length res)
