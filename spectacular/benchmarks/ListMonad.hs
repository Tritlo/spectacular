{-# LANGUAGE OverloadedStrings #-}
-- The monad laws for lists.
import Control.Monad
import Spectacular

import System.Environment (getArgs)

main = do
  [s,p] <- map read <$> getArgs
  --tacularSpec' 7 3 extraReps [
  res <- tacularSpec' s p (const Nothing) [
    con "return" (return :: A -> [A]),
    con ">>=" ((>>=) :: [A] -> (A -> [B]) -> [B]),
    con "++" ((++) :: [A] -> [A] -> [A]),
    con ">=>" ((>=>) :: (A -> [B]) -> (B -> [C]) -> A -> [C]) ]
  mapM print res
  print (length res)
