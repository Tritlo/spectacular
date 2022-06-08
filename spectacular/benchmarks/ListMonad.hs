{-# LANGUAGE OverloadedStrings #-}
-- The monad laws for lists.
import Control.Monad
import Spectacular

main = tacularSpec' 7 3 (const Nothing) [
  con "return" (return :: A -> [A]),
  con ">>=" ((>>=) :: [A] -> (A -> [B]) -> [B]),
  con "++" ((++) :: [A] -> [A] -> [A]),
  con ">=>" ((>=>) :: (A -> [B]) -> (B -> [C]) -> A -> [C]) ]