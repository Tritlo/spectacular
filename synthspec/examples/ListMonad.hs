{-# LANGUAGE OverloadedStrings #-}
-- The monad laws for lists.
import Control.Monad
import SynthSpec

main = synthSpec' 20 1 (const Nothing) [
  con "return" (return :: A -> [A]),
  con ">>=" ((>>=) :: [A] -> (A -> [B]) -> [B]),
  con "++" ((++) :: [A] -> [A] -> [A]),
  con ">=>" ((>=>) :: (A -> [B]) -> (B -> [C]) -> A -> [C]) ]
