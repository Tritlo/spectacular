{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module SynthSpec.Types where
import Data.Dynamic
import Data.Map (Map)
import Data.Text (Text)
import qualified Data.Map as Map
import GHC.Base (Any)
import Application.TermSearch.Type (TypeSkeleton(..))

import Data.Typeable
import Data.Char (toLower)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Monoid as M
import Application.TermSearch.Dataset
import Application.TermSearch.Type
import Data.ECTA (Node (Node), mkEdge, Edge (Edge), pathsMatching, mapNodes, createMu)
import Data.ECTA.Term
import Application.TermSearch.Utils (theArrowNode, arrowType, var1, var2, var3, var4, varAcc, mkDatatype)
import Data.ECTA (union)
import Data.ECTA.Paths (getPath, mkEqConstraints, path, Path)
import Data.Proxy

-- Types supported by ECTA
newtype A = A Any deriving Typeable
newtype B = B Any deriving Typeable
newtype C = C Any deriving Typeable
newtype D = D Any deriving Typeable
newtype Acc = Acc Any deriving Typeable

tyGivens :: [(Text, TypeSkeleton)]
tyGivens = map toEqInst ["A","B","C","D","Acc"]
          ++ eqLaws
          ++ eqDef
  where toEqInst s = ("<@Eq_" <> s <> "@>",TCons "Eq" [TCons s []])
        -- TODO: This should come from ghc itself, like in the plugin.
        eqLaws = [("<@Eq_[a]@>", TFun (TCons "Eq" [TVar "a"]) $
                                   TCons "Eq" [TCons "[]" [TVar "a"]])]
        eqDef = [("(==)", TFun (TCons "Eq" [TVar "a"]) $
                               TFun (TVar "a") $
                               TFun (TVar "a") $
                               TCons "Bool" [])]

arith :: (Typeable a, Num a, Eq a) => Proxy a -> Sig
arith p = Map.fromList [ ("0", toDyn zero),
                         ("1", toDyn $ (fromInteger 1) `asProxyTypeOf` p),
                         -- FIX
                         ("((==) @"<> trtext <> ")", toDyn f )]
  where tr = typeRep p
        trtext = T.pack $ show tr
        skel = typeRepToTypeSkeleton tr
        zero = (fromInteger 0) `asProxyTypeOf` p
        -- TODO: There must be a better way, right?
        f a b = (a - b) == zero

typeRepToTypeSkeleton :: TypeRep -> TypeSkeleton
typeRepToTypeSkeleton tr
     | [] <- tra,
       ltc <- map toLower tcn,
       ltc `elem` ["a", "b", "c","d", "acc"]
       -- = TVar (T.pack ltc)
       = TCons (T.pack tcn) [] -- (T.pack ltc)
     | tcn == "->",
       [arg,ret] <- args
     = TFun arg ret
     | otherwise = TCons (T.pack tcn) args
  where (tc, tra) = splitTyConApp tr
        tcn = tyConName tc
        args = map typeRepToTypeSkeleton tra


prettyMatchRep :: Map.Map Text TypeSkeleton -> Map.Map Text [Text] -> Term -> [Text]
prettyMatchRep skels groups (Term (Symbol t) _) | ty <- skeletonToTypeRep tsk =
  let str = case ty of
               Just t  -> T.pack (" :: " ++  show t)
               _ -> T.pack (" :: " ++ show tsk)
  in map (M.<> str) terms
  where tsk = case skels Map.!? t of
                Just r -> r
                _ -> skels Map.! (T.pack $ tail $ T.unpack t) -- for generalization
        terms = case groups Map.!? t of
                  Just r -> r
                  _ -> groups Map.! (T.pack $ tail $ T.unpack t)

type Sig = Map Text Dynamic


con :: Typeable a => Text -> a -> Sig
con name fun = Map.singleton name (toDyn fun)

skeletonToTypeRep :: TypeSkeleton -> Maybe TypeRep
skeletonToTypeRep _ = Nothing
