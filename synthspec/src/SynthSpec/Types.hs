{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, OverloadedStrings,
             ScopedTypeVariables, TypeApplications, RecordWildCards #-}

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
import Data.Maybe (mapMaybe)
import Debug.Trace (traceShowId)

-- Types supported by ECTA
newtype A = A Any deriving Typeable
newtype B = B Any deriving Typeable
newtype C = C Any deriving Typeable
newtype D = D Any deriving Typeable
newtype Acc = Acc Any deriving Typeable

sigGivens :: Sig -> [(Text,TypeSkeleton)]
sigGivens sigs = eqDef ++ eqLaws 
                 ++ mapMaybe toEqInst (Map.keys allCons)
                 ++ (concatMap consNames (Map.assocs allCons))
  where trs = map sfTypeRep $ Map.elems sigs
        -- we specialcase lists
        --cons t@(TCons "[]" r) = Map.unionsWith (+) $ map cons r
        cons t@(TCons _ r) = Map.unionsWith (+) $
                                (Map.singleton t (1 :: Int)):(map cons r)
        cons (TFun arg ret) = Map.unionWith (+) (cons arg) (cons ret)
        cons (TVar _) = Map.empty
        allCons = Map.unionsWith max $ map cons trs
        toEqInst e@(TCons t []) = Just ("<@Eq_"<>t<>"@>", TCons "Eq" [e])
        toEqInst _ = Nothing
        eqLaws = [("<@Eq_[a]@>", TFun (TCons "Eq" [TVar "a"]) $
                                   TCons "Eq" [TCons "[]" [TVar "a"]])]
        eqDef = [("(==)", TFun (TCons "Eq" [TVar "a"]) $
                               TFun (TVar "a") $
                               TFun (TVar "a") $
                               TCons "Bool" [])]
        consNames (t@(TCons "[]" [TCons a []]), n) =
            map (\name -> (name, t))
              $ take n
              $ (map (\n-> "xs_" <> a <> "_" <> (T.pack (show n)))) [0..]
        consNames (t@(TCons a []), n) = 
            map (\name -> (name, t))
              $ take n 
              $ (map (\n-> "x_" <> a <> "_" <> (T.pack (show n)))) [0..]
        consNames _ = []





arith :: (Typeable a, Num a, Eq a) => Proxy a -> Sig
arith p = Map.fromList $
            ("<@Eq_"<>trtext<>"@>", 
                SigFunc { sf_func = toDyn eq
                        , sf_rep = Just (TCons "Eq" [TCons trtext []])
                        , sf_required=False}):(
                map (fmap extraFunc) $
                 [ ("0", toDyn zero)
                 , ("1", toDyn $ (fromInteger 1) `asProxyTypeOf` p)
                 --, ("((==) @("<> trtext <> "))", toDyn eq)
                 , ("((+) @("<> trtext <> "))", toDyn plus)
                 , ("((*) @("<> trtext <> "))", toDyn mul)
                 , ("((-) @("<> trtext <> "))", toDyn minus)
                 , ("(sign @("<> trtext <> "))", toDyn sign)
                 , ("(abs @("<> trtext <> "))", toDyn ab)
                 , ("(negate @("<> trtext <> "))", toDyn neg)
                 , ("(fromInteger @("<> trtext <> "))", toDyn fromI) ])
  where tr = typeRep p
        trtext = T.pack $ show tr
        skel = typeRepToTypeSkeleton tr
        zero = (fromInteger 0) `asProxyTypeOf` p
        eq a b = (==) (asProxyTypeOf a p) (asProxyTypeOf b p)
        plus a b = (+) (asProxyTypeOf a p) (asProxyTypeOf b p)
        mul a b = (*) (asProxyTypeOf a p) (asProxyTypeOf b p)
        minus a b = (-) (asProxyTypeOf a p) (asProxyTypeOf b p)

        sign = flip asProxyTypeOf p . signum
        ab = flip asProxyTypeOf p . abs
        neg = flip asProxyTypeOf p . negate
        fromI = flip asProxyTypeOf p . fromInteger 

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

type Sig = Map Text Func

data Func = SigFunc { sf_func :: Dynamic
                    , sf_required :: Bool
                    , sf_rep :: Maybe TypeSkeleton}

instance Show Func where
  show (SigFunc {..}) = show sf_func

-- ConFunc comes from the user provided signature, and we want at least
-- one of these to show up.
conFunc :: Dynamic -> Func
conFunc f = SigFunc {sf_func = f, sf_required = True, sf_rep = Nothing}

-- extraFuncs are from generators like arith, but we don't *require* them,
-- they're just extra.
extraFunc :: Dynamic -> Func
extraFunc f = SigFunc {sf_func = f, sf_required = False, sf_rep = Nothing}

dropInfo :: Func -> Dynamic
dropInfo = sf_func

sfTypeRep :: Func -> TypeSkeleton
sfTypeRep (SigFunc{..}) = 
    case sf_rep of
      Just r -> r
      _ -> typeRepToTypeSkeleton $ dynTypeRep sf_func

con :: Typeable a => Text -> a -> Sig
con name fun = Map.singleton name $ (conFunc $ toDyn fun)

extra :: Typeable a => Text -> a -> Sig
extra name fun = Map.singleton name $ (extraFunc $ toDyn fun)

skeletonToTypeRep :: TypeSkeleton -> Maybe TypeRep
skeletonToTypeRep _ = Nothing
