{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, OverloadedStrings,
             ScopedTypeVariables, TypeApplications, RecordWildCards, GADTs,
             StandaloneDeriving #-}

module SynthSpec.Types where
import Data.Dynamic
import Data.Map (Map)
import Data.Text (Text)
import qualified Data.Map as Map
import GHC.Base (Any)
import Application.TermSearch.Type (TypeSkeleton(..))
import GHC.Stack (HasCallStack)

import Data.Typeable
import Type.Reflection (someTypeRep, SomeTypeRep(..))
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
import Data.Maybe (mapMaybe, fromJust)
import Debug.Trace (traceShowId, trace, traceShowM)

import Test.QuickCheck (Arbitrary(..), Property(..), Testable(..), Gen(..))
import qualified Test.QuickCheck as QC
import System.IO.Unsafe
import Unsafe.Coerce
import Test.QuickCheck.Property
import Data.List (groupBy, nub, sort)
import Data.Function (on)
import Data.Maybe (catMaybes)
import Debug.Trace

-- Types supported by ECTA
-- newtype A = A Any deriving Typeable
-- newtype B = B Any deriving Typeable
-- newtype C = C Any deriving Typeable
-- newtype D = D Any deriving Typeable
-- newtype Acc = Acc Any deriving Typeable
--
newtype A = A Int deriving (Typeable, Eq, Show, Ord)
newtype B = B Int deriving (Typeable, Eq, Show, Ord)
newtype C = C Int deriving (Typeable, Eq, Show, Ord)
newtype D = D Int deriving (Typeable, Eq, Show, Ord)
newtype Acc = Acc Int deriving (Typeable, Eq, Show, Ord)

instance Arbitrary A where
  arbitrary = A <$> arbitrary
instance Arbitrary B where
  arbitrary = B <$> arbitrary
instance Arbitrary C where
  arbitrary = C <$> arbitrary
instance Arbitrary D where
  arbitrary = D <$> arbitrary
instance Arbitrary Acc where
  arbitrary = Acc <$> arbitrary


sigGivens :: Sig -> Sig 
sigGivens sigs = eqDef
                 -- <> eqLaws
                 <> Map.fromList (mapMaybe toEqInst (Map.keys allCons))
                 <> Map.fromList (concatMap consNames (Map.assocs allCons))
  where trs = map sfTypeRep $ Map.elems sigs
        -- we specialcase lists
        --cons t@(TCons "[]" r) = Map.unionsWith (+) $ map cons r
        cons t@(TCons "[]" [TCons "[]" [TCons a []]]) = (Map.singleton t (1 :: Int))
        cons t@(TCons "[]" [TCons a []]) = (Map.singleton t (1 :: Int))
        cons t@(TCons _ r) = Map.unionsWith (+) $
                                (Map.singleton t (1 :: Int)):(map cons r)
        cons (TFun arg ret) = Map.unionWith (+) (cons arg) (cons ret)
        cons (TVar _) = Map.empty
        allCons = Map.unionsWith max $ map cons trs
        toEqInst e | TCons "[]" [TCons t []] <- e = g t (\a -> "["<>a<>"]")
                   | TCons "[]" [TCons "[]" [TCons t []]] <- e =
                                g t (\c -> "[["<>c<>"]]")
                   | TCons t [] <- e = g t id
           where g t mod = Just ("<@Eq_"<>(mod t)<>"@>",
                                GivenFun (GivenInst tra (eqInst (mod t)))
                                $ TCons "Eq" [e])
                            where tra = textToTy $ mod t
        toEqInst _ = Nothing

        -- Needs template haskell for user-given instances.
        -- in core f: (Eq a => Eq [a])
        -- (==) (f (Eq a)) :: Eq [a]
        -- (==) @[A]
        -- TODO:
        -- eqLaws = Map.singleton "<@Eq_[a]@>"
        --             $ GivenFun (GivenLaw "Eq_[a]")
        --             $ TFun (TCons "Eq" [TVar "a"])
        --             $ TCons "Eq" [TCons "[]" [TVar "a"]]
        eqDef = Map.singleton "(==)" $ 
                    GivenFun (GivenDef "(==)")
                             $ TFun (TCons "Eq" [TVar "a"])
                             $ TFun (TVar "a")
                             $ TFun (TVar "a")
                             $ TCons "Bool" []
        consNames (t, n) | TCons "[]" [TCons a []] <- t = g a (\c -> "["<>c<>"]")
                         | TCons "[]" [TCons "[]" [TCons a []]] <- t =
                                g a (\c -> "[["<>c<>"]]")
                         | TCons a [] <- t = g a id
                         | otherwise = []
           where g a mod = map ((\gf@(GivenFun gv _) -> (gvToName gv, gf)) .
                               (\v -> GivenFun (GivenVar (textToTy $ mod a) v
                                                         (getArb   $ mod a)) t)) [0..(n-1)]
        textToTy :: Text -> TypeRep
        textToTy "A"          =  typeRep (Proxy :: Proxy A)
        textToTy "B"          =  typeRep (Proxy :: Proxy B)
        textToTy "C"          =  typeRep (Proxy :: Proxy C)
        textToTy "D"          =  typeRep (Proxy :: Proxy D)
        textToTy "Acc"        =  typeRep (Proxy :: Proxy Acc)
        textToTy "Int"        =  typeRep (Proxy :: Proxy Int)
        textToTy "Char"       =  typeRep (Proxy :: Proxy Char)
        textToTy "Integer"    =  typeRep (Proxy :: Proxy Integer)
        textToTy "Double"     =  typeRep (Proxy :: Proxy Double)
        textToTy "[A]"        =  typeRep (Proxy :: Proxy [A])
        textToTy "[B]"        =  typeRep (Proxy :: Proxy [B])
        textToTy "[[A]]"      =  typeRep (Proxy :: Proxy [[A]])
        -- textToTy "[C]"        =  typeRep (Proxy :: Proxy [C])
        -- textToTy "[D]"        =  typeRep (Proxy :: Proxy [D])
        -- textToTy "[Acc]"      =  typeRep (Proxy :: Proxy [Acc])
        -- textToTy "[Int]"      =  typeRep (Proxy :: Proxy [Int])
        -- textToTy "[Char]"     =  typeRep (Proxy :: Proxy [Char])
        -- textToTy "[Integer]"  =  typeRep (Proxy :: Proxy [Integer])
        -- textToTy "[Double]"   =  typeRep (Proxy :: Proxy [Double])
        textToTy x = error $ "unknown type '" ++ (T.unpack x) ++ "'"
        getArb :: Text -> DynGen
        getArb "A"          =  DynGen (arbitrary :: Gen A)
        getArb "B"          =  DynGen (arbitrary :: Gen B)
        getArb "C"          =  DynGen (arbitrary :: Gen C)
        getArb "D"          =  DynGen (arbitrary :: Gen D)
        getArb "Acc"        =  DynGen (arbitrary :: Gen Acc)
        getArb "Int"        =  DynGen (arbitrary :: Gen Int)
        getArb "Char"       =  DynGen (arbitrary :: Gen Char)
        getArb "Integer"    =  DynGen (arbitrary :: Gen Integer)
        getArb "Double"     =  DynGen (arbitrary :: Gen Double)
        getArb "[A]"        =  DynGen (arbitrary :: Gen [A])
        getArb "[B]"        =  DynGen (arbitrary :: Gen [B])
        getArb "[[A]]"      =  DynGen (arbitrary :: Gen [[A]])
        -- getArb "[C]"        =  DynGen (arbitrary :: Gen [C])
        -- getArb "[D]"        =  DynGen (arbitrary :: Gen [D])
        -- getArb "[Acc]"      =  DynGen (arbitrary :: Gen [Acc])
        -- getArb "[Int]"      =  DynGen (arbitrary :: Gen [Int])
        -- getArb "[Char]"     =  DynGen (arbitrary :: Gen [Char])
        -- getArb "[Integer]"  =  DynGen (arbitrary :: Gen [Integer])
        -- getArb "[Double]"   =  DynGen (arbitrary :: Gen [Double])
        getArb x = error $ "unknown type '" ++ (T.unpack x) ++ "'"
        eqInst :: Text -> Dynamic
        eqInst "A"          =  toDyn ((==) :: A -> A -> Bool)
        eqInst "B"          =  toDyn ((==) :: B -> B -> Bool)
        eqInst "C"          =  toDyn ((==) :: C -> C -> Bool)
        eqInst "D"          =  toDyn ((==) :: D -> D -> Bool)
        eqInst "Acc"        =  toDyn ((==) :: Acc -> Acc -> Bool)
        eqInst "Int"        =  toDyn ((==) :: Int -> Int -> Bool)
        eqInst "Char"       =  toDyn ((==) :: Char -> Char -> Bool)
        eqInst "Integer"    =  toDyn ((==) :: Integer -> Integer -> Bool)
        eqInst "Double"     =  toDyn ((==) :: Double -> Double -> Bool)
        eqInst "[A]"        =  toDyn ((==) :: [A] -> [A] -> Bool)
        eqInst "[B]"        =  toDyn ((==) :: [B] -> [B] -> Bool)
        eqInst "[[A]]"      =  toDyn ((==) :: [[A]] -> [[A]] -> Bool)
        -- eqInst "[C]"        =  toDyn ((==) :: [C] -> [C] -> Bool)
        -- eqInst "[D]"        =  toDyn ((==) :: [D] -> [D] -> Bool)
        -- eqInst "[Acc]"      =  toDyn ((==) :: [Acc] -> [Acc] -> Bool)
        -- eqInst "[Int]"      =  toDyn ((==) :: [Int] -> [Int] -> Bool)
        -- eqInst "[Char]"     =  toDyn ((==) :: [Char] -> [Char] -> Bool)
        -- eqInst "[Integer]"  =  toDyn ((==) :: [Integer] -> [Integer] -> Bool)
        -- eqInst "[Double]"   =  toDyn ((==) :: [Double] -> [Double] -> Bool)
        eqInst x = error $ "unknown type '" ++ (T.unpack x) ++ "'"






arith :: (Typeable a, Num a, Eq a) => Proxy a -> Sig
arith p = Map.fromList $
            -- ("<@Eq_"<>trtext<>"@>", 
            --     GenFunc { gf_func = toDyn eq
            --             , gf_rep = Just (TCons "Eq" [TCons trtext []]) }):
                (map (fmap extraFunc) $
                 [ ("0", toDyn zero)
                 , ("1", toDyn $ (fromInteger 1) `asProxyTypeOf` p)
                 --, ("((==) @("<> trtext <> "))", toDyn eq)
                 -- TODO: prune?
                 -- , ("((+) @("<> trtext <> "))", toDyn plus)
                 -- , ("((*) @("<> trtext <> "))", toDyn mul)
                 -- , ("((-) @("<> trtext <> "))", toDyn minus)
                 -- , ("(sign @("<> trtext <> "))", toDyn sign)
                 -- , ("(abs @("<> trtext <> "))", toDyn ab)
                 -- , ("(negate @("<> trtext <> "))", toDyn neg)
                 -- , ("(fromInteger @("<> trtext <> "))", toDyn fromI)
                 ]
                 )
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
                    , sf_rep :: Maybe TypeSkeleton}
          | GenFunc { gf_func :: Dynamic
                    , gf_rep :: Maybe TypeSkeleton}
          | GivenFun {given_info :: GivenInfo, giv_rep :: TypeSkeleton}
          deriving (Show)

data GivenInfo where
    GivenDef :: Text -> GivenInfo
    GivenInst :: TypeRep -> Dynamic -> GivenInfo
    GivenVar :: TypeRep -> Int -> DynGen -> GivenInfo


deriving instance Show GivenInfo

instance Eq GivenInfo where
  (GivenDef t) == (GivenDef s) = s == t
  (GivenInst t _) == (GivenInst s _) = t == s
  (GivenVar t i _) == (GivenVar s j _) = (i == j) && (t == s)

instance Ord GivenInfo where
  compare (GivenDef t) (GivenDef s) = compare t s
  compare (GivenInst t _) (GivenInst s _) = compare t s
  compare (GivenVar t i _) (GivenVar s j _) = if t == s
                                              then compare i j
                                              else compare t s
  compare (GivenDef {}) _ = LT
  compare (GivenInst {}) (GivenDef {}) = GT
  compare (GivenInst {}) (GivenVar {}) = LT
  compare (GivenVar {}) _ = GT


gvToName :: GivenInfo -> Text
gvToName (GivenVar tr i _) = nm<>ss<>sep<>trn<>r
  where howNested tc | "[]" <- tyConName (typeRepTyCon tc),
                       [tra] <- typeRepArgs tc
                       = (1+) <$> howNested tra
                     | otherwise = (tyConName $ typeRepTyCon tc, 0)
        (tcn,hn) = howNested tr
        ss = T.pack (replicate hn 's')
        (nm,r) = if i < length varns
                 then (T.pack [(varns !! i)], "")
                 else ("x", "_" <> is)
        sep = "::"
        trn :: Text
        trn = T.pack (show tr)
        is :: Text
        is = T.pack (show i)
        varns :: String
        varns = "xyzabcdefghijklmnopqrtuv"
gvToName _ = error "not a given var!"


data DynGen where
   DynGen :: forall a. Typeable a => Gen a -> DynGen

instance Show DynGen where
  show (DynGen dg) = show (toDyn dg)

-- instance Show Func where
--   show (SigFunc {..}) = show sf_func
--   show (GenFunc {..}) = show gf_func
--   show (GivenFun tr) = "given<" ++ (show tr) ++ ">"

-- ConFunc comes from the user provided signature, and we want at least
-- one of these to show up.
conFunc :: Dynamic -> Func
conFunc f = SigFunc {sf_func = f, sf_rep = Nothing}

-- extraFuncs are from generators like arith, but we don't *require* them,
-- they're just extra.
extraFunc :: Dynamic -> Func
extraFunc f = GenFunc {gf_func = f, gf_rep = Nothing}


sfFunc :: Func -> Dynamic
sfFunc (SigFunc {..}) = sf_func
sfFunc (GenFunc {..}) = gf_func
-- Should not happen
sfFunc (GivenFun {}) = toDyn (()::())

sfRequired :: Func -> Bool
sfRequired (SigFunc {}) = True
sfRequired _ = False

sfTypeRep :: Func -> TypeSkeleton
sfTypeRep (SigFunc{..}) = 
    case sf_rep of
      Just r -> r
      _ -> typeRepToTypeSkeleton $ dynTypeRep sf_func
sfTypeRep (GenFunc{..}) = 
    case gf_rep of
      Just r -> r
      _ -> typeRepToTypeSkeleton $ dynTypeRep gf_func
sfTypeRep (GivenFun {..}) = giv_rep

con :: Typeable a => Text -> a -> Sig
con name fun = Map.singleton name $ (conFunc $ toDyn fun)

extra :: Typeable a => Text -> a -> Sig
extra name fun = Map.singleton name $ (extraFunc $ toDyn fun)

skeletonToTypeRep :: TypeSkeleton -> Maybe TypeRep
skeletonToTypeRep _ = Nothing

flipTerm :: Term -> Term
flipTerm (Term "app" ((Term s sargs):rest)) = flipTerm (Term s $ map flipTerm (sargs ++ rest))
flipTerm t = t

eqLi :: (a -> a -> Bool) -> [a] -> [a] -> Bool
eqLi f [] [] = True
eqLi f (a:as) (b:bs) = if f a b then eqLi f as bs else False
eqLi _ _ _ = False



type VarVals = Map Text Dynamic



getVars :: Sig -> Term -> Gen VarVals
getVars sig (Term (Symbol sym) args) = do
    vv <- Map.unions <$> (mapM (getVars sig) args)
    case sig Map.!? sym of
        Just (GivenFun {given_info = GivenVar _ _ (DynGen g) }) -> do
            v <- toDyn <$> g
            return (vv <> (Map.singleton sym v))
        _ -> return vv 

traceShowIdLbl :: Show a => String -> a -> a
-- traceShowIdLbl lbl a = (trace (lbl ++ show a) a)
traceShowIdLbl _ a = a


-- We don't want to keep repeating the same laws
reduceVars :: Sig -> Term -> Term
reduceVars sig term = simplified
  where vars :: Term -> [GivenInfo]
        vars (Term (Symbol s) []) |
            Just (GivenFun {given_info=v@(GivenVar _ _ _)}) <- sig Map.!? s =
                [v]
        vars (Term _ args) = concatMap vars args
        howMany :: Term -> [[GivenInfo]]
        howMany = groupBy ((==) `on` (\(GivenVar tr _ _) -> tr)) . sort . nub . vars
        substs vs = catMaybes $ zipWith f vs [0..]
          where f v@(GivenVar tr i g) j = if i == j then Nothing
                                          else Just (v,GivenVar tr j g)
        changes :: Map GivenInfo GivenInfo 
        changes = Map.unions $ map (Map.fromList . substs) $ howMany term
        applRw :: Term -> Term
        applRw ttr@(Term (Symbol s) [])
           | Just (GivenFun {given_info=v@(GivenVar _ _ _)}) <- sig Map.!? s,
             Just v' <- changes Map.!? v = Term (Symbol (gvToName v')) []
           | otherwise = ttr
        applRw (Term s args) = Term s (map applRw args)
        simplified = applRw term
        


                


-- Note: should be flipped 
termToGen :: Sig -> VarVals -> Term -> Gen Dynamic
termToGen sig init_vv (Term "(==)" [eq_i, a_g, b_g])
    | a_g == b_g = return (toDyn True) -- short-circuit the trivial case
    | otherwise =
    do eq <- fmap (traceShowIdLbl "eq:") $ 
                termToGen sig Map.empty (traceShowIdLbl "eq_i:" eq_i)
       vv <- if Map.null init_vv
             then do vva <- traceShowIdLbl "vva:" <$> getVars sig a_g
                     vvb <- traceShowIdLbl "vva:" <$> getVars sig b_g
                     return (vva <> vvb)
             else return init_vv
       a  <- fmap (traceShowIdLbl "a:")  $ termToGen sig vv (traceShowIdLbl "a_g:" a_g)
       b  <- fmap (traceShowIdLbl "b:")  $ termToGen sig vv (traceShowIdLbl "b_g:" b_g)
       return $ fromJust $ dynApply (fromJust $ dynApply eq a) b
termToGen sig vv (Term (Symbol sym) []) = 
  case sig Map.!? sym of 
   Just (GivenFun {given_info = GivenVar _ _ _}) ->
        case vv Map.!? sym of
          Just var_val -> return var_val
          _ -> error "Variable not found!!"
   Just (GivenFun {given_info = GivenDef "(==)"}) -> error "Givendef should not be"
   Just (GivenFun {given_info = GivenInst _ inst}) -> return inst
   Just sf@(SigFunc {}) -> return $ sfFunc sf
   Just gf@(GenFunc {}) -> return $ sfFunc gf
   Just x -> error $ show x
   Nothing -> error "not found!"
termToGen sig vv (Term (Symbol sym) args) =
 do  symGen <- fmap (traceShowIdLbl "symGen: ") $ termToGen sig vv (Term (Symbol sym) [])
     argGens <- mapM (termToGen sig vv) args
     return $ foldl (\f v -> fromJust (dynApply f v)) symGen $
                traceShowIdLbl "argGens: " argGens
   

dynProp :: Gen Dynamic -> Property
dynProp gen = QC.forAll gen (flip fromDyn False)

-- TODO: can we kill a branch once a rewriteable term is detected?
--
