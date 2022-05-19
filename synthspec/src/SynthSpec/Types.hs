{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, OverloadedStrings,
             ScopedTypeVariables, TypeApplications, RecordWildCards, GADTs,
             StandaloneDeriving, KindSignatures, PolyKinds, RankNTypes,
             GeneralizedNewtypeDeriving, FlexibleContexts #-}

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
import qualified Type.Reflection as TR

import qualified Data.Monoid as M
import qualified Test.QuickCheck as QC

newtype A = A M.Any deriving (Typeable, Eq, Show, Ord)
newtype B = B M.Any deriving (Typeable, Eq, Show, Ord)
newtype C = C M.Any deriving (Typeable, Eq, Show, Ord)
newtype D = D M.Any deriving (Typeable, Eq, Show, Ord)
newtype Acc = Acc M.Any deriving (Typeable, Eq, Show, Ord)


deriving instance Arbitrary A
deriving instance QC.CoArbitrary A
deriving instance Arbitrary B
deriving instance Arbitrary C
deriving instance Arbitrary D
deriving instance Arbitrary Acc

data GeneratedInstance = Gend {
    g_tr :: TypeRep,
    g_arb :: DynGen,
    g_eq :: Maybe Dynamic,
    g_empty_li :: Dynamic,
    g_li_i :: GeneratedInstance
    }

sigGivens :: Sig -> Sig 
sigGivens sigs = eqDef
                 -- <> eqLaws
                 <> Map.fromList (mapMaybe toEqInst (Map.keys allCons))
                 <> Map.fromList (mapMaybe toEmptyLi (Map.keys allCons))
                 <> Map.fromList (concatMap consNames (Map.assocs allCons))
  where trs = map sfTypeRep $ Map.elems sigs
        -- we specialcase lists
        --cons t@(TCons "[]" r) = Map.unionsWith (+) $ map cons r
        -- cons t@(TCons "[]" [TCons "[]" [TCons a []]]) = (Map.singleton t (1 :: Int))
        -- cons t@(TCons "[]" [TCons a []]) = (Map.singleton t (1 :: Int))
        cons t@(TCons _ r) = Map.unionsWith (+) $
                                (Map.singleton t (1 :: Int)):(map cons r)
        cons t@(TFun arg ret) = Map.unionsWith (+) [
                (Map.singleton t (1 :: Int)),
                (cons arg),
                (cons ret)]
        cons (TVar _) = Map.empty
        allCons = Map.unionsWith max $ map cons trs
        toEqInst e | Just rep <- genRep e,
                     Just eqf <- g_eq rep = g rep eqf
           where g rep eqf = Just ("<@Eq_"<>(T.pack $ show $ g_tr rep)<>"@>",
                                   GivenFun (GivenInst (g_tr rep) eqf)
                                   $ TCons "Eq" [e])
        toEqInst _ = Nothing
        toEmptyLi e | Just rep <- genRep e = g rep
                    | otherwise = Nothing
           where g rep = Just ("[]_<["<> (T.pack $ show $ g_tr rep)<>"]>",
                               extraFunc (g_empty_li rep))
                    

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

        consNames (t, n) | Just r <- genRep t = g r
                         | otherwise = []
           where g rep = map ((\gf@(GivenFun gv _) -> (gvToName gv, gf)) .
                              (\v -> GivenFun (GivenVar (g_tr rep) v
                              (g_arb rep)) t)) [0..(n-1)]

        genRepFromProxy :: (Eq a, Typeable a, Arbitrary a) =>
                           Proxy a -> GeneratedInstance
        genRepFromProxy (Proxy :: Proxy a) = Gend {..}
          where g_tr = typeRep (Proxy :: Proxy a)
                g_arb = DynGen (arbitrary :: Gen a)
                g_eq = Just (toDyn wrappedEq)
                --g_eq = Just (toDyn ((==) :: a -> a -> Bool))
                g_empty_li = toDyn ([] :: [a])
                g_li_i = genRepFromProxy (Proxy :: Proxy [a])
                -- TODO: do something fancier here.
                wrappedEq :: a -> a -> Property
                wrappedEq a b = property (((==) a b))

        genRepFromProxyNoEq :: (Typeable a, Arbitrary a) =>
                               Proxy a -> GeneratedInstance
        genRepFromProxyNoEq (Proxy :: Proxy a) = Gend {..}
          where g_tr = typeRep (Proxy :: Proxy a)
                g_arb = DynGen (arbitrary :: Gen a)
                g_empty_li = toDyn ([] :: [a])
                g_eq = Nothing
                g_li_i = genRepFromProxyNoEq (Proxy :: Proxy [a])


        genRep :: TypeSkeleton -> Maybe GeneratedInstance
        genRep (TCons "A"        []) = Just $ genRepFromProxy (Proxy :: Proxy A)
        genRep (TCons "B"        []) = Just $ genRepFromProxy (Proxy :: Proxy B)
        genRep (TCons "C"        []) = Just $ genRepFromProxy (Proxy :: Proxy C)
        genRep (TCons "D"        []) = Just $ genRepFromProxy (Proxy :: Proxy D)
        genRep (TCons "Acc"      []) = Just $ genRepFromProxy (Proxy :: Proxy Acc)
        genRep (TCons "()"       []) = Just $ genRepFromProxy (Proxy :: Proxy ())
        genRep (TCons "Int"      []) = Just $ genRepFromProxy (Proxy :: Proxy Int)
        genRep (TCons "Bool"     []) = Just $ genRepFromProxy (Proxy :: Proxy Bool)
        genRep (TCons "Char"     []) = Just $ genRepFromProxy (Proxy :: Proxy Char)
        genRep (TCons "Integer"  []) = Just $ genRepFromProxy (Proxy :: Proxy Integer)
        genRep (TCons "Double"   []) = Just $ genRepFromProxy (Proxy :: Proxy Double)
        genRep (TCons "Float"    []) = Just $ genRepFromProxy (Proxy :: Proxy Float)
        genRep (TCons "Ordering" []) = Just $ genRepFromProxy (Proxy :: Proxy Ordering)
        genRep (TCons "Word"     []) = Just $ genRepFromProxy (Proxy :: Proxy Word)
        genRep (TCons "[]" [ts]) = g_li_i <$> genRep ts
        genRep (TFun (TCons "A" []) (TCons "B" []))
            = Just $ genRepFromProxyNoEq (Proxy :: Proxy (A->B))
        genRep (TFun _ _) = Nothing
        -- Some special cases for HugeLists
        genRep (TCons "(,)" [TCons "A" [], TCons "B" []]) = Just $ genRepFromProxy (Proxy :: Proxy (A,B))
        genRep (TCons "(,)" [TCons "[]" [TCons "A" []], TCons "[]" [TCons "B" []]])
            = Just $ genRepFromProxy (Proxy :: Proxy ([A],[B]))
        genRep (TCons "(,)" [TCons "[]" [TCons "A" []], TCons "[]" [TCons "A" []]])
            = Just $ genRepFromProxy (Proxy :: Proxy ([A],[A]))
        genRep x = trace ("*** Warning: Could not generate instances for '" ++ (show x) ++ "', ignoring...") Nothing






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
                 --, ("((+) @("<> trtext <> "))", toDyn plus)
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
gvToName (GivenVar tr i _) = var<>is<>"_<"<>trn <>">"
  where
        trn = T.pack (show tr)
        is = T.pack (show i)
        var = case tyConName (typeRepTyCon tr) of
                "[]" -> "xs"
                "->" -> "f"
                _ -> "x"
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

termVars :: Sig -> Term -> [(Text, GivenInfo)]
termVars sig (Term (Symbol s) []) |
    Just (GivenFun {given_info=v@(GivenVar _ _ _)}) <- sig Map.!? s = [(s,v)]
termVars sig (Term _ args) = concatMap (termVars sig) args

-- note: after this the lookup in the sig won't fire!
renameSymbols :: Map Text Text -> Term -> Term
renameSymbols changes ttr@(Term (Symbol s) args)
    | Just s' <- changes Map.!? s = Term (Symbol s') subv
    | otherwise = Term (Symbol s) subv
    where subv = map (renameSymbols changes) args


-- We don't want to keep repeating the same laws,
-- and we want to have nicer names for variables
reduceVars :: Sig -> Term -> Term
reduceVars sig term = simplified
  where howMany :: Term -> [[GivenInfo]]
        howMany = groupBy ((==) `on` (\(GivenVar tr _ _) -> tr)) 
                  . sort . nub . map snd . termVars sig
        substs vs = catMaybes $ zipWith f vs [0..]
          where f v@(GivenVar tr i g) j = if i == j then Nothing
                                          else Just (gvToName v,
                                                     gvToName $ GivenVar tr j g)
        changes = Map.unions $ map (Map.fromList . substs) $ howMany term
        simplified = renameSymbols changes term
        


-- Note: should be flipped 
termToGen :: Sig -> VarVals -> Term -> Gen Dynamic
termToGen sig init_vv (Term "(==)" [eq_i, a_g, b_g])
    | a_g == b_g = return (toDyn True) -- short-circuit the trivial case
    | otherwise =
    do eq <- termToGen sig Map.empty eq_i
       vv <- if Map.null init_vv
             then do vva <- getVars sig a_g
                     vvb <- getVars sig b_g
                     return (vva <> vvb)
             else return init_vv
       a  <- termToGen sig vv a_g
       b  <- termToGen sig vv b_g
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
 do  symGen <- termToGen sig vv (Term (Symbol sym) [])
     argGens <- mapM (termToGen sig vv) args
     return $ foldl (\f v -> fromJust (dynApply f v)) symGen  argGens
   

dynProp :: Gen Dynamic -> Property
dynProp gen = QC.forAll gen (flip fromDyn (property False))

-- TODO: can we kill a branch once a rewriteable term is detected?
--
