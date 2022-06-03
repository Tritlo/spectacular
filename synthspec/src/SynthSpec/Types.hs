{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, OverloadedStrings,
             ScopedTypeVariables, TypeApplications, RecordWildCards, GADTs,
             StandaloneDeriving, KindSignatures, PolyKinds, RankNTypes,
             GeneralizedNewtypeDeriving, FlexibleContexts, TupleSections #-}

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
import Data.List (groupBy, nub, sort, sortBy)
import Data.Function (on)
import Data.Maybe (catMaybes)
import Debug.Trace
import qualified Type.Reflection as TR

import qualified Data.Monoid as M
import qualified Test.QuickCheck as QC
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Hashable (hash, Hashable)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

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

sigGivens :: (TypeSkeleton -> TypeSkeleton) -> Sig 
          -> (Sig, Map TypeSkeleton (Text, Dynamic) , Map TypeSkeleton (Text,Func))
sigGivens typeMod sigs = (--eqDef <>
                   -- Map.fromList (mapMaybe toEqInst allCons) <>
                   -- Map.fromList (mapMaybe toEmptyLi allCons) <>
                   Map.fromList (mapMaybe consName allCons)
                 , eq_insts
                 , arbs)
  where trs = map (typeMod . sfTypeRep) $ Map.elems sigs
        user_eq = mapMaybe g_eq $ Map.assocs sigs
          where g_eq (k, GivenFun gv@(GivenInst _ eq) tsk)  = Just (tsk, (k,eq))
                g_eq _ = Nothing
        eq_insts = Map.fromList $ user_eq ++
                    (mapMaybe (\c -> ((c,) . fmap sfFunc) <$> toEqInst c)
                                $ filter isCon allCons)
        user_arbs = mapMaybe g_arb $ Map.assocs sigs
          where g_arb (k, f@(GivenFun (GivenVar {})  tsk)) = Just (tsk, (k,f))
                g_arb _ = Nothing
        arbs = Map.fromList 
                    (user_arbs ++
                    mapMaybe (\ty -> (ty,)  <$> consName ty) allCons)
        
        isCon (TCons _ _) = True
        isCon _ = False
        -- we specialcase lists
        cons :: TypeSkeleton -> Set TypeSkeleton
        cons t@(TCons _ r) = Set.unions $ (Set.singleton t):(map cons r)
        cons t@(TFun arg ret) = Set.singleton t <> cons arg <> cons ret
        cons (TVar _) = Set.empty
        addLi :: TypeSkeleton -> [TypeSkeleton]
        addLi t = t:(addLi' 0 t) -- bump this to get more [A], [[A]],
                                 -- [[[A]]], etc.
          where addLi' :: Int -> TypeSkeleton -> [TypeSkeleton]
                addLi' 0 _ = []
                addLi' n t = t':(addLi' (n-1) t')
                 where t' = TCons "[]" [t]
                
        allCons = nubHash $ concatMap addLi $ Set.toList $ Set.unions $ map cons trs
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
                    

        consName :: TypeSkeleton -> Maybe (Text, Func)
        consName t = g <$> genRep t
           where g rep = toTup (GivenFun (GivenVar (g_tr rep) 0 (g_arb rep)) t) 
                 toTup gf@(GivenFun gv _) = (gvToName gv, gf)
        
        -- We have show here as well, but could be removed.


        genRep :: TypeSkeleton -> Maybe GeneratedInstance
        genRep (TVar a) = genRep (TCons (T.toUpper a) [])
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
        genRep (TFun (TCons "A" []) (TCons "A" []))
            = Just $ genRepFromProxyNoEq (Proxy :: Proxy (A->A))
        genRep (TFun _ _) = Nothing
        -- Some special cases for HugeLists
        genRep (TCons "(,)" [TCons "A" [], TCons "B" []]) = Just $ genRepFromProxy (Proxy :: Proxy (A,B))
        genRep (TCons "(,)" [TCons "A" [], TCons "A" []]) = Just $ genRepFromProxy (Proxy :: Proxy (A,A))
        genRep (TCons "(,)" [TCons "[]" [TCons "A" []], TCons "[]" [TCons "B" []]])
            = Just $ genRepFromProxy (Proxy :: Proxy ([A],[B]))
        genRep (TCons "(,)" [TCons "[]" [TCons "A" []], TCons "[]" [TCons "A" []]])
            = Just $ genRepFromProxy (Proxy :: Proxy ([A],[A]))
        genRep x = trace ("*** Warning: Could not generate instances for '" ++ (show x) ++ "', ignoring...") Nothing


addEquality :: (Eq a, Typeable a) => Proxy a -> Sig
addEquality (Proxy :: Proxy a) = Map.singleton key val
  where g_tr = typeRep (Proxy :: Proxy a)
        wrappedEq :: a -> a -> Property
        wrappedEq a b = property ((==) a b)
        key = "<@Eq_"<>(T.pack $ show g_tr)<>"@>"
        val = GivenFun (GivenInst g_tr (toDyn wrappedEq)) $
                        TCons "Eq" [typeRepToTypeSkeleton g_tr]

addArbitrary :: (Typeable a, Arbitrary a) => Proxy a -> Sig
addArbitrary (Proxy :: Proxy a) = Map.singleton (gvToName gv) val
  where g_tr = typeRep (Proxy :: Proxy a)
        g_arb = DynGen (arbitrary :: Gen a)
        gv = GivenVar g_tr 0 g_arb
        val = GivenFun gv $ typeRepToTypeSkeleton g_tr

genRepFromProxy :: (Show a, Eq a, Typeable a, Arbitrary a) =>
                    Proxy a -> GeneratedInstance
genRepFromProxy (Proxy :: Proxy a) = Gend {..}
    where g_tr = typeRep (Proxy :: Proxy a)
          g_arb = DynGen (arbitrary :: Gen a)
          g_eq = Just (toDyn wrappedEq)
          --g_eq = Just (toDyn ((==) :: a -> a -> Bool))
          g_empty_li = toDyn ([] :: [a])
          g_li_i = genRepFromProxy (Proxy :: Proxy [a])
          -- TODO: do something fancier here.
          -- we could add a Show here?
          wrappedEq :: a -> a -> Property
          wrappedEq a b = property ((==) a b)

genRepFromProxyNoEq :: (Typeable a, Arbitrary a) =>
                        Proxy a -> GeneratedInstance
genRepFromProxyNoEq (Proxy :: Proxy a) = Gend {..}
    where g_tr = typeRep (Proxy :: Proxy a)
          g_arb = DynGen (arbitrary :: Gen a)
          g_empty_li = toDyn ([] :: [a])
          g_eq = Nothing
          g_li_i = genRepFromProxyNoEq (Proxy :: Proxy [a])





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

moreGenerators :: Func -> [Func]
moreGenerators (GivenFun (GivenVar tr _ g) grep) =
    map (\v -> (GivenFun (GivenVar tr v g) grep)) [0..]
moreGenerators _ = []

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


gvToNameNoType :: GivenInfo -> Text
gvToNameNoType (GivenVar tr i _) = var<>is
  where trn = T.pack (show tr)
        is = T.pack (show i)
        var = case tyConName (typeRepTyCon tr) of
                "[]" -> "xs"
                "->" -> "f"
                _ -> "x"
gvToNameNoType _ = error "not a given var!"

gvToName :: GivenInfo -> Text
gvToName gv@(GivenVar tr _ _) = (gvToNameNoType gv)<>"_<"<>trn <>">"
    where trn = T.pack (show tr)
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
sfFunc (GivenFun {given_info = GivenInst _ inst_f}) = inst_f
sfFunc (GivenFun {}) = toDyn (() :: ()) 

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
termVars sig (Term "app" [_,f,v]) = concatMap (termVars sig) [f,v]
termVars sig (Term "(==)" [_,lhs,rhs]) = concatMap (termVars sig) [lhs,rhs]
termVars sig (Term (Symbol s) args)
    | Just (GivenFun {given_info=v@(GivenVar _ _ _)}) <- sig Map.!? s = [(s,v)]
    | otherwise = []

-- note: after this the lookup in the sig won't fire!
renameSymbols :: Map Text Text -> Term -> Term
renameSymbols changes ttr@(Term (Symbol s) args)
    | Just s' <- changes Map.!? s = Term (Symbol s') subv
    | otherwise = Term (Symbol s) subv
    where subv = map (renameSymbols changes) args


-- We don't want to keep repeating the same laws,
-- and we want to have nicer names for variables
simplifyVars :: Sig -> Term -> Term
simplifyVars sig term = simplified
  where howMany :: Term -> [[GivenInfo]]
        gv_tr (GivenVar tr _ _) = tr
        tvs = nub . map snd . termVars sig
        howMany = groupBy ((==) `on` gv_tr) . sort . tvs
        substs vs = catMaybes $ zipWith f vs [0..]
          where f v@(GivenVar tr i g) j = 
                    if i == j then Nothing
                    else Just (gvToName v, gvToName $ GivenVar tr j g)
        fewer_vars :: Map Text Text
        fewer_vars = Map.unions $ map (Map.fromList . substs) $ howMany term
        with_fewer_vars :: Term
        with_fewer_vars = renameSymbols fewer_vars term
        -- We want to avoid things where just the order of the variables 
        -- is changed.
        -- TODO: does this help? Is it safe/
        whatOrder :: Term -> [[GivenInfo]]
        whatOrder = groupBy ((==) `on` gv_tr) . sortBy (compare `on` gv_tr) . tvs
        subst_order vs =  zipWith f vs [0..]
          where f v@(GivenVar tr i g) j = (gvToName v, gvToName $ GivenVar tr j g)
        reordered_vars :: Map Text Text
        reordered_vars = Map.unions $ map (Map.fromList . subst_order) $
                            whatOrder with_fewer_vars
        simplified = renameSymbols reordered_vars with_fewer_vars

generalizeType :: TypeSkeleton -> TypeSkeleton
generalizeType (TCons s []) | s `elem` ["A","B","C","D","Acc"]
    = TVar (T.pack $ map toLower $ T.unpack s)
generalizeType (TCons s r) = TCons s $ map generalizeType r
generalizeType (TFun arg ret) = TFun (generalizeType arg) (generalizeType ret)
generalizeType tsk = tsk


monomorphiseType :: TypeSkeleton -> TypeSkeleton
monomorphiseType (TCons s []) | s `elem` ["A","B","C","D","Acc"] = TCons "A" []
monomorphiseType (TCons s r) = TCons s $ map monomorphiseType r
monomorphiseType (TFun arg ret) = TFun (monomorphiseType arg) (monomorphiseType ret)
monomorphiseType tsk = tsk

dropNpTypes :: Term -> Term
dropNpTypes (Term "app" [_,f,v]) = Term "app" [dropNpTypes f,dropNpTypes v]
dropNpTypes (Term s [_]) = Term s []
dropNpTypes (Term s args) = Term s $ map dropNpTypes args

unifyAllVars :: Sig -> Term -> Term
unifyAllVars sig (Term (Symbol s) _) |
    Just (GivenFun {given_info=gv@GivenVar {}}) <- sig Map.!? s = 
        Term "<_>" []
        -- Term (Symbol $ gvToNameNoType gv) []
unifyAllVars sig (Term s args) = Term s $ map (unifyAllVars sig) args

toTemplate :: Sig -> Term -> Term
toTemplate sig (Term (Symbol s) ty) |
    Just (GivenFun {given_info=(GivenVar _ i _) }) <- sig Map.!? s = 
         Term (Symbol $ "<v>") ty
toTemplate sig (Term s args) = Term s $ map (toTemplate sig) args
 
-- When we generalize types, the types of the functions don't match, but
-- since we can coerce between A and B etc. we can actually apply the
-- function. In case the coerce is *wrong*, this error will be inside
-- the generator and so unobservable.
unsafeApply :: Dynamic -> Dynamic -> Dynamic
unsafeApply df@(Dynamic (TR.Fun _ tr) f) dx@(Dynamic _ x)
 = case dynApply df dx of
    Just r -> r
    _ -> Dynamic (unsafeCoerce tr) (unsafeCoerce f x)


-- Note: should be npTermed
termToGen :: Dynamic -> Sig -> VarVals -> Term -> Gen Dynamic
termToGen eq_inst sig init_vv (Term "(==)" [eq_i, a_g, b_g])
    | a_g == b_g = return (toDyn True) -- short-circuit the trivial case
    | otherwise =
    do vv <- if Map.null init_vv
             then do vva <- getVars sig a_g
                     vvb <- getVars sig b_g
                     return (vva <> vvb)
             else return init_vv
       a  <- termToGen eq_inst sig vv a_g
       b  <- termToGen eq_inst sig vv b_g
       return $ unsafeApply (unsafeApply eq_inst a) b
termToGen eq_inst sig vv (Term "app" [_,f_g,v_g]) = do
  f <- termToGen eq_inst sig vv f_g
  v <- termToGen eq_inst sig vv v_g
  return $ unsafeApply f v
termToGen _ sig vv (Term (Symbol sym) _) = do
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
   

dynProp :: Gen Dynamic -> Property
dynProp gen = QC.forAll gen (flip fromDyn (property False))

nubHash :: Hashable a => [a] -> [a]
nubHash li = nubHash' IntSet.empty li
  where nubHash' _ [] = []
        nubHash' seen (a:as) | (hash a) `IntSet.member` seen = nubHash' seen as
        nubHash' seen (a:as) = a:(nubHash' (IntSet.insert (hash a) seen) as)

-- TODO: can we kill a branch once a rewriteable term is detected?
--
