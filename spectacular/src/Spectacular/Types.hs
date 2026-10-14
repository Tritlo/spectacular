{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, OverloadedStrings,
             ScopedTypeVariables, TypeApplications, RecordWildCards, GADTs,
             StandaloneDeriving, KindSignatures, PolyKinds, RankNTypes,
             GeneralizedNewtypeDeriving, FlexibleContexts, TupleSections,
             PatternSynonyms, DeriveGeneric #-}

module Spectacular.Types where
import Data.Dynamic
import Data.Map (Map)
import Data.Text (Text)
import qualified Data.Map as Map
import GHC.Generics (Generic)

import Data.Typeable
import Data.Char (toLower)
import qualified Data.Text as T
import qualified Data.Monoid as M
import Data.CFTA.Symbol (Symbol (Symbol))
import qualified Data.CFTA.Term as CT
import Data.Proxy
import Data.Maybe (mapMaybe)
import Debug.Trace (trace)

import Test.QuickCheck (Arbitrary(..), Property(..), Testable(..), Gen(..))
import qualified Test.QuickCheck as QC
import Unsafe.Coerce
import Test.QuickCheck.Property
import qualified Type.Reflection as TR

import qualified Data.Set as Set
import Data.Set (Set)
import Data.Hashable (hash, Hashable)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

-- | A type: a type variable, a function type, or a type constructor with
-- its arguments.
data TypeSkeleton
  = TVar Text
  | TFun TypeSkeleton TypeSkeleton
  | TCons Text [TypeSkeleton]
  deriving (Eq, Ord, Show, Read, Generic)

instance Hashable TypeSkeleton

-- | A term of the automata. The symbols are interned texts.
type Term = CT.Term Symbol

-- | A term as its symbol and the list of its children.
pattern Term :: Symbol -> [Term] -> Term
pattern Term s ts = CT.Node s ts
{-# COMPLETE Term #-}

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
    g_li_i :: GeneratedInstance
    }

sigGivens :: (TypeSkeleton -> TypeSkeleton) -> Sig -> (TypeSkeleton -> (Maybe GeneratedInstance))
          -> (Sig, Map TypeSkeleton (Text, Dynamic) , Map TypeSkeleton (Text,Func))
sigGivens typeMod sigs extraReps = (
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
        addLi t = t:(addLi' 1 t) -- bump this to get more [A], [[A]],
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

        consName :: TypeSkeleton -> Maybe (Text, Func)
        consName t = g <$> genRep t
           where g rep = toTup (GivenFun (GivenVar (g_tr rep) 0 (g_arb rep)) t) 
                 toTup gf@(GivenFun gv _) = (gvToName gv, gf)
        

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
        --- To allow for types not considered here
        --- Not sure if this is the best way to go about it
        genRep x = 
          case extraReps x of 
            Just t -> Just t
            Nothing -> trace ("*** Warning: Could not generate instances for '" ++ (show x) ++ "', ignoring...") Nothing

addExplicitEquality :: Typeable a => (a -> a -> Bool) -> Sig
addExplicitEquality (fun :: a -> a -> Bool) = Map.singleton key val
  where g_tr = typeRep (Proxy :: Proxy a)
        wrapped a b = property (fun a b)
        key = "<@Eq_"<>(T.pack $ show g_tr)<>"@>"
        val = GivenFun (GivenInst g_tr (toDyn wrapped)) $
                        TCons "Eq" [typeRepToTypeSkeleton g_tr]

        

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
          g_eq = Nothing
          g_li_i = genRepFromProxyNoEq (Proxy :: Proxy [a])




arith :: (Typeable a, Num a, Eq a) => Proxy a -> Sig
arith p = Map.fromList $
                (map (fmap extraFunc) $
                 [ ("0", toDyn zero)
                 , ("1", toDyn $ (fromInteger 1) `asProxyTypeOf` p)
                 ]
                 )
  where zero = (fromInteger 0) `asProxyTypeOf` p

typeRepToTypeSkeleton :: TypeRep -> TypeSkeleton
typeRepToTypeSkeleton tr
     | [] <- tra,
       ltc <- map toLower tcn,
       ltc `elem` ["a", "b", "c","d", "acc"]
       = TCons (T.pack tcn) []
     | tcn == "->",
       [arg,ret] <- args
     = TFun arg ret
     | otherwise = TCons (T.pack tcn) args
  where (tc, tra) = splitTyConApp tr
        tcn = specialName tc
        args = map typeRepToTypeSkeleton tra

-- | The name of a type constructor. GHC 9.6 and later give some built-in
-- type constructors new names, for example List for []. This function
-- gives the name of the special syntax, which the generators use.
specialName :: TyCon -> String
specialName tc
  | tc == tyConOf (Proxy :: Proxy [()]) = "[]"
  | tc == tyConOf (Proxy :: Proxy ((), ())) = "(,)"
  | tc == tyConOf (Proxy :: Proxy ()) = "()"
  | tc == tyConOf (Proxy :: Proxy (() -> ())) = "->"
  | otherwise = tyConName tc

-- | The type constructor of a type.
tyConOf :: Typeable a => Proxy a -> TyCon
tyConOf = typeRepTyCon . typeRep


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
    GivenInst :: TypeRep -> Dynamic -> GivenInfo
    GivenVar :: TypeRep -> Int -> DynGen -> GivenInfo


deriving instance Show GivenInfo

instance Eq GivenInfo where
  (GivenInst t _) == (GivenInst s _) = t == s
  (GivenVar t i _) == (GivenVar s j _) = (i == j) && (t == s)

instance Ord GivenInfo where
  compare (GivenInst t _) (GivenInst s _) = compare t s
  compare (GivenVar t i _) (GivenVar s j _) = if t == s
                                              then compare i j
                                              else compare t s
  compare (GivenInst {}) (GivenVar {}) = LT
  compare (GivenVar {}) _ = GT


gvToNameNoType :: GivenInfo -> Text
gvToNameNoType (GivenVar tr i _) = var<>is
  where trn = T.pack (show tr)
        is = T.pack (show i)
        var = case specialName (typeRepTyCon tr) of
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

type VarVals = Map Text Dynamic


getVars :: Sig -> Term -> Gen VarVals
getVars sig (Term (Symbol sym) args) = do
    vv <- Map.unions <$> (mapM (getVars sig) args)
    case sig Map.!? sym of
        Just (GivenFun {given_info = GivenVar _ _ (DynGen g) }) -> do
            v <- toDyn <$> g
            return (vv <> (Map.singleton sym v))
        _ -> return vv 

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
