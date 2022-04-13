{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
module CCTP.Plugin (plugin) where

import GhcPlugins hiding ((<>))
import TcHoleErrors
import TcHoleFitTypes
import TcRnTypes
import Constraint

import CCTP.Utils

import Application.TermSearch.Dataset
import Application.TermSearch.Type
import Application.TermSearch.TermSearch hiding (allConstructors, generalize)
import Data.ECTA
import Data.ECTA.Term

import qualified Data.Map as Map
import Data.Text (pack, unpack, Text)
import Data.Maybe (fromMaybe, mapMaybe, isJust, fromJust)
import Data.Tuple (swap)
import Data.List (sortOn, groupBy, nub, nubBy, (\\))
import Data.Function (on)
import qualified Data.Monoid as M
import MonadUtils (concatMapM)
import TcRnMonad (writeTcRef, newTcRef, readTcRef, mapMaybeM, getTopEnv)
import TcEnv (tcLookupId, tcLookupIdMaybe, tcLookup)
import qualified Data.Bifunctor as Bi
import TcRnDriver (tcRnGetInfo)
import GHC (ClsInst)
import InstEnv (ClsInst(ClsInst, is_tvs, is_cls_nm, is_tys))
import Language.Dot.Pretty (renderDot)
import ConLike (ConLike(RealDataCon))
import Data.ECTA.Paths (Path, mkEqConstraints)
import Application.TermSearch.Utils
import Data.Containers.ListUtils (nubOrd)


plugin :: Plugin
plugin =
  defaultPlugin
    { holeFitPlugin = \opts ->
        Just $
          HoleFitPluginR {
            hfPluginInit = newTcRef [],
            hfPluginRun = \ref ->
                  ( HoleFitPlugin
                   { candPlugin = \_ c -> writeTcRef ref c >> return [],
                     fitPlugin = \h _ -> readTcRef ref >>= ectaPlugin opts h
                                  }
                              ),
            hfPluginStop = const (return ())
          }
    }


pAnyFunc :: Node
pAnyFunc = Node (map ($ 1) hoogleComps)


invertMap :: Ord b => Map.Map a b -> Map.Map b [a]
invertMap = toMap . groupBy ((==) `on` fst) . sortOn fst . map swap . Map.toList
  where toMap = Map.fromList . map (\((a,r):rs) -> (a,r:map snd rs))


prettyMatch :: Map.Map Text TypeSkeleton -> Map.Map Text [Text] -> Term -> TcM [Text]
prettyMatch skels groups (Term (Symbol t) _) =
  do ty <- skeletonToType tsk
     let str = case ty of
               Just t  -> pack (" :: " ++  showSDocUnsafe (ppr t))
               _ -> pack (" :: " ++ show tsk)
     return $ map (M.<> str) terms
  where tsk = skels Map.! t
        terms = groups Map.! t

candsToComps :: [HoleFitCandidate] -> TcM [((Text, TypeSkeleton), [Type])]
candsToComps = mapMaybeM (fmap (fmap extract) . candToTN)
  where candToTN :: HoleFitCandidate -> TcM (Maybe (Text, (TypeSkeleton, [Type])))
        candToTN cand = fmap (fmap (nm,) . (>>= typeToSkeleton)) (c2t cand)
          where nm = pack $ occNameString $ occName cand
                c2t cand =
                  case cand of
                    IdHFCand id -> return $ Just $ idType id
                    NameHFCand nm -> tcTyThingTypeMaybe <$> tcLookup nm
                    GreHFCand GRE{..} -> tcTyThingTypeMaybe  <$> tcLookup gre_name
        extract (a, (b,c)) = ((a,b), c)
        tcTyThingTypeMaybe :: TcTyThing -> Maybe Type
        tcTyThingTypeMaybe (ATcId tttid _) = Just $ idType tttid
        tcTyThingTypeMaybe (AGlobal (AnId ttid)) =Just $ idType ttid
        tcTyThingTypeMaybe (AGlobal (AConLike (RealDataCon con))) = Just $ idType $ dataConWorkId con
        tcTyThingTypeMaybe _ =  Nothing


instToTerm :: ClsInst -> Maybe (Text, TypeSkeleton)
instToTerm ClsInst{..} | [] <- is_tvs,
                         all isJust args,
                         jargs <- map (fst . fromJust) args =
  Just (clsstr <> tystr,TCons clsstr jargs )
  where clsstr =  pack $  showSDocUnsafe $ ppr is_cls_nm
        tystr = pack $ showSDocUnsafe $ ppr is_tys
        args = map typeToSkeleton is_tys
instToTerm _ =  Nothing

globalTyVars :: [Node]
globalTyVars = [var1, var2, var3, var4, varAcc]

type Comps = [(Text,TypeSkeleton)]
mtau :: Comps -> Node
mtau comps = createMu
  (\n -> union
    (  (arrowType n n:globalTyVars)
    ++ map (Node . (: []) . constructorToEdge n) usedConstructors
    )
  )
 where
  constructorToEdge :: Node -> (Text, Int) -> Edge
  constructorToEdge n (nm, arity) = Edge (Symbol nm) (replicate arity n)

  usedConstructors = allConstructors comps

generalize :: Comps -> Node -> Node
generalize comps n@(Node [_]) = Node
  [mkEdge s ns' (mkEqConstraints $ map pathsForVar vars)]
 where
  vars                = globalTyVars
  nWithVarsRemoved    = mapNodes (\x -> if x `elem` vars then mtau comps else x) n
  (Node [Edge s ns']) = nWithVarsRemoved

  pathsForVar :: Node -> [Path]
  pathsForVar v = pathsMatching (== v) n
generalize _ n = n -- error $ "cannot generalize: " ++ show n


allConstructors :: Comps -> [(Text, Int)]
allConstructors comps =
  nubOrd (concatMap (getConstructors . snd) comps
  ++ [("Bool", 1), ("Map", 2)]) \\ [("Fun", 2)]
 where
  getConstructors :: TypeSkeleton -> [(Text, Int)]
  getConstructors (TVar _    ) = []
  getConstructors (TFun t1 t2) = getConstructors t1 ++ getConstructors t2
  getConstructors (TCons nm ts) =
    (nm, length ts) : concatMap getConstructors ts


ectaPlugin :: [CommandLineOption] -> TypedHole -> [HoleFitCandidate] -> TcM [HoleFit]
ectaPlugin opts TyH{..} scope  | Just hole <- tyHCt,
                                 ty <- ctPred hole = do
      -- We need the generalize (and tau) function here as well to make
      -- the candiateComponents work with type variables that can
      -- be instantiated.
      (fun_comps, scons) <- fmap (nubBy eqType . concat) . unzip <$> candsToComps scope
      -- The constraints are there and added to the graph... but we have to
      -- be more precise when we add them to the machine. Any time a
      -- function requires a constraint to hold for one of it's variables,
      -- we have to add a path equality to the ECTA.
      let constraints = filter (tcReturnsConstraintKind . tcTypeKind) scons
      hsc_env <- getTopEnv
      instance_comps <- mapMaybe instToTerm . concat <$>
                             mapMaybeM (fmap (fmap (\(_,_,c,_,_) -> c) . snd)
                                       . liftIO  . tcRnGetInfo hsc_env . getName
                                       . tyConAppTyCon) constraints
      let scope_comps = fun_comps ++ instance_comps
      let (scopeNode, anyArg, skels, groups) =
            let argNodes = map (Bi.bimap Symbol (generalize scope_comps . typeToFta)) scope_comps
                anyArg = generalize scope_comps $ Node $
                   map (\(s,t) -> Edge (Symbol s) [typeToFta t]) scope_comps
                scopeNode = anyArg
                skels = Map.fromList scope_comps
                groups = Map.fromList $ map (\(t,_) -> (t,[t])) scope_comps
            in (scopeNode, anyArg, skels, groups)
      case typeToSkeleton ty of
         Just (t, cons) | resNode <- typeToFta t -> do
             let res = getAllTerms $ refold $ reduceFully $ filterType scopeNode resNode
             ppterms <- concatMapM (prettyMatch skels groups . prettyTerm ) res
             let moreTerms = map (pp . prettyTerm) $ concatMap (getAllTerms . refold . reduceFully . flip filterType resNode ) (tk anyArg 3)
             liftIO $ writeFile "scope-node.dot" $ renderDot $ toDot scopeNode
             return $ map (RawHoleFit . text . unpack) $ ppterms ++ moreTerms
         _ ->  do liftIO $ putStrLn $  "Could not skeleton `" ++ showSDocUnsafe (ppr ty) ++"`"
                  return []
