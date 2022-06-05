{-# OPTIONS -fno-max-valid-hole-fits #-}
{-# LANGUAGE OverloadedStrings, TypeApplications, RecordWildCards,
             TupleSections, StandaloneDeriving, DeriveAnyClass,
             DeriveGeneric, BangPatterns #-}
module Spectacular (
    module Spectacular.Types,
    module Data.Proxy,
    tacularSpec,
    tacularSpec'
) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
-- import qualified Data.Map.Lazy as Map
-- import Data.Map.Lazy (Map)
import Data.Tuple (swap)
-- import qualified Data.Map as Map
-- import Data.Map (Map)
import qualified Data.Dynamic as Dyn
import Data.Dynamic (Dynamic)
import qualified Data.Bifunctor as Bi
import MonadUtils (concatMapM)
import Spectacular.Types
import Spectacular.Utils
import Spectacular.Testing
import qualified Spectacular.Utils as SS
import Data.Proxy (Proxy(..))


import Application.TermSearch.Dataset
import Application.TermSearch.Type
import Application.TermSearch.TermSearch hiding (allConstructors, generalize)
import Data.ECTA
import Data.ECTA.Term
import Data.ECTA.Internal.ECTA.Operations ( nodeRepresents,
                                            nodeRepresentsTemplate,
                                            edgeRepresentsTemplate)
import Data.ECTA.Internal.ECTA.Enumeration
    (expandPartialTermFrag, getUVarValue, UVarValue(..), TermFragment(..),
     getUVarRepresentative, getPruneDeps, addPruneDep, deletePruneDep,
     fragRepresents, EnumerationState, runEnumerateM, enumPrune,
     initEnumerationState, mergeNodeIntoUVarVal)
import Data.Persistent.UnionFind ( uvarToInt, intToUVar, UVar )
import Data.List hiding (union)
import qualified Test.QuickCheck as QC
import Control.Monad (zipWithM_, filterM, when, mzero)
import qualified Data.Text as T
import qualified Data.Set as Set
import qualified System.Environment as Env
import qualified Text.Read as TR
import Debug.Trace
import Data.Maybe (fromMaybe, catMaybes, mapMaybe, isJust)
import Data.Char (isAlphaNum)
import Data.Either (rights)
import qualified Data.Monoid as M

import qualified Control.Concurrent.Async as CCA
import qualified Control.Concurrent as CC

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.Hashable (hash, Hashable)
import qualified Data.HashSet as HS
import qualified Data.List as L
import Data.Function (on)
import GHC.TopHandler
import Data.Containers.ListUtils (nubOrdOn)

-- TODO: make this an e-graph or similar datastructure
data Rewrite = Rewrite [Term] (IntMap Term) deriving (Show)

rwrMap :: Rewrite -> IntMap Term
rwrMap (Rewrite _ r) = r

updateRewrites :: Either Term Term -> Rewrite -> IO Rewrite
updateRewrites (Left (Term "(==)" [_,a,b])) rw =
    return $ updRw a b rw
updateRewrites (Right hole_rule) (Rewrite holeRules mp) =
    return (Rewrite (hole_rule:holeRules) mp)
updateRewrites _ r = return r



data StEcta = StEcta { scope_comps  :: Comps,
                      any_arg       :: Node,
                      eq_insts      :: Map TypeSkeleton (T.Text, Dynamic),
                      arb_insts     :: Map TypeSkeleton (T.Text, Func),
                      sig_ty_cons   :: [TypeSkeleton],
                      compl_sig     :: Sig
                      } deriving (Show)


hasSmallerRewrite :: Rewrite -> Term -> Bool
hasSmallerRewrite rw@(Rewrite _ rw_mp) t@(Term _ args) =
 case rw_mp IM.!? (hash t) of
   Just r -> termSize t <= termSize r
   _ -> any (hasSmallerRewrite rw) args

hasRewrite :: Rewrite -> Term -> Bool
hasRewrite rw@(Rewrite _ rw_mp) t@(Term _ args) =
 case rw_mp IM.!? (hash t) of
   Just r -> True
   _ -> any (hasRewrite rw) args

generalizedTerm :: IntMap T.Text -> Term -> [Term]
generalizedTerm arbs t@(Term (Symbol tsy) [ty]) =
    case arbs IM.!? (hash ty) of
        Just el | tsy == el -> [t]
        Just el -> [Term (Symbol el) [ty]]
        _ -> []
generalizedTerm arbs t@(Term "app" [ty,f,v]) =
    let gf = (f:generalizedTerm arbs f)
        gv = (v:generalizedTerm arbs v)
        combs = [Term "app" [ty,f',v'] | f' <- gf, v' <- gv]
    in case arbs IM.!? (hash ty) of
        Just el -> (Term (Symbol el) [ty]):combs
        _ -> combs
generalizedTerm arbs t@(Term (Symbol tsy) []) =
    [Term (Symbol el) [] | el <- IM.elems arbs]
generalizedTerm arbs t@(Term "app" [f,v]) =
    let gf = (f:generalizedTerm arbs f)
        gv = (v:generalizedTerm arbs v)
        combs = [Term "app" [f',v'] | f' <- gf, v' <- gv]
    in [Term (Symbol el) [] | el <- IM.elems arbs] ++ combs
generalizedTerm _ t = [t] -- shouldn't happend

-- If there is a law that involves arbitrary xs and ys, it must in particular
-- also hold whenever xs == ys. So it suffices to explore laws where we have
-- only a single generator in scope and then generalizing them.
generalizeLaw :: Sig -> Term -> (Sig, [Term])
generalizeLaw sig t@(Term "(==)" [ty,lhs,rhs]) =
    let (lhsig, lhss) = generalizedLaw' sig lhs
        (rhsig, rhss) = generalizedLaw' lhsig rhs
        varIds = Map.elems . termVarIds rhsig -- we can't simplify more,
                                               -- since they need to be of
                                               -- different types.
    in (rhsig,  -- We want the most general one first with the
                -- lowest variables. We just keep the first one
                -- so it's OK if we generate too many.
                -- TODO: we can probably do better by splitting the
                -- varIds here into the lhs and rhs, but we leave it like
                -- this for now. We count the number of variables of each
                -- type and sort by that. Note that from the way we generate
                -- it, the terms are already sorted by varIds.
                map fst $ concat $ reverse $ -- then we reverse and concat,
                                             -- so that the terms with the
                                             -- biggest number of variables
                                             -- are first.
                groupBy ((==) `on` (map fst . snd)) $ -- we group by number of
                                                      -- variables of each type
                sortOn (map fst . snd) $ -- we sort on the number of variables
                                         -- of each type
                nubOrdOn (map snd . snd) $ -- we remove those that are equal
                                           -- modulo renaming
                map (fmap (map countAndRename) ) $ -- we count and rename
                filter ( not . all (all (== 0)) . snd) $ -- the original term
                filter (any prune . snd) $ -- we remove things that are
                                           -- obviously equal
                map (\t -> (t, varIds t)) $
                [Term "(==)" [ty, lhs',rhs'] | lhs' <- lhss, rhs' <- rhss])
  where var_count = Map.unionWith max (countVars sig lhs) (countVars sig rhs)
        -- If the list doesn't start with 0 and has a variable outside
        -- the list, we can disregard it immediately
        prune :: [Int] -> Bool
        prune (0:r) | lr <- length r, lr == 0 || any (lr <=) r  = False
        prune _ = True
        countAndRename :: [Int] -> (Int, [Int])
        countAndRename var_ids = (IntSet.size u_set, map (uv_mp IM.!) var_ids)
          where u_set = IntSet.fromList var_ids
                u_vars = IntSet.toAscList u_set
                uv_mp = IM.fromList $ zip u_vars [0..]
        generalizedLaw' sig c@(Term (Symbol tsy) [ty]) =
           case sig Map.!? tsy of
              Just v@(GivenFun (GivenVar {}) grep) ->
                  let gens = take (var_count Map.! grep) $ moreGenerators v
                      f (GivenFun v@(GivenVar {}) _) = Just v
                      f _ = Nothing
                      gnames = mapMaybe (fmap gvToName . f) gens
                      gsig = Map.fromList $ zip gnames gens
                  in (sig <> gsig, [Term (Symbol n) [ty] | n <- gnames] )
              _ -> (sig, [c])
        generalizedLaw' sig (Term "app" [ty,f,v]) =
            let (fsig, fs) = generalizedLaw' sig f
                (vsig, vs) = generalizedLaw' fsig v
            in (vsig, [Term "app" [ty, f',v'] | f' <- fs, v' <- vs])

termVarIds :: Sig -> Term -> Map TypeSkeleton [Int]
termVarIds sig (Term (Symbol tsy) [_]) =
    case sig Map.!? tsy of
        Just v@(GivenFun (GivenVar _ i _) grep) -> Map.singleton grep [i]
        _ -> Map.empty
termVarIds sig (Term symbol args) =
    Map.unionsWith (++) $ map (termVarIds sig) args


countVars :: Sig -> Term -> Map TypeSkeleton Int
countVars sig (Term (Symbol tsy) [_]) =
    case sig Map.!? tsy of
        Just v@(GivenFun (GivenVar _ _ _) grep) -> Map.singleton grep 1
        _ -> Map.empty
countVars sig (Term symbol args) =
    Map.unionsWith (+) $ map (countVars sig) args



hasSubsumption :: Rewrite -> IntMap T.Text -> Term -> Maybe Term
hasSubsumption rw@(Rewrite _ rw_mp) arbs t@(Term s args) =
    L.find (flip IM.member rw_mp . hash) (generalizedTerm arbs t)

hasSubsCanon :: Sig -> Rewrite -> IntMap T.Text -> Term -> Maybe Term
hasSubsCanon sig rw@(Rewrite _ rw_mp) arbs t@(Term s args) =
    L.find (flip IM.member rw_mp . hash
            . canonicalize sig) (generalizedTerm arbs $ canonicalize sig t)

hasAnySub :: Rewrite -> Term -> Bool
-- TODO: this is a LINEAR scan, we should be able to do a lot better.
hasAnySub rw@(Rewrite seen _) t | any (termHoleEq $ dropNpTypes t) seen = True
  where -- Equality on terms based on holes
        termHoleEq :: Term -> Term -> Bool
        termHoleEq  _ (Term (Symbol s) _) | T.isPrefixOf "<_" s = True
        termHoleEq t1@(Term s1 a1) t2@(Term s2 a2) =
            hash t1 == hash t2 || ( s1 == s2 && length a1 == length a2
                                    && all (uncurry termHoleEq) (zip a1 a2))
hasAnySub rw@(Rewrite seen _) (Term _ (_:args)) = any (hasAnySub rw) args
hasAnySub _ _ = False

typeSkeletonToTerm :: TypeSkeleton -> Term
typeSkeletonToTerm (TCons s args)
    = Term (Symbol s) $ map typeSkeletonToTerm args
typeSkeletonToTerm (TFun f v) =
    Term "->" [Term "(->)" [], typeSkeletonToTerm f, typeSkeletonToTerm v]

termTyToTypeSkeleton  :: Term -> TypeSkeleton
termTyToTypeSkeleton (Term "->" [Term "(->)" [], a, b]) =
    TFun (termTyToTypeSkeleton a) (termTyToTypeSkeleton b)
termTyToTypeSkeleton (Term (Symbol s) args) =
    TCons s $ map termTyToTypeSkeleton args


-- [Note: re-writes]: We don't need to do the re-write if there is a smaller
-- version, because that will already have been seen.

-- [Note: Hole-rewrites]
-- perforate :: Term -> Term -> Term
-- perforate v t@(Term s args) | v == t = Term "_" args
--                             | otherwise = Term s $ map (perforate v) args
-- fillHole :: Term -> Term -> Term
-- fillHole fill (Term "_" args) = fill
-- fillHole fill (Term s args) = Term s (map (fillHole fill) args)

-- -- TODO: probably a lot better way to do his
-- matchHole :: (Term, Term) -> Term -> Term
-- matchHole rule@(typ,holed) term@(Term s args) =
--     case filled Map.!? term of
--         Just fill -> fill
--         -- We could probably reuse the filleds but eh.
--         _ -> Term s (map (matchHole rule) args)
--   where getOfType :: Term -> Term -> [Term]
--         getOfType typ t@(Term _ (tts:rest)) | typ == tts = (t:(concatMap (getOfType typ) rest))
--                                             | otherwise = concatMap (getOfType typ) rest
--         getOfType _ _ = []
--         filled = Map.fromList $ map (\fill -> (fillHole fill holed, fill))
--                               $ getOfType typ term

updRw :: Term -> Term -> Rewrite -> Rewrite
updRw a b (Rewrite hole_rules mp) =
    let (sml,big) = if termSize a < termSize b
                    then (a,b) else if termSize a == termSize b
                                    then if length (show a) < length (show b)
                                         then (a,b)
                                         else (b,a)
                                    else (b,a)
    in -- traceShow (ppNpTerm big ++ " ==> " ++ ppNpTerm sml) $
       Rewrite hole_rules (IM.insert (hash big) sml mp)

applyRewrites :: Rewrite -> Node -> IO Node
applyRewrites r n = return n

initRewrites :: IO Rewrite
initRewrites = return $ Rewrite [] IM.empty

termSize :: Term -> Int
termSize (Term s []) = 1
termSize (Term s [_]) = 1
termSize (Term s [_, f,v]) = 1 + termSize f + termSize v
termSize (Term s [f,v]) = 1 + termSize f + termSize v
termSize (Term s args) = 1 + sum (map termSize args)

-- if we find a rewrite from anything to a given var, it holds
-- for all things of that type! i.e. if x == x ++ [],
-- then we can rewrite all instances of (_ :: [A] ++ []) to (_::[A])
-- best would probably be to apply this in the node.


-- TODO: we're maybe calling getUVarValue too often here.
oracle :: ([Term],[Term])
            -> UVar
            -> Either TermFragment Node
            -> EnumerateM Bool
oracle (templs,rws) uv (Left tf) = do
    deps <- getPruneDeps
    -- traceShowM (uv, tf)
    -- traceShowM deps
    -- tv <- getUVarValue (intToUVar 0)
    -- case tv of
    --     UVarEnumerated t -> expandPartialTermFrag t >>= traceShowM
    --     _ -> return ()
    if IM.null deps
    then if (uv == intToUVar 0)
         then {-# SCC "fresh-start" #-} fragRepresents True tf (rws ++ templs)
         else return False -- a type is being selected.
    else case deps IM.!? (uvarToInt uv) of
            Just rw' -> do deletePruneDep (uvarToInt uv)
                           {-# SCC "resume" #-} fragRepresents True tf rw'
            _ -> return False
-- TODO: this is too strong, it just throws everything away even if
-- we wouldn't encounter that one.
oracle (templs,rws) uv (Right n) = do
    return (any (nodeRepresentsTemplate n) (templs ++ rws))
    -- let cf n = M.Any (any (nodeRepresentsTemplate n) $ templs)
    --     will_encounter =  M.getAny (crush (onNormalNodes cf) n)
    -- let rmIfRep n | any (nodeRepresentsTemplate n) (templs ++ rws) = EmptyNode
    --     rmIfRep n = n
    --     newNode = mapNodes rmIfRep n
    -- UVarUnenumerated _ scs <- getUVarValue uv
    -- mergeNodeIntoUVarVal uv newNode scs
    -- return False
    -- in return $
hasTemplate :: Term -> Bool
hasTemplate (Term (Symbol s) args) = T.isPrefixOf "<v" s || any hasTemplate args


type TermSet = HS.HashSet Term

data GoState = GoState {seen :: !IntSet, --hashed integers
                        rwrts :: Rewrite,
                        unique_terms :: !(Map Term TermSet),
                        stecta :: StEcta,
                        so_far :: !Int,
                        lvl_nums :: ![Int],
                        cur_lvl :: Int,
                        law_nums :: [Int],
                        current_terms :: [Term],
                        rewrite_terms :: ![Term],
                        ty_cons_to_check :: [TypeSkeleton],
                        phase_number :: Int
                        } deriving (Show)

tacularSpec :: [Sig] -> IO ()
tacularSpec sigs =
    do args <- Env.getArgs
       let size = case args of
                    arg:_ | Just n <- TR.readMaybe arg -> n
                    _ -> 6 -- Set to 6 to save time on the flight xD:w
       let phase = case args of
                    _:arg:_ | Just n <- TR.readMaybe arg -> n
                    _ -> 3 -- Set to 6 to save time on the flight xD:w
       tacularSpec' size phase (const Nothing) sigs

tacularSpec' :: Int -> Int -> (TypeSkeleton -> (Maybe GeneratedInstance)) -> [Sig] -> IO ()
tacularSpec' size phase extraReps sigs =
    do let sig = mconcat sigs
           mkStecta sig givenTrans skelTrans =
                    StEcta { scope_comps = sc, any_arg = ag,
                             compl_sig = compl_sig,
                             sig_ty_cons = Map.keys eq_insts,
                             eq_insts = eq_insts,
                             arb_insts = arbs }
             where skels =  Map.assocs $ (skelTrans  . sfTypeRep) <$> sig
                   (givenSig, eq_insts, arbs) = sigGivens givenTrans sig extraReps
                   givens = Map.assocs $ (givenTrans . sfTypeRep) <$> givenSig
                   compl_sig = sig <> givenSig
                   sc = skels ++ givens
                   ag = Node $ map (\(s,t) -> Edge s [t]) $
                        -- we generalize the functions in the signature but not
                        -- This means we don't select givens as candidates
                        -- for application which is what we want, we don't
                        -- want to apply variables to each other.
                        ngnodes givens ++ gnodes skels
                   addSyms st tt = map (Bi.bimap (Symbol . st) (tt . typeToFta))
                   ngnodes = addSyms id id
                   gnodes = addSyms id (generalize sc)
           StEcta { compl_sig = compl_sig,
                    arb_insts = arb_insts,
                    sig_ty_cons = sig_ty_cons} = mkStecta sig id id
       -- putStrLn "sig"
       -- putStrLn "------------------------------------------------------------"
       -- mapM_ print $ Map.assocs sig
       -- putStrLn "given sig"
       -- putStrLn "------------------------------------------------------------"

       putStrLn $ "In Scope (" ++ show (Map.size compl_sig) ++ " functions/constants):"
       putStrLn "---------------------------------"
       mapM_ (putStrLn . T.unpack) $ Map.keys compl_sig
       putStrLn ""
       putStrLn "Type constructors (and derived) in the signature:"
       putStrLn "---------------------------------"
       mapM_ print sig_ty_cons
       putStrLn ""
       putStrLn "Variable generators"
       putStrLn "---------------------------------"
       mapM_ print (Map.assocs arb_insts)
       putStrLn ""

       let isId :: Term -> Bool
           isId (Term "(==)" [_, a,b]) = (hash a) == (hash b)
           isId _ = False

           mtk _ _ _ 0 = []
           mtk _ anyArg False 1 = [anyArg]
           mtk comps anyArg True 1 = [anyArg, SS.applyOperator comps]
           mtk comps anyArg _ k = map constructApp [1.. (k-1)]
            where
                constructApp :: Int -> Node
                constructApp i =
                    mapp (union $ mtk comps anyArg False i)
                         (union $ mtk comps anyArg True (k-i))



       putStrLn "Laws according to Haskell's (==):"
       putStrLn "---------------------------------"
       let qc_args = QC.stdArgs { QC.chatty = False,
                                  QC.maxShrinks = 0,
                                  QC.maxSuccess = 100}

           -- TODO: add e-graphs and rewrites.
           go :: Int -> Int -> IO ()
           go n phase  =
                  do rwrts <- initRewrites
                     let stecta@StEcta{..} = mkStecta sig monomorphiseType monomorphiseType
                     go' GoState {seen = IntSet.empty,
                                  rewrite_terms = [],
                                  rwrts = rwrts,
                                  unique_terms = Map.empty,
                                  stecta = stecta,
                                  so_far = 0,
                                  cur_lvl = 0,
                                  lvl_nums = [1..(n+1)],
                                  law_nums = [1..],
                                  phase_number = 1,
                                  current_terms = [],
                                  ty_cons_to_check = sig_ty_cons
                                  }
             where
               go' :: GoState -> IO ()
               go' (GoState{ lvl_nums = [],
                             phase_number = pn@(1),
                            current_terms = [] , ..}) = do
                    putStrLn $ "Fully monomorphic phase finished.." ++ show so_far ++ " terms examined."
                    putStrLn $ show (sum $ map HS.size $ Map.elems unique_terms) ++ " unique terms discovered."
                    when (pn < phase) $ do
                        putStrLn $ "Starting phase with more types...."
                        let stecta@StEcta{..} = mkStecta sig id id
                        go' GoState{ cur_lvl = 0,
                                    phase_number = 2,
                                    lvl_nums= [1..cur_lvl],
                                    ty_cons_to_check = sig_ty_cons,
                                    current_terms=[],..}
               go' (GoState{ lvl_nums = [],
                             phase_number = pn@(2),
                            current_terms = [] , ..}) = do
                    putStrLn $ "Monomorphic phases finished.." ++ show so_far ++ " terms examined."
                    putStrLn $ show (sum $ map HS.size $ Map.elems unique_terms) ++ " unique terms discovered."
                    when (pn < phase) $ do
                        putStrLn $ "Starting mono-polymorphic phase...."
                        let stecta@StEcta{..} = mkStecta sig id (generalizeType . monomorphiseType)
                        go' GoState{ cur_lvl = 0,
                                    phase_number = 3,
                                    lvl_nums= [1..cur_lvl],
                                    ty_cons_to_check = sig_ty_cons,
                                    current_terms=[],..}
               go' (GoState{ lvl_nums = [],
                             phase_number = pn@(3),
                            current_terms = [] , ..}) = do
                 putStrLn $ "Mono-polymorphic phase done! " ++ show so_far ++ " terms examined."
                 putStrLn $ show (sum $ map HS.size $ Map.elems unique_terms) ++ " unique terms discovered."
                 when (pn < phase) $ do
                     let stecta@StEcta{..} = mkStecta sig id generalizeType
                     putStrLn $ "Starting fully-polymorphic phase...."
                     go' GoState{ cur_lvl = 0,
                                 phase_number = 4,
                                 lvl_nums= [1..cur_lvl],
                                 ty_cons_to_check = sig_ty_cons,
                                 current_terms=[],..}
               go' (GoState{ lvl_nums = [],
                            current_terms = [] , ..}) = do
                 putStrLn $ "Done! " ++ show so_far ++ " terms examined."
                 putStrLn $ show (sum $ map HS.size $ Map.elems unique_terms) ++ " unique terms discovered."
               go' GoState {stecta=stecta@StEcta{..},
                            ty_cons_to_check = [],
                            lvl_nums = (lvl_num:lvl_nums),
                            current_terms = current_terms@[],..} = do
                    go' GoState {ty_cons_to_check = sig_ty_cons, cur_lvl = lvl_num, ..}
               go' GoState {stecta=stecta@StEcta{..},
                            ty_cons_to_check = (tc:ty_cons_to_check),
                            current_terms = [],..} = do
                --putStrLn ("Checking " ++ (T.unpack $ ppTy tc) ++ " with size " ++ show lvl_num ++ "...")

                refreshCount "Folding ECTA" "" "" cur_lvl so_far
                let toText e = T.pack $ ppNpTerm $ npTerm e
                    nextNode = union $ mtk scope_comps any_arg False cur_lvl

                filtered_and_reduced <- fmap refold <$> collectStats $
                    (return $ reduceFully $ (filterType nextNode $ typeToFta tc))


                let terms = getAllTermsPrune
                              (oracle $ partition hasTemplate rewrite_terms)
                              filtered_and_reduced

                go' GoState{ current_terms=terms,..}
               go' GoState{law_nums = law_nums@(n:ns),
                           current_terms = (full_term:terms),
                           stecta = stecta@StEcta{..},
                           ..}
                 | Term "filter" [current_ty,_] <- full_term,
                   not (current_ty `Map.member` unique_terms) =
                    go' (GoState{current_terms = terms,
                                unique_terms = Map.insert current_ty (HS.singleton np_term) unique_terms,
                                ..})
                 | (hash np_term) `IntSet.member` seen = skip seen
                 | hasSmallerRewrite rwrts' np_term = skip (IntSet.insert (hash np_term) seen)
                 | hasAnySub rwrts' np_term = skip (IntSet.insert (hash np_term) seen)
                 | otherwise = do
                    let other_terms = HS.toList $ unique_terms Map.! current_ty
                        terms_to_test = map termToTest other_terms
                         -- No need to run multiple tests if there are no variables!
                        runTest eq_inst sig t =
                            -- We test 100x per variable, but for constants we
                            -- need only test once!
                            let nvs = 100
                                qc_args' = qc_args {QC.maxSuccess = nvs}
                            in collectStats $ (quickCheckBoolOnly qc_args' $
                                                  dynProp $ termToGen eq_inst sig Map.empty t)
                        testAll :: Dynamic -> Sig -> [Term] -> IO (Maybe Term)
                        testAll eq_inst sig [] = return Nothing
                        testAll eq_inst sig (t:ts) =
                            do r <- runTest eq_inst sig t
                               if r then return (Just t)
                               else testAll eq_inst sig ts
                        testAllPar :: Dynamic -> Sig -> [Term] -> IO (Maybe Term)
                        testAllPar eq_inst sig [] = return Nothing
                        testAllPar eq_inst sig terms =
                          do n <- CC.getNumCapabilities
                             if n == 1
                             then testAll eq_inst sig terms
                             else if n >= length terms
                                  then testAllPar' [] $ map (:[]) terms
                                  else testAllPar' [] $ (chunks ((length terms) `div` n) terms)
                          where firstSuccessful :: [CCA.Async (Maybe Term)]  -> IO (Maybe Term)
                                firstSuccessful [] = return Nothing
                                firstSuccessful as = do
                                     do (a,r) <- CCA.waitAny as
                                        let as' = filter (/= a) as
                                        case r of
                                            Just _ -> do mapM CCA.cancel as'
                                                         return r
                                            _ -> firstSuccessful as'
                                testAllPar' :: [CCA.Async (Maybe Term)]
                                            -> [[Term]] -> IO (Maybe Term)
                                -- if there's only one, no need for async
                                testAllPar' [] [] = return Nothing
                                testAllPar' [] [c] = testAll eq_inst sig c
                                -- if we don't have any more chunks to start, we
                                -- just finish it
                                testAllPar' as [] = firstSuccessful as
                                -- otherwise, we have to start the work (and we check if we've finished anything so far)
                                testAllPar' as (c:cs) =
                                    CCA.withAsync (testAll eq_inst sig c) $
                                        \a -> testAllPar' (a:as) cs
                        testAllInOrderAsync :: Dynamic -> Sig -> [Term] -> IO (Maybe Term)
                        testAllInOrderAsync _ _ [] = return Nothing
                        testAllInOrderAsync eq_inst sig (a:as) =
                             CCA.withAsync (runTest eq_inst sig a) $ \aref ->
                                 CCA.withAsync (testAllInOrderAsync eq_inst sig as) $ \asref -> do
                                     ares <- CCA.wait aref
                                     -- if the first one is succesful, we don't care
                                     -- about the rest!
                                     if ares then do CCA.cancel asref
                                                     return (Just a)
                                             else CCA.wait asref

                    refreshCount ("exploring " ++ (show current_ty)) ""
                                 -- (" (" ++ (show $ length terms) ++ " left at this size)")
                                 ("(" ++ (show $ length terms_to_test) ++ " to test...)") cur_lvl so_far
                    holds <- testAllPar eq_inst compl_sig terms_to_test


                    let sf' = so_far + 1
                    case holds of
                        Nothing -> do refreshCount ("exploring " ++ (show current_ty)) ""
                                                   -- (" (" ++ (show $ length terms) ++ " left at this size)")

                                                   "" cur_lvl sf'
                                      go' GoState { so_far = sf',
                                                    current_terms = terms,
                                                    unique_terms =
                                                      Map.adjust (HS.insert wip_rewritten) current_ty unique_terms,
                                                    rwrts = rwrts',..}

                        -- These tests are expensive, so we only do them for laws that hold.
                        Just t -> do
                            -- putStrLn ("\r" ++ (ppNpTerm $ npTerm' t) ++  " ")
                            let (gsig, glaws) =
                                  -- We have to be a bit careful about the order
                                  -- of the generalized laws, because we test
                                  -- them in order.
                                        generalizeLaw compl_sig $ npTerm' t

                            -- If we don't find a more general law, we use the one
                            -- we found.
                            --mapM_ print glaws
                            refreshCount "generalizing" "" ("(" ++ show (length glaws) ++ " possibilities...)") cur_lvl sf'
                            most_general <- fromMaybe t <$> testAllInOrderAsync eq_inst gsig glaws
                            let (Term "(==)" [_,_,mgrhs]) = canonicalize gsig most_general

                            -- Note: this should be t, because the variables
                            -- don't exist outside here!
                            rwrts''@(Rewrite s _)
                                    <- do let npt = npTerm' t
                                          r1 <- updateRewrites (Left $ npt) rwrts'
                                          let npmg = npTerm' most_general
                                          r2 <- if npt /= npmg
                                                then updateRewrites (Left npmg) r1
                                                else return r1
                                          updateRewrites (Right mgrhs) r2
                            let law_str = (show n <> ". ") <> (ppNpTerm $ most_general)
                                lsl = max 0 (80 - length law_str)
                            putStrLn ("\r" ++ law_str ++ replicate lsl ' ')
                            refreshCount  ("exploring " ++ (show current_ty))  ""
                                          -- (" (" ++ (show $ length terms) ++ " left at this size)")
                                           "" cur_lvl sf'
                            -- continue sf' rwrts'' ns terms
                            let Term "filter" [_, rewrite_term] = full_term
                                new_rw = toTemplate gsig rewrite_term
                                new_rws = (new_rw:rewrite_terms)
                                -- we've learned a new rewrite, so we restart the
                                -- machine with a new oracle function.
                            go' GoState {
                                    seen = seen <> IntSet.singleton (hash np_term),
                                    so_far=sf',
                                    rwrts = rwrts'',
                                    law_nums = ns,
                                    current_terms = terms,
                                    rewrite_terms = new_rws,
                                    ..}
                  where skip seen = do go' GoState{so_far = so_far+1,
                                                    current_terms = terms, ..}
                        -- wrt variable renaming
                        np_term = npTerm' full_term
                        Term "filter" [current_ty,_] = full_term

                        term_eq_insts = Map.fromList $ map (Bi.first typeSkeletonToTerm)
                                                     $ Map.assocs eq_insts
                        (eq_txt, eq_inst) = term_eq_insts Map.! current_ty
                        termToTest o = Term "(==)" [ Term (Symbol eq_txt) []
                                                   , o, wip_rewritten]
                        -- we're probably missing out on some rewrites due to
                        -- us operating on the flipped term

                        (wip_rewritten, rwrts') = (np_term, rwrts)
       go size phase

canonicalize :: Sig -> Term -> Term
canonicalize sig = unifyAllVars sig . dropNpTypes

npTerm :: Term -> Term
npTerm (Term "filter" [_,
                      Term "app" [_,
                                  _,
                                  Term "app" [_,
                                              _,
                                              Term "app" [_,
                                                          _,
                                                          Term "(==)" _ ,
                                                          Term eqi _],
                                              lhs],
                                  rhs ]])
            = Term "(==)" [Term eqi [], npTerm lhs, npTerm rhs]
npTerm (Term "app" [t,_,a,v]) =  (Term "app" $ [t, npTerm a, npTerm v])
npTerm t = t

npTerm' :: Term -> Term
npTerm' (Term "filter" [_,term]) = npTerm' term
npTerm' (Term "app" [t,_,a,v]) =  (Term "app" $ [t, npTerm' a, npTerm' v])
npTerm' t = t


showNpTerm :: Term -> String
showNpTerm = ppTerm' 0
 where ppTerm' n (Term "app" ns) = intercalate "\n" $ ((replicate n ' ' ++ "app" ):(map ((replicate (n+2) ' ' ++) . ppTerm' (n+2)) ns))
       ppTerm' 0 (Term "(==)" [_, lhs, rhs]) = intercalate "\n"  [ppTerm' 0 lhs, ppTerm' 0 rhs]
       ppTerm' _ t = show t

ppNpTerm :: Term -> String
ppNpTerm t | (Term "(==)" [_, lhs, rhs]) <- t = ppTerm' False lhs <> " == " <> ppTerm' False rhs
           | otherwise = ppTerm' False t
  where
        ppTerm' True (Term "app" [_,f,v]) = "(" <> ppTerm' True f <> " " <> ppTerm' True v <> ")"
        ppTerm' _ (Term "app" [_,f,v]) = ppTerm' True f <> " " <> ppTerm' True v
        ppTerm' True (Term "app" [f,v]) = "(" <> ppTerm' True f <> " " <> ppTerm' True v <> ")"
        ppTerm' _ (Term "app" [f,v]) = ppTerm' True f <> " " <> ppTerm' True v
        ppTerm' True (Term (Symbol t) _) = parIfReq (T.unpack t)
        ppTerm' _ (Term (Symbol t) _) = T.unpack t
        parIfReq s@(c:_) | c /= '(', c /= '[', not (isAlphaNum c) = "("<>s<>")"
        parIfReq s = s

refreshCount :: String -> String -> String -> Int -> Int -> IO ()
refreshCount _ _ _ _ _ = return ()
refreshCount pre mid post size i = putStr (o ++ fill ++ "\r") >> flushStdHandles
  where o' = "\r\ESC[K"
            ++ pre ++ " terms of size " ++ show size
             ++ mid
            ++ ", " ++ show i ++ " examined so far. "
        o = if length (o' ++ post) <= 120 then o' ++ post
            else (take 117 (o' ++ post)) ++ "..."
        fill = replicate (max 0 (length o - 120)) ' '

ppTy :: TypeSkeleton -> T.Text
ppTy (TCons t []) = t
ppTy (TCons "[]" r) = "[" <> (mconcat $ intersperse " " $ map ppTy r) <> "]"
ppTy (TCons "(,)" r) = "(" <> (mconcat $ intersperse "," $ map ppTy r) <> ")"
ppTy (TCons t r) = t <> (mconcat $ " ":(intersperse " " $ map ppTy r))
ppTy (TVar v) = v
ppTy (TFun arg ret) = "(" <> ppTy arg <> " -> " <> ppTy ret <> ")"

-- TODO:
-- 2. knuth-bendix completion algorithm (we're almost there)
--    what to do when the size is the same? We want only one way to reduce a term
--    resolve critical pairs: if a term can be rewritten with two different rules
--    might not be stable, but we *don't need confluence*. Term indexing:
--    have a hashtable of the root node. Makes it a lot faster.
-- 4. Look at DbOpt file for examples of how we can apply rewrites directly.
-- 8. We should be able to do the "rewrites" by cleverly constructing the ECTAs
--
-- 11. make term a pattern synonym and compute the hash when we construct
--     the term.
--
-- Check for equality in the presence of non-total functions, e.g.
-- reverse (reverse xs) = xs. Allow an option to add more information for this,
-- i.e. reverse (reverse xs) = traverse xs, but not xs.
-- functions should also behave the same on the undefined list.
--
-- i.e. False && a = False
-- but  a && False = seq a False
--
--
