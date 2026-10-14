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
import Data.Dynamic (Dynamic)
import qualified Data.Bifunctor as Bi
import Spectacular.Types
import Spectacular.Utils
import Spectacular.Testing
import Data.Proxy (Proxy(..))


import Data.CFTA.Equality (Node (Node), Edge (Edge), union, refold,
                           reducePartially, withoutRedundantEdges, fixWithin,
                           termsPrune, TermFragment, EnumerateM,
                           expandPartialTermFrag, PartialSymbol (..),
                           UVar, uvarToInt)
import Data.CFTA.Symbol (Symbol (Symbol))
import qualified Data.CFTA.Term as CT
import Data.List hiding (union)
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Random (mkQCGen)
import qualified Data.Text as T
import qualified System.Environment as Env
import qualified Text.Read as TR
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Char (isAlphaNum)

import qualified Control.Concurrent.Async as CCA
import qualified Control.Concurrent as CC

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.IntMap.Strict as IM
import Data.Hashable (hash)
import qualified Data.HashSet as HS
import Data.Function (on)
import System.IO (hFlush, stdout)
import Data.Containers.ListUtils (nubOrdOn)

data StEcta = StEcta { scope_comps  :: Comps,
                      any_arg       :: Node Symbol,
                      eq_insts      :: Map TypeSkeleton (T.Text, Dynamic),
                      arb_insts     :: Map TypeSkeleton (T.Text, Func),
                      sig_ty_cons   :: [TypeSkeleton],
                      compl_sig     :: Sig,
                      given_sig     :: Sig
                      } deriving (Show)


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



typeSkeletonToTerm :: TypeSkeleton -> Term
typeSkeletonToTerm (TCons s args)
    = Term (Symbol s) $ map typeSkeletonToTerm args
typeSkeletonToTerm (TFun f v) =
    Term "->" [Term "(->)" [], typeSkeletonToTerm f, typeSkeletonToTerm v]

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


oracle :: ([Term],[Term])
            -> (Int, TypeSkeleton)
            -> UVar
            -> Either (TermFragment Symbol) (Node Symbol)
            -> EnumerateM Symbol (Bool,(Int,TypeSkeleton))
oracle (templs,rws) st@(lvl,TCons tsk _) uv (Left tf)
    -- Only the root UVar is checked. Its fragment holds the symbols of the
    -- whole term, and the UVars below it hold the types.
    | uvarToInt uv == 0 = do partial <- expandPartialTermFrag tf
                             return (fragRepresents partial (rws ++ templs), st)
    | otherwise = return (False, st)
oracle _ st _ (Right _) = return (False, st)

-- | Whether a subterm of a partial term matches one of the templates.
-- A template symbol "<v>" matches any subterm. The types are not compared.
fragRepresents :: CT.Term (PartialSymbol Symbol) -> [Term] -> Bool
fragRepresents (CT.Node (ConcreteSymbol "filter") [_,t]) rwrs = fragRepresents t rwrs
fragRepresents tf@(CT.Node (ConcreteSymbol "app") [_,_,f,v]) rwrs =
    any (ruleMatches tf) rwrs || fragRepresents f rwrs || fragRepresents v rwrs
fragRepresents tf@(CT.Node (ConcreteSymbol _) [_]) rwrs = any (ruleMatches tf) rwrs
fragRepresents tf@(CT.Node (UVarHole _) []) rwrs = any (ruleMatches tf) rwrs
fragRepresents tf@(CT.Node TruncatedRecursion []) rwrs = any (ruleMatches tf) rwrs
fragRepresents tf _ = error $ "unrecognized frag! " ++ show tf

-- | Whether a partial term matches a template at its root.
ruleMatches :: CT.Term (PartialSymbol Symbol) -> Term -> Bool
ruleMatches _ (Term (Symbol "<v>") _) = True
ruleMatches (CT.Node (ConcreteSymbol "app") [_,_,tf_f,tf_v])
            (Term "app" [_,_,rw_f,rw_v]) =
    ruleMatches tf_f rw_f && ruleMatches tf_v rw_v
ruleMatches (CT.Node (ConcreteSymbol ts) [_]) (Term rws [_]) = ts == rws
ruleMatches _ _ = False

hasTemplate :: Term -> Bool
hasTemplate (Term (Symbol s) args) = T.isPrefixOf "<v" s || any hasTemplate args


type TermSet = HS.HashSet Term

data GoState = GoState {seen :: !IntSet, --hashed integers
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
                    _ -> 6
       let phase = case args of
                    _:arg:_ | Just n <- TR.readMaybe arg -> n
                    _ -> 3
       _ <- tacularSpec' size phase (const Nothing) sigs
       return ()

tacularSpec' :: Int -> Int -> (TypeSkeleton -> (Maybe GeneratedInstance)) -> [Sig] -> IO [String]
tacularSpec' size phase extraReps sigs =
    do let sig = mconcat sigs
           mkStecta sig givenTrans skelTrans =
                    StEcta { scope_comps = sc, any_arg = ag,
                             compl_sig = compl_sig,
                             given_sig = givenSig,
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

       putStrLn "Laws according to Haskell's (==):"
       putStrLn "---------------------------------"
       -- Each test run starts from the same seed, so that the laws are the
       -- same in each run.
       let qc_args = QC.stdArgs { QC.chatty = False,
                                  QC.maxShrinks = 0,
                                  QC.maxSuccess = 100,
                                  QC.replay = Just (mkQCGen 0, 0)}

           -- TODO: add e-graphs and rewrites.
           go :: Int -> Int -> IO [String]
           go n phase  =
                  do let stecta@StEcta{..} = mkStecta sig monomorphiseType monomorphiseType
                     go' GoState {seen = IntSet.empty,
                                  rewrite_terms = [],
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
               go' :: GoState -> IO [String]
               go' (GoState{ lvl_nums = [],
                             phase_number = pn@(1),
                            current_terms = [] , ..}) = do
                    putStrLn $ "Fully monomorphic phase finished.." ++ show so_far ++ " terms examined."
                    putStrLn $ show (sum $ map HS.size $ Map.elems unique_terms) ++ " unique terms discovered."
                    if (pn < phase) 
                    then do
                        putStrLn $ "Starting phase with more types...."
                        let stecta@StEcta{..} = mkStecta sig id id
                        go' GoState{ cur_lvl = 0,
                                    phase_number = 2,
                                    lvl_nums= [1..cur_lvl],
                                    ty_cons_to_check = sig_ty_cons,
                                    current_terms=[],..}
                    else return []
               go' (GoState{ lvl_nums = [],
                             phase_number = pn@(2),
                            current_terms = [] , ..}) = do
                    putStrLn $ "Monomorphic phases finished.." ++ show so_far ++ " terms examined."
                    putStrLn $ show (sum $ map HS.size $ Map.elems unique_terms) ++ " unique terms discovered."
                    if (pn < phase) 
                    then do
                        putStrLn $ "Starting mono-polymorphic phase...."
                        let stecta@StEcta{..} = mkStecta sig monomorphiseType (generalizeType . monomorphiseType)
                        go' GoState{ cur_lvl = 0,
                                    phase_number = 3,
                                    lvl_nums= [1..cur_lvl],
                                    ty_cons_to_check = sig_ty_cons,
                                    current_terms=[],..}
                    else return []
               go' (GoState{ lvl_nums = [],
                             phase_number = pn@(3),
                            current_terms = [] , ..}) = do
                    putStrLn $ "Mono-polymorphic phase done! " ++ show so_far ++ " terms examined."
                    putStrLn $ show (sum $ map HS.size $ Map.elems unique_terms) ++ " unique terms discovered."
                    if (pn < phase) 
                    then do
                        let stecta@StEcta{..} = mkStecta sig id generalizeType
                        putStrLn $ "Starting fully-polymorphic phase...."
                        go' GoState{ cur_lvl = 0,
                                    phase_number = 4,
                                    lvl_nums= [1..cur_lvl],
                                    ty_cons_to_check = sig_ty_cons,
                                    current_terms=[],..}
                    else return []
               go' (GoState{ lvl_nums = [],
                            current_terms = [] , ..}) = do
                 putStrLn $ "Done! " ++ show so_far ++ " terms examined."
                 putStrLn $ show (sum $ map HS.size $ Map.elems unique_terms) ++ " unique terms discovered."
                 return []
               go' GoState {stecta=stecta@StEcta{..},
                            ty_cons_to_check = [],
                            lvl_nums = (lvl_num:lvl_nums),
                            current_terms = current_terms@[],..} = do
                    go' GoState {ty_cons_to_check = sig_ty_cons, cur_lvl = lvl_num, ..}
               go' GoState {stecta=stecta@StEcta{..},
                            ty_cons_to_check = (tc:ty_cons_to_check),
                            current_terms = [],..} = do
                let nextNode = union $ tk scope_comps any_arg False cur_lvl

                refreshCount "Reducing  ECTA" (" for " ++ show tc) "" cur_lvl so_far
                let max_rounds = 100
                    !ecta = filterType nextNode $ typeToFta tc
                    !reduced = fixWithin max_rounds (withoutRedundantEdges . reducePartially) ecta
                refreshCount "Refolding ecta" (" for " ++ show tc) "" cur_lvl so_far

                !folded <- return $ refold reduced

                let o = oracle $ partition hasTemplate rewrite_terms
                let terms = termsPrune (cur_lvl, tc) o folded
                -- We want to display a message once the first term is found.
                -- in particular, it hangs after this messages for HugeLists 6
                refreshCount "Finding first term " (" for " ++ show tc) "" cur_lvl so_far
                case terms of
                    (t:_) -> refreshCount "Folded, exploring " (" for " ++ show tc) "" cur_lvl so_far
                    _ -> return ()

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
                 -- if we've seen it before, we can immediately skip.
                 | (hash np_term) `IntSet.member` seen = skip seen
                 -- We don't want terms that are all variables.
                 | termSize np_term > 1,
                    allFromSig given_sig np_term = skip (seen <> IntSet.singleton (hash np_term))
                 | otherwise = do
                    let other_terms = HS.toList $ unique_terms Map.! current_ty
                        terms_to_test = map termToTest other_terms
                         -- No need to run multiple tests if there are no variables!
                        runTest eq_inst sig t =
                            -- We test 100x per variable, but for constants we
                            -- need only test once!
                            let nvs = 100
                                qc_args' = qc_args {QC.maxSuccess = nvs}
                            in testProperty qc_args' $
                                   dynProp $ termToGen eq_inst sig Map.empty t
                        -- Test the candidate against the representatives in
                        -- turn. Return the first representative that it
                        -- equals, and whether a test threw.
                        testAll :: Dynamic -> Sig -> [Term] -> IO (Maybe Term, Bool)
                        testAll eq_inst sig [] = return (Nothing, False)
                        testAll eq_inst sig (t:ts) =
                            do r <- runTest eq_inst sig t
                               case r of
                                 TestPassed -> return (Just t, False)
                                 TestFailed -> testAll eq_inst sig ts
                                 Untestable -> (\(m, _) -> (m, True)) <$> testAll eq_inst sig ts
                        testAllPar :: Dynamic -> Sig -> [Term] -> IO (Maybe Term, Bool)
                        testAllPar eq_inst sig [] = return (Nothing, False)
                        testAllPar eq_inst sig terms =
                          do n <- CC.getNumCapabilities
                             if n == 1
                             then testAll eq_inst sig terms
                             else if n >= length terms
                                  then testAllPar' [] $ map (:[]) terms
                                  else testAllPar' [] $ (chunks ((length terms) `div` n) terms)
                          where firstSuccessful :: Bool -> [CCA.Async (Maybe Term, Bool)]
                                                -> IO (Maybe Term, Bool)
                                firstSuccessful u [] = return (Nothing, u)
                                firstSuccessful u as = do
                                     do (a,r@(m, u')) <- CCA.waitAny as
                                        let as' = filter (/= a) as
                                        case m of
                                            Just _ -> do mapM_ CCA.cancel as'
                                                         return r
                                            _ -> firstSuccessful (u || u') as'
                                testAllPar' :: [CCA.Async (Maybe Term, Bool)]
                                            -> [[Term]] -> IO (Maybe Term, Bool)
                                -- if there's only one, no need for async
                                testAllPar' [] [] = return (Nothing, False)
                                testAllPar' [] [c] = testAll eq_inst sig c
                                -- if we don't have any more chunks to start, we
                                -- just finish it
                                testAllPar' as [] = firstSuccessful False as
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
                                     if ares == TestPassed
                                     then do CCA.cancel asref
                                             return (Just a)
                                     else CCA.wait asref

                    refreshCount ("exploring " ++ (show current_ty)) ""
                                 ("(" ++ (show $ length terms_to_test) ++ " to test...)") cur_lvl so_far
                    (holds, untestable) <- testAllPar eq_inst compl_sig terms_to_test


                    let sf' = so_far + 1
                    case holds of
                        Nothing -> do refreshCount ("exploring " ++ (show current_ty)) ""
                                                   "" cur_lvl sf'
                                      -- A test threw. The candidate or a
                                      -- representative caused it, so test
                                      -- the candidate alone. A candidate
                                      -- that we cannot test does not become
                                      -- a representative.
                                      testable <- if untestable
                                                  then (== TestPassed) <$>
                                                         testProperty qc_args
                                                           (dynProp $ selfEqualityGen eq_inst compl_sig wip_rewritten)
                                                  else return True
                                      go' GoState { so_far = sf',
                                                    current_terms = terms,
                                                    unique_terms =
                                                      if testable
                                                      then Map.adjust (HS.insert wip_rewritten) current_ty unique_terms
                                                      else unique_terms,
                                                    ..}

                        -- These tests are expensive, so we only do them for laws that hold.
                        Just t -> do
                            let (gsig, glaws) =
                                  -- We have to be a bit careful about the order
                                  -- of the generalized laws, because we test
                                  -- them in order.
                                        generalizeLaw compl_sig $ npTerm' t

                            -- If we don't find a more general law, we use the one
                            -- we found.
                            refreshCount "generalizing" "" ("(" ++ show (length glaws) ++ " possibilities...)") cur_lvl sf'
                            most_general <- fromMaybe t <$> testAllInOrderAsync eq_inst gsig glaws
                            let law_str = (show n <> ". ") <> (ppNpTerm $ most_general)
                                lsl = max 0 (80 - length law_str)
                            putStrLn ("\r" ++ law_str ++ replicate lsl ' ')
                            refreshCount  ("exploring " ++ (show current_ty))  ""
                                           "" cur_lvl sf'
                            let Term "filter" [_, rewrite_term] = full_term
                                new_rw = toTemplate gsig rewrite_term
                                new_rws = (new_rw:rewrite_terms)
                                -- we've learned a new rewrite, so we restart the
                                -- machine with a new oracle function.
                            (law_str:) <$>
                               go' GoState {
                                    seen = seen <> IntSet.singleton (hash np_term),
                                    so_far=sf',
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

                        wip_rewritten = np_term
       go size phase

npTerm' :: Term -> Term
npTerm' (Term "filter" [_,term]) = npTerm' term
npTerm' (Term "app" [t,_,a,v]) =  (Term "app" $ [t, npTerm' a, npTerm' v])
npTerm' t = t


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

allFromSig sig (Term "app" [_,f,v]) = allFromSig sig f && allFromSig sig v
allFromSig sig (Term (Symbol t) _) = t `Map.member` sig

refreshCount :: String -> String -> String -> Int -> Int -> IO ()
refreshCount pre mid post size i = putStr (o ++ fill ++ "\r") >> hFlush stdout
  where o' = "\r\ESC[K"
            ++ pre ++ " terms of size " ++ show size
             ++ mid
            ++ ", " ++ show i ++ " examined so far. "
        o = if length (o' ++ post) <= 120 then o' ++ post
            else (take 117 (o' ++ post)) ++ "..."
        fill = replicate (max 0 (length o - 120)) ' '

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
