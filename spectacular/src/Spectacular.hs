{-# LANGUAGE OverloadedStrings, TypeApplications, RecordWildCards,
             TupleSections, StandaloneDeriving, DeriveAnyClass,
             DeriveGeneric, BangPatterns #-}
module Spectacular (
    module Spectacular.Types,
    module Data.Proxy,
    tacularSpec,
    discoverMonomorphic,
    experimentalPhases
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
                           runs)
import Data.CFTA.Symbol (Symbol (Symbol))
import Data.List hiding (union)
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Random (mkQCGen)
import qualified Data.Text as T
import Control.Monad (when)
import qualified System.Environment as Env
import qualified Text.Read as TR
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Char (isAlphaNum)

import qualified Control.Concurrent.Async as CCA
import qualified Control.Concurrent as CC

import qualified Data.IntSet as IntSet
import qualified Data.IntMap.Strict as IM
import qualified Data.HashSet as HS
import Data.Function (on)
import System.IO (hFlush, hPutStr, stderr)
import Data.Containers.ListUtils (nubOrdOn)

data StEcta = StEcta { any_arg       :: Node Symbol,
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


-- | Whether a rule rewrites a subterm of the term to a smaller term in the
-- Knuth-Bendix order. Then the term equals a smaller term, which the search
-- sees, so the term is redundant. The subterms are the term, and the
-- function and the argument of an application; the types are not subterms.
-- This is ordered rewriting, as in Twee: a law that the order cannot
-- orient, such as commutativity, rewrites an instance only when the
-- instance gets smaller.
reducible :: [(Term, Term)] -> Term -> Bool
reducible rules t =
    any rewrites rules ||
    case t of
      Term "app" [_, f, v] -> reducible rules f || reducible rules v
      _ -> False
  where
    rewrites (l, r) = case matchTemplate l t Map.empty of
        Just s | Just r' <- instantiate s r -> kboGreater t r'
        _ -> False

-- | Replace the template variables of a template by their terms.
instantiate :: Map Symbol Term -> Term -> Maybe Term
instantiate s (Term h@(Symbol name) args)
    | "<v>" `T.isPrefixOf` name = Map.lookup h s
    | otherwise = Term h <$> traverse (instantiate s) args

-- | Match a template against a term, and extend the substitution of the
-- template variables. A template variable matches a term of its type. A
-- template variable that occurs again must match an equal term.
matchTemplate :: Term -> Term -> Map Symbol Term -> Maybe (Map Symbol Term)
matchTemplate (Term h@(Symbol name) [ty]) t s
    | "<v>" `T.isPrefixOf` name =
        case t of
          Term _ (ty' : _) | ty' == ty ->
              case Map.lookup h s of
                Nothing -> Just (Map.insert h t s)
                Just u | u == t -> Just s
                _ -> Nothing
          _ -> Nothing
matchTemplate (Term "app" [ty, f, v]) (Term "app" [ty', f', v']) s
    | ty == ty' = matchTemplate f f' s >>= matchTemplate v v'
matchTemplate (Term a [ty]) (Term b [ty']) s
    | a == b && ty == ty' = Just s
matchTemplate _ _ _ = Nothing

-- | The Knuth-Bendix order on ground terms: s > t. Each symbol has the
-- weight 1. An application is the binary symbol app, which is above the
-- other symbols, and the other symbols compare by their names. The
-- generated variables of a term are constants here. The order is
-- well-founded and closed under contexts, so rewriting with it ends.
kboGreater :: Term -> Term -> Bool
kboGreater s t = weight s > weight t || (weight s == weight t && sameWeight)
  where
    weight (Term "app" [_, f, v]) = 1 + weight f + weight v
    weight _ = 1 :: Int
    sameWeight = case (s, t) of
        (Term "app" [_, f, v], Term "app" [_, g, u]) -> lexGreater [f, v] [g, u]
        (Term "app" _, _) -> True
        (_, Term "app" _) -> False
        (Term a _, Term b _) -> a > b
    lexGreater (a:as) (b:bs)
        | a == b = lexGreater as bs
        | otherwise = kboGreater a b
    lexGreater _ _ = False


type TermSet = HS.HashSet Term

-- | The state of the search. The phases and the sizes share it.
data Search = Search {
    -- | The terms that the search does not test again.
    seen :: !(HS.HashSet Term),
    -- | The representatives of each type.
    unique_terms :: !(Map Term TermSet),
    -- | The laws, as pairs of templates in both directions.
    rewrite_rules :: ![(Term, Term)],
    -- | The number of terms that the search examined.
    so_far :: !Int,
    -- | The number of laws that the search found.
    law_count :: !Int
    }

-- | The settings of the search, which do not change.
data Settings = Settings {
    -- | Whether to show the progress on stderr.
    progress :: Bool,
    -- | The arguments of the tests.
    qcArgs :: QC.Args
    }

-- | Print the laws of a signature, with terms up to the size that the first
-- program argument gives (6 by default). The types are monomorphic, as in
-- 'discoverMonomorphic'.
tacularSpec :: [Sig] -> IO ()
tacularSpec sigs =
    do args <- Env.getArgs
       let size = case args of
                    arg:_ | Just n <- TR.readMaybe arg -> n
                    _ -> 6
       _ <- discoverMonomorphic size (const Nothing) sigs
       return ()

-- | The laws of a signature with terms up to a size. The types are
-- monomorphic: A, B, C, D, and Acc all become A (phase 1). The function
-- gives the generators and the equalities of other types.
discoverMonomorphic :: Int -> (TypeSkeleton -> Maybe GeneratedInstance) -> [Sig] -> IO [String]
discoverMonomorphic size = experimentalPhases size 1

-- | The laws of a signature, with the phases from 1 to the given phase.
-- Phases 2 to 4 are experimental. Phase 2 keeps A, B, C, D, and Acc apart.
-- Phases 3 and 4 generalize the types of the functions. A test that needs a
-- value at a type other than its own, apart from A to Acc, is untestable
-- (see 'unsafeApply').
experimentalPhases :: Int -> Int -> (TypeSkeleton -> Maybe GeneratedInstance) -> [Sig] -> IO [String]
experimentalPhases size phase extraReps sigs =
    do -- SPECTACULAR_PROGRESS=1 shows the progress of the search on stderr.
       progress <- (== Just "1") <$> Env.lookupEnv "SPECTACULAR_PROGRESS"
       let sig = mconcat sigs
           StEcta { compl_sig = compl_sig,
                    arb_insts = arb_insts,
                    sig_ty_cons = sig_ty_cons} = mkStecta extraReps sig id id
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
       let env = Settings { progress = progress,
                            qcArgs = QC.stdArgs { QC.chatty = False,
                                                  QC.maxShrinks = 0,
                                                  QC.maxSuccess = 100,
                                                  QC.replay = Just (mkQCGen 0, 0)} }
       runPhases env size (max 1 (min 4 phase)) extraReps sig

-- 1. The runtime signature and the search space.

-- | The runtime signature and the search space of one phase: the signature
-- with the generated variables and the equalities, the node of the atoms,
-- and the types to test. The first function changes the types of the
-- generated variables, and the second the types of the functions.
mkStecta :: (TypeSkeleton -> Maybe GeneratedInstance) -> Sig
         -> (TypeSkeleton -> TypeSkeleton) -> (TypeSkeleton -> TypeSkeleton) -> StEcta
mkStecta extraReps sig givenTrans skelTrans =
         StEcta { any_arg = ag,
                  compl_sig = compl_sig,
                  given_sig = givenSig,
                  sig_ty_cons = Map.keys eq_insts,
                  eq_insts = eq_insts,
                  arb_insts = arbs }
  where skels =  Map.assocs $ skelTrans . sfTypeRep <$> sig
        (givenSig, eq_insts, arbs) = sigGivens givenTrans sig extraReps
        givens = Map.assocs $ givenTrans . sfTypeRep <$> givenSig
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

-- | The phases: the message at the end of the phase, the message at the
-- start of the phase, and the changes of the types of the generated
-- variables and of the functions.
phases :: [(String, String, TypeSkeleton -> TypeSkeleton, TypeSkeleton -> TypeSkeleton)]
phases =
  [ ("Fully monomorphic phase finished..", "", monomorphiseType, monomorphiseType)
  , ("Monomorphic phases finished..", "Starting phase with more types....", id, id)
  , ("Mono-polymorphic phase done! ", "Starting mono-polymorphic phase....",
     monomorphiseType, generalizeType . monomorphiseType)
  , ("Done! ", "Starting fully-polymorphic phase....", id, generalizeType) ]

-- | Run the phases from 1 to the given phase. The search state goes from
-- one phase to the next.
runPhases :: Settings -> Int -> Int -> (TypeSkeleton -> Maybe GeneratedInstance) -> Sig -> IO [String]
runPhases env size lastPhase extraReps sig =
    go (zip [1..] phases) Search { seen = HS.empty,
                                   unique_terms = Map.empty,
                                   rewrite_rules = [],
                                   so_far = 0,
                                   law_count = 0 }
  where
    go ((pn, (finished, starting, givenTrans, skelTrans)) : rest) s
      | pn <= lastPhase = do
          when (pn > 1) $ putStrLn starting
          (laws, s') <- runPhase env size (mkStecta extraReps sig givenTrans skelTrans) s
          putStrLn $ finished ++ show (so_far s') ++ " terms examined."
          putStrLn $ show (sum $ map HS.size $ Map.elems (unique_terms s')) ++ " unique terms discovered."
          (laws ++) <$> go rest s'
    go _ _ = return []

-- | Run one phase: the sizes from 1 to the given size, and for each size
-- each type to test.
runPhase :: Settings -> Int -> StEcta -> Search -> IO ([String], Search)
runPhase env@Settings{..} size stecta@StEcta{..} = go [ (lvl, tc) | lvl <- [1 .. size], tc <- sig_ty_cons ]
  where
    go [] s = return ([], s)
    go ((lvl, tc) : rest) s = do
        refreshCount progress "Reducing  ECTA" (" for " ++ show tc) "" lvl (so_far s)
        let !reduced = searchSpace stecta lvl tc
        refreshCount progress "Refolding ecta" (" for " ++ show tc) "" lvl (so_far s)
        !folded <- return $ refold reduced
        -- Each accepting run gives one term, as with termsPrune.
        let terms = map fst $ runs "Mu" folded
        -- We want to display a message once the first term is found.
        -- in particular, it hangs after this messages for HugeLists 6
        refreshCount progress "Finding first term " (" for " ++ show tc) "" lvl (so_far s)
        case terms of
            (_:_) -> refreshCount progress "Folded, exploring " (" for " ++ show tc) "" lvl (so_far s)
            _ -> return ()
        (laws, s') <- considerAll lvl terms s
        (more, s'') <- go rest s'
        return (laws ++ more, s'')
    considerAll _ [] s = return ([], s)
    considerAll lvl (t : ts) s = do
        (law, s') <- consider env stecta lvl t s
        (more, s'') <- considerAll lvl ts s'
        return (maybe more (: more) law, s'')

-- 2. The candidate terms.

-- | The reduced automaton of the terms of a size and a type.
searchSpace :: StEcta -> Int -> TypeSkeleton -> Node Symbol
searchSpace StEcta{..} lvl tc =
    let !ecta = filterType (union $ tk any_arg lvl) $ typeToFta tc
    in fixWithin 100 (withoutRedundantEdges . reducePartially) ecta

-- 3. The test of a candidate, and the law that it gives.

-- | Consider one candidate term. Prune it, or keep it as the first
-- representative of its type, or test it against the representatives of
-- its type. Give the law that the test finds, if any.
consider :: Settings -> StEcta -> Int -> Term -> Search -> IO (Maybe String, Search)
consider Settings{..} StEcta{..} lvl full_term s@Search{..}
     -- A known law rewrites the term to a smaller term, so the
     -- term is redundant.
     | reducible rewrite_rules np_term = return (Nothing, s)
     | not (current_ty `Map.member` unique_terms) =
        return (Nothing, s { unique_terms = Map.insert current_ty (HS.singleton np_term) unique_terms,
                             seen = HS.insert np_term seen })
     -- if we've seen it before, we can immediately skip.
     | np_term `HS.member` seen = return (Nothing, s { so_far = so_far + 1 })
     -- We don't want terms that are all variables.
     | termSize np_term > 1,
        allFromSig given_sig np_term =
        return (Nothing, s { so_far = so_far + 1, seen = HS.insert np_term seen })
     | otherwise = do
        let other_terms = HS.toList $ unique_terms Map.! current_ty
            terms_to_test = map termToTest other_terms
        refreshCount progress ("exploring " ++ show current_ty) ""
                     ("(" ++ show (length terms_to_test) ++ " to test...)") lvl so_far
        (holds, untestable) <- testAllPar qcArgs eq_inst compl_sig terms_to_test
        let sf' = so_far + 1
        case holds of
            Nothing -> do
                refreshCount progress ("exploring " ++ show current_ty) "" "" lvl sf'
                -- A test threw. The candidate or a representative caused
                -- it, so test the candidate alone. A candidate that we
                -- cannot test does not become a representative.
                testable <- if untestable
                            then (== TestPassed) <$>
                                   testProperty qcArgs
                                     (dynProp $ selfEqualityGen eq_inst compl_sig np_term)
                            else return True
                -- A later phase enumerates the representative again, so
                -- it goes into seen too.
                return (Nothing,
                        if testable
                        then s { so_far = sf',
                                 unique_terms = Map.adjust (HS.insert np_term) current_ty unique_terms,
                                 seen = HS.insert np_term seen }
                        else s { so_far = sf' })
            -- These tests are expensive, so we only do them for laws that hold.
            Just t -> do
                let n = law_count + 1
                    (gsig, glaws) =
                      -- We have to be a bit careful about the order
                      -- of the generalized laws, because we test
                      -- them in order.
                      generalizeLaw compl_sig $ npTerm' t
                -- If we don't find a more general law, we use the one
                -- we found.
                refreshCount progress "generalizing" "" ("(" ++ show (length glaws) ++ " possibilities...)") lvl sf'
                most_general <- fromMaybe t <$> testAllInOrderAsync qcArgs eq_inst gsig glaws
                let law_str = (show n <> ". ") <> ppNpTerm most_general
                when progress $ hPutStr stderr "\r\ESC[K"
                putStrLn law_str
                refreshCount progress ("exploring " ++ show current_ty) "" "" lvl sf'
                return (Just law_str,
                        s { seen = HS.insert np_term seen,
                            so_far = sf',
                            law_count = n,
                            rewrite_rules = lawRules gsig most_general ++ rewrite_rules })
  where -- wrt variable renaming
        np_term = npTerm' full_term
        Term "filter" [current_ty,_] = full_term

        term_eq_insts = Map.fromList $ map (Bi.first typeSkeletonToTerm)
                                     $ Map.assocs eq_insts
        (eq_txt, eq_inst) = term_eq_insts Map.! current_ty
        termToTest o = Term "(==)" [ Term (Symbol eq_txt) [], o, np_term]

-- | The rules of a law: its two sides as templates, with the variables of
-- the law, in both directions.
lawRules :: Sig -> Term -> [(Term, Term)]
lawRules gsig (Term "(==)" [_, l, r]) = [(l', r'), (r', l')]
  where l' = toTemplate gsig l
        r' = toTemplate gsig r
lawRules _ _ = []

-- | Test an equation: the property that its two sides are equal.
runTest :: QC.Args -> Dynamic -> Sig -> Term -> IO TestResult
runTest qcArgs eq_inst sig t = testProperty qcArgs $ dynProp $ termToGen eq_inst sig Map.empty t

-- | Test the equations in turn. Return the first equation that holds, and
-- whether a test threw.
testAll :: QC.Args -> Dynamic -> Sig -> [Term] -> IO (Maybe Term, Bool)
testAll _ _ _ [] = return (Nothing, False)
testAll qcArgs eq_inst sig (t:ts) =
    do r <- runTest qcArgs eq_inst sig t
       case r of
         TestPassed -> return (Just t, False)
         TestFailed -> testAll qcArgs eq_inst sig ts
         Untestable -> (\(m, _) -> (m, True)) <$> testAll qcArgs eq_inst sig ts

-- | 'testAll' on one chunk of the equations for each capability.
testAllPar :: QC.Args -> Dynamic -> Sig -> [Term] -> IO (Maybe Term, Bool)
testAllPar _ _ _ [] = return (Nothing, False)
testAllPar qcArgs eq_inst sig terms =
  do n <- CC.getNumCapabilities
     if n == 1
     then testAll qcArgs eq_inst sig terms
     else if n >= length terms
          then testAllPar' [] $ map (:[]) terms
          else testAllPar' [] $ chunks (length terms `div` n) terms
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
        testAllPar' [] [c] = testAll qcArgs eq_inst sig c
        -- if we don't have any more chunks to start, we
        -- just finish it
        testAllPar' as [] = firstSuccessful False as
        -- otherwise, we have to start the work (and we check if we've finished anything so far)
        testAllPar' as (c:cs) =
            CCA.withAsync (testAll qcArgs eq_inst sig c) $
                \a -> testAllPar' (a:as) cs

-- | Test the equations at the same time, and give the first one in the
-- list that holds.
testAllInOrderAsync :: QC.Args -> Dynamic -> Sig -> [Term] -> IO (Maybe Term)
testAllInOrderAsync _ _ _ [] = return Nothing
testAllInOrderAsync qcArgs eq_inst sig (a:as) =
     CCA.withAsync (runTest qcArgs eq_inst sig a) $ \aref ->
         CCA.withAsync (testAllInOrderAsync qcArgs eq_inst sig as) $ \asref -> do
             ares <- CCA.wait aref
             -- if the first one is succesful, we don't care
             -- about the rest!
             if ares == TestPassed
             then do CCA.cancel asref
                     return (Just a)
             else CCA.wait asref

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

-- | Show the progress of the search on one line of stderr, if the first
-- argument is True.
refreshCount :: Bool -> String -> String -> String -> Int -> Int -> IO ()
refreshCount False _ _ _ _ _ = return ()
refreshCount True pre mid post size i = hPutStr stderr (o ++ fill ++ "\r") >> hFlush stderr
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
