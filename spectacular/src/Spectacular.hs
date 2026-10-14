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
import qualified Spectacular.DecisionTree as DT
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
import Data.Maybe (fromMaybe)
import Data.Char (isAlphaNum)

import qualified Data.HashSet as HS
import Data.Function (on)
import System.IO (hFlush, hPutStr, stderr)
import Data.Containers.ListUtils (nubOrd)

data StEcta = StEcta { any_arg       :: Node Symbol,
                      eq_insts      :: Map TypeSkeleton (T.Text, Dynamic),
                      arb_insts     :: Map TypeSkeleton (T.Text, Func),
                      sig_ty_cons   :: [TypeSkeleton],
                      compl_sig     :: Sig,
                      given_sig     :: Sig,
                      -- | The complete signature with more variables of each
                      -- type, for the instances of the schemas.
                      inst_sig      :: Sig,
                      -- | The variables of each type, from the variable with
                      -- the index 0 of the type.
                      schema_vars   :: Map Symbol [Symbol],
                      -- | The test cases that all terms of the phase share.
                      test_cases    :: [VarVals]
                      } deriving (Show)

-- | The number of variables of each type that fill the holes of a schema.
-- QuickSpec uses 4 by default (@Use (UpTo 4)@).
variablesPerType :: Int
variablesPerType = 4

-- | The largest schema that the search instantiates when the schema is a new
-- representative. Without it, the search does not find laws such as
-- commutativity, whose two sides have the same schema. QuickSpec uses 5
-- (@cfg_max_commutative_size@). The size of a term is the number of its
-- leaves, as in 'searchSpace'.
maxCommutativeSize :: Int
maxCommutativeSize = 5

-- | Put the variables into the holes of a schema, from left to right.
fillHoles :: (Symbol -> Bool) -> [Symbol] -> Term -> Term
fillHoles isVar vars0 t0 = fst (go vars0 t0)
  where
    go vars (Term "app" [ty, f, v]) =
        let (f', vars') = go vars f
            (v', vars'') = go vars' v
        in (Term "app" [ty, f', v'], vars'')
    go (x : vars) (Term s tys) | isVar s = (Term x tys, vars)
    go vars t = (t, vars)

-- | The holes of a schema, from left to right. A hole is a variable.
holes :: (Symbol -> Bool) -> Term -> [Symbol]
holes isVar (Term "app" [_, f, v]) = holes isVar f ++ holes isVar v
holes isVar (Term s _) = [s | isVar s]

-- | The most general instance of a schema: each hole gets a different
-- variable of its type.
mostGeneral :: (Symbol -> Bool) -> Map Symbol [Symbol] -> Term -> Term
mostGeneral isVar vars t = fillHoles isVar (snd (mapAccumL next Map.empty (holes isVar t))) t
  where next counts x = let n = Map.findWithDefault 0 x counts
                        in (Map.insert x (n + 1) counts, (vars Map.! x) !! n)

-- | The instances of a schema: each hole gets one of the first
-- 'variablesPerType' variables of its type. The instances with more
-- different variables come first, as in QuickSpec.
schemaInstances :: (Symbol -> Bool) -> Map Symbol [Symbol] -> Term -> [Term]
schemaInstances isVar vars t =
    [ fillHoles isVar (map snd ivs) t
    | ivs <- sortOn generality (mapM (zip [0 :: Int ..] . take variablesPerType . (vars Map.!)) (holes isVar t)) ]
  where generality ivs = (negate (length (nubOrd (map snd ivs))), map fst ivs)


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


-- | The rules of the laws, by the head of their left sides (see
-- 'spineHead'). A rule whose head is a template variable has the key
-- Nothing, because it can match a term with any head.
type Rules = Map (Maybe (Symbol, Int)) [(Term, Term)]

-- | Add rules to the index of the rules.
addRules :: [(Term, Term)] -> Rules -> Rules
addRules new rules = foldr add rules new
  where add rule@(l, _) = Map.insertWith (++) (key l) [rule]
        key l = case spineHead l of
            (Symbol h, _) | "<v>" `T.isPrefixOf` h -> Nothing
            k -> Just k

-- | The head of a term: the symbol of the function of its application
-- spine, and the number of the arguments of the spine. A template whose
-- head is a symbol matches only a term with the same head.
spineHead :: Term -> (Symbol, Int)
spineHead (Term "app" [_, f, _]) = fmap (+ 1) (spineHead f)
spineHead (Term s _) = (s, 0)

-- | Whether a rule rewrites a subterm of the term to a smaller term in the
-- Knuth-Bendix order. Then the term equals a smaller term, which the search
-- sees, so the term is redundant. The subterms are the term, and the
-- function and the argument of an application; the types are not subterms.
-- This is ordered rewriting, as in Twee: a law that the order cannot
-- orient, such as commutativity, rewrites an instance only when the
-- instance gets smaller. Only the rules with the head of the subterm, and
-- the rules with a template variable as head, can match the subterm.
reducible :: (Symbol -> Bool) -> Rules -> Term -> Bool
reducible isVar rules t =
    any rewrites (Map.findWithDefault [] (Just (spineHead t)) rules ++ Map.findWithDefault [] Nothing rules) ||
    case t of
      Term "app" [_, f, v] -> reducible isVar rules f || reducible isVar rules v
      _ -> False
  where
    rewrites (l, r) = case matchTemplate l t Map.empty of
        Just s | Just r' <- instantiate s r -> kboCompare isVar t r' == GT
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

-- | The Knuth-Bendix order on ground terms. Each symbol has the weight 1.
-- An application is the binary symbol app, which is above the other
-- symbols. Of the other symbols, the generated variables are below the
-- constants, so that the more general terms come first, and symbols of one
-- kind compare by their names, then by their types. The generated
-- variables of a term are constants here. The order is total,
-- well-founded, and closed under contexts, so rewriting with it ends.
kboCompare :: (Symbol -> Bool) -> Term -> Term -> Ordering
kboCompare isVar s t = compare (weight s) (weight t) <> sameWeight s t
  where
    weight (Term "app" [_, f, v]) = 1 + weight f + weight v
    weight _ = 1 :: Int
    sameWeight (Term "app" [_, f, v]) (Term "app" [_, g, u]) =
        kboCompare isVar f g <> kboCompare isVar v u
    sameWeight (Term "app" _) _ = GT
    sameWeight _ (Term "app" _) = LT
    sameWeight (Term a tys) (Term b tys') =
        compare (not (isVar a)) (not (isVar b)) <> compare a b <> compare tys tys'

-- | Whether a symbol is a generated variable of the signature.
isGivenVar :: Sig -> Symbol -> Bool
isGivenVar sig (Symbol x) = case sig Map.!? x of
    Just (GivenFun {given_info = GivenVar {}}) -> True
    _ -> False



-- | The state of the search. The phases and the sizes share it.
data Search = Search {
    -- | The terms that the search does not test again.
    seen :: !(HS.HashSet Term),
    -- | The decision tree of the representative schemas of each type.
    trees :: !(Map Term DT.DecisionTree),
    -- | The decision tree of the instances of each representative schema.
    instance_trees :: !(Map Term DT.DecisionTree),
    -- | The representative schemas whose instances are in their trees.
    instantiated :: !(HS.HashSet Term),
    -- | The rules of the laws, by the heads of their left sides.
    rewrite_rules :: !Rules,
    -- | The number of terms that the search examined.
    so_far :: !Int,
    -- | The number of laws that the search found.
    law_count :: !Int
    }

-- | The settings of the search, which do not change.
data Settings = Settings {
    -- | Whether to show the progress on stderr.
    progress :: Bool,
    -- | The number of test cases that the terms of a phase share.
    numTests :: Int,
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
       -- SPECTACULAR_TESTS sets the number of test cases (100 by default).
       numTests <- fromMaybe 100 . (>>= TR.readMaybe) <$> Env.lookupEnv "SPECTACULAR_TESTS"
       let sig = mconcat sigs
           StEcta { compl_sig = compl_sig,
                    arb_insts = arb_insts,
                    sig_ty_cons = sig_ty_cons} = mkStecta size numTests extraReps sig id id
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
                            numTests = numTests,
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
mkStecta :: Int -> Int -> (TypeSkeleton -> Maybe GeneratedInstance) -> Sig
         -> (TypeSkeleton -> TypeSkeleton) -> (TypeSkeleton -> TypeSkeleton) -> StEcta
mkStecta size numTests extraReps sig givenTrans skelTrans =
         StEcta { any_arg = ag,
                  compl_sig = compl_sig,
                  given_sig = givenSig,
                  inst_sig = inst_sig,
                  schema_vars = Map.fromList [ (Symbol x, map (Symbol . fst) vs) | (x, vs) <- moreVars ],
                  sig_ty_cons = Map.keys eq_insts,
                  eq_insts = eq_insts,
                  test_cases = testCases numTests inst_sig,
                  arb_insts = arbs }
  where skels =  Map.assocs $ skelTrans . sfTypeRep <$> sig
        -- The most general instance of a schema of the given size has at
        -- most size variables of a type.
        moreVars = [ (x, [ (gvToName gv, g) | g@(GivenFun gv _) <- take (max variablesPerType size) (moreGenerators f) ])
                   | (x, f@(GivenFun {given_info = GivenVar {}})) <- Map.assocs compl_sig ]
        inst_sig = Map.fromList (concatMap snd moreVars) <> compl_sig
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
                                   trees = Map.empty,
                                   instance_trees = Map.empty,
                                   instantiated = HS.empty,
                                   rewrite_rules = Map.empty,
                                   so_far = 0,
                                   law_count = 0 }
  where
    go ((pn, (finished, starting, givenTrans, skelTrans)) : rest) s
      | pn <= lastPhase = do
          when (pn > 1) $ putStrLn starting
          (laws, s') <- runPhase env size (mkStecta size (numTests env) extraReps sig givenTrans skelTrans) s
          putStrLn $ finished ++ show (so_far s') ++ " terms examined."
          putStrLn $ show (sum $ map DT.size $ Map.elems (trees s')) ++ " unique terms discovered."
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
        -- Each accepting run gives one term. The terms come in the order
        -- of kboCompare, so that the laws do not depend on the order in
        -- which microcfta interned the nodes and the edges.
        let terms = map snd $ sortBy (kboCompare (isGivenVar compl_sig) `on` fst)
                        [ (npTerm' t, t) | (t, _) <- runs "Mu" folded ]
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
        (laws, s') <- consider env stecta lvl t s
        (more, s'') <- considerAll lvl ts s'
        return (laws ++ more, s'')

-- 2. The candidate terms.

-- | The reduced automaton of the terms of a size and a type.
searchSpace :: StEcta -> Int -> TypeSkeleton -> Node Symbol
searchSpace StEcta{..} lvl tc =
    let !ecta = filterType (union $ tk any_arg lvl) $ typeToFta tc
    in fixWithin 100 (withoutRedundantEdges . reducePartially) ecta

-- 3. The test of a candidate, and the laws that it gives.

-- | The result of the exploration of a term in the tree of the instances of
-- a schema, as in QuickSpec.
data Explored
  = -- | The term is a new representative.
    Singleton
  | -- | The term equals a representative: the law.
    Discovered String
  | -- | A known law rewrites the term, the term is a representative already,
    -- or a comparison threw.
    Knew

-- | Consider one candidate term. The term is a schema: it has one variable
-- of each type, which stands for the holes. The rule is that of QuickSpec 2
-- (section 3.2.3 of the paper, and Explore/Schemas.hs). Prune the schema if a
-- known law rewrites its most general instance. Otherwise, test the schema
-- against the representative schemas of its type. If the schema equals a
-- representative, test its most general instance against the instances of
-- the representative. If that instance is new, test all instances of the
-- two schemas. A new representative schema is also instantiated if it is
-- small. Give the laws that the tests find.
consider :: Settings -> StEcta -> Int -> Term -> Search -> IO ([String], Search)
consider Settings{..} StEcta{..} lvl full_term s0
     -- A known law rewrites the most general instance to a smaller term. The
     -- law rewrites each instance in the same way, so the schema is
     -- redundant.
     | reducible isVar (rewrite_rules s0) most_general = return ([], s0)
     -- if we've seen it before, we can immediately skip.
     | np_term `HS.member` seen s0 = return ([], s0 { so_far = so_far s0 + 1 })
     -- We don't want terms that are all variables.
     | termSize np_term > 1,
        allFromSig given_sig np_term =
        return ([], s0 { so_far = so_far s0 + 1, seen = HS.insert np_term (seen s0) })
     | otherwise = do
        let tree = Map.findWithDefault DT.empty current_ty (trees s0)
        refreshCount progress ("exploring " ++ show current_ty) ""
                     ("(" ++ show (DT.size tree) ++ " representatives...)") lvl (so_far s0)
        -- The schema goes into the decision tree of its type. It is
        -- evaluated on the test cases of its path only.
        inserted <- DT.insert (valuesEqual eq_inst) np_term (values np_term) tree
        let s = s0 { so_far = so_far s0 + 1 }
            -- A later phase enumerates the schema again, so it goes into
            -- seen.
            s' = s { seen = HS.insert np_term (seen s0) }
        (laws, s'') <- case inserted of
            -- A comparison threw, so the schema does not become a
            -- representative.
            DT.Untested -> return ([], s)
            DT.Distinct tree'
                | lvl <= maxCommutativeSize -> instantiateRep np_term with_tree
                | otherwise ->
                    return ([], with_tree { instance_trees =
                                              Map.insert np_term (DT.leaf most_general (values most_general))
                                                         (instance_trees s0) })
              where with_tree = s' { trees = Map.insert current_ty tree' (trees s0) }
            DT.EqualTo rep -> exploreIn rep s'
        refreshCount progress ("exploring " ++ show current_ty) "" "" lvl (so_far s)
        return (laws, s'')
  where -- wrt variable renaming
        np_term = npTerm' full_term
        Term "filter" [current_ty,_] = full_term
        isVar = isGivenVar inst_sig
        most_general = mostGeneral isVar schema_vars np_term

        term_eq_insts = Map.fromList $ map (Bi.first typeSkeletonToTerm)
                                     $ Map.assocs eq_insts
        (eq_txt, eq_inst) = term_eq_insts Map.! current_ty
        -- The values of a term on the test cases, evaluated when needed.
        values u = map (\tc -> evalTerm inst_sig tc u) test_cases

        -- The schema equals the representative schema rep. Test the most
        -- general instance of the schema against the instances of rep.
        exploreIn rep s = do
            (explored, s') <- exploreInstance rep most_general s
            case explored of
                Discovered law -> return ([law], s')
                Knew -> return ([], s')
                Singleton -> do
                    (rep_laws, s'') <- if rep `HS.member` instantiated s'
                                       then return ([], s')
                                       else instantiateRep rep s'
                    (laws, s''') <- instantiate rep np_term s''
                    return (rep_laws ++ laws, s''')

        instantiateRep rep s = instantiate rep rep s { instantiated = HS.insert rep (instantiated s) }

        -- Test the instances of a schema against the instances of the
        -- representative schema rep, the most general instances first.
        instantiate rep schema = go (schemaInstances isVar schema_vars schema)
          where go [] s = return ([], s)
                go (i : is) s = do
                    (explored, s') <- exploreInstance rep i s
                    (laws, s'') <- go is s'
                    return (case explored of
                                Discovered law -> law : laws
                                _ -> laws,
                            s'')

        -- Test an instance against the instances of the representative
        -- schema rep. Print the law that the test finds, and add its rules.
        exploreInstance rep i s
            | reducible isVar (rewrite_rules s) i = return (Knew, s)
            | otherwise = do
                let table = Map.findWithDefault DT.empty rep (instance_trees s)
                inserted <- DT.insert (valuesEqual eq_inst) i (values i) table
                case inserted of
                    DT.Untested -> return (Knew, s)
                    DT.Distinct table' ->
                        return (Singleton, s { instance_trees = Map.insert rep table' (instance_trees s) })
                    DT.EqualTo w
                        | w == i -> return (Knew, s)
                        | otherwise -> do
                            let n = law_count s + 1
                                law = Term "(==)" [Term (Symbol eq_txt) [], w, i]
                                law_str = show n <> ". " <> ppNpTerm law
                            when progress $ hPutStr stderr "\r\ESC[K"
                            putStrLn law_str
                            return (Discovered law_str,
                                    s { law_count = n,
                                        rewrite_rules = addRules (lawRules inst_sig law) (rewrite_rules s) })

-- | The rules of a law: its two sides as templates, with the variables of
-- the law, in both directions. A direction is not a rule if its right side
-- is heavier and has each variable at least as often as its left side.
-- Then each instance of the right side is heavier in the Knuth-Bendix order,
-- so the direction cannot make a term smaller.
lawRules :: Sig -> Term -> [(Term, Term)]
lawRules gsig (Term "(==)" [_, l, r]) = filter canReduce [(l', r'), (r', l')]
  where l' = toTemplate gsig l
        r' = toTemplate gsig r
        canReduce (a, b) = weight b <= weight a || any (\x -> count x b < count x a) (vars a)
        weight (Term "app" [_, f, v]) = 1 + weight f + weight v
        weight _ = 1 :: Int
        vars (Term "app" [_, f, v]) = vars f ++ vars v
        vars (Term h@(Symbol x) _) = [h | "<v>" `T.isPrefixOf` x]
        count x t = length (filter (== x) (vars t))
lawRules _ _ = []

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
