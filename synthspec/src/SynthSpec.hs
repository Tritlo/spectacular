{-# OPTIONS -fno-max-valid-hole-fits #-}
{-# LANGUAGE OverloadedStrings, TypeApplications, RecordWildCards,
             TupleSections, StandaloneDeriving, DeriveAnyClass,
             DeriveGeneric #-}
module SynthSpec (
    module SynthSpec.Types,
    module Data.Proxy,
    synthSpec
) where

-- slower, but uses less memory.
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
-- import qualified Data.Map as Map
-- import Data.Map (Map)
import qualified Data.Dynamic as Dyn
import Data.Dynamic (Dynamic)
import qualified Data.Bifunctor as Bi
import MonadUtils (concatMapM)
import SynthSpec.Types
import SynthSpec.Utils
import qualified SynthSpec.Utils as SS
import Data.Proxy (Proxy(..))


import Application.TermSearch.Dataset
import Application.TermSearch.Type
import Application.TermSearch.TermSearch hiding (allConstructors, generalize)
import Data.ECTA
import Data.ECTA.Term
import Data.List hiding (union)
import qualified Test.QuickCheck as QC
import Control.Monad (zipWithM_, filterM, when)
import qualified Data.Text as T
import qualified Data.Set as Set
import qualified System.Environment as Env
import qualified Text.Read as TR
import Debug.Trace
import Data.Maybe (fromMaybe, catMaybes, mapMaybe)
import Data.Char (isAlphaNum)
import Data.Either (rights)

import qualified Control.Concurrent.Async as CCA
import qualified Control.Concurrent as CC

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.Hashable (hash, Hashable)
import qualified Data.List as L
import Data.Function (on)

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



data StEcta = StEcta {scope_comps :: Comps, any_arg :: Node} deriving (Show)

updateEcta :: Rewrite -> StEcta -> IO StEcta
updateEcta rwr@(Rewrite _ rw_mp)
    StEcta{ scope_comps=scope_comps
          , any_arg = Node any_args} = return $ StEcta{..}
  where any_arg = Node any_args
updateEcta _ stecta = return $ stecta


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
    in (rhsig, -- We don't want laws that are the same up to renaming
               -- so we remove the ones that are the same after
               -- simplification of variables
               nubHash $ map (simplifyVars rhsig) $
            [Term "(==)" [ty, lhs',rhs'] | lhs' <- lhss, rhs' <- rhss])
  where var_count = countVars sig t  
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
        termHoleEq (Term "<_>" _) _ = True
        termHoleEq  _ (Term "<_>" _) = True
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

badRewrite :: Rewrite -> Term -> (Term, Maybe Rewrite)
badRewrite rwr@(Rewrite hole_rules mp) orig_term
    | Just smllr <- mp IM.!? (hash term) = (runMatch smllr,Nothing)
    | (args',mb_rwrs) <- unzip $ map (badRewrite rwr) args,
      args' /= args =
        let rwr' = case catMaybes mb_rwrs of
                     [] -> rwr
                     rs -> Rewrite hole_rules (IM.unions $ map rwrMap rs)
            t' = Term s args'
            (rwt, rwrAfterRewrite) = badRewrite rwr' t'
            rwr'' = fromMaybe rwr' rwrAfterRewrite
            finalRwt = case s of
                        "(==)" -> rwr''
                        _ -> updRw term rwt rwr''
        in (runMatch rwt, Just $ simplify finalRwt)
    | otherwise = (term, Nothing)
  where runMatch = id -- flip (foldr matchHole) hole_rules
        term@(Term s args) = runMatch orig_term
        simplify :: Rewrite -> Rewrite
        simplify (Rewrite h rw) = if rw == rw'
                                   then (Rewrite h rw)
                                   else simplify (Rewrite h rw')
         where shortCircuit :: (Int,Term) -> (Int, Term)
               shortCircuit (k,t) = case rw IM.!? (hash t) of
                                      Just r -> shortCircuit (k,r)
                                      _ -> (k,t)

               rw' = IM.fromAscList $ map shortCircuit $ IM.assocs rw

--badRewrite rwr term = (term, Nothing)




data GoState = GoState {seen :: IntSet, --hashed integers
                        rwrts :: Rewrite,
                        unique_terms :: Map TypeSkeleton [Term],
                        stecta :: StEcta,
                        type_cons :: [TypeSkeleton],
                        current_ty :: TypeSkeleton,
                        so_far :: Int,
                        lvl_nums :: [Int],
                        law_nums :: [Int],
                        current_terms :: [Term]
                        } deriving (Show)



synthSpec :: [Sig] -> IO ()
synthSpec sigs =
    do let (givenSig, eq_insts, arbs) = sigGivens sig
           int_arbs = IM.fromList $ map (\(tsk,(gn,_)) -> (hash (typeSkeletonToTerm tsk), gn)) 
                                  $ Map.assocs arbs
           simpl_int_arbs = IM.fromList $ map (\(tsk,(_,(GivenFun {given_info=gv@GivenVar{}})))
                                            -> (hash (typeSkeletonToTerm tsk), gvToNameNoType gv)) 
                                        $ Map.assocs arbs
           sig_ty_cons = Map.keys eq_insts
           complSig = sig <> givenSig
           sig = mconcat sigs
       -- putStrLn "sig"
       -- putStrLn "------------------------------------------------------------"
       -- mapM_ print $ Map.assocs sig
       -- putStrLn "given sig"
       -- putStrLn "------------------------------------------------------------"

       putStrLn $ "In Scope (" ++ show (Map.size complSig) ++ " functions/constants):"
       putStrLn "---------------------------------"
       mapM_ (putStrLn . T.unpack) $ Map.keys complSig
       putStrLn ""
       putStrLn "Type constructors in the signature:"
       putStrLn "---------------------------------"
       mapM_ print sig_ty_cons
       putStrLn ""
       putStrLn "Variable generators"
       putStrLn "---------------------------------"
       mapM_ print (Map.assocs arbs)
       putStrLn ""

       -- print $ (Dyn.dynTypeRep . sfFunc) <$> sig
       let givens = Map.assocs $ sfTypeRep <$> givenSig
           skels = (generalizeType . sfTypeRep) <$> sig
           scope_comps = (Map.assocs skels) ++ givens
           addSyms st tt = map (Bi.bimap (Symbol . st) (tt . typeToFta))
           -- ngnodes = addSyms id id
           gnodes = addSyms id (generalize scope_comps)
           anyArg = Node $ map (\(s,t) -> Edge s [t]) $
                        (gnodes givens) ++ gnodes (Map.assocs skels)
       -- putStrLn "givens"
       -- putStrLn "------------------------------------------------------------"
       -- mapM_ print givens
       -- putStrLn "skels"
       -- putStrLn "------------------------------------------------------------"
       -- print skels
       -- putStrLn "req"
       -- putStrLn "------------------------------------------------------------"
       -- print reqSkels
       -- print boolTy
       -- let res = getAllTerms $ refold $ reduceFully $ filterType anyArg resNode
           -- TODO: make it generate the terms in a more "sane" order.
           -- even_more_terms =
           --   map prettyTerm $
           --     concatMap (getAllTerms . refold . reduceFully . flip filterType resNode )
           --               (rtkUpToKAtLeast1 argNodes scope_comps anyArg True 8)
       putStrLn "Laws according to Haskell's (==):"
       putStrLn "---------------------------------"
       let qc_args = QC.stdArgs { QC.chatty = False,
                                  QC.maxShrinks = 0,
                                  QC.maxSuccess = 1000}
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



           -- TODO: add e-graphs and rewrites.
           go :: Int -> IO ()
           go n = do rwrts <- initRewrites
                     go' GoState {seen = IntSet.empty,
                                  rwrts = rwrts,
                                  unique_terms = Map.empty,
                                  stecta = StEcta{ scope_comps = scope_comps,
                                                   any_arg = anyArg},
                                  type_cons = sig_ty_cons,
                                  current_ty = error "no type yet!",
                                  so_far = 0,
                                  lvl_nums = [1..n],
                                  law_nums = [1..],
                                  current_terms = [] }
           go' :: GoState -> IO ()
           go' (GoState{ lvl_nums = [],
                        current_terms = [],
                        type_cons = _, ..}) = do
             putStrLn $ "Done! " ++ show so_far ++ " terms examined."
             putStrLn $ show (sum $ map (length) $ Map.elems unique_terms) ++ " unique terms discovered."
            --  when (not (null (rwrMap rwrts))) $ do
            --    putStrLn "Final rewrites:"
            --    putStrLn "---------------"
            --    mapM_ (\(k,v) -> putStrLn ((ppNpTerm k) ++ " ==> " ++ (ppNpTerm v)))
            --          (Map.assocs (rwrMap rwrts))
            --    putStrLn "---------------"
             reportStats
             return ()
           go' (GoState{ type_cons = [],
                         lvl_nums = (lvl_num:lvl_nums),
                         current_terms = [],
                         ..}) = do
            putStrLn (show so_far ++ " terms examined so far")
            putStrLn $ show (sum $ map (length) $ Map.elems unique_terms) ++ " unique terms discovered."
            putStrLn ("Looking for exprs with " ++ show (lvl_num+1) ++ " terms...")
            -- If we find any rewrites for the scope, we apply them here.
            -- when (not (null (rwrMap rwrts))) $ do
            --   putStrLn "Current rewrites:"
            --   putStrLn "-----------------"
            --   mapM_ (\(k,v) -> putStrLn ((ppNpTerm k) ++ " ==> " ++ (ppNpTerm v)))
            --         (Map.assocs (rwrMap rwrts))
            --   putStrLn "-----------------"
            stecta' <- updateEcta rwrts stecta
            go' GoState { stecta=stecta',
                          type_cons = sig_ty_cons,
                          current_terms =[], ..}
           go' GoState {stecta=stecta@StEcta{..},
                        type_cons = (tc:tcs),
                        lvl_nums=lvl_nums@(lvl_num:_),
                        current_terms = [],..} = do
            --putStrLn ("Checking " ++ (T.unpack $ ppTy tc) ++ " with size " ++ show lvl_num ++ "...")

            let toText e = T.pack $ ppNpTerm $ npTerm e
                unique_args = concatMap (\(t,es) -> map ((,typeToFta t) . Symbol . toText ) es)
                                $ Map.assocs unique_terms
                nextNode = union $ mtk scope_comps any_arg True lvl_num
                -- TODO: where to best do the rewrites?
            -- filtered_and_reduced <- fmap refold <$> collectStats $
            --     reduceFullyAndLog $ filterType nextNode (typeToFta tc)
            filtered_and_reduced <- fmap refold <$> collectStats $
                (return $ reduceFully $ filterType nextNode (typeToFta tc))

            rewritten <- applyRewrites rwrts filtered_and_reduced
            go' GoState{current_terms = getAllTerms rewritten,
                        type_cons = tcs,
                        current_ty = tc,..}
           go' GoState{law_nums = law_nums@(n:ns),
                       current_terms = (full_term:terms), ..}
              -- if there is a possible re-write that's *smaller*, then we can
              -- skip right away, since we'll already have tested that one.

             | hasSmallerRewrite rwrts np_term = skip
             | hasRewrite rwrts $ canonicalize complSig np_term = skip
             | (hash $ canonicalize complSig wip_rewritten) `IntSet.member` seen = skip
             | not (current_ty `Map.member` unique_terms) =
                go' (GoState{current_terms = terms,
                            unique_terms = Map.insert current_ty [wip_rewritten] unique_terms,
                            ..})
             | Just gt <- hasSubsumption rwrts' int_arbs wip_rewritten = skip
             | (npc,r3) <- badRewrite rwrts' (canonicalize complSig np_term),
               Just gt <- hasSubsCanon sig rwrts' simpl_int_arbs npc = skip
             | hasAnySub rwrts' np_term = skip
             | otherwise = do
                let other_terms = unique_terms Map.! current_ty
                    terms_to_test = map termToTest other_terms
                -- putStrLn $ ("Testing: " <> ppNpTerm wip_rewritten
                --            <> " :: " <> (T.unpack $ ppTy current_ty))
                -- putStrLn $ show np_term
                -- putStrLn $ show (canonicalize complSig np_term)

                let -- No need to run multiple tests if there are no variables!
                    runTest eq_inst sig t =
                        -- We test 100x per variable, but for constants we
                        -- need only test once!
                        let nvs = max (length (termVars sig t) * 100) 1
                            qc_args' = qc_args {QC.maxSuccess = nvs}
                        in collectStats $ QC.isSuccess <$>
                                           (QC.quickCheckWithResult qc_args' $
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

                holds <- testAllPar eq_inst complSig terms_to_test


                case holds of
                    Nothing -> go' GoState {so_far = (so_far + length terms_to_test),
                                            current_terms = terms,
                                            unique_terms =
                                              Map.adjust (wip_rewritten:) current_ty unique_terms,
                                            rwrts = rwrts',..}
                    Just t -> do
                        let (gsig, glaws) =
                              -- We have to be a bit careful about the order
                              -- of the generalized laws, because we test
                              -- them in order.
                              fmap ( reverse
                                   . sortOn (sum . Map.elems . countVars gsig)
                                   . filter (\l -> hash l /= hash t)) $
                                    generalizeLaw complSig $ npTerm' t
                        
                        -- If we don't find a more general law, we use the one
                        -- we found.
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
                        putStrLn ((show n <> ". ") <> (ppNpTerm $ most_general))
                        continue rwrts'' ns terms
              where continue rwrts law_nums terms =
                      go' GoState {seen = 
                                  (hash $ canonicalize complSig wip_rewritten) `IntSet.insert` seen,
                                  so_far=(so_far+1),
                                  current_terms = terms, ..}
                    skip = go' GoState{so_far = so_far+1,
                                       current_terms = terms, ..}
                    -- wrt variable renaming
                    np_term = npTerm' full_term
                    (eq_txt, eq_inst) = eq_insts Map.! current_ty
                    termToTest o = Term "(==)" [ Term (Symbol eq_txt) []
                                               , o, wip_rewritten]
                    -- we're probably missing out on some rewrites due to
                    -- us operating on the flipped term

                    (wip_rewritten, rwrts') = (fromMaybe rwrts) <$>
                                                badRewrite rwrts np_term
       args <- Env.getArgs
       let size = case args of
                    arg:_ | Just n <- TR.readMaybe arg -> n
                    _ -> 6 -- Set to 6 to save time on the flight xD:w
       go size

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
-- 10. We would like to be able to have things like `reverse :: [a] -> [a]`
--     in the signature, and have the `a` be instantiated for all the
--     possible types.
--
--
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
