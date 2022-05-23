{-# OPTIONS -fno-max-valid-hole-fits #-}
{-# LANGUAGE OverloadedStrings, TypeApplications, RecordWildCards #-}
module SynthSpec (
    module SynthSpec.Types,
    module Data.Proxy,
    synthSpec
) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Dynamic as Dyn
import qualified Data.Bifunctor as Bi
import MonadUtils (concatMapM)
import SynthSpec.Types
import SynthSpec.Utils
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

-- TODO: make this an e-graph or similar datastructure
data Rewrite = Rewrite [(Term, Term)] (Map Term Term) deriving (Show)

rwrMap :: Rewrite -> Map Term Term
rwrMap (Rewrite _ r) = r

updateRewrites :: Either Term (Term,Term) -> Rewrite -> IO Rewrite
updateRewrites (Left (Term "(==)" [_,a,b])) rw = 
    return $ updRw a b rw
updateRewrites (Right hole_rule) (Rewrite holeRules mp) =
    return (Rewrite (hole_rule:holeRules) mp)
updateRewrites _ r = return r



data StEcta = StEcta {scope_comps :: Comps, any_arg :: Node} 

updateEcta :: Rewrite -> StEcta -> IO StEcta
updateEcta rwr@(Rewrite _ rw_mp) 
    StEcta{ scope_comps=scope_comps
          , any_arg = Node any_args} = return $ StEcta{..}
  where any_arg = Node any_args
updateEcta _ stecta = return $ stecta
        

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
    in Rewrite hole_rules (Map.insert big sml mp)

applyRewrites :: Rewrite -> Node -> IO Node
applyRewrites r n = return n

initRewrites :: IO Rewrite
initRewrites = return $ Rewrite [] Map.empty

termSize :: Term -> Int
termSize (Term s []) = 1
termSize (Term s args) = 1 + sum (map termSize args)

-- if we find a rewrite from anything to a given var, it holds
-- for all things of that type! i.e. if x == x ++ [],
-- then we can rewrite all instances of (_ :: [A] ++ []) to (_::[A]) 
-- best would probably be to apply this in the node.

badRewrite :: Rewrite -> Term -> (Term, Maybe Rewrite)
badRewrite rwr@(Rewrite hole_rules mp) orig_term
    | Just smllr <- mp Map.!? term = (runMatch smllr,Nothing)
    | (args',mb_rwrs) <- unzip $ map (badRewrite rwr) args,
      args' /= args =
        let rwr' = case catMaybes mb_rwrs of
                     [] -> rwr
                     rs -> Rewrite hole_rules (Map.unions $ map rwrMap rs)
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
         where shortCircuit :: (Term,Term) -> (Term, Term)
               shortCircuit (k,t) = case rw Map.!? t of
                                      Just r -> shortCircuit (k,r)
                                      _ -> (k,t)

               rw' = Map.fromAscList $ map shortCircuit $ Map.assocs rw
              
--badRewrite rwr term = (term, Nothing)


            

synthSpec :: [Sig] -> IO ()
synthSpec sigs = 
    do let givenSig = sigGivens sig
           complSig = sig <> givenSig
           sig = mconcat sigs
       -- putStrLn "sig"
       -- putStrLn "------------------------------------------------------------"
       -- mapM_ print $ Map.assocs sig
       -- putStrLn "given sig"
       -- putStrLn "------------------------------------------------------------"
       
       putStrLn $ "In Scope (" ++ show (Map.size complSig) ++ " functions/constants):"
       mapM_ (putStrLn . T.unpack) $ Map.keys complSig
       putStrLn "---------------------------------"
       -- print $ (Dyn.dynTypeRep . sfFunc) <$> sig
       let givens = Map.assocs $ sfTypeRep <$> givenSig
           skels = sfTypeRep <$> sig
           reqSkels = sfTypeRep <$> Map.filter sfRequired sig
           scope_comps = (Map.assocs skels) ++ givens
           addSyms st tt = map (Bi.bimap (Symbol . st) (tt . typeToFta))
           ngnodes = addSyms id id
           gnodes = addSyms id (generalize scope_comps)
           -- argnodes are the ones we require at least 1 of.
           argNodes = ngnodes $ (Map.assocs reqSkels) ++ givens
           anyArg = Node $ map (\(s,t) -> Edge s [t]) $ 
                        (gnodes givens) ++ ngnodes (Map.assocs skels)
           groups = Map.fromList $ map (\(t,_) -> (t,[t])) $ scope_comps ++ givens
           boolTy = typeRepToTypeSkeleton $ Dyn.dynTypeRep $ Dyn.toDyn True
           resNode = typeToFta boolTy
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
           isId (Term "(==)" [_, a,b]) = a == b
           isId _ = False
            
           -- TODO: add e-graphs and rewrites.
           go :: Int -> IO ()
           go n = do rwrts <- initRewrites
                     let stecta = StEcta {scope_comps = scope_comps,
                                          any_arg = anyArg}
                     go' Set.empty rwrts stecta [0.. n] [1..] []
           go' _ rwrts _ [] _ [] = do
             when (not (null (rwrMap rwrts))) $ do
               putStrLn "Final rewrites:"
               putStrLn "---------------"
               mapM_ (\(k,v) -> putStrLn ((ppNpTerm k) ++ " ==> " ++ (ppNpTerm v)))
                     (Map.assocs (rwrMap rwrts))
               putStrLn "---------------"
             return ()
           go' seen rwrts stecta (lvl_num:lvl_nums) nums []  = do
            putStrLn ("Looking for exprs with " ++ show lvl_num ++ " terms...")
            -- If we find any rewrites for the scope, we apply them here.
            when (not (null (rwrMap rwrts))) $ do
              putStrLn "Current rewrites:"
              putStrLn "-----------------"
              mapM_ (\(k,v) -> putStrLn ((ppNpTerm k) ++ " ==> " ++ (ppNpTerm v)))
                    (Map.assocs (rwrMap rwrts))
              putStrLn "-----------------"
            stecta' <- updateEcta rwrts stecta
            let StEcta {..} = stecta'
                nextNode = union $ tk scope_comps any_arg True lvl_num
                -- TODO: where to best do the rewrites?
                filtered_and_reduced = refold $ reduceFully $ filterType nextNode resNode
            -- print filtered_and_reduced 
            -- print rwrts
            rewritten <- applyRewrites rwrts filtered_and_reduced
            go' seen rwrts stecta' lvl_nums nums $ getAllTerms rewritten
           go' seen rwrts stecta lvl_nums nums@(n:ns) (full_term:terms)
             | simplified `Set.member` seen = skip
             | isId wip_rewritten = skip
             | otherwise = do
               --putStrLn $ T.unpack ("Testing: " <> pp term)
               -- putStrLn $ T.unpack ("Testing: " <> pp term)
               let termGen = termToGen complSig Map.empty wip_rewritten
               -- (fmap (flip Dyn.fromDyn False) $ QC.generate termGen) >>= print
               holds <- QC.isSuccess <$>
                          QC.quickCheckWithResult qc_args (dynProp termGen)
               if not holds then continue rwrts' nums terms
               else do putStrLn ((show n <> ". ") <> (ppNpTerm $ np_term))
                       let (Term "(==)" [_,lhs@(Term (Symbol lhss) (lht:_)),rhs]) = np_term
                       -- Find hole-rewrites
                       rwrts'' <- case complSig Map.!? lhss of
                                    Just (GivenFun {given_info = GivenVar {}}) -> do
                                        -- let holey = perforate lhs rhs
                                        -- putStrLn $ ppNpTerm $ holey
                                        -- updateRewrites (Right (lht, holey)) rwrts'
                                        updateRewrites (Left wip_rewritten) rwrts'
                                    _ -> updateRewrites (Left wip_rewritten) rwrts'
                       continue rwrts'' ns terms
              where np_term = npTerm full_term
                    continue rwrts = go' (simplified `Set.insert` seen) rwrts stecta lvl_nums
                    skip = go' seen rwrts' stecta lvl_nums nums terms
                    -- wrt variable renaming
                    simplified = simplifyVars complSig $ npTerm full_term
                    -- we're probably missing out on some rewrites due to
                    -- us operating on the flipped term
                    (wip_rewritten, rwrts') = (fromMaybe rwrts) <$>
                                                badRewrite rwrts simplified
       args <- Env.getArgs
       let size = case args of
                    arg:_ | Just n <- TR.readMaybe arg -> n
                    _ -> 6 -- Set to 6 to save time on the flight xD:w
       go size

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
        ppTerm' True (Term (Symbol t) _) = parIfReq (T.unpack t)
        ppTerm' _ (Term (Symbol t) _) = T.unpack t
        parIfReq s@(c:_) | c /= '(', c /= '[', not (isAlphaNum c) = "("<>s<>")"
        parIfReq s = s
        

-- TODO:
-- 2. knuth-bendix completion algorithm (we're almost there)
--    what to do when the size is the same? We want only one way to reduce a term
--    resolve critical pairs: if a term can be rewritten with two different rules
--    might not be stable, but we *don't need confluence*. Term indexing: 
--    have a hashtable of the root node. Makes it a lot faster.
-- 3. If we discover that e.g. ((==) xs0_[A]) (((++) []) xs0_[A]), we've found
--    something that is idempotent! Same with e.g. ((==) x0_A) (head (cons x0_A) xs0_[A]),
--    it will always hold for any value of that *type*, (so e.g. 
--    ((==) xs0_[A]) (((++) []) xs0_[A]) means that
--    ((==) (concat xss0_[[A]]) (((++) []) (concat xss0_[[A]])) etc etc..
--
--    (See [Note Hole-rewrite]. We also need to capture subsumption i.e.)
--    ((==) x) (cons x (xs)) implies it for all xs, so anything that's there
--    can be replaced.
-- 4. Look at DbOpt file for examples of how we can apply rewrites directly.
--
--
-- Check for equality in the presence of non-total functions, e.g.
-- reverse (reverse xs) = xs. Allow an option to add more information for this,
-- i.e. reverse (reverse xs) = traverse xs, but not xs.
-- functions should also behave the same on the undefined list.
--
-- i.e. False && a = False
-- but  a && False = seq a False
