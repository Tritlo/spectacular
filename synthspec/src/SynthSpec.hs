{-# OPTIONS -fno-max-valid-hole-fits #-}
{-# LANGUAGE OverloadedStrings, TypeApplications #-}
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
import CCTP.Utils hiding (prettyTerm)
import Data.Proxy (Proxy(..))


import Application.TermSearch.Dataset
import Application.TermSearch.Type
import Application.TermSearch.TermSearch hiding (allConstructors, generalize)
import Data.ECTA
import Data.ECTA.Term
import Data.List
import qualified Test.QuickCheck as QC
import Control.Monad (zipWithM_, filterM)
import qualified Data.Text as T
import qualified Data.Set as Set
import qualified System.Environment as Env
import qualified Text.Read as TR
import Debug.Trace
import Data.Maybe (fromMaybe, catMaybes)

-- TODO: make this an e-graph or similar datastructure
data Rewrite = Rewrite (Map Term Term) deriving (Show)

rwrMap :: Rewrite -> Map Term Term
rwrMap (Rewrite r) = r

updateRewrites :: Term -> Rewrite -> IO Rewrite
updateRewrites (Term "(==)" [_,a,b]) rw = 
    return $ updRw a b rw
updateRewrites _ r = return r

updRw :: Term -> Term -> Rewrite -> Rewrite
updRw a b (Rewrite mp) =
    let (sml,big) = if termSize a < termSize b
                    then (a,b) else if termSize a == termSize b
                                    then if length (show a) < length (show b)
                                         then (a,b)
                                         else (b,a)
                                    else (b,a)
    in Rewrite (Map.insert big sml mp)

applyRewrites :: Rewrite -> Node -> IO Node
applyRewrites r n = return n

initRewrites :: IO Rewrite
initRewrites = return $ Rewrite Map.empty

termSize :: Term -> Int
termSize (Term s []) = 1
termSize (Term s args) = 1 + sum (map termSize args)

-- if we find a rewrite from anything to a given var, it holds
-- for all things of that type! i.e. if x == x ++ [],
-- then we can rewrite all instances of (_ :: [A] ++ []) to (_::[A]) 
-- best would probably be to apply this in the node.

badRewrite :: Rewrite -> Term -> (Term, Maybe Rewrite)
badRewrite rwr@(Rewrite mp) term@(Term s args)
    | Just smllr <- mp Map.!? term = (smllr,Nothing)
    | (args',mb_rwrs) <- unzip $ map (badRewrite rwr) args,
      args' /= args =
        let rwr' = case catMaybes mb_rwrs of
                     [] -> rwr
                     rs -> Rewrite (Map.unions $ map rwrMap rs)
            t' = Term s args'
            (rwt, rwrAfterRewrite) = badRewrite rwr' t'
            finalRwt = updRw term rwt $ fromMaybe rwr' rwrAfterRewrite
        in (rwt, Just finalRwt)
    | otherwise = (term, Nothing)
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
       mapM_ print $ Map.assocs givenSig
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
       let res = getAllTerms $ refold $ reduceFully $ filterType anyArg resNode
           -- TODO: make it generate the terms in a more "sane" order.
           -- even_more_terms =
           --   map prettyTerm $
           --     concatMap (getAllTerms . refold . reduceFully . flip filterType resNode )
           --               (rtkUpToKAtLeast1 argNodes scope_comps anyArg True 8)
       putStrLn "Laws"
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
                     go' Set.empty rwrts [0.. n] [1..] []
           go' _ _ [] _ [] = return ()
           go' seen rwrts (lvl_num:lvl_nums) nums []  = do
            putStrLn ("Looking for exprs with " ++ show lvl_num ++ " terms...")
            let nextNode = rtkOfSize [] scope_comps anyArg True lvl_num
                -- TODO: where to best do the rewrites?
                filtered_and_reduced = refold $ reduceFully $ filterType nextNode resNode
            -- print filtered_and_reduced 
            -- print rwrts
            rewritten <- applyRewrites rwrts filtered_and_reduced
            let terms = map prettyTerm $ getAllTerms rewritten
            go' seen rwrts lvl_nums nums terms 
           go' seen rwrts lvl_nums nums@(n:ns) (term:terms)
             | simplified `Set.member` seen = skip
             | isId wip_rewritten = skip
             | otherwise = do
               -- putStrLn $ T.unpack ("Testing: " <> pp term)
               let termGen = termToGen complSig Map.empty wip_rewritten
               holds <- QC.isSuccess <$>
                          QC.quickCheckWithResult qc_args (dynProp termGen)
               if not holds then continue rwrts' nums terms
               else do putStrLn ((show n <> ". ") <> T.unpack (pp $ term))
                       -- TODO: e-graph optimization (egg), queue-up updates
                       -- to the rewrites.
                       rwrts'' <- updateRewrites wip_rewritten rwrts'
                       continue rwrts'' ns terms
              where continue rwrts = go' (simplified `Set.insert` seen) rwrts lvl_nums
                    skip = go' seen rwrts' lvl_nums nums terms
                    -- wrt variable renaming
                    simplified = reduceVars complSig term
                    (wip_rewritten, rwrts') = (fromMaybe rwrts) <$>
                                                badRewrite rwrts (flipTerm simplified)
       args <- Env.getArgs
       let size = case args of
                    arg:_ | Just n <- TR.readMaybe arg -> n
                    _ -> 7
       go size
                   
-- TODO:
-- 1. check if QC timeout can be bumped easily, otherwise email Nick
-- 2. update rewrites when new ones are updated, knuth-bendix completion algorithm:
--    what to do when the size is the same? We want only one way to reduce a term
--    resolve critical pairs: if a term can be rewritten with two different rules
--    might not be stable, but we *don't need confluence*. Term indexing: 
--    have a hashtable of the root node. Makes it a lot faster.
--
--
