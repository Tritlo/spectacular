{-# LANGUAGE OverloadedStrings, TypeApplications #-}
module SynthSpec (
    module SynthSpec.Types,
    module Data.Proxy,
    synthSpec
) where

import qualified Data.Map as Map
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
           transform = map prettyTerm . getAllTerms . refold . reduceFully . flip filterType resNode
           -- even_more_terms = map transform (rtkUpToK [] scope_comps anyArg True 7)
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
           go n = go' Set.empty [0.. n] [1..] []
           go' _ [] _ [] = return ()
           go' seen (lvl_num:lvl_nums) nums []  = do
            putStrLn ("Looking for exprs with " ++ show lvl_num ++ " terms...")
            let lvl_terms = transform $ rtkOfSize [] scope_comps anyArg True lvl_num
            go' seen lvl_nums nums lvl_terms
           go' seen lvl_nums nums@(n:ns) (term:terms)
             | isId (flipTerm term) = skip
             | term `Set.member` seen = skip
             | otherwise = do
               -- putStrLn $ T.unpack ("Testing: " <> pp term)
               let flipped = flipTerm term
                   termGen = termToGen complSig Map.empty flipped
               holds <- QC.isSuccess <$>
                          QC.quickCheckWithResult qc_args (dynProp termGen)
               if not holds then continue nums terms
               else do putStrLn ((show n <> ". ") <> T.unpack (pp term))
                       continue ns terms
              where continue = go' (term `Set.insert` seen) lvl_nums
                    skip = go' seen lvl_nums nums terms
       go 7
                   
