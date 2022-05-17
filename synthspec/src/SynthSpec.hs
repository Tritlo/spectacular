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
           even_more_terms =
             map prettyTerm $
               concatMap (getAllTerms . refold . reduceFully . flip filterType resNode )
                         (rtkUpToKAtLeast1 argNodes scope_comps anyArg True 6)
       -- putStrLn "even_more_terms"
       -- putStrLn "------------------------------------------------------------"
       -- mapM_ (print . pp) even_more_terms
       -- mapM_ (print) even_more_terms
       -- putStrLn "flipped"
       -- putStrLn "------------------------------------------------------------"
       -- mapM_ (print . flipTerm) even_more_terms
       putStrLn "Laws"
       putStrLn "------------------------------------------------------------"
       let qc_args = QC.stdArgs { QC.chatty = False,
                                  QC.maxShrinks = 0,
                                  QC.maxSuccess = 1000}
       let go :: [Term] -> IO ()
           go = go' Set.empty [1..] 
           go' _ _ [] = return ()
           go' seen nums@(n:ns) (term:terms)
             | term `Set.member` seen = go' seen nums terms
             | otherwise = do
               -- putStrLn $ T.unpack ("Testing: " <> pp term)
               let termGen = termToGen complSig Map.empty $ flipTerm term
               holds <- QC.isSuccess <$> QC.quickCheckWithResult qc_args (dynProp termGen)
               if not holds then continue nums terms
               else do putStrLn ((show n <> ". ") <> T.unpack (pp term))
                       continue ns terms
              where continue = go' (term `Set.insert` seen)
       go even_more_terms
                   
       --mapM_ (print) even_more_terms
       -- mapM_ (QC.generate @Bool. termToProp complSig) even_more_terms
