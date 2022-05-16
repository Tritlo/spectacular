{-# LANGUAGE OverloadedStrings #-}
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

synthSpec :: [Sig] -> IO ()
synthSpec sigs = 
    do print sig
       print $ (Dyn.dynTypeRep . dropInfo) <$> sig
       let givens = sigGivens sig
           skels = sfTypeRep <$> sig
           reqSkels = sfTypeRep <$> Map.filter sf_required sig
           scope_comps = (Map.assocs skels) ++ givens
           addSyms st tt = map (Bi.bimap (Symbol . st) (tt . typeToFta))
           ngnodes = addSyms id id
           gnodes = addSyms id (generalize scope_comps)
           -- argnodes are the ones we require at least 1 of.
           argNodes = ngnodes $ (Map.assocs reqSkels) ++ givens
           anyArg = Node $ map (\(s,t) -> Edge s [t]) $ 
                        (gnodes givens) ++ ngnodes (Map.assocs skels)
           groups = Map.fromList $ map (\(t,_) -> (t,[t])) scope_comps
           boolTy = typeRepToTypeSkeleton $ Dyn.dynTypeRep $ Dyn.toDyn True
           resNode = typeToFta boolTy
       putStrLn "givens"
       putStrLn "------------------------------------------------------------"
       mapM_ print givens
       putStrLn "skels"
       putStrLn "------------------------------------------------------------"
       print skels
       putStrLn "req"
       putStrLn "------------------------------------------------------------"
       print reqSkels
       print boolTy
       let res = getAllTerms $ refold $ reduceFully $ filterType anyArg resNode
           even_more_terms =
             map (pp . prettyTerm) $
               concatMap (getAllTerms . refold . reduceFully . flip filterType resNode )
                         (rtkUpToKAtLeast1 argNodes scope_comps anyArg True 5)
       putStrLn "even_more_terms"
       putStrLn "------------------------------------------------------------"
       mapM_ print even_more_terms
  where sig = mconcat sigs
