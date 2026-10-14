{-# LANGUAGE OverloadedStrings #-}
-- | Ordered rewriting with the laws that the search found. A law gives
-- rules: its two sides as templates, in which the variables of the law are
-- template variables. A rule rewrites a term only when the term gets
-- smaller in the Knuth-Bendix order on ground terms, as in Twee.
module Spectacular.Rewriting (
    Rules,
    addRules,
    reducible,
    kboCompare,
    lawRules,
) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Text as T
import Data.CFTA.Symbol (Symbol (Symbol))

import Spectacular.Types

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
