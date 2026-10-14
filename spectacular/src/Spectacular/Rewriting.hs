{-# LANGUAGE OverloadedStrings #-}
-- | Ordered rewriting with the laws that the search found, and the prover
-- that completes the rules. A law gives rules: its two sides as templates,
-- in which the variables of the law are template variables. A rule
-- rewrites a term only when the term gets smaller in the Knuth-Bendix
-- order, as in Twee.
module Spectacular.Rewriting (
    Rules,
    emptyRules,
    reducible,
    joinable,
    kboCompare,
    addLaw,
) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Text as T
import Data.Containers.ListUtils (nubOrd)
import Data.List (permutations, sortOn)
import Data.Maybe (isJust)
import Control.Applicative ((<|>))
import Data.CFTA.Symbol (Symbol (Symbol))

import Spectacular.Types

-- | Rules by the head of their left sides (see 'spineHead'). A rule whose
-- head is a template variable has the key Nothing, because it can match a
-- term with any head.
type Index = Map (Maybe (Symbol, Int)) [(Term, Term)]

-- | The rules of the laws. An oriented rule makes each instance smaller, so
-- it rewrites without a test of the order. An unoriented rule rewrites an
-- instance only if the order says that the instance gets smaller. A rule
-- rewrites only if each template variable of its right side is in its left
-- side. The other rules cannot rewrite, because a match of the left side
-- does not give the right side, but they show that an equation follows
-- (see 'subsumed').
data Rules = Rules {
    -- | The rules that make each instance smaller.
    oriented :: !Index,
    -- | The rules that make some instances smaller.
    unoriented :: !Index,
    -- | The rules that cannot rewrite.
    nonRewriting :: !Index
    }

-- | No rules.
emptyRules :: Rules
emptyRules = Rules Map.empty Map.empty Map.empty

-- | Add the rules of an equation, and give the new rules too. If one side
-- is greater than the other for each instance ('kboGreater' without a
-- ranking), the equation gives the oriented rule from the greater side,
-- because the other direction cannot make a term smaller. Otherwise it
-- gives the unoriented rules in both directions, for ordered rewriting.
addEquation :: (Term, Term) -> Rules -> ([(Term, Term)], Rules)
addEquation (l, r) rules
    | kboGreater Map.empty l r = ([(l, r)], rules { oriented = insert (l, r) (oriented rules) })
    | kboGreater Map.empty r l = ([(r, l)], rules { oriented = insert (r, l) (oriented rules) })
    | otherwise = ([(l, r), (r, l)], foldr addUnoriented rules [(l, r), (r, l)])
  where
    addUnoriented rule@(a, b) rs
        | all (`elem` templateVars a) (templateVars b) = rs { unoriented = insert rule (unoriented rs) }
        | otherwise = rs { nonRewriting = insert rule (nonRewriting rs) }
    insert rule@(a, _) = Map.insertWith (++) (key a) [rule]
    key a = case spineHead a of
        (h, _) | isTemplateVar h -> Nothing
        k -> Just k

-- | All the rules.
allRules :: Rules -> [(Term, Term)]
allRules rules = concatMap (concat . Map.elems) [oriented rules, unoriented rules, nonRewriting rules]

-- | The head of a term: the symbol of the function of its application
-- spine, and the number of the arguments of the spine. A template whose
-- head is a symbol matches only a term with the same head.
spineHead :: Term -> (Symbol, Int)
spineHead (Term "app" [_, f, _]) = fmap (+ 1) (spineHead f)
spineHead (Term s _) = (s, 0)

-- | The rules that can match a term: the rules with the head of the term,
-- and the rules with a template variable as head.
candidates :: Index -> Term -> [(Term, Term)]
candidates rules t = Map.findWithDefault [] (Just (spineHead t)) rules ++ Map.findWithDefault [] Nothing rules

-- | Whether a symbol is a template variable.
isTemplateVar :: Symbol -> Bool
isTemplateVar (Symbol name) = "<v>" `T.isPrefixOf` name

-- | Rewrite one subterm of a term, the outermost and leftmost first. A rule
-- rewrites a subterm only if the order says that the subterm is greater
-- than its rewritten form. The subterms are the term, and the function and
-- the argument of an application; the types are not subterms.
rewriteStep :: (Term -> Term -> Bool) -> Rules -> Term -> Maybe Term
rewriteStep greater rules t =
    case [ r' | (l, r) <- candidates (oriented rules) t, Just s <- [matchTemplate l t Map.empty],
                Just r' <- [instantiate s r] ]
         ++ [ r' | (l, r) <- candidates (unoriented rules) t, Just s <- [matchTemplate l t Map.empty],
                   Just r' <- [instantiate s r], greater t r' ] of
      r' : _ -> Just r'
      [] -> case t of
          Term "app" [ty, f, v] ->
              (\f' -> Term "app" [ty, f', v]) <$> rewriteStep greater rules f
              <|> (\v' -> Term "app" [ty, f, v']) <$> rewriteStep greater rules v
          _ -> Nothing

-- | The normal form of a term: rewrite it until no rule rewrites it. Each
-- step makes the term smaller in a well-founded order, so this ends.
normalForm :: (Term -> Term -> Bool) -> Rules -> Term -> Term
normalForm greater rules t = maybe t (normalForm greater rules) (rewriteStep greater rules t)

-- | Whether a rule rewrites a subterm of the term to a smaller term in the
-- Knuth-Bendix order. Then the term equals a smaller term, which the search
-- sees, so the term is redundant. This is ordered rewriting, as in Twee: a
-- law that the order cannot orient, such as commutativity, rewrites an
-- instance only when the instance gets smaller.
reducible :: (Symbol -> Bool) -> Rules -> Term -> Bool
reducible isVar rules = isJust . rewriteStep (groundGreater isVar) rules

-- | Whether the known laws prove a law: the two sides of the law have the
-- same normal form, or their normal forms are an instance of a rule (see
-- 'subsumed'). The variables of the law are constants here. Each step is an
-- instance of a known law, so then the law follows from the known laws for
-- all values of its variables.
joinable :: (Symbol -> Bool) -> Rules -> Term -> Term -> Bool
joinable isVar rules a b = a' == b' || subsumed rules (a', b') || subsumed rules (b', a')
  where a' = normalForm (groundGreater isVar) rules a
        b' = normalForm (groundGreater isVar) rules b

-- | The ground order of 'kboCompare' as a test.
groundGreater :: (Symbol -> Bool) -> Term -> Term -> Bool
groundGreater isVar a b = kboCompare isVar a b == GT

-- | Replace the template variables of a template by their terms.
instantiate :: Map Symbol Term -> Term -> Maybe Term
instantiate s (Term h args)
    | isTemplateVar h = Map.lookup h s
    | otherwise = Term h <$> traverse (instantiate s) args

-- | Match a template against a term, and extend the substitution of the
-- template variables. A template variable matches a term of its type. A
-- template variable that occurs again must match an equal term.
matchTemplate :: Term -> Term -> Map Symbol Term -> Maybe (Map Symbol Term)
matchTemplate (Term h [ty]) t s
    | isTemplateVar h =
        case t of
          Term _ (ty' : _) | ty' == ty ->
              case Map.lookup h s of
                Nothing -> Just (Map.insert h t s)
                Just u | u == t -> Just s
                _ -> Nothing
          _ -> Nothing
-- The type of an application follows from the types of its leaves, so an
-- application needs no check of its type.
matchTemplate (Term "app" [_, f, v]) (Term "app" [_, f', v']) s =
    matchTemplate f f' s >>= matchTemplate v v'
matchTemplate (Term a [ty]) (Term b [ty']) s
    | a == b && ty == ty' = Just s
matchTemplate _ _ _ = Nothing

-- | The weight of a term in the Knuth-Bendix order: each symbol has the
-- weight 1, and an application is the binary symbol app.
weight :: Term -> Int
weight (Term "app" [_, f, v]) = 1 + weight f + weight v
weight _ = 1

-- | The number of leaves of a term, which is the size of a term in the
-- search.
leaves :: Term -> Int
leaves (Term "app" [_, f, v]) = leaves f + leaves v
leaves _ = 1

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
    sameWeight (Term "app" [_, f, v]) (Term "app" [_, g, u]) =
        kboCompare isVar f g <> kboCompare isVar v u
    sameWeight (Term "app" _) _ = GT
    sameWeight _ (Term "app" _) = LT
    sameWeight (Term a tys) (Term b tys') =
        compare (not (isVar a)) (not (isVar b)) <> compare a b <> compare tys tys'

-- | The Knuth-Bendix order on templates: whether s > t for each instance in
-- which the template variables compare as the ranking says. A template
-- variable without a rank compares with no other term, and a template
-- variable is never greater than a constant or below it. Other symbols
-- compare as in 'kboCompare'.
--
-- The instance of s must not be lighter than the instance of t. Let c x be
-- the number of occurrences of x in s minus the number in t. A variable
-- without a rank can have any weight, so c x must not be negative. For
-- the ranked variables, a greater variable has an instance that is not
-- lighter, so the sum of c over the variables of a rank and the greater
-- ranks must not be negative, for each rank.
kboGreater :: Map Symbol Int -> Term -> Term -> Bool
kboGreater rank s t =
    ws >= wt
    && all ((>= 0) . c) unranked && all (>= 0) (scanr1 (+) (map c ranked))
    && (ws > wt || sameWeight s t)
  where
    ws = weight s
    wt = weight t
    -- The occurrences of the variables of s, minus those of t.
    diff = occurrences (-1) t (occurrences 1 s Map.empty)
    occurrences n (Term "app" [_, f, v]) m = occurrences n v (occurrences n f m)
    occurrences n (Term x _) m
        | isTemplateVar x = Map.insertWith (+) x n m
        | otherwise = m
    ranked = sortOn (rank Map.!) (filter (`Map.member` rank) (Map.keys diff))
    unranked = filter (`Map.notMember` rank) (Map.keys diff)
    c x = diff Map.! x
    sameWeight (Term "app" [_, f, v]) (Term "app" [_, g, u])
        | f == g = kboGreater rank v u
        | otherwise = kboGreater rank f g
    sameWeight (Term a tys@[_]) (Term b tys'@[_])
        | isTemplateVar a || isTemplateVar b =
            case (Map.lookup a rank, Map.lookup b rank) of
              (Just i, Just j) -> i > j
              _ -> False
        | otherwise = (compare a b <> compare tys tys') == GT
    sameWeight _ _ = False

-- | The template variables of a template, from left to right, with each
-- occurrence.
templateVars :: Term -> [Symbol]
templateVars (Term "app" [_, f, v]) = templateVars f ++ templateVars v
templateVars (Term x _) = [x | isTemplateVar x]

-- | The leaves of a template that are template variables, from left to
-- right, once each.
templateVarLeaves :: Term -> [Term]
templateVarLeaves t = nubOrd (go t)
  where go (Term "app" [_, f, v]) = go f ++ go v
        go u@(Term x _) = [u | isTemplateVar x]

-- | Give new names to the template variables of a template.
rename :: (Symbol -> Symbol) -> Term -> Term
rename f (Term "app" [ty, g, v]) = Term "app" [ty, rename f g, rename f v]
rename f (Term x tys) | isTemplateVar x = Term (f x) tys
rename _ t = t

-- | Replace the template variables of a template by their terms, and the
-- template variables in these terms too.
substitute :: Map Symbol Term -> Term -> Term
substitute s (Term "app" [ty, f, v]) = Term "app" [ty, substitute s f, substitute s v]
substitute s t@(Term x _)
    | isTemplateVar x, Just u <- Map.lookup x s = substitute s u
    | otherwise = t

-- | The most general unifier of two templates. A template variable unifies
-- with a term of its type that does not contain the variable.
unify :: Term -> Term -> Maybe (Map Symbol Term)
unify a0 b0 = go a0 b0 Map.empty
  where
    go a b s = case (walk s a, walk s b) of
        (Term x [ty], t) | isTemplateVar x -> bind s x ty t
        (t, Term x [ty]) | isTemplateVar x -> bind s x ty t
        (Term "app" [ty, f, v], Term "app" [ty', g, u]) | ty == ty' -> go f g s >>= go v u
        (Term c [ty], Term d [ty']) | c == d && ty == ty' -> Just s
        _ -> Nothing
    walk s t@(Term x [_])
        | isTemplateVar x, Just u <- Map.lookup x s = walk s u
        | otherwise = t
    walk _ t = t
    bind s x ty t = case t of
        Term y [_] | y == x -> Just s
        Term _ (ty' : _) | ty' == ty, not (occurs s x t) -> Just (Map.insert x t s)
        _ -> Nothing
    occurs s x u = case walk s u of
        Term "app" [_, f, v] -> occurs s x f || occurs s x v
        Term y _ -> y == x

-- | The subterms of a template that are not template variables, each with
-- the function that puts a term in its place.
contexts :: Term -> [(Term, Term -> Term)]
contexts t@(Term "app" [ty, f, v]) =
    (t, id) : [ (u, \x -> Term "app" [ty, put x, v]) | (u, put) <- contexts f ]
           ++ [ (u, \x -> Term "app" [ty, f, put x]) | (u, put) <- contexts v ]
contexts t@(Term x _)
    | isTemplateVar x = []
    | otherwise = [(t, id)]

-- | The critical pairs of two rules: the left side of the second rule
-- unifies with a subterm of the left side of the first rule, which is not a
-- template variable. The instance of the first left side then rewrites in
-- two ways, and the two results are equal.
criticalPairs :: (Term, Term) -> (Term, Term) -> [(Term, Term)]
criticalPairs (l1, r1) (l2, r2) =
    [ (substitute s r1, substitute s (put r2'))
    | (u, put) <- contexts l1, Just s <- [unify u l2'] ]
  where apart (Symbol x) = Symbol ("<v>'" <> T.drop 3 x)
        l2' = rename apart l2
        r2' = rename apart r2

-- | The critical pairs of a rule with each rule of the index, in the two
-- orders.
criticalPairsWith :: Rules -> (Term, Term) -> [(Term, Term)]
criticalPairsWith rules new =
    concat [ criticalPairs new old ++ criticalPairs old new | old <- allRules rules ]

-- | Whether an equation is an instance of a rule of the index, in the same
-- context on the two sides, as in Twee. Then the equation follows from the
-- rule. The two sides of the rule match the two sides of the equation with
-- one substitution, so a rule with a variable on one side only can subsume
-- too. An equation that the order cannot orient is never ground joinable
-- with only the ordering of its variables, so without this test the
-- completion adds it again for each critical pair that gives it.
subsumed :: Rules -> (Term, Term) -> Bool
subsumed rules (s, t) =
    or [ True | (l, r) <- concatMap (`candidates` s) [oriented rules, unoriented rules, nonRewriting rules],
                Just m <- [matchTemplate l s Map.empty],
                Just _ <- [matchTemplate r t m] ]
    || case (s, t) of
         (Term "app" [ty, f, v], Term "app" [ty', g, u]) | ty == ty' ->
             (f == g && subsumed rules (v, u)) || (v == u && subsumed rules (f, g))
         _ -> False

-- | The number of template variables up to which 'groundJoinable' tests
-- each ordering of the variables.
maxOrderedVars :: Int
maxOrderedVars = 4

-- | Whether an equation is ground joinable: for each ordering of its
-- template variables, its two sides have the same normal form in the
-- Knuth-Bendix order under that ordering (Martin and Nipkow, as in Twee).
-- An ordering can also make variables equal. With more than
-- 'maxOrderedVars' variables, the test uses only the order without a
-- ranking of the variables, which is weaker.
groundJoinable :: Rules -> (Term, Term) -> Bool
groundJoinable rules (s, t)
    | length vs > maxOrderedVars = joinableUnder (Map.empty, Map.empty)
    | otherwise = all joinableUnder (orderings vs)
  where
    vs = nubOrd (templateVarLeaves s ++ templateVarLeaves t)
    joinableUnder (merge, rank) = nf (substitute merge s) == nf (substitute merge t)
      where nf = normalForm (kboGreater rank) rules

-- | The total preorders of the template variables: the variables of a block
-- are equal, and the blocks have the ranks of their places. Only variables
-- of one type can be equal. Each preorder gives the substitution that puts
-- the first variable of a block for the others, and the ranks of the first
-- variables.
orderings :: [Term] -> [(Map Symbol Term, Map Symbol Int)]
orderings vs =
    [ ( Map.fromList [ (x, b) | b : rest <- order, Term x _ <- rest ]
      , Map.fromList [ (x, i) | (i, Term x _ : _) <- zip [0 ..] order ] )
    | blocks <- partitions vs, order <- permutations blocks ]
  where
    partitions [] = [[]]
    partitions (v : rest) =
        concat [ ([v] : p) : [ before ++ (v : b) : after | (before, b : after) <- splits p, sameType v b ]
               | p <- partitions rest ]
    splits p = [ splitAt i p | i <- [0 .. length p - 1] ]
    sameType (Term _ ty) (Term _ ty' : _) = ty == ty'
    sameType _ [] = False

-- | Add a law to the rules, and complete the rules. This is ordered
-- (unfailing) completion, as Twee does it: each critical pair of a new
-- rule with a rule of the index becomes an equation, unless its two sides
-- are ground joinable. The new equation then gives new rules, and its
-- critical pairs follow. A critical pair whose normal form has a side with
-- more leaves than the given size is dropped, as in QuickSpec. The rules of
-- the critical pairs make the rewriting stronger, so that a law that
-- follows from the earlier laws is not found again.
addLaw :: Int -> Sig -> Term -> Rules -> Rules
addLaw maxSize gsig (Term "(==)" [_, l, r]) rules0 =
    complete rules1 (concatMap (criticalPairsWith rules1) new)
  where
    (new, rules1) = addEquation (toTemplate gsig l, toTemplate gsig r) rules0
    complete rules [] = rules
    complete rules ((s, t) : queue)
        | s' == t' || leaves s' > maxSize || leaves t' > maxSize
          || subsumed rules (s', t') || groundJoinable rules (s', t') =
            complete rules queue
        | otherwise = complete rules' (queue ++ concatMap (criticalPairsWith rules') new')
      where
        nf = normalForm (kboGreater Map.empty) rules
        s' = nf s
        t' = nf t
        (new', rules') = addEquation (canonical (s', t')) rules
addLaw _ _ _ rules = rules

-- | Give the template variables of an equation the names @<v>0@, @<v>1@,
-- and so on, in the order of their first occurrence, so that equal
-- equations have equal names.
canonical :: (Term, Term) -> (Term, Term)
canonical (s, t) = (rename name s, rename name t)
  where names = Map.fromList (zip [ x | Term x _ <- nubOrd (templateVarLeaves s ++ templateVarLeaves t) ] [0 :: Int ..])
        name x = Symbol ("<v>" <> T.pack (show (names Map.! x)))
