-- | Decision trees of terms, as in QuickSpec. A tree holds the
-- representatives of the terms of one type. A branch at depth k divides the
-- terms by their values on test case k, so a term that goes into the tree
-- is evaluated only on the test cases on its path. Two terms are equal when
-- they have the same values on all test cases.
module Spectacular.DecisionTree (
    DecisionTree,
    Inserted (..),
    leaf,
    insert,
    size,
) where

import Data.Dynamic (Dynamic)

import Spectacular.Types (Term)

-- | A decision tree of terms.
data DecisionTree
  = -- | A representative, with its values on the test cases from the depth
    -- of the leaf on.
    Leaf Term [Dynamic]
  | -- | The children, each with the value on the test case of the depth.
    Branch [(Dynamic, DecisionTree)]

-- | The result of an insertion.
data Inserted
  = -- | The term is a new representative, in this tree.
    Distinct DecisionTree
  | -- | The term has the values of this representative on all test cases.
    EqualTo Term
  | -- | A comparison threw, so the term cannot be tested.
    Untested

-- | The tree with one representative and its values on all test cases.
leaf :: Term -> [Dynamic] -> DecisionTree
leaf = Leaf

-- | The number of representatives in a tree.
size :: DecisionTree -> Int
size (Leaf _ _) = 1
size (Branch children) = sum (map (size . snd) children)

-- | Insert a term, with its values on the test cases, into a tree. The
-- function compares two values; it gives Nothing when the comparison throws.
insert :: (Dynamic -> Dynamic -> IO (Maybe Bool)) -> Term -> [Dynamic] -> DecisionTree -> IO Inserted
insert equal t vs (Branch children) = case vs of
    [] -> error "DecisionTree.insert: a branch below the last test case"
    v : vs' -> go [] children
      where
        go before [] = return $ Distinct $ Branch $ reverse before ++ [(v, Leaf t vs')]
        go before (child@(w, sub) : after) = do
            e <- equal w v
            case e of
                Nothing -> return Untested
                Just False -> go (child : before) after
                Just True -> below (\sub' -> Branch (reverse before ++ (w, sub') : after))
                                   <$> insert equal t vs' sub
insert equal t vs (Leaf y ws) = case (vs, ws) of
    ([], _) -> return (EqualTo y)
    (_, []) -> return (EqualTo y)
    (v : vs', w : ws') -> do
        e <- equal w v
        case e of
            Nothing -> return Untested
            Just False -> return $ Distinct $ Branch [(w, Leaf y ws'), (v, Leaf t vs')]
            Just True -> below (\sub -> Branch [(w, sub)]) <$> insert equal t vs' (Leaf y ws')

-- | Put the tree of a new representative in its place in the parent.
below :: (DecisionTree -> DecisionTree) -> Inserted -> Inserted
below place (Distinct sub) = Distinct (place sub)
below _ result = result
