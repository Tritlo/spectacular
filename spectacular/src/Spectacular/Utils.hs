{-# LANGUAGE  OverloadedStrings #-}
module Spectacular.Utils where

import Spectacular.Types (TypeSkeleton (..))
import Data.Text (Text)
import Data.CFTA.Equality (Node (Node), mkEdge, Edge (Edge), pathsMatching, mapNodes, createMu,
                           union, getPath, mkEqConstraints, path, Path, equalityConstraint)
import Data.CFTA.Symbol (Symbol (Symbol))
import Data.Containers.ListUtils (nubOrd)


-- | The marker that is the first child of a function type.
theArrowNode :: Node Symbol
theArrowNode = Node [Edge "(->)" []]

-- | The node of a function type.
arrowType :: Node Symbol -> Node Symbol -> Node Symbol
arrowType n1 n2 = Node [Edge "->" [theArrowNode, n1, n2]]

-- | The node of a type constructor with its arguments.
mkDatatype :: Text -> [Node Symbol] -> Node Symbol
mkDatatype s ns = Node [Edge (Symbol s) ns]

-- | The leaves of the type variables.
var1, var2, var3, var4, varAcc :: Node Symbol
var1 = Node [Edge "var1" []]
var2 = Node [Edge "var2" []]
var3 = Node [Edge "var3" []]
var4 = Node [Edge "var4" []]
varAcc = Node [Edge "acc" []]

-- | Keep the terms of a node whose type child equals the type.
filterType :: Node Symbol -> Node Symbol -> Node Symbol
filterType n t =
  Node [mkEdge "filter" [t, n] (equalityConstraint $ mkEqConstraints [[path [0], path [1, 0]]])]

-- | The nodes of the terms with k leaves: the atoms, or the applications of
-- the terms of i leaves to the terms of k - i leaves.
tk :: Node Symbol -> Int -> [Node Symbol]
tk _ 0 = []
tk anyArg 1 = [anyArg]
tk anyArg k = map constructApp [1 .. (k-1)]
 where
   constructApp :: Int -> Node Symbol
   constructApp i =
      mapp (union $ tk anyArg i)
           (union $ tk anyArg (k-i))

mapp :: Node Symbol -> Node Symbol -> Node Symbol
mapp n1 n2 = Node [
    mkEdge "app"
    [getPath (path [0,2]) n1, theArrowNode, n1, n2]
    (equalityConstraint $ mkEqConstraints [
          [path [1], path [2, 0, 0]] -- it's a function
        , [path [3, 0], path [2, 0, 1]]
        , [path [0], path [2,0,2]]
        ]
    )]

        
chunks :: Int -> [a] -> [[a]]
chunks _ [] = []
chunks n xs = f:chunks n nxt
  where (f,nxt) = splitAt n xs

allConstructors :: Comps -> [(Text, Int)]
allConstructors comps = nubOrd (concatMap (getConstructors . snd) comps)
 where
  getConstructors :: TypeSkeleton -> [(Text, Int)]
  getConstructors (TVar _    ) = []
  getConstructors (TFun t1 t2) = getConstructors t1 ++ getConstructors t2
  getConstructors (TCons nm ts) =
    (nm, length ts) : concatMap getConstructors ts

type Comps = [(Text,TypeSkeleton)]

mtau :: Comps -> Node Symbol
mtau comps = createMu
  (\n -> union
    (  (arrowType n n:globalTyVars)
    ++ map (Node . (: []) . constructorToEdge n) usedConstructors
    )
  )
 where
  constructorToEdge :: Node Symbol -> (Text, Int) -> Edge Symbol
  constructorToEdge n (nm, arity) = Edge (Symbol nm) (replicate arity n)

  usedConstructors = allConstructors comps

globalTyVars :: [Node Symbol]
globalTyVars = [var1, var2, var3, var4, varAcc]

generalize :: Comps -> Node Symbol -> Node Symbol
generalize comps n@(Node [_]) = Node
  [mkEdge s ns' (equalityConstraint $ mkEqConstraints $ map pathsForVar vars)]
 where
  vars                = globalTyVars
  nWithVarsRemoved    = mapNodes (\x -> if x `elem` vars
                                        then mtau comps else x) n
  (Node [Edge s ns']) = nWithVarsRemoved

  pathsForVar :: Node Symbol -> [Path]
  pathsForVar v = pathsMatching (== v) n
generalize _ n = n -- error $ "cannot generalize: " ++ show n

typeToFta :: TypeSkeleton -> Node Symbol
typeToFta (TVar "a"  ) = var1
typeToFta (TVar "b"  ) = var2
typeToFta (TVar "c"  ) = var3
typeToFta (TVar "d"  ) = var4
typeToFta (TVar "acc") = varAcc
-- TODO: lift this restriction
typeToFta (TVar v) =
  error
    $ "Current implementation only supports function signatures with type variables a, b, c, d, and acc, but got "
    ++ show v
typeToFta (TFun  t1    t2      ) = arrowType (typeToFta t1) (typeToFta t2)
typeToFta (TCons "Fun" [t1, t2]) = arrowType (typeToFta t1) (typeToFta t2)
typeToFta (TCons s     ts      ) = mkDatatype s (map typeToFta ts)
