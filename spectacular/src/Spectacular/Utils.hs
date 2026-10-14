{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE  OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Spectacular.Utils where

import Spectacular.Types (TypeSkeleton (..), Term, pattern Term)
import Data.Text (pack, Text, unpack)
import Data.Maybe (mapMaybe, isJust, fromJust)

import Data.Map (Map)
import qualified Data.Map as Map

import GHC.IO.Unsafe
import Data.IORef
import Data.Char (isAlpha, isAscii)
import Data.CFTA.Equality (Node (Node), mkEdge, Edge (Edge), pathsMatching, mapNodes, createMu,
                           union, getPath, mkEqConstraints, path, Path, equalityConstraint)
import Data.CFTA.Symbol (Symbol (Symbol))
import Debug.Trace (traceShow)
import qualified Data.Monoid as M
import Data.List (groupBy, sortOn, permutations)
import Data.Function (on)
import Data.Tuple (swap)
import Data.Containers.ListUtils (nubOrd)
import Data.List (subsequences)

import Data.Time.Clock (diffUTCTime, getCurrentTime)
import Control.Monad.IO.Class (MonadIO (..))
import qualified GHC.Stack as GHS
import Text.Printf (printf)
import System.CPUTime (getCPUTime)
import Control.Monad (when)


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

constFunc :: Symbol -> Node Symbol -> Edge Symbol
constFunc s t = Edge s [t]

applyOperator :: Comps -> Node Symbol
applyOperator comps = Node
  [ constFunc
    "$"
    (generalize comps $ arrowType (arrowType var1 var2) (arrowType var1 var2))
  , constFunc "id" (generalize comps  $ arrowType var1 var1)
  ]

tk :: Comps -> Node Symbol -> Bool -> Int -> [Node Symbol]
tk _ _ _ 0 = []
tk _ anyArg False 1 = [anyArg]
tk comps anyArg True 1 = [anyArg, applyOperator comps]
tk comps anyArg _ k = map constructApp [1 .. (k-1)]
 where
   constructApp :: Int -> Node Symbol
   constructApp i =
      mapp (union $ tk comps anyArg False i)
           (union $ tk comps anyArg True (k-i))

type Argument = (Symbol, Node Symbol)
rtk :: [Argument] -> Comps -> Node Symbol -> Bool -> Int -> [Node Symbol]
rtk [] comps anyArg includeApplyOp k = tk comps anyArg False k
rtk [(s,t)] _ _ _ 1 = [Node [constFunc s t]] -- If we have one arg we use it
rtk args _ _ _ k | k < length args = []
rtk args comps anyArg _ k = concatMap (\i -> map (constructApp i) allSplits) [1..(k-1)]
  where allSplits = map (`splitAt` args) [0.. (length args)]
        constructApp :: Int -> ([Argument], [Argument]) -> Node Symbol
        constructApp i (xs, ys) =
          let f = union $ rtk xs comps anyArg False i
              x = union $ rtk ys comps anyArg True (k-i)
          in mapp f x

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

removeDicts :: Term -> Term
removeDicts t = cleanup $ maybe t id $ rd t
 where rd (Term (Symbol t) args) | up@('<':'@':_) <- unpack t,
                                   '>':'@':_ <- reverse up = Nothing
                                 | args' <- mapMaybe rd args =
                                   if null args' && t == "app"
                                   then Nothing
                                   else Just $ Term (Symbol t) args'
       cleanup (Term (Symbol "app") [arg]) = cleanup arg
       cleanup (Term (Symbol t) args) = Term (Symbol t) $ map cleanup args



pp :: Term -> Text
pp = parIfReq . mconcat . pp' False . removeDicts
 where
  parIfReq :: Text -> Text
  parIfReq t | (s:_) <- unpack t,
              s /= '(',
              not (isAlpha s) = "(" <> t <> ")"
             | otherwise = t

  pp' :: Bool -> Term -> [Text]
  pp' _ (Term (Symbol t) [])  = [t]
  pp' par (Term (Symbol "app") (arg:rest)) | res@(_:_) <- concatMap (pp' True) rest =
      [rpar <> wparifreq <> " " <> mconcat (concatMap (pp' True) rest) <> lpar]
                                           | otherwise = [wparifreq]
    where parg = pp arg
          (rpar,lpar) = if par then ("(", ")") else ("","")
          wparifreq = if length (words $ unpack parg) > 1
                      then "(" <> parg <> ")" else parg

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

invertMap :: Ord b => Map.Map a b -> Map.Map b [a]
invertMap = toMap . groupBy ((==) `on` fst) . sortOn fst . map swap . Map.toList
  where toMap = Map.fromList . map (\((a,r):rs) -> (a,r:map snd rs))



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





-- Some stats:
--
--
-- | Stopwatch for a given function, measures the time taken by a given act.
time :: MonadIO m => m a -> m ((Integer, Integer), a)
time act = do
  wallTimeStart <- liftIO getCurrentTime
  start <- liftIO getCPUTime
  r <- act
  done <- liftIO getCPUTime
  wallTimeEnd <- liftIO getCurrentTime
  return ((done - start, round (diffUTCTime wallTimeEnd wallTimeStart * 1e12)), r)

statsRef :: IORef (Map.Map (String, Int) (Integer, Integer))
{-# NOINLINE statsRef #-}
statsRef = unsafePerformIO $ newIORef Map.empty



collectStats :: (MonadIO m, GHS.HasCallStack) => m a -> m a
collectStats = id
-- collectStats a = do
--   (t, r) <- time a
--   let ((_, GHS.SrcLoc {..}) : _) = GHS.getCallStack GHS.callStack
--   let inF (a1, b1) (a2, b2) = (a1 + a2, b1 + b2)
--   liftIO $ modifyIORef' statsRef (Map.insertWith inF (srcLocFile, srcLocStartLine) t)
--   -- We don't want to flood the terminal with output
--   -- GHS.withFrozenCallStack $ liftIO $ putStrLn (showTime t)
--   return r

resetStats :: MonadIO m => m ()
resetStats = liftIO $ writeIORef statsRef Map.empty

getStats :: MonadIO m => m [String]
getStats =
  liftIO $
    let pp ((f, l), t) = f ++ ":" ++ show l ++ " " ++ showTime t
     in map pp . Map.toList <$> readIORef statsRef

reportStats :: MonadIO m => m ()
reportStats = return ()
-- reportStats = liftIO $ do
--   putStrLn "SUMMARY"
--   getStats >>= mapM_ putStrLn 

-- | Transforms time given in ns (as measured by "time") into a string
showTime :: (Integer, Integer) -> String
showTime (cpu_time, wall_time) =
  ("CPU " ++ showTime cpu_time) ++ " WALL " ++ showTime wall_time
  where
    msOrS res =
      if res > 1000
        then printf "%.2f" ((fromIntegral res * 1e-3) :: Double) ++ "s"
        else show res ++ "ms"
    showTime time_w = msOrS res
      where
        res :: Integer
        res = floor $ fromIntegral time_w * (1e-9 :: Double)
