{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module Data.ECTA.Internal.ECTA.Enumeration (
    TermFragment(..)
  , termFragToTruncatedTerm

  , SuspendedConstraint(..)
  , scGetPathTrie
  , scGetUVar
  , descendScs
  , UVarValue(..)

  , EnumerationState(..)
  , uvarCounter
  , uvarRepresentative
  , uvarValues
  , pruneDeps
  , initEnumerationState


  , EnumerateM
  , getUVarRepresentative
  , assimilateUvarVal
  , mergeNodeIntoUVarVal
  , getUVarValue
  , getTermFragForUVar
  , runEnumerateM

  , getPruneDepsOf
  , getPruneDeps
  , addPruneDep
  , deletePruneDep
  , fragRepresents

  , enumerateNode
  , enumerateEdge
  , firstExpandableUVar
  , enumerateOutUVar
  , enumerateOutFirstExpandableUVar
  , enumerateFully
  , expandTermFrag
  , expandPartialTermFrag
  , expandUVar

  , getAllTruncatedTerms
  , getAllTerms
  , getAllTermsPrune
  , enumPrune
  , naiveDenotation
  , naiveDenotationBounded
  ) where

import qualified Data.Text as T
import Control.Monad ( forM_, guard, unless, when, filterM )
import Control.Monad.State.Strict ( StateT(..) )
import qualified Data.IntMap as IntMap
import Data.Maybe ( fromMaybe, isJust, mapMaybe )
import Data.Monoid ( Any(..) )
import Data.Semigroup ( Max(..) )
import           Data.Sequence ( Seq((:<|), (:|>)) )
import qualified Data.Sequence as Sequence
import Control.Monad.Identity ( Identity )

import Control.Lens ( use, ix, (%=), (.=) )
import Control.Lens.TH ( makeLenses )
import           Pipes
import qualified Pipes.Prelude as Pipes

import Data.List.Index ( imapM )

import Data.ECTA.Internal.ECTA.Operations
import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Paths
import Data.ECTA.Term
import           Data.Persistent.UnionFind ( UnionFind, UVar, uvarToInt, intToUVar, UVarGen )
import qualified Data.Persistent.UnionFind as UnionFind
import Data.Text.Extended.Pretty
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Debug.Trace

-------------------------------------------------------------------------------


---------------------------------------------------------------------------
------------------------------- Term fragments ----------------------------
---------------------------------------------------------------------------

data TermFragment = TermFragmentNode !Symbol ![TermFragment]
                  | TermFragmentUVar UVar
  deriving ( Eq, Ord, Show )

termFragToTruncatedTerm :: TermFragment -> Term
termFragToTruncatedTerm (TermFragmentNode s ts) = Term s (map termFragToTruncatedTerm ts)
termFragToTruncatedTerm (TermFragmentUVar uv)   = Term (Symbol $ "v" <> pretty (uvarToInt uv)) []

---------------------------------------------------------------------------
------------------------------ Enumeration state --------------------------
---------------------------------------------------------------------------

-----------------------
------- Suspended constraints
-----------------------

data SuspendedConstraint = SuspendedConstraint !PathTrie !UVar
  deriving ( Eq, Ord, Show )

scGetPathTrie :: SuspendedConstraint -> PathTrie
scGetPathTrie (SuspendedConstraint pt _) = pt

scGetUVar :: SuspendedConstraint -> UVar
scGetUVar (SuspendedConstraint _ uv) = uv

descendScs :: Int -> Seq SuspendedConstraint -> Seq SuspendedConstraint
descendScs i scs = Sequence.filter (not . isEmptyPathTrie . scGetPathTrie)
                   $ fmap (\(SuspendedConstraint pt uv) -> SuspendedConstraint (pathTrieDescend pt i) uv)
                          scs

-----------------------
------- UVarValue
-----------------------

data UVarValue = UVarUnenumerated { contents    :: !(Maybe Node)
                                  , constraints :: !(Seq SuspendedConstraint)
                                  }
               | UVarEnumerated   { termFragment :: !TermFragment }
               | UVarEliminated
  deriving ( Eq, Ord, Show )

intersectUVarValue :: UVarValue -> UVarValue -> UVarValue
intersectUVarValue (UVarUnenumerated mn1 scs1) (UVarUnenumerated mn2 scs2) =
  let newContents = case (mn1, mn2) of
                      (Nothing, x      ) -> x
                      (x,       Nothing) -> x
                      (Just n1, Just n2) -> Just (intersect n1 n2)
      newConstraints = scs1 <> scs2
  in UVarUnenumerated newContents newConstraints

intersectUVarValue UVarEliminated            _                         = error "intersectUVarValue: Unexpected UVarEliminated"
intersectUVarValue _                         UVarEliminated            = error "intersectUVarValue: Unexpected UVarEliminated"
intersectUVarValue _                         _                         = error "intersectUVarValue: Intersecting with enumerated value not implemented"


-----------------------
------- Top-level state
-----------------------

data EnumerationState = EnumerationState {
    _uvarCounter        :: UVarGen
  , _uvarRepresentative :: UnionFind
  , _uvarValues         :: Seq UVarValue
  -- Added for pruning, hardcoded for now.
  , _pruneDeps          :: !(IntMap.IntMap [Term])
  }
  deriving ( Eq, Ord, Show )

makeLenses ''EnumerationState


initEnumerationState :: Node -> EnumerationState
initEnumerationState n = let (uvg, uv) = UnionFind.nextUVar UnionFind.initUVarGen
                         in EnumerationState uvg
                                             (UnionFind.withInitialValues [uv])
                                             (Sequence.singleton (UVarUnenumerated (Just n) Sequence.Empty))
                                             IntMap.empty



---------------------------------------------------------------------------
---------------------------- Enumeration monad ----------------------------
---------------------------------------------------------------------------

---------------------
-------- Monad
---------------------


type EnumerateM = StateT EnumerationState []

runEnumerateM :: EnumerateM a -> EnumerationState -> [(a, EnumerationState)]
runEnumerateM = runStateT

-- Prune deps --
getPruneDeps :: EnumerateM (IntMap.IntMap [Term])
getPruneDeps = use pruneDeps

getPruneDepsOf :: Int -> EnumerateM (Maybe [Term])
getPruneDepsOf uv = do pd <- use pruneDeps
                       return (pd IntMap.!? uv)

addPruneDep :: Int -> Term -> EnumerateM ()
addPruneDep uv rw = pruneDeps %= IntMap.adjust (rw:) uv

addPruneDeps :: Int -> [Term] -> EnumerateM ()
addPruneDeps uv rws = pruneDeps %= IntMap.adjust (rws ++) uv

deletePruneDep :: Int -> EnumerateM ()
deletePruneDep uv = pruneDeps %= (IntMap.delete uv)

changePruneDep :: Int -> Int -> EnumerateM ()
changePruneDep src trg = do pd <- getPruneDepsOf src
                            case pd of
                              Just ts -> deletePruneDep src >> addPruneDeps trg ts
                              _ -> return ()

---------------------
-------- UVar accessors
---------------------

nextUVar :: EnumerateM UVar
nextUVar = do c <- use uvarCounter
              let (c', uv) = UnionFind.nextUVar c
              uvarCounter .= c'
              return uv

addUVarValue :: Maybe Node -> EnumerateM UVar
addUVarValue x = do uv <- nextUVar
                    uvarValues %= (:|> (UVarUnenumerated x Sequence.Empty))
                    return uv

getUVarValue :: UVar -> EnumerateM UVarValue
getUVarValue uv = do uv' <- getUVarRepresentative uv
                     let idx = uvarToInt uv'
                     values <- use uvarValues
                     return $ Sequence.index values idx

getTermFragForUVar :: UVar -> EnumerateM TermFragment
getTermFragForUVar uv =  termFragment <$> getUVarValue uv

getUVarRepresentative :: UVar -> EnumerateM UVar
getUVarRepresentative uv = do uf <- use uvarRepresentative
                              let (uv', uf') = UnionFind.find uv uf
                              uvarRepresentative .= uf'
                              return uv'


---------------------
-------- Creating UVar's
---------------------

pecToSuspendedConstraint :: PathEClass -> EnumerateM SuspendedConstraint
pecToSuspendedConstraint pec = do uv <- addUVarValue Nothing
                                  return $ SuspendedConstraint (getPathTrie pec) uv


---------------------
-------- Merging UVar's / nodes
---------------------

assimilateUvarVal :: UVar -> UVar -> EnumerateM ()
assimilateUvarVal uvTarg uvSrc
                                | uvTarg == uvSrc      = return ()
                                | otherwise            = do
  values <- use uvarValues
  let srcVal  = Sequence.index values (uvarToInt uvSrc)
  let targVal = Sequence.index values (uvarToInt uvTarg)
  case srcVal of
    UVarEliminated -> return () -- Happens from duplicate constraints
    _              -> do
      let v = intersectUVarValue srcVal targVal
      guard (contents v /= Just EmptyNode)
      uvarValues.(ix $ uvarToInt uvTarg) .= v
      uvarValues.(ix $ uvarToInt uvSrc)  .= UVarEliminated


mergeNodeIntoUVarVal :: UVar -> Node -> Seq SuspendedConstraint -> EnumerateM ()
mergeNodeIntoUVarVal uv n scs = do
  uv' <- getUVarRepresentative uv
  let idx = uvarToInt uv'
  uvarValues.(ix idx) %= intersectUVarValue (UVarUnenumerated (Just n) scs)
  newValues <- use uvarValues
  guard (contents (Sequence.index newValues idx) /= Just EmptyNode)


---------------------
-------- Variant maintainer
---------------------

-- This thing here might be a performance issue. UPDATE: Yes it is; clocked at 1/3 the time and 1/2 the
-- allocations of enumerateFully
--
-- It exists because it was easier to code / might actually be faster
-- to update referenced uvars here than inline in firstExpandableUVar.
-- There is no Sequence.foldMapWithIndexM.
refreshReferencedUVars :: EnumerateM ()
refreshReferencedUVars = do
  values <- use uvarValues
  
  updated <- traverse (\case UVarUnenumerated n scs ->
                               UVarUnenumerated n <$>
                                   mapM (\sc -> SuspendedConstraint (scGetPathTrie sc)
                                                                       <$> getUVarRepresentative (scGetUVar sc))
                                        scs

                             x                      -> return x)
                      values

  uvarValues .= updated


---------------------
-------- Core enumeration algorithm
---------------------
--

enumerateNode :: Seq SuspendedConstraint -> Node -> EnumerateM TermFragment
enumerateNode = enumerateNode' False

enumerateNode' :: Bool -> Seq SuspendedConstraint -> Node -> EnumerateM TermFragment
enumerateNode' _ _   EmptyNode = mzero
enumerateNode' eager_suspend scs n         =
  let (hereConstraints, descendantConstraints) = Sequence.partition (\(SuspendedConstraint pt _) -> isTerminalPathTrie pt) scs
  in case hereConstraints of
       Sequence.Empty -> case n of
                           Mu _    -> TermFragmentUVar <$> addUVarValue (Just n)
                           Node es -> enumerateEdge' eager_suspend scs =<< lift es
                           _       -> error $ "enumerateNode: unexpected node " <> show n

       (x :<| xs)     -> do reps <- mapM (getUVarRepresentative . scGetUVar) hereConstraints
                            forM_ xs $ \sc -> uvarRepresentative %= UnionFind.union (scGetUVar x) (scGetUVar sc)
                            uv <- getUVarRepresentative (scGetUVar x)
                            mapM_ (assimilateUvarVal uv) reps

                            mergeNodeIntoUVarVal uv n descendantConstraints
                            return $ TermFragmentUVar uv

enumerateEdge :: Seq SuspendedConstraint -> Edge -> EnumerateM TermFragment
enumerateEdge = enumerateEdge' False

suspendNode :: Seq SuspendedConstraint -> Node -> EnumerateM TermFragment
suspendNode scs' n = do uv <- addUVarValue (Just n)
                        mergeNodeIntoUVarVal uv n scs'
                        return $ TermFragmentUVar uv

enumerateEdge' :: Bool -> Seq SuspendedConstraint -> Edge -> EnumerateM TermFragment
enumerateEdge' eager_suspend scs e = do
  let highestConstraintIndex = getMax $ foldMap (\sc -> Max $ fromMaybe (-1) $ getMaxNonemptyIndex $ scGetPathTrie sc) scs
  guard $ highestConstraintIndex < length (edgeChildren e)

  newScs <- Sequence.fromList <$> mapM pecToSuspendedConstraint (unsafeGetEclasses $ edgeEcs e)
  let scs' = scs <> newScs
      enumIt i n = enumerateNode' eager_suspend (descendScs i scs') n
      suspendIt i n = suspendNode (descendScs i scs') n
      -- Note: we would like to eagerly suspend here to catch things like 
      -- "reverse reverse" even before it forms. But it seems to fail
      -- right away and no output... strange. TODO: fix
      -- nextFun = if eager_suspend then suspendIt else enumIt
      nextFun = enumIt
  TermFragmentNode (edgeSymbol e) <$> imapM nextFun (edgeChildren e)
                               


---------------------
-------- Enumeration-loop control
---------------------

data ExpandableUVarResult = ExpansionStuck | ExpansionDone | ExpansionNext !UVar deriving (Show)

-- Can speed this up with bitvectors

findExpandableUVars :: EnumerateM (Maybe (IntMap.IntMap Any))
findExpandableUVars = do
    values <- use uvarValues
    -- check representative uvars because only representatives are updated
    candidateMaps <- mapM (\i -> do rep <- getUVarRepresentative (intToUVar i)
                                    v <- getUVarValue rep
                                    case v of
                                        (UVarUnenumerated (Just (Mu _)) Sequence.Empty) -> return IntMap.empty
                                        (UVarUnenumerated (Just (Mu _)) _             ) -> return $ IntMap.singleton (uvarToInt rep) (Any False)
                                        (UVarUnenumerated (Just _)      _)              -> return $ IntMap.singleton (uvarToInt rep) (Any False)
                                        _                                               -> return IntMap.empty)
                              [0..(Sequence.length values - 1)]
    let candidates = IntMap.unions candidateMaps

    if IntMap.null candidates then
      return Nothing
     else do
      let ruledOut = foldMap
                      (\case (UVarUnenumerated _ scs) -> foldMap
                                                             (\sc -> IntMap.singleton (uvarToInt $ scGetUVar sc) (Any True))
                                                             scs

                             _                         -> IntMap.empty)
                      values

      let unconstrainedCandidateMap = IntMap.filter (not . getAny) (ruledOut <> candidates)
      return (Just unconstrainedCandidateMap)

firstExpandableUVar :: EnumerateM ExpandableUVarResult
firstExpandableUVar = do
      mb_unconstrainedCandidateMap <- findExpandableUVars
      case mb_unconstrainedCandidateMap of
        Nothing -> return ExpansionDone
        Just unconstrainedCandidateMap ->
            case IntMap.lookupMin unconstrainedCandidateMap of
                Nothing     -> return ExpansionStuck
                Just (i, _) -> return $ ExpansionNext $ intToUVar i

lastExpandableUVar :: EnumerateM ExpandableUVarResult
lastExpandableUVar = do
      mb_unconstrainedCandidateMap <- findExpandableUVars
      case mb_unconstrainedCandidateMap of
        Nothing -> return ExpansionDone
        Just unconstrainedCandidateMap ->
            case IntMap.lookupMax unconstrainedCandidateMap of
                Nothing     -> return ExpansionStuck
                Just (i, _) -> return $ ExpansionNext $ intToUVar i


ruleMatches :: Bool -> TermFragment -> Term -> EnumerateM Bool
-- TODO: this should match types
ruleMatches susOk _ (Term (Symbol "<v>") _) = return True
ruleMatches susOk (TermFragmentNode "app" [tf_ret_ty,tf_fun_ty,tf_f,tf_v])
                  (Term             "app" [rw_ret_ty,rw_fun_ty,rw_f,rw_v]) = do
    rw_f_m <- ruleMatches susOk tf_f rw_f
    if not rw_f_m then return False
    else ruleMatches susOk tf_v rw_v
ruleMatches susOk (TermFragmentNode ts [tf_ty])
                  (Term             rws [rw_ty]) = return (ts == rws)
                  
ruleMatches susOk (TermFragmentUVar uv) rw =
    do val <- getUVarValue uv
       case val of
           UVarEnumerated t -> ruleMatches susOk t rw
           _ -> return False -- do when susOk (addPruneDep (uvarToInt uv) rw)
                   -- return False
ruleMatches _ _ _ = return False

fragRepresents :: Bool -> TermFragment -> [Term] -> EnumerateM Bool
fragRepresents susOk (TermFragmentNode "filter" [_,t]) rwrs = fragRepresents susOk t rwrs
fragRepresents susOk tf@(TermFragmentNode "app" [_,_,f,v]) rwrs = do
    -- traceShowM ("frpappf", f)
    -- traceShowM ("frpappv", v)
    -- traceShowM ("frpapprw", rwrs)
    tf_m <- filterM (ruleMatches susOk tf) rwrs
    -- traceShowM ("frpapptfm", tf_m)
    if not (null tf_m) then return True
    else do r <- or <$> mapM (flip (fragRepresents False) rwrs) [f,v]
            -- traceShowM ("frpappr", r)
            return r
fragRepresents susOk tf@(TermFragmentNode s [_]) rwrs = do
    -- traceShowM ("frps", s)
    -- traceShowM ("frpsrw", rwrs)
    tf_m <- filterM (ruleMatches susOk tf) rwrs
    -- traceShowM ("frpstfm", tf_m)
    if not (null tf_m) then return True
    else return False
fragRepresents susOk tf@(TermFragmentUVar uv) rwrs =
    do uv_m <- filterM (ruleMatches susOk tf) rwrs
       if not (null uv_m) then return True
       else do val <- getUVarValue uv
               case val of
                 UVarEnumerated t -> fragRepresents susOk t rwrs
                 _ -> return False -- do when susOk (addPruneDeps (uvarToInt uv) rwrs)
                         -- return False
fragRepresents _ tf _ = error $ "unrecognized frag! " ++ show tf

    


anyIsTemplate :: [Term] -> Bool
anyIsTemplate = any (\(Term (Symbol s) _) -> T.isPrefixOf "<v" s)

enumerateOutUVar' :: Bool -> UVar -> EnumerateM TermFragment
enumerateOutUVar' eager_suspend uv =
    do UVarUnenumerated (Just n) scs <- getUVarValue uv
       uv' <- getUVarRepresentative uv

       t <- case n of
              Mu _ -> enumerateNode' eager_suspend scs (unfoldOuterRec n)
              _    -> enumerateNode' eager_suspend scs n


       uvarValues.(ix $ uvarToInt uv') .= UVarEnumerated t
       pd <- getPruneDepsOf (uvarToInt uv)
       case pd of
          Just rws -> do deletePruneDep (uvarToInt uv)
                         res <- fragRepresents True t rws
                         if res then mzero
                         else return t
          _ -> refreshReferencedUVars >> return t

enumerateOutUVar :: UVar -> EnumerateM TermFragment
enumerateOutUVar = enumerateOutUVar' False

enumerateOutFirstExpandableUVar :: EnumerateM ()
enumerateOutFirstExpandableUVar = do
  muv <- firstExpandableUVar
  case muv of
    ExpansionNext uv -> void $ enumerateOutUVar uv
    ExpansionDone    -> mzero
    ExpansionStuck   -> mzero

enumerateFully :: EnumerateM ()
enumerateFully  =  const () <$> enumerateFully' () False (\ x _ _ -> return (False, x))

enumerateFully' :: forall a. a
                -> Bool
                -> (a -> UVar -> Either TermFragment Node -> EnumerateM (Bool, a))
                -> EnumerateM Bool
enumerateFully' ost eager_suspend oracle = do
  muv <- if eager_suspend
        then do hints <- IntMap.keysSet <$> getPruneDeps
                if IntSet.null hints
                -- if we aren't targeting any terms, just expand the first one
                then {-# SCC "no-hints" #-} firstExpandableUVar
                else do expandable <- findExpandableUVars
                        case expandable of 
                          Nothing -> return ExpansionDone
                          Just ucm | IntMap.null ucm -> return ExpansionStuck
                          Just ucm -> let expSet = IntMap.keysSet ucm
                                          inters = IntSet.intersection expSet hints
                                      in return $ ExpansionNext $ intToUVar
                                                -- We synthesize from the back
                                                -- so we see more subterms
                                                -- asap.
                                                $ IntSet.findMax inters
                                          
                else firstExpandableUVar
  case muv of
   ExpansionStuck   -> mzero
   ExpansionDone    -> return True
   ExpansionNext uv ->
    let continue ost' = do
          tf <- enumerateOutUVar' eager_suspend uv
          (should_prune, ost'') <- oracle ost' uv (Left tf)
          if should_prune then mzero
          else enumerateFully' ost'' eager_suspend oracle
    in do UVarUnenumerated (Just n) scs <- getUVarValue uv
          case n of 
            Mu _ | scs == Sequence.empty -> return True
            _ -> do (should_prune, ost') <- oracle ost uv (Right n)
                    if should_prune then mzero else continue ost'



---------------------
-------- Expanding an enumerated term fragment into a term
---------------------


expandPartialTermFrag :: TermFragment -> EnumerateM Term
expandPartialTermFrag (TermFragmentNode s ts) = Term s <$> mapM expandPartialTermFrag ts
expandPartialTermFrag (TermFragmentUVar uv)  =
    do val <- getUVarValue uv
       case val of
        UVarEnumerated t                 -> expandPartialTermFrag t
        UVarUnenumerated (Just (Mu _)) _ -> return $ Term "Mu" []
        _ -> return $ Term (Symbol $ "<v" <> pretty (uvarToInt uv) <> ">") []


expandTermFrag :: TermFragment -> EnumerateM Term
expandTermFrag (TermFragmentNode s ts) = Term s <$> mapM expandTermFrag ts
expandTermFrag (TermFragmentUVar uv)  =
    do val <- getUVarValue uv
       case val of
        UVarEnumerated t                 -> expandTermFrag t
        UVarUnenumerated (Just (Mu _)) _ -> return $ Term "Mu" []
        _                                -> 
            error "expandTermFrag: Non-recursive, unenumerated node encountered"

expandUVar :: UVar -> EnumerateM Term
expandUVar uv = do UVarEnumerated t <- getUVarValue uv
                   expandTermFrag t


---------------------
-------- Full enumeration
---------------------

getAllTruncatedTerms :: Node -> [Term]
getAllTruncatedTerms n = map (termFragToTruncatedTerm . fst) $
                         flip runEnumerateM (initEnumerationState n) $ do
                           enumerateFully
                           getTermFragForUVar (intToUVar 0)

getAllTermsPrune :: forall a. a -> (a -> UVar -> Either TermFragment Node -> EnumerateM (Bool,a))
                 -> Node -> [Term]
getAllTermsPrune ost oracle n =
    map fst $ flip runEnumerateM (initEnumerationState n) $ enumPrune ost oracle

enumPrune :: forall a. a -> (a -> UVar -> Either TermFragment Node -> EnumerateM (Bool,a)) -> EnumerateM Term
enumPrune a oracle = do finished <- enumerateFully' a True oracle
                        if finished then expandUVar (intToUVar 0) else mzero

getAllTerms :: Node -> [Term]
getAllTerms = getAllTermsPrune () (\ _ _ _ -> return (False,()))


-- | Inefficient enumeration
--
-- For ECTAs with 'Mu' nodes may produce an infinite list or may loop indefinitely, depending on the ECTAs. For example, for
--
-- > createMu $ \r -> Node [Edge "f" [r], Edge "a" []]
--
-- it will produce
--
-- > [ Term "a" []
-- > , Term "f" [Term "a" []]
-- > , Term "f" [Term "f" [Term "a" []]]
-- > , ...
-- > ]
--
-- This happens to work currently because non-recursive edges are interned before recursive edges.
--
-- TODO: It would be much nicer if this did fair enumeration. It would avoid the beforementioned dependency on interning
-- order, and it would give better enumeration for examples such as
--
-- > Node [Edge "h" [
-- >     createMu $ \r -> Node [Edge "f" [r], Edge "a" []]
-- >   , createMu $ \r -> Node [Edge "g" [r], Edge "b" []]
-- >   ]]
--
-- This will currently produce
--
-- > [ Term "h" [Term "a" [], Term "b" []]
-- > , Term "h" [Term "a" [], Term "g" [Term "b" []]]
-- > , Term "h" [Term "a" [], Term "g" [Term "g" [Term "b" []]]]
-- > , ..
-- > ]
--
-- where it always unfolds the /second/ argument to @h@, never the first.
naiveDenotation :: Node -> [Term]
naiveDenotation = naiveDenotationBounded Nothing

-- | set a boundary on the depth of Mu node unfolding
-- if the boundary is set to @Just n@, then @n@ levels of Mu node unfolding will be performed
-- if the boundary is set to @Nothing@, then no boundary is set and the Mu nodes will be always unfolded
naiveDenotationBounded :: Maybe Int -> Node -> [Term]
naiveDenotationBounded maxDepth node = Pipes.toList $ every (go maxDepth node)
  where
    -- | Note that this code uses the decision that f(a,a) does not satisfy the constraint 0.0=1.0 because those paths are empty.
    --   It would be equally valid to say that it does.
    ecsSatisfied :: Term -> EqConstraints -> Bool
    ecsSatisfied t ecs = all (\ps -> isJust (getPath (head ps) t) && all (\p' -> getPath (head ps) t == getPath p' t) ps)
                             (map unPathEClass $ unsafeGetEclasses ecs)

    go :: Maybe Int -> Node -> ListT Identity Term
    go _       EmptyNode = mzero
    go mbDepth n@(Mu _)  = case mbDepth of
                             Nothing            -> go Nothing (unfoldOuterRec n)
                             Just d | d <= 0    -> mzero
                                    | otherwise -> go (Just $ d - 1) (unfoldOuterRec n)
    go _       (Rec _)   = error "naiveDenotation: unexpected Rec"
    go mbDepth (Node es) = do
      e <- Select $ each es

      children <- mapM (go mbDepth) (edgeChildren e)

      let res = Term (edgeSymbol e) children
      guard $ ecsSatisfied res (edgeEcs e)
      return res
