{-# LANGUAGE RecordWildCards #-}
module Data.EGraph where
import qualified Data.Map as Map
import Data.Persistent.UnionFind (UnionFind, UVar, UVarGen, initUVarGen, nextUVar)
import qualified Data.Persistent.UnionFind as UF
import Data.Interned.Extended.HashTableBased (Id)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.ECTA (Node)
import Data.ECTA.Internal.ECTA.Type (nodeIdentity)


type EId = Int

data EGraph op = Egg { ec_map :: Map UVar EId
                     , union_find :: UnionFind
                     , hashcons :: Map (ENode op) UVar
                     , worklist :: [UVar]
                     , uvar_gen :: UVarGen
                      }

data ENode op = ENode { op :: op
                      , e_children :: [UVar] }

instance Eq op => Eq (ENode op) where
    ENode{op=eop1, e_children=ec1}
     == ENode{op=eop2, e_children=ec2}  = eop1 == eop2 && ec1 == ec2

instance Ord op => Ord (ENode op) where
    compare ENode{op=eop1, e_children=ec1}
            ENode{op=eop2, e_children=ec2} =
     case compare eop1 eop2 of
         EQ -> compare ec1 ec2
         o -> o

emptyGraph :: Ord op => EGraph op
emptyGraph = Egg Map.empty UF.empty Map.empty [] initUVarGen

canonicalize :: Ord op => EGraph op -> ENode op -> (EGraph op, ENode op)
canonicalize egg@Egg{..} ENode{..}
    | (egg', chs) <- findMany egg e_children =
     (egg', ENode {op=op, e_children=chs})


find :: Ord op => EGraph op -> UVar -> (EGraph op, UVar)
find egg@Egg{..} id | (u,uf) <- UF.find id union_find
  = (egg{union_find = uf}, u)

findMany :: Ord op => EGraph op -> [UVar] -> (EGraph op, [UVar])
findMany egg [uv] | (e', uv') <- find egg uv = (e',[uv'])
findMany egg (uv:uvs) | (e', uv') <- find egg uv
                = (uv':) <$> findMany e' uvs


add :: Ord op => EGraph op -> ENode op -> (EGraph op, UVar)
add egg@Egg{..} node@ENode{..}
    | Just uv <- hashcons Map.!? node' = (egg', uv)
    | (ugvar_gen', uv) <- nextUVar uvar_gen,
      -- update the children
      hashcons' <- Map.insert node' uv hashcons
      = (egg{uvar_gen=ugvar_gen',
             hashcons=hashcons'}, uv)

  where (egg', node') = canonicalize egg node



merge :: Ord op => EGraph op -> UVar -> UVar -> (EGraph op, UVar)
merge egg@Egg{..} id1 id2
    | (u1,uf) <- UF.find id1 union_find,
      (u2, uf') <- UF.find id2 uf =
          (egg{union_find = uf'}, u2)
    | uf <- UF.union id1 id2 union_find,
      (u',uf') <- UF.find id1 uf
      = (egg{union_find = uf', worklist = u':worklist}, u')


rebuild :: EGraph op -> EGraph op
rebuild egg@Egg{worklist = []} = egg
rebuild egg@Egg{..} = undefined
