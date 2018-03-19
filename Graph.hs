------------------------
-- graph library
--2017.11
--Sule
------------------------
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Graph where

import Data.Hashable
import Data.List (foldl')
import qualified Data.HashMap as H
import Data.HashMap ((!))
import Algorithm
import Data.Tree
import qualified Data.Set as S

--------------------------------------------------
-- class and instances of Node
class (Hashable k, Ord k) =>
      Node n k w where
  label :: n k w -> k
  predMap :: n k w -> H.Map k w
  succMap :: n k w -> H.Map k w
  adjMap :: n k w -> H.Map k w
  -- if directed then return degreeP+degreeN
  degree :: n k w -> Int
  -- positive degree of node
  degreeP :: n k w -> Int
  -- negative degree of node
  degreeN :: n k w -> Int
  parseN :: (Read k, Read w) =>Int-> (k, String) -> n k w

-------------------------------------------------
-- directed Node
data NodeD k w =
  NodeD (H.Map k w)
        k
        (H.Map k w)

instance (Hashable k, Ord k) => Node NodeD k w where
  label (NodeD _ vs _) = vs
  predMap (NodeD m _ _) = m
  succMap (NodeD _ _ m) = m
  adjMap = H.union <$> predMap <*> succMap
  degreeP node = H.size $ succMap node
  degreeN node = H.size $ predMap node
  degree = (+) <$> degreeP <*> degreeN

--------------------------------------------------
-- undirected Node
data NodeUD k w =
  NodeUD k
         (H.Map k w)
  deriving (Show)

instance (Hashable k, Ord k) => Node NodeUD k w where
  label (NodeUD v _) = v
  adjMap (NodeUD _ m) = m
  degree node = H.size $ adjMap node
  parseN x (v, str) = NodeUD v $ H.fromList prs
    where
      prs =  map read $take x $words str

--------------------------------------------------
-- class and instances of Graph
class (Node n k w) =>
      Graph g n k w where
  parseG :: (Read k, Read w) =>Int-> String -> g n k w
  fromList :: [n k w] -> g n k w
  sInsertNode :: k -> n k w -> g n k w -> g n k w
  lookupNode :: g n k w -> k -> Maybe (n k w)
  findNode:: g n k w -> k -> n k w
  deepIn::(Hashable k, Ord k,Ord w,Bounded w,Num w)=>g n k w->w->k->H.Map k w
  insertNode :: k -> n k w -> g n k w -> g n k w
  isEulerCircleExist :: g n k w -> Bool
  isEulerPathExist :: g n k w -> Bool
  groups::(Ord w,Show k) => g n k w -> w -> H.Map Int (S.Set k)
  connectedComponents :: (Ord w,Show k) => g n k w -> w -> H.Map k Int
  shortestPathG::(Hashable k, Ord k,Ord w,Bounded w,Num w)=>g n k w->w->PathFinder k
  minimumSpanningTree::(Hashable k, Ord k,Ord w,Bounded w,Num w)=>g n k w->w->TreeFinder k
  weight::(Num w)=>g n k w->[(k,k)]->Maybe w
  treeWeight::(Num w)=>g n k w->Tree k->Maybe w

--------------------------------------------------
-- undirected Graph
newtype GraphUD n k w =
  GraphUD (H.Map k (n k w))
  deriving (Show)

type GraphM k w = GraphUD NodeUD k w

instance (Hashable k, Ord k) => Graph GraphUD NodeUD k w where
  -- awesome expression
  weight g = foldl' (\z (a,b)-> (+)<$>z<*>(H.lookup b.adjMap=<<lookupNode g a)) (Just 0) 
  treeWeight g = weight g . edgeT
  parseG x str =
    GraphUD $ foldl' (\z p@(k, _) -> H.insert k (parseN x p) z) H.empty ls
    where
      ls =
        read str :: (Read k =>
                       [(k, String)])
  findNode (GraphUD g)= (H.!) g  
  groups g= build.connectedComponents g
        where build = H.foldWithKey (\k gp res->H.alter (alt k) gp res) H.empty 
              alt k (Just os)=Just $ S.insert k os
              alt _ Nothing = Just $ S.empty
  fromList = GraphUD . foldl' (\z nd@(NodeUD v adj) -> H.insert v nd z) H.empty
  lookupNode (GraphUD hm) = flip H.lookup hm
  deepIn g limit k = case lookupNode g k of
    Just nd-> H.filter (<limit) $ adjMap nd
    Nothing->H.empty
  minimumSpanningTree g = mst . deepIn g
  shortestPathG g= shortestPath . deepIn g
  isEulerCircleExist (GraphUD hm) =
    H.null $ H.filter (\n -> degree n `mod` 2 == 1) hm
  isEulerPathExist (GraphUD hm) =
    (== 2) $ H.size $ H.filter (\n -> degree n `mod` 2 == 1) hm
  connectedComponents (GraphUD g) limit = H.fold build H.empty g
    where
      build (NodeUD v adjs) hmp =
        let ks = S.filter (`H.member` hmp) $ S.fromList $H.keys $ H.filter (<limit) adjs
            ls = S.map (hmp!) ks
            maxS = S.lookupMax ls
            maxt = H.fold max 0 hmp
            hmp' = case maxS of
              Just maxs->H.insert v maxs hmp
              Nothing->H.insert v (maxt+1) hmp
        in case maxS of
            Just maxs->H.map (\x -> if S.member x ls then maxs else x) hmp'
            Nothing->hmp'

  -- simplified  
  sInsertNode k n (GraphUD g) = GraphUD $ H.insert k n g
  -- prefer the new node
  insertNode k n (GraphUD g) = GraphUD $ H.foldWithKey f g $ adjMap n
    -- change rn(the adj node of n) in graph  -- change its adj map, each insert n's key and w in n's adjMap
    where
      f rk rw =
        H.alter
          (\vn ->
             case vn of
               Just (NodeUD v adj) -> Just (NodeUD v $ H.insert k rw adj)
               Nothing -> Just (NodeUD rk $ H.singleton k rw))
          rk

--------------------------------------------------
-- directed Graph
newtype GraphD n k w =
  GraphD (H.Map k (n k w))

instance (Hashable k, Ord k) => Graph GraphD NodeD k w where
  lookupNode (GraphD hm) = flip H.lookup hm
  isEulerCircleExist (GraphD hm) =
    H.null $ H.filter (\n -> degreeN n /= degreeP n) hm
  isEulerPathExist (GraphD hm) =
    (== 2) $ H.size $ H.filter (\n -> degreeN n /= degreeP n) hm
  sInsertNode k n (GraphD g) = GraphD $ H.insert k n g
  insertNode k n (GraphD g) =
    GraphD $ H.foldWithKey fs (H.foldWithKey fp g $ predMap n) $ succMap n
    where
      fs rk rw =
        H.alter
          (\vn ->
             case vn of
               Just (NodeD adj v suc) -> Just (NodeD (H.insert k rw adj) v suc)
               Nothing -> Just (NodeD (H.singleton k rw) rk H.empty))
          rk
      fp rk rw =
        H.alter
          (\vn ->
             case vn of
               Just (NodeD pre v adj) -> Just (NodeD pre v $ H.insert k rw adj)
               Nothing -> Just (NodeD H.empty rk $ H.singleton k rw))
          rk

treeEdges=edgeT         