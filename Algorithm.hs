------------------------------------------------------------
-- sule
-- 2018.1
------------------------------------------------------------
module Algorithm
  ( PathFinder
  , TreeFinder
  , StateGen
  , shortestPath
  , mst
  , edgeT
  ) where

import           Control.Concurrent
import           Data.Hashable
import qualified Data.HashMap  as H
import           Data.Tree
import qualified Data.Set as S


--------------------------------------------------
-- |general type of search algorithm, state->action->states map
-- action has type : state -> H.Map state w
type Search state w
   = state -> (state -> H.Map state w) -> H.Map state state

-- |general type of search algorithm, IO version
type IOSearch state w
   = MVar state -> MVar (H.Map state state) -> MVar (H.Map state state) -> state -> (state -> H.Map state w) -> IO ()


type IOPathFinder state = state -> state -> IO [state]

type PathFinder state = state -> state -> [state]

type TreeFinder state = state -> Tree state

type StateGen state w = state -> H.Map state w

--------------------------------------------------
-- |dijkstra search algorithm
dijkstra ::
     (Ord w, Num w, Bounded w, Hashable state, Eq state,Ord state)
  => (state, w)
  -> state
  -> H.Map state (w, state)
  -> StateGen state w
  -> H.Map state state
  -> H.Map state state
dijkstra (state, sw) target open stateGen close
  | H.null open'' = close
  | H.member target close = close
  | otherwise = dijkstra (bestState, bestW) target open' stateGen close'
  where
    close' = H.insert bestState preState close
    open' = H.delete bestState open''
    (bestState, preState, bestW) =
      H.foldWithKey 
        (\rst (bw, pst) a@(_, _, rbw)-> 
           if rbw > bw
             then (rst, pst, bw)
             else a)
        (state, state, maxBound)
        open''
    open'' =
      H.unionWith
        (\a@(rsw, _) b@(rsw', _) ->
           if rsw' > rsw
             then a
             else b)
        open
        nexts
    nexts = H.map (\w -> (w + sw, state)) $stateGen state `H.difference` close

--------------------------------------------------
-- |get hash table of shortest path
shortestPathTable ::
     (Ord w, Num w, Bounded w, Hashable state, Eq state,Ord state)
  => state->Search state w
shortestPathTable target initSt stateGen =
  dijkstra (initSt, 0 ) target open stateGen $ H.singleton initSt initSt
  where
    open = H.map (\w -> (w, initSt)) $stateGen initSt

--------------------------------------------------
-- |concurrent version dijkstra
conDijkstra ::
     (Ord w, Num w, Bounded w, Hashable state, Eq state,Ord state)
  => MVar state
  -> MVar (H.Map state state)
  -> MVar (H.Map state state)
  -> (state, w)
  -> H.Map state (w, state)
  -> StateGen state w
  -> H.Map state state
  -> IO ()
conDijkstra key mbox nbox (state, sw) open stateGen close
  | H.null open'' = do
    tryTakeMVar mbox
    tryPutMVar mbox close
    return ()
  | otherwise = do
    skey <- tryReadMVar key
    case skey of
      Just _ -> return ()
      Nothing -> do
        box <- tryReadMVar nbox
        tryTakeMVar mbox
        tryPutMVar mbox close
        case box of
          Just cont ->
            if H.null $ H.intersection cont close -- need fix
              then conDijkstra
                     key
                     mbox
                     nbo
                     (bestState, bestW)
                     open'
                     stateGen
                     close'
              else do
                tryPutMVar key state
                return ()
          Nothing ->
            conDijkstra key mbox nbox (bestState, bestW) open' stateGen close'
  where
    close' = H.insert bestState preState close
    open' = H.delete bestState open''
    (bestState, preState, bestW) =
      H.foldWithKey
        (\rst (bw, pst) a@(_, _, rbw)->
           if rbw > bw
             then (rst, pst, bw)
             else a)
        (state, state, maxBound)
        open''
    open'' =
      H.unionWith
        (\a@(rsw, _) b@(rsw', _) ->
           if rsw' > rsw
             then a
             else b)
        open
        nexts
    nexts = H.map (\w -> (w + sw, state)) $stateGen state `H.difference` close



--------------------------------------------------
-- |concurrent bidirectional search, based on concurrent version dijkstra
conBDS ::
     (Ord w, Num w, Bounded w, Hashable state, Eq state,Ord state)
  => StateGen state w
  -> StateGen state w
  -> IOPathFinder state
conBDS genS genT s t = do
  box1 <- newEmptyMVar :: IO (MVar (H.Map state state))
  box2 <- newEmptyMVar :: IO (MVar (H.Map state state))
  key <- newEmptyMVar :: IO (MVar state)
  flag <- newEmptyMVar :: IO (MVar Bool)
  forkIO $ do
    shortestPathTableIO key box1 box2 s genS
    putMVar flag True
  shortestPathTableIO key box2 box1 t genT
  takeMVar flag
  skey <- tryReadMVar key
  case skey of
    Just sk -> do
      Just htbl1 <- tryReadMVar box1
      Just htbl2 <- tryReadMVar box2
      return $ reverse (getStatesR htbl2 sk) ++ [sk] ++ getStatesR htbl1 sk
    Nothing -> do
      Just htbl1 <- tryReadMVar box1
      return $ t : getStatesR htbl1 t


--------------------------------------------------
-- |get hash table of shortest path, IO version
shortestPathTableIO ::
     (Ord w, Num w, Bounded w, Hashable state, Eq state,Ord state)
  => IOSearch state w
shortestPathTableIO key box1 box2 initSt stateGen =
  conDijkstra key box1 box2 (initSt, 0) open stateGen $
  H.singleton initSt initSt
  where
    open = H.map (\w -> (w, initSt)) $stateGen initSt

--------------------------------------------------
-- |Prim  : Minimum Spanning Tree Algorithm
prim ::
     (Ord w, Num w, Bounded w, Hashable state, Eq state,Ord state)
  => (state, w)  -- init state and weight
  -> H.Map state (w, state)  -- open table, init with initState's adj states, expand automatically
  -> StateGen state w  -- state expand algorithm
  -> H.Map state state  -- close table, init with k:initState v:initState
  -> H.Map state state  -- every state only have one parent state, so the tree can be stored as a Map
prim (state, sw) open stateGen close
  | H.null open'' = close
  | otherwise = prim (bestState, bestW) open' stateGen close'
  where
    close' = H.insert bestState preState close
    open' = H.delete bestState open''
    (bestState, preState, bestW) =
      H.foldWithKey
        (\rst (bw, pst) a@(_, _, rbw)->
           if rbw > bw
             then (rst, pst, bw)
             else a)
        (state, state, maxBound)
        open''
    open'' =
      H.unionWith
        (\a@(rsw, _) b@(rsw', _) ->
           if rsw' > rsw
             then a
             else b)
        open
        nexts
    nexts = H.map (const (sw, state)) $stateGen state `H.difference` close

--------------------------------------------------
-- |camputing the minimum spanning tree
mstTable::(Ord w, Num w, Bounded w, Hashable state, Eq state,Ord state)
  => Search state w
mstTable initSt stateGen =
  prim (initSt, 0 ) open stateGen $ H.singleton initSt initSt
  where
    open = H.map (\w -> (w, initSt)) $stateGen initSt

--------------------------------------------------
-- |helper function to get list of states
getStatesR ::
     (Hashable state, Eq state,Ord state)
  => H.Map state state
  -> state
  -> [state]
getStatesR h st =
  case H.lookup st h of
    Just st' ->
      if st' == st
        then []
        else st' : getStatesR h st'
    Nothing -> []

--------------------------------------------------
-- |based on dijkstra
shortestPath :: (Ord w, Num w, Bounded w, Hashable state, Eq state,Ord state)=>
  StateGen state w -> PathFinder state
shortestPath stateGen s t
  |s==t = []
  |otherwise = t:ans
  where
    resTbl = shortestPathTable t s stateGen
    ans=getStatesR resTbl t

--------------------------------------------  ------
-- |based on prim
mst::(Ord w, Num w, Bounded w, Hashable state, Eq state,Ord state)=>
  StateGen state w -> TreeFinder state
mst gen st = mapToTree (mstTable st gen) st

mapToTree::(Hashable state, Eq state,Ord state)=>H.Map state state->TreeFinder state
mapToTree m = unfoldTree (\r->(r,S.toList $S.delete r $ (H.!) htree r))
    where
      htree = reverseHashTree m

reverseHashTree::(Hashable state, Eq state,Ord state)=>H.Map state state->H.Map state (S.Set state)
reverseHashTree tree = H.foldWithKey (H.adjust.S.insert) (H.fromList $ zip (H.keys tree) $repeat S.empty) tree
    
edgeT::Tree a->[(a,a)]
edgeT (Node l chds) = concat $ zip (repeat l) (map rootLabel chds) : map edgeT chds
