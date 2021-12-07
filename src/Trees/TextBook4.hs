{-# LANGUAGE TupleSections #-}

module Trees.TextBook4 (mktreeSimple, satcheckSimple, prepPTree, applyRule)  where

-- closure only on literals

import Data.PLProp ( Prop(..) )

import Random.PLprops -- just for testing. 

data PTree = Br2 TProp (PTree,PTree)
           | Br1 TProp (Maybe PTree)
           | Closed
    deriving (Show,Eq,Ord)

type TProp = (Prop,Bool)

-- | build a non-branching tree from a list of tprops
nbfl :: [TProp] -> PTree
nbfl [x] = Br1 x Nothing
nbfl (x:xs) = Br1 x (Just (nbfl xs))
nbfl _ = error "bad"

-- | take the output of a branching rule, and apply it to the subtree (tested, correct)
applyB :: ([TProp],[TProp]) -> PTree -> PTree
applyB (lps,rps) t = case t of
  Br2 tp (lt,rt) -> Br2 tp (applyB (lps,rps) lt ,applyB (lps,rps) rt )
  Br1 tp m_pt -> case m_pt of
    Nothing -> Br2 tp (nbfl lps,nbfl rps) -- the work is done here
    Just pt -> Br1 tp (Just (applyB (lps,rps) pt))
  Closed -> Closed

-- | take the output of a non-branching, and apply it to the subtree (tested, correct)
applyNB :: [TProp] -> PTree -> PTree
applyNB tp t = case t of
  Br2 tp' (lt,rt) -> Br2 tp' (applyNB tp lt,applyNB tp rt)
  Br1 tp' m_pt -> case m_pt of
    Nothing -> Br1 tp' (Just $ nbfl tp) -- the work is done here
    Just pt -> Br1 tp' (Just (applyNB tp pt))
  Closed -> Closed

select :: Prop -> PTree -> PTree
select (Negation (Negation l))  = applyNB [(l,False)]
select (Conjunction l r)  = applyNB [(l,False),(r,False)]
select (Negation (Disjunction l r))  = applyNB [(Negation l,False), (Negation r,False)]
select (Negation (Conditional l r))  = applyNB [(l,False), (Negation r,False)]
select (Disjunction l r)  = applyB ([(l, False)],[(r, False)])
select (Conditional l r) = applyB ([(Negation l, False)], [(r,False)])
select (Negation (Conjunction l r)) = applyB ([(Negation r, False)], [(Negation l, False)])
select (Biconditional l r) = applyB ([(Negation l, False), (Negation r, False)],[(l, False), (r,False)])
select (Negation (Biconditional l r)) = applyB ([(Negation l, False), (r,False)],[(l,False), (Negation r,False)])
select (Negation x)   = id
select (Basic x)  = id

applyRule :: PTree -> PTree
applyRule t = case t of
  Br2 (Basic x,False) (lt,rt) -> Br2 (Basic x,False) (applyRule lt,applyRule rt)
  Br2 (Negation (Basic x),False) (lt,rt) -> Br2 (Negation (Basic x),False) (applyRule lt,applyRule rt)
  Br2 (p,False) (lt,rt) -> let f = select p in
      Br2 (p,True) (f lt,f rt) -- apply appropriate rule to each branch
  Br2 (p,True) (lt,rt) -> Br2 (p,True) (applyRule lt,applyRule rt) -- recurse on each branch
  Br1 (Basic x,False) m_pt -> case m_pt of
    Nothing -> Br1 (Basic x,False) m_pt -- do nothing when there is nothing to do
    Just pt -> Br1 (Basic x,False) (Just (applyRule pt)) -- recurse down the branch
  Br1 (Negation (Basic x),False) m_pt -> case m_pt of
    Nothing -> Br1 (Negation (Basic x),False) m_pt -- do nothing when there is nothing to do
    Just pt -> Br1 (Negation (Basic x),False) (Just (applyRule pt)) -- recurse down the branch
  Br1 (p,False) m_pt -> select p $ Br1 (p,True) m_pt -- apply appropriate rule to branch
  Br1 (p,True) m_pt -> case m_pt of
    Nothing -> Br1 (p,True) m_pt -- do nothing when there is nothing to do
    Just pt -> Br1 (p,True) (Just (applyRule pt)) -- recurse down the branch
  Closed -> Closed

applyClosure :: PTree -> PTree
applyClosure = applyClosure1 []

applyClosure1 :: [Prop] -> PTree -> PTree
applyClosure1 acc t = case t of
  Br2 tp (lt,rt) -> Br2 tp (applyClosure1 (acclits tp acc) lt, applyClosure1 (acclits tp acc) rt)
  Br1 tp m_pt -> case m_pt of
    Nothing -> if check (acclits tp acc) then Br1 tp (Just Closed) else Br1 tp Nothing
    Just pt -> Br1 tp (Just $ applyClosure1 (acclits tp acc) pt)
  Closed -> Closed

acclits :: TProp -> [Prop] -> [Prop]
acclits (Basic x,_) ps = Basic x : ps
acclits (Negation (Basic x),_) ps = Negation (Basic x) : ps
acclits _ ps = ps

check :: [Prop] -> Bool
check xs = any (\x -> (x `elem` xs) && Negation x `elem` xs) xs

hasopen :: PTree -> Bool
hasopen (Br2 p (lt,rt)) = hasopen lt || hasopen rt
hasopen (Br1 p t) = maybe True hasopen t
hasopen Closed = False

prepPTree :: [Prop] -> PTree
prepPTree ps = nbfl (prepTProps ps)

prepTProps :: [Prop] -> [TProp]
prepTProps = map (, False)

mktreeSimple :: [Prop] -> PTree
mktreeSimple ps = mktreeSimple1 (prepPTree ps)

mktreeSimple1 :: PTree -> PTree
mktreeSimple1 t = let new = applyClosure t in
    mktreeSimple2 new new

mktreeSimple2 :: PTree -> PTree -> PTree
mktreeSimple2 old t = let new = (applyClosure . applyRule) t in
    if old == new
        then old
        else mktreeSimple2 new new

satcheckSimple :: [Prop] -> Bool
satcheckSimple t = hasopen (mktreeSimple t)



--}