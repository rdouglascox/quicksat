{-# LANGUAGE TupleSections #-}

module Trees.TextBook6 (mktreeSimple, satcheckSimple, prepPTree)  where

-- ordered application of rule, closure at end, only on lits

import Data.PLProp

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

selectB :: Prop -> PTree -> PTree
selectB (Disjunction l r)  = applyB ([(l, False)],[(r, False)])
selectB (Conditional l r) = applyB ([(Negation l, False)], [(r,False)])
selectB (Negation (Conjunction l r)) = applyB ([(Negation r, False)], [(Negation l, False)])
selectB (Biconditional l r) = applyB ([(Negation l, False), (Negation r, False)],[(l, False), (r,False)])
selectB (Negation (Biconditional l r)) = applyB ([(Negation l, False), (r,False)],[(l,False), (Negation r,False)])
selectB _ = id

selectNB :: Prop -> PTree -> PTree
selectNB (Negation (Negation l))  = applyNB [(l,False)]
selectNB (Conjunction l r)  = applyNB [(l,False),(r,False)]
selectNB (Negation (Disjunction l r))  = applyNB [(Negation l,False), (Negation r,False)]
selectNB (Negation (Conditional l r))  = applyNB [(l,False), (Negation r,False)]
selectNB _= id

isbranching :: Prop -> Bool 
isbranching (Disjunction l r) = True
isbranching (Conditional l r) = True
isbranching (Negation (Conjunction l r)) = True
isbranching (Biconditional l r) = True
isbranching (Negation (Biconditional l r)) = True
isbranching _ = False

isnonbranching :: Prop -> Bool
isnonbranching = not . isbranching

applyRuleNB :: PTree -> PTree
applyRuleNB t = case t of
  Br2 (Basic x,False) (lt,rt) -> Br2 (Basic x,False) (applyRuleNB lt,applyRuleNB rt)
  Br2 (Negation (Basic x),False) (lt,rt) -> Br2 (Negation (Basic x),False) (applyRuleNB lt,applyRuleNB rt)
  Br2 (p,False) (lt,rt) -> if isnonbranching p
    then let f = selectNB p in Br2 (p,True) (f lt,f rt) -- apply appropriate rule to each branch
    else Br2 (p,False) (applyRuleNB lt,applyRuleNB rt)
  Br2 (p,True) (lt,rt) -> Br2 (p,True) (applyRuleNB lt,applyRuleNB rt) -- recurse on each branch
  Br1 (Basic x,False) m_pt -> case m_pt of
    Nothing -> Br1 (Basic x,False) m_pt -- do nothing when there is nothing to do
    Just pt -> Br1 (Basic x,False) (Just (applyRuleNB pt)) -- recurse down the branch
  Br1 (Negation (Basic x),False) m_pt -> case m_pt of
    Nothing -> Br1 (Negation (Basic x),False) m_pt -- do nothing when there is nothing to do
    Just pt -> Br1 (Negation (Basic x),False) (Just (applyRuleNB pt)) -- recurse down the branch
  Br1 (p,False) m_pt -> if isnonbranching p
    then selectNB p $ Br1 (p,True) m_pt -- apply appropriate rule to branch
    else case m_pt of
    Nothing -> Br1 (p,False) m_pt -- do nothing when there is nothing to do
    Just pt -> Br1 (p,False) (Just (applyRuleNB pt)) -- recurse down the branch
  Br1 (p,True) m_pt -> case m_pt of
    Nothing -> Br1 (p,True) m_pt -- do nothing when there is nothing to do
    Just pt -> Br1 (p,True) (Just (applyRuleNB pt)) -- recurse down the branch
  Closed -> Closed

applyRuleB :: PTree -> PTree
applyRuleB t = case t of
  Br2 (Basic x,False) (lt,rt) -> Br2 (Basic x,False) (applyRuleB lt,applyRuleB rt)
  Br2 (Negation (Basic x),False) (lt,rt) -> Br2 (Negation (Basic x),False) (applyRuleB lt,applyRuleB rt)
  Br2 (p,False) (lt,rt) -> if isbranching p
    then let f = selectB p in Br2 (p,True) (f lt,f rt) -- apply appropriate rule to each branch
    else Br2 (p,False) (applyRuleB lt,applyRuleB rt)
  Br2 (p,True) (lt,rt) -> Br2 (p,True) (applyRuleB lt,applyRuleB rt) -- recurse on each branch
  Br1 (Basic x,False) m_pt -> case m_pt of
    Nothing -> Br1 (Basic x,False) m_pt -- do nothing when there is nothing to do
    Just pt -> Br1 (Basic x,False) (Just (applyRuleB pt)) -- recurse down the branch
  Br1 (Negation (Basic x),False) m_pt -> case m_pt of
    Nothing -> Br1 (Negation (Basic x),False) m_pt -- do nothing when there is nothing to do
    Just pt -> Br1 (Negation (Basic x),False) (Just (applyRuleB pt)) -- recurse down the branch
  Br1 (p,False) m_pt -> if isbranching p
    then selectB p $ Br1 (p,True) m_pt -- apply appropriate rule to branch
    else case m_pt of
    Nothing -> Br1 (p,False) m_pt -- do nothing when there is nothing to do
    Just pt -> Br1 (p,False) (Just (applyRuleB pt)) -- recurse down the branch
  Br1 (p,True) m_pt -> case m_pt of
    Nothing -> Br1 (p,True) m_pt -- do nothing when there is nothing to do
    Just pt -> Br1 (p,True) (Just (applyRuleB pt)) -- recurse down the branch
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
mktreeSimple1 t = mktreeSimple2 t t

mktreeSimple2 :: PTree -> PTree -> PTree
mktreeSimple2 old t = let new = applyRuleNB t in
    if old == new
        then mktreeSimple3 new new
        else mktreeSimple2 new new

mktreeSimple3 :: PTree -> PTree -> PTree
mktreeSimple3 old t = let new = applyRuleB t in
    if old == new
        then old
        else mktreeSimple2 new new

satcheckSimple :: [Prop] -> Bool
satcheckSimple t = hasopen $ applyClosure (mktreeSimple t)



--}