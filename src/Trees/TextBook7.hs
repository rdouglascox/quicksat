{-# LANGUAGE TupleSections #-}

module Trees.TextBook7 (mktreeSimple, satcheckSimple, prepPTree, applyRule) where

-- using native tree structure

import Data.PLProp ( Prop(..) )

import Data.Tree

type TProp = (Prop,Bool)

nbfl :: [TProp] -> Tree TProp
nbfl [x] = Node x []
nbfl (x:xs) = Node x [nbfl xs]
nbfl _ = error "bad"

applyB :: ([TProp],[TProp]) -> Tree TProp -> Tree TProp
applyB (lpr,rps) (Node x []) = Node x [nbfl lpr,nbfl rps]
applyB (lpr,rps) (Node x ts) = Node x (map (applyB (lpr,rps)) ts)

applyNB :: [TProp] -> Tree TProp -> Tree TProp
applyNB tps (Node x []) = Node x [nbfl tps]
applyNB tps (Node x ts) = Node x (map (applyNB tps) ts)

select :: Prop -> Tree TProp -> Tree TProp
select (Negation (Negation l))  = applyNB [(l,False)]
select (Conjunction l r)  = applyNB [(l,False),(r,False)]
select (Negation (Disjunction l r))  = applyNB [(Negation l,False), (Negation r,False)]
select (Negation (Conditional l r))  = applyNB [(l,False), (Negation r,False)]
select (Disjunction l r)  = applyB ([(l, False)],[(r, False)])
select (Conditional l r) = applyB ([(Negation l, False)], [(r,False)])
select (Negation (Conjunction l r)) = applyB ([(Negation r, False)], [(Negation l, False)])
select (Biconditional l r) = applyB ([(Negation l, False), (Negation r, False)],[(l, False), (r,False)])
select (Negation (Biconditional l r)) = applyB ([(Negation l, False), (r,False)],[(l,False), (Negation r,False)])
select _  = id

applyRule :: Tree TProp -> Tree TProp
applyRule (Node (p,True) ts) = Node (p,True) (map applyRule ts)
applyRule (Node (Basic x,False) ts) = Node (Basic x,False) (map applyRule ts)
applyRule (Node (Negation (Basic x),False) ts) = Node (Negation (Basic x),False) (map applyRule ts)
applyRule (Node (p,False) []) = select p $ Node (p,True) []
applyRule (Node (p,False) ts) = select p $ Node (p,True) ts

check :: [Prop] -> Bool
check xs = any (\x -> x `elem` xs && Negation x `elem` xs) xs

hasopen :: Tree TProp -> Bool
hasopen t = not (all check (paths t))

paths :: Tree TProp -> [[Prop]]
paths = paths1 []

paths1 :: [Prop] -> Tree TProp -> [[Prop]]
paths1 acc (Node (x,_) []) = [x:acc]
paths1 acc (Node (x,_) ts) = concatMap (paths1 (x:acc)) ts

prepPTree :: [Prop] -> Tree TProp
prepPTree ps = nbfl (prepTProps ps)

prepTProps :: [Prop] -> [TProp]
prepTProps = map (, False)

mktreeSimple :: [Prop] -> Tree TProp
mktreeSimple t = let new = prepPTree t in
    mktreeSimple2 new new

mktreeSimple2 :: Tree TProp -> Tree TProp -> Tree TProp
mktreeSimple2 old t = let new = applyRule t in
    if old == new
        then old
        else mktreeSimple2 new new

satcheckSimple :: [Prop] -> Bool
satcheckSimple t = hasopen (mktreeSimple t)