{-# LANGUAGE TupleSections #-}

module Trees.JeffreyTrees  where

-- (mktreeSimple, satcheckSimple, prepPTree, appendNodes)

-- proof trees following the algorithm described in Jeffrey's Formal Logic: Its Scope and Limits
-- Jeffrey offers two main heuristics for tree building: (i) apply non-branching rules first, 
-- with double negation given special priority (ii) simply work from the root of the tree down
-- when it comes to finding a propositions to which no rule has been applied yet

import Data.PLProp ( Prop(..) )
import Data.List

import Data.Tree -- we simply use the haskell data type for trees 
import Data.Char (ord)
-- the nodes of the tree are of the form Maybe TProp
-- with Nothing representing a closed branch
-- and Just p representing an open branch

type TProp = (Prop,Bool) -- a TProp or a "tagged" proposition is just an ordered
-- pair of a proposition and a boolean value indicating whether the proposition 
-- has had a rule applied to it or not

type PTree = Tree (Maybe TProp) -- a helpful type-synonym for us

-- | make a non-branching tree from a list of propositions
mknb :: [TProp] -> PTree
mknb [x] = Node (Just x) []
mknb (x:xs) = Node (Just x) [mknb xs]
mknb [] = error "I can't make a non-branching tree from an empty list of propositions!"

-- | append the output a rule to all the open nodes of a tree
-- | this rule is more general than it needs to be.
-- | we could split the application into the branching and
-- | non-branching case, but this turns out to be nicer
appendNodes :: [[TProp]] -> PTree -> PTree
appendNodes pss (Node Nothing t) = Node Nothing t
appendNodes pss (Node (Just t) []) = Node (Just t) (map mknb pss)
appendNodes pss (Node (Just t) ts) = Node (Just t) (map (appendNodes pss) ts)

-- | a function which takes a proposition and returns the appropriate function
-- | from trees to trees to expand the proof tree with
selectRule :: TProp -> PTree -> PTree
selectRule (Negation (Negation l),_)  = appendNodes [[(l,False)]]
selectRule (Conjunction l r,_)  = appendNodes [[(l,False),(r,False)]]
selectRule (Negation (Disjunction l r),_)  = appendNodes [[(Negation l,False), (Negation r,False)]]
selectRule (Negation (Conditional l r),_)  = appendNodes [[(l,False), (Negation r,False)]]
selectRule (Disjunction l r,_)  = appendNodes [[(l, False)],[(r, False)]]
selectRule (Conditional l r,_) = appendNodes [[(Negation l, False)], [(r,False)]]
selectRule (Negation (Conjunction l r),_) = appendNodes [[(Negation r, False)], [(Negation l, False)]]
selectRule (Biconditional l r,_) = appendNodes [[(Negation l, False), (Negation r, False)],[(l, False), (r,False)]]
selectRule (Negation (Biconditional l r),_) = appendNodes [[(Negation l, False), (r,False)],[(l,False), (Negation r,False)]]
selectRule _  = id

-- | apply non-branching rules, indicating whether a rule was applied or not
-- | if no rules were applied, we stop looping the application of Alpha rules
applyAlphaRules :: PTree -> (PTree,Bool)
applyAlphaRules (Node Nothing t) = (Node Nothing t,False)
applyAlphaRules (Node (Just t) []) = if alphaGo t
    then (selectRule t $ Node (Just (check t)) [],True)
    else (Node (Just t) [],False)
applyAlphaRules (Node (Just t) ts) = if alphaGo t
    then (selectRule t $ Node (Just (check t)) [],True)
    else (Node (Just t) ts,False)

check :: TProp -> TProp
check (x,y) = (x,True)

alphaGo :: TProp -> Bool
alphaGo (p,False) = isAlpha p
alphaGo (p,True) = False

isAlpha :: Prop -> Bool
isAlpha (Negation (Negation l)) = True
isAlpha (Conjunction l r) = True
isAlpha (Negation (Disjunction l r)) = True
isAlpha (Negation (Conditional l r)) = True
isAlpha _ = False

applyBetaRules :: PTree -> (PTree,Bool)
applyBetaRules (Node Nothing t) = (Node Nothing t,False)
applyBetaRules (Node (Just t) []) = if betaGo t
    then (selectRule t $ Node (Just (check t)) [],True)
    else (Node (Just t) [],False)
applyBetaRules (Node (Just t) ts) = if betaGo t
    then (selectRule t $ Node (Just (check t)) [],True)
    else (Node (Just t) ts,False)

betaGo :: TProp -> Bool
betaGo (p,False) = isBeta p
betaGo (p,True) = False

isBeta :: Prop -> Bool
isBeta (Disjunction l r) = True
isBeta (Conditional l r) = True
isBeta (Negation (Conjunction l r)) = True
isBeta (Biconditional l r) = True
isBeta (Negation (Biconditional l r)) = True
isBeta _ = False

isDN :: Prop -> Bool
isDN (Negation (Negation l)) = True
isDN _ = False

dnGo :: TProp -> Bool
dnGo (p,False) = isDN p
dnGo (p,True) = False

applyDN :: PTree -> (PTree,Bool)
applyDN (Node Nothing t) = (Node Nothing t,False)
applyDN (Node (Just t) []) = if dnGo t
    then (selectRule t $ Node (Just (check t)) [],True)
    else (Node (Just t) [],False)
applyDN (Node (Just t) ts) = if dnGo t
    then (selectRule t $ Node (Just (check t)) [],True)
    else (Node (Just t) ts,False)

-- | close any paths that contain contraditions
closure :: PTree -> PTree
closure = closure1 []

closure1 :: [Prop] -> PTree -> PTree
closure1 [] (Node Nothing t) = Node Nothing t
closure1 [] (Node (Just (p,b)) []) = Node (Just (p,b)) []
closure1 [] (Node (Just (p,b)) ts) = Node (Just (p,b)) (map (closure1 [p]) ts)
closure1 xs (Node Nothing t) = Node Nothing t
closure1 xs (Node (Just (p,b)) []) = if contras (p:xs)
    then Node (Just (p,b)) [Node Nothing []]
    else Node (Just (p,b)) []
closure1 xs (Node (Just (p,b)) ts) = Node (Just (p,b)) (map (closure1 (p:xs)) ts)

-- | are there any contraditory propositions in the list?
contras :: [Prop] -> Bool
contras xs = any (\x -> x `elem` xs && Negation x `elem` xs) xs

-- | does the tree have any open paths?
hasopen :: PTree -> Bool
hasopen (Node Nothing t) = False
hasopen (Node (Just t) []) = True
hasopen (Node (Just (p,b)) ts) = any hasopen ts

-- | all applied?
allapplied :: PTree -> Bool
allapplied (Node Nothing t) = True
allapplied (Node (Just (p,True)) []) = True
allapplied (Node (Just (Basic p,False)) []) = True
allapplied (Node (Just (Negation (Basic p),False)) []) = True
allapplied (Node (Just (p,False)) []) = False
allapplied (Node (Just (p,True)) ts) = all allapplied ts
allapplied (Node (Just (p,False)) ts) = False

-- prepare the tree and make the tree etc.

prepPTree :: [Prop] -> PTree
prepPTree ps = mknb (prepTProps ps)

prepTProps :: [Prop] -> [TProp]
prepTProps = map (, False)

-- | okay, here we finally make the tree basically we want to loop the 
-- | non-branching rules until they cannot be applied
-- | then we switch to the branching rules


jeffreyloop :: PTree -> PTree
jeffreyloop t = let t1 = closure (loopN t) in
        if not (hasopen t1)
            then t1
            else let (t2,tag) = applyAlphaRules t1 in
                if tag
                    then jeffreyloop t2
                    else let (t3,tag) = applyBetaRules t2 in
                                  if allapplied t3
                                     then t3
                                     else jeffreyloop t3

loopN :: PTree -> PTree
loopN t = let (newtree,tag) = applyDN t in
    if tag
        then loopN newtree
        else newtree

mktreeSimple :: [Prop] -> PTree
mktreeSimple = jeffreyloop . prepPTree

satcheckSimple :: [Prop] -> Bool
satcheckSimple t = hasopen (mktreeSimple t)

