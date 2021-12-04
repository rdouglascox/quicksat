module Trees.TextBook2 (mktreeSimple, satcheckSimple, prepPTree, applyRule) where

-- (mktreeSimple, satcheckSimple, prepPTree, applyRule) 

-- textbook style trees, but only one proposition per node of the tree, 
-- no non-branching first


-- naive tree building with closure check on every rule

import Data.PLProp ( Prop(..) )

data PTree = Closed | Empty | NonBranching TProp PTree | Branching TProp (PTree,PTree)
    deriving (Show,Eq,Ord)

data TProp = TProp Prop Bool
    deriving (Show,Eq,Ord)


applyBranching :: ([TProp],[TProp]) -> PTree -> PTree
applyBranching (l,r) (Branching p (lb,rb)) = Branching p (applyBranching (l,r) lb,applyBranching (l,r) rb)
applyBranching (l,r) (NonBranching p t) = Branching p (nonbranchingfromlist l, nonbranchingfromlist r)
applyBranching (l,r) Empty = Empty
applyBranching x Closed = Closed

applyNonBranching :: [TProp] -> PTree -> PTree
applyNonBranching x (Branching p (lb,rb)) = Branching p (applyNonBranching x lb,applyNonBranching x rb)
applyNonBranching x (NonBranching p t) = nonbranchingfromlist (p: x)
applyNonBranching x Empty = Empty
applyNonBranching x Closed = Closed

nonbranchingfromlist :: [TProp] -> PTree
nonbranchingfromlist [x] = NonBranching x Empty
nonbranchingfromlist (x:xs) = NonBranching x (nonbranchingfromlist xs)
nonbranchingfromlist _ = error "bad"


doubleNegationRuleDef :: TProp -> [TProp]
doubleNegationRuleDef (TProp (Negation (Negation p)) _) = [TProp p False]

conjunctionRuleDef :: TProp -> [TProp]
conjunctionRuleDef (TProp (Conjunction l r) _) = [TProp l False,TProp r False]

negdisjunctionRuleDef :: TProp -> [TProp]
negdisjunctionRuleDef (TProp (Negation (Disjunction l r)) _) = [TProp (Negation l) False, TProp (Negation r) False]

negconditionalRuleDef :: TProp -> [TProp]
negconditionalRuleDef (TProp (Negation (Conditional l r)) _) = [TProp l False, TProp (Negation r) False]

disjunctionRuleDef :: TProp -> ([TProp],[TProp])
disjunctionRuleDef (TProp (Disjunction l r) _) = ([TProp l False],[TProp r False])

conditionalRuleDef :: TProp -> ([TProp],[TProp])
conditionalRuleDef (TProp (Conditional l r)_) = ([TProp (Negation l) False], [TProp r False])

negconjunctionRuleDef :: TProp -> ([TProp],[TProp])
negconjunctionRuleDef (TProp (Negation (Conjunction l r))_) = ([TProp  (Negation r) False], [TProp (Negation l) False])

biconditionalRuleDef :: TProp -> ([TProp],[TProp])
biconditionalRuleDef (TProp (Biconditional l r)_) = ([TProp l False, TProp r False],[TProp (Negation l) False, TProp (Negation r) False])
    
negbiconditionalRuleDef :: TProp -> ([TProp],[TProp])
negbiconditionalRuleDef (TProp (Negation (Biconditional l r))_) = ([TProp  (Negation l) False, TProp r False],[TProp l False, TProp (Negation r) False])

select :: TProp -> PTree -> PTree
select p@(TProp (Negation (Negation l)) _) = applyNonBranching (doubleNegationRuleDef p)
select p@(TProp (Conjunction l r) _) = applyNonBranching (conjunctionRuleDef p)
select p@(TProp (Negation (Disjunction l r)) _) = applyNonBranching (negdisjunctionRuleDef p)
select p@(TProp (Negation (Conditional l r)) _) = applyNonBranching (negconditionalRuleDef p)
select p@(TProp (Disjunction l r) _) = applyBranching (disjunctionRuleDef p)
select p@(TProp (Conditional l r)_) = applyBranching (conditionalRuleDef p)
select p@(TProp (Negation (Conjunction l r))_) = applyBranching (negconjunctionRuleDef p)
select p@(TProp (Biconditional l r)_) = applyBranching (biconditionalRuleDef p)
select p@(TProp (Negation (Biconditional l r))_) = applyBranching (negbiconditionalRuleDef p)
select p@(TProp (Negation x)  _) = id
select p@(TProp (Basic x)  _) = id

applyRule :: PTree -> PTree
applyRule Empty = Empty
applyRule Closed = Closed
applyRule (Branching (TProp p False) (lt,rt)) = Branching (TProp p True) (f lt,f rt)
    where f = select (TProp p False)
applyRule (NonBranching (TProp p False) t) = NonBranching (TProp p True) (f t)
    where f = select (TProp p False)
applyRule x = x




applyClosure :: PTree -> PTree
applyClosure = applyClosure1 []

applyClosure1 :: [Prop] -> PTree -> PTree
applyClosure1 acc (Branching p (lt,rt)) = Branching p (applyClosure1 (pfromtp p : acc) lt,applyClosure1 (pfromtp p : acc) rt)
applyClosure1 acc (NonBranching p t) = applyClosure1 (pfromtp p: acc) t
applyClosure1 acc Closed = Closed
applyClosure1 acc Empty = if check acc 
    then Closed
    else Empty

pfromtp :: TProp -> Prop
pfromtp (TProp p _) = p

check :: [Prop] -> Bool
check xs = any (\x -> (x `elem` xs) && Negation x `elem` xs) xs

prepPTree :: [Prop] -> PTree
prepPTree ps = nonbranchingfromlist (prepTProps ps)

prepTProps :: [Prop] -> [TProp]
prepTProps = map (`TProp` False)

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

hasopen :: PTree -> Bool
hasopen (Branching p (lt,rt)) = hasopen lt || hasopen rt
hasopen (NonBranching p t) = hasopen t
hasopen Empty = True 
hasopen Closed = False

satcheckSimple :: [Prop] -> Bool
satcheckSimple t = hasopen (mktreeSimple t)

--}