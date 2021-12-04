module Trees.TextBook1 (mktreeSimple, satcheckSimple, prepPTree, applyRule) where

-- naive tree building with closure check on every rule

import Data.PLProp ( Prop(..) )

data PTree = DeadLeaf [TProp] | Leaf [TProp] | Branch [TProp] (PTree,PTree)
    deriving (Show,Eq,Ord)

data TProp = TProp Prop Bool
    deriving (Show,Eq,Ord)


applyBranching :: ([TProp],[TProp]) -> PTree -> PTree
applyBranching (l,r) (Branch ps (lb,rb)) = Branch ps (applyBranching (l,r) lb,applyBranching (l,r) rb)
applyBranching (l,r) (Leaf ps) = Branch ps (Leaf l,Leaf r)
applyBranching (l,r) (DeadLeaf ps) = DeadLeaf ps

applyNonBranching :: [TProp] -> PTree -> PTree
applyNonBranching x (Branch ps (lb,rb)) = Branch ps (applyNonBranching x lb,applyNonBranching x rb)
applyNonBranching x (Leaf ps) = Leaf (ps ++ x)
applyNonBranching x (DeadLeaf ps) = DeadLeaf ps

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
applyRule = applyRule1 []

applyRule1 :: [TProp] -> PTree -> PTree
applyRule1 acc (Branch ps x) = applyRuleB acc (Branch ps x)
applyRule1 acc (Leaf ps) = applyRuleL acc (Leaf ps)
applyRule1 acc (DeadLeaf ps) = DeadLeaf ps

applyRuleB :: [TProp] -> PTree -> PTree
applyRuleB acc (Branch (p@(TProp (Basic q) False):ps) (lb,rb)) = applyRuleB (acc ++ [p]) (Branch ps (lb,rb))
applyRuleB acc (Branch (p@(TProp (Negation (Basic q)) False):ps) (lb,rb)) = applyRuleB (acc ++ [p]) (Branch ps (lb,rb))
applyRuleB acc (Branch (TProp p False:ps) (lb,rb)) = select (TProp p False) (Branch (acc ++ (TProp p True:ps)) (lb,rb))
applyRuleB acc (Branch (p:ps) (lb,rb)) = applyRuleB (acc ++ [p]) (Branch ps (lb,rb))
applyRuleB acc (Branch [] (lb,rb)) = Branch acc (applyRule1 [] lb,applyRule rb)

applyRuleL :: [TProp] -> PTree -> PTree
applyRuleL acc (Leaf (p@(TProp (Basic q) False):ps)) = applyRuleL (acc ++ [p]) (Leaf ps)
applyRuleL acc (Leaf (p@(TProp (Negation (Basic q)) False):ps)) = applyRuleL (acc ++ [p]) (Leaf ps)
applyRuleL acc (Leaf (TProp p False: ps)) = select (TProp p False) (Leaf (acc ++ TProp p True: ps))
applyRuleL acc (Leaf (p:ps)) = applyRuleL (acc ++ [p]) (Leaf ps)
applyRuleL acc (Leaf []) = Leaf acc

applyClosure :: PTree -> PTree
applyClosure = applyClosure1 []

applyClosure1 :: [Prop] -> PTree -> PTree
applyClosure1 acc (Branch ps (lb,rb)) = Branch ps (applyClosure1 (pfromtp ps ++ acc) lb,applyClosure1 (pfromtp ps ++ acc) rb)
applyClosure1 acc (Leaf ps) = if check (acc ++ pfromtp ps)
    then DeadLeaf ps
    else Leaf ps
applyClosure1 acc (DeadLeaf xs) = DeadLeaf xs

pfromtp :: [TProp] -> [Prop]
pfromtp [] = []
pfromtp (TProp p _:xs) = p : pfromtp xs

check :: [Prop] -> Bool
check xs = any (\x -> (x `elem` xs) && Negation x `elem` xs) xs

prepPTree :: [Prop] -> PTree
prepPTree ps = Leaf (prepTProps ps)

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
hasopen (Branch ps (lr,rb)) = hasopen lr || hasopen rb
hasopen (Leaf ps) = True
hasopen (DeadLeaf ps) = False

satcheckSimple :: [Prop] -> Bool
satcheckSimple t = hasopen (mktreeSimple t)