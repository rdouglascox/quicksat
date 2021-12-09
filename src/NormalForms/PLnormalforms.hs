module NormalForms.PLnormalforms where

import Data.PLProp

import Control.Applicative ( Applicative(liftA2) )

import qualified Data.Set as S
import qualified Data.List as L

nnf :: Prop -> Prop
nnf (Conjunction p q) = Conjunction (nnf p) (nnf q)
nnf (Disjunction p q) = Disjunction (nnf p) (nnf q)
nnf (Conditional p q) = Disjunction (nnf (Negation p)) (nnf q) 
nnf (Biconditional p q) = Disjunction (Conjunction (nnf p) (nnf q)) (Conjunction (nnf (Negation p))(nnf (Negation q)))
nnf (Negation (Negation p)) = nnf p
nnf (Negation (Conjunction p q)) = Disjunction (nnf (Negation p)) (nnf (Negation q))
nnf (Negation (Disjunction p q)) = Conjunction (nnf (Negation p)) (nnf (Negation q))
nnf (Negation (Conditional p q)) = Conjunction (nnf p) (nnf (Negation q))    
nnf (Negation (Biconditional p q)) = Disjunction (Conjunction (nnf p) (nnf (Negation q))) (Conjunction (nnf (Negation p)) (nnf q))
nnf x = x

dnf' :: Prop -> Prop
dnf' = rawdnf . nnf

distrib :: Prop -> Prop 
distrib (Conjunction p (Disjunction q r)) = Disjunction (distrib (Conjunction p q)) (distrib (Conjunction p r))
distrib (Conjunction (Disjunction p q) r) = Disjunction (distrib (Conjunction p r)) (distrib (Conjunction q r))
distrib x = x

rawdnf :: Prop -> Prop 
rawdnf (Conjunction p q) = distrib (Conjunction (rawdnf p) (rawdnf q))
rawdnf (Disjunction p q) = Disjunction (rawdnf p) (rawdnf q)
rawdnf x = x

distrib' :: S.Set (S.Set Prop) -> S.Set (S.Set Prop) -> S.Set (S.Set Prop)
distrib' xs ys = S.fromList $ [S.union x y | x <- S.toList xs, y <- S.toList ys]

purednf :: Prop -> S.Set (S.Set Prop)
purednf (Conjunction p q) = distrib' (purednf p) (purednf q)
purednf (Disjunction p q) = S.union (purednf p) (purednf q)
purednf x = S.singleton (S.singleton x)

negative :: Prop -> Bool 
negative (Negation p) = True
negative _ = False

positive :: Prop -> Bool
positive = not . negative

negate' :: Prop -> Prop 
negate' (Negation p) = p 
negate' x = Negation x

trivial :: S.Set Prop -> Bool 
trivial lits = let (pos,neg) = S.partition positive lits in
   S.intersection pos (S.map negate' neg) /= S.empty

simpdnf :: Prop -> S.Set (S.Set Prop)
simpdnf fm = let djs = S.filter (not . trivial) (purednf (nnf fm)) in
    S.filter (\d -> not (any (`S.isProperSubsetOf` d) djs)) djs

listdisj :: S.Set Prop -> Prop 
listdisj s = if S.null s then Disjunction (Basic 'A') (Negation (Basic 'A'))
    else foldr1 Disjunction (S.elems s)

listconj :: S.Set Prop -> Prop 
listconj s = if S.null s then Conjunction (Basic 'A') (Negation (Basic 'A'))
    else foldr1 Conjunction (S.elems s)

dnf :: Prop -> Prop
dnf fm = listdisj (S.map listconj (simpdnf fm))

purecnf :: Prop -> S.Set (S.Set Prop)
purecnf fm = S.map (S.map negate') (purednf (nnf (Negation fm)))

simpcnf :: Prop -> S.Set (S.Set Prop)
simpcnf fm = let cjs = S.filter (not. trivial) (purecnf fm) in
    S.filter (\x -> not (any (`S.isProperSubsetOf` x) cjs)) cjs

cnf :: Prop -> Prop
cnf fm = listconj (S.map listdisj (simpcnf fm))

