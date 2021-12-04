module Data.PLProp (Prop (..)) where

data Prop = Basic Char
          | Negation Prop
          | Conjunction Prop Prop
          | Disjunction Prop Prop
          | Conditional Prop Prop
          | Biconditional Prop Prop
    deriving (Show,Eq,Ord)