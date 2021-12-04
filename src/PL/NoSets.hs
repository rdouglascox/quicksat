
data PTree = NonBranching TProp PTree | Branching TProp PTree PTree 

type TProp = (Prop,Bool)

data Prop = Basic String 
          | Negation Prop
          | Conjunction Prop Prop
          | Disjunction Prop Prop
          | Conditional Prop Prop
          | Biconditional Prop Prop

