module Printing.PLprop (printprop,printprops) where

import Data.PLProp ( Prop(..) )

import Data.List ( intercalate )

printprop :: Prop -> String
printprop = printPLprop

printprops :: [Prop] -> String
printprops = printPLprops

printPLprop :: Prop -> String
printPLprop (Basic x) = [x]
printPLprop (Negation x) = "~" ++ printPLprop x
printPLprop (Conjunction x y) = "(" ++ printPLprop x ++ "&" ++ printPLprop y ++ ")"
printPLprop (Disjunction x y) = "(" ++ printPLprop x ++ "v" ++ printPLprop y ++ ")"
printPLprop (Conditional x y) = "(" ++ printPLprop x ++ "->" ++ printPLprop y ++ ")"
printPLprop (Biconditional x y) = "(" ++ printPLprop x ++ "<->" ++ printPLprop y ++ ")"

printPLprops :: [Prop] -> String
printPLprops ps = intercalate ", " (map printPLprop ps)