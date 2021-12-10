module Tables.Tables (makeRawTable, getbasics, taut, tablesat, norow, norow', RawTable, MatrixHeader, Matrix, Body,  BodyHeader, ) where

import Data.PLProp
import Data.List
import Data.Char
import System.Random

-- matrix function

table :: Int -> [[Bool]]
table x = iterate expand [[]] !! x
    where
    expand xs = map (True:) xs ++ map (False:) xs

-- an assignment is just a pair of a proposition (a basic prop) and a truth value

type Assignment = [(Prop,Bool)]

-- here's how we make an assignment etc

getass :: Assignment -> Prop -> Bool
getass (x:xs) p = if fst x == p
                  then snd x
                  else getass xs p

makeass :: [Prop] -> [Bool] -> Assignment
makeass = zip

makeassignments :: [Prop] -> [[Bool]] -> [Assignment]
makeassignments ps bss = let basics = sortbasics ps in
                  map (makeass basics) bss

sortbasics :: [Prop] -> [Prop]
sortbasics xs = (sort . nub) (concatMap getbasics xs)

getbasics :: Prop -> [Prop]
getbasics (Basic x) = [Basic x]
getbasics (Negation x) = getbasics x
getbasics (Conjunction x y) = getbasics x ++ getbasics y
getbasics (Disjunction x y) = getbasics x ++ getbasics y
getbasics (Conditional x y) = getbasics x ++ getbasics y
getbasics (Biconditional x y) = getbasics x ++ getbasics y

-- here is how we do the evaluations

val :: Assignment -> Prop -> Bool
val ass (Basic x) = getass ass (Basic x)
val ass (Negation x) = not $ val ass x
val ass (Conjunction x y) = val ass x && val ass y
val ass (Disjunction x y) = val ass x || val ass y
val ass (Conditional x y) = not (val ass x) || val ass y
val ass (Biconditional x y) = val ass x == val ass y

eval :: Prop -> Assignment -> Bool
eval x y = val y x

getcolumn :: [Assignment] -> Prop -> [Bool]
getcolumn asss p = map (eval p) asss


type MatrixHeader = [Prop]
type BodyHeader = [Prop]
type Matrix = [[Bool]]
type Body = [[Bool]]

type RawTable = (MatrixHeader,BodyHeader,Matrix,Body)


makeRawTable :: [Prop] -> RawTable
makeRawTable ps = (makeMatrixHeader,makeBodyHeader,makeMatrix,makeBody)
    where makeMatrixHeader = sortbasics (concatMap getbasics ps)
          makeBodyHeader = ps
          makeMatrix = table $ length $ makeMatrixHeader
          makeBody = transpose $ map (getcolumn ass) ps
              where ass = makeassignments ps makeMatrix

-- Semantic Functions

makeTableBody :: [Prop] -> [[Bool]]
makeTableBody ps = makeBody
    where makeMatrixHeader = sortbasics (concatMap getbasics ps)
          makeBodyHeader = ps
          makeMatrix = table $ length $ makeMatrixHeader
          makeBody = transpose $ map (getcolumn ass) ps
              where ass = makeassignments ps makeMatrix

tablesat :: [Prop] -> Bool
tablesat ps = any and (makeTableBody ps)

taut :: [Prop] -> Bool
taut ps = all and (makeTableBody ps)

norow :: [Prop] -> Bool
norow ps = not $ any row (makeTableBody ps)

norow' :: [Prop] -> Bool
norow' ps = not (any row (makeTableBody ps)) && not (taut [last ps])

row :: [Bool] -> Bool
row x = not (and (tail $ reverse x)  && head (reverse x) == False)