module Correctness.Correctness (test, testall, equivtest) where

import Data.PLProp

import qualified Trees.TextBook1 as TB1
import qualified Trees.TextBook2 as TB2
import qualified Trees.TextBook3 as TB3
import qualified Trees.TextBook4 as TB4
import qualified Trees.TextBook5 as TB5
import qualified  Trees.TextBook7 as TB7
import qualified  NormalForms.PLnormalforms as NF1
import qualified DP.DP as DP1
import qualified DP.DPLL as DPLL1
import qualified Tables.Tables as T1
import qualified Trees.JeffreyTrees as JT1

import Random.PLprops

import Printing.PLprop (printprops,printprop)
import DP.DP

-- | functions to test against each other here

correct :: [Prop] -> Bool
-- correct = TB1.satcheckSimple -- known correct sat checking function here
correct = T1.tablesat

check :: [Prop] -> Bool
check =JT1.satcheckSimple -- sat checking function to test here


using :: [[Prop]]
using = testprops1 -- which list of list of propositions to test against

yesnotest :: Bool
yesnotest = map correct using == map check using

yesnotestall :: [Bool]
yesnotestall = map (\x -> map correct x == map check x) [testprops1,testprops2,testprops3,testprops4,testprops5,testprops10]

testfilter :: [[Prop]]
testfilter = filter (\x -> correct x /= check x) using

testfilterall :: [[Prop]]
testfilterall = filter (\x -> correct x /= check x) (concat [testprops1,testprops2,testprops3,testprops4,testprops5,testprops10])

test :: IO ()
test = do
    print yesnotest
    putStrLn "disagreeing on:"
    mapM_ (\x -> putStrLn $ printprops x ++ " Correct says: " ++ show (correct x)) testfilter

testall :: IO ()
testall = do
    mapM_ print yesnotestall
    putStrLn "disagreeing on:"
    mapM_ (\x -> putStrLn $ printprops x ++ " Correct says: " ++ satstring (correct x) ++ " And Check says: " ++ satstring (check x)) testfilterall

satstring :: Bool -> String
satstring True = "it is satisfiable"
satstring False = "it is not satisfiable"

equivtest :: IO ()
equivtest = do
    mapM_ print equivs

equivs :: [Bool]
equivs = map (not . correct . (:[])) equivpairs

equivsshow :: [Prop]
equivsshow = filter (correct . (:[])) equivpairs

equivsshow' :: [[Prop]]
equivsshow' = map (: []) equivsshow

equivpairs :: [Prop]
equivpairs = zipWith (\x y -> Negation (Biconditional x y) ) (concat testprops10) (map DP1.cnf $ concat testprops10)

dpsattrace :: [Prop] -> IO ()
dpsattrace ps = do
    let input = DP1.simpcnf (foldr1 Conjunction ps)
    putStrLn "\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"
    putStrLn ("The raw input was: " ++ printprops ps)
    putStrLn ("The raw CNF representation is: " ++ printprop (cnf (foldr1 Conjunction ps)))
    putStrLn ("Correct says (of the raw input): " ++ satstring (correct ps) )
    putStrLn ("Correct says (of the raw CNF representation):" ++ satstring (correct [cnf (foldr1 Conjunction ps)]))
    putStrLn ("Is the raw cnf equivalent to the raw input?: " ++ myequivtest (cnf (foldr1 Conjunction ps)) (foldr1 Conjunction ps))
    putStrLn ("The set based CNF is: " ++ printSets input)
    putStrLn "Here's what DP has to say for itself:\n"
    DP1.dptrace input

myequivtest :: Prop -> Prop -> String
myequivtest x y = if correct [Negation (Biconditional x y)]
    then "Not Equivalent"
    else "Equivalent"