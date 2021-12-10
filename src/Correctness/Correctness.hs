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

import Random.PLprops

import Printing.PLprop (printprops)
import DP.DP (onelittestapply)

-- | functions to test against each other here

correct :: [Prop] -> Bool
-- correct = TB1.satcheckSimple -- known correct sat checking function here
correct = NF1.dnfsat -- also known to be correct (but much faster)

check :: [Prop] -> Bool
check =DP1.dpsat -- sat checking function to test here

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
    mapM_ (\x -> putStrLn $ printprops x ++ " Correct says: " ++ show (correct x) ++ istaut x ++ " And DP says: " ++ show (check x) ++ istaut2 x) testfilterall

istaut :: [Prop] -> String 
istaut p = if correct (map Negation p)
    then " But its negation is satisfiable"
    else " But its negation is not satisfiable"

istaut2 :: [Prop] -> String 
istaut2 p = if check (map Negation p)
    then " But its negation is satisfiable"
    else " But its negation is not satisfiable"

equivtest :: IO ()
equivtest = do
    mapM_ print equivs

equivs :: [Bool]
equivs = map (not . correct . (:[])) equivpairs

equivsshow :: [Prop]
equivsshow = filter (correct . (:[])) equivpairs

equivpairs :: [Prop]
equivpairs = zipWith (\x y -> Negation (Biconditional x y) ) (concat testprops10) (map DP1.cnf $ concat testprops10)

equisat :: [Bool]
equisat = map ((\x -> correct [x] == correct [DP1.restest x]) . DP1.cnf) (concat testprops10)

doesitapply :: [Bool]
doesitapply = map (DP1.restestapply . DP1.cnf) (concat testprops10)