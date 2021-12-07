module Correctness.Correctness (test) where

import Data.PLProp ( Prop )

import qualified Trees.TextBook1 as TB1
import qualified Trees.TextBook2 as TB2
import qualified Trees.TextBook3 as TB3
import qualified Trees.TextBook4 as TB4
import qualified Trees.TextBook5 as TB5
import qualified  Trees.TextBook7 as TB7

import Random.PLprops ( testprops1 )

import Printing.PLprop (printprops)

-- | functions to test against each other here

correct :: [Prop] -> Bool
correct = TB1.satcheckSimple -- known correct sat checking function here

check :: [Prop] -> Bool
check = TB7.satcheckSimple -- sat checking function to test here

using :: [[Prop]]
using = testprops1 -- which list of list of propositions to test against

yesnotest :: Bool
yesnotest = map correct using == map check using

testfilter :: [[Prop]]
testfilter = filter (\x -> correct x /= check x) using

test :: IO ()
test = do
    print yesnotest
    putStrLn "disagreeing on:"
    mapM_ (putStrLn . printprops) testfilter
