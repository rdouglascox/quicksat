module Main where

import Criterion.Main

import Random.PLprops
import Data.PLProp ( Prop(..) )

import qualified  Trees.TextBook1 as TB1
import qualified  Trees.TextBook2 as TB2

main :: IO ()
main = defaultMain [
    bgroup "testprops1"  (testblock testprops1) 
                        ,
    bgroup "testprops2"  (testblock testprops2)
                        ,
    bgroup "testprops3"  (testblock testprops3)
                        ,
    bgroup "testprops4"  (testblock testprops4)
    ]

testblock ps = [ bench "TextBook1" $ whnf (deepmap TB1.mktreeSimple) ps
            , bench "TextBook2" $ whnf (deepmap TB2.mktreeSimple) ps
            ]


deepmap :: ([Prop] -> a) -> [[Prop]] -> [a]
deepmap f [] = []
deepmap f (x:xs) = f x `seq` f x : deepmap f xs `seq` deepmap f xs