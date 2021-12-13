module Main where

import Criterion.Main
    ( defaultMain, bench, bgroup, whnf, Benchmark )

import Random.PLprops
    ( testprops1, testprops2, testprops3, testprops4, testprops5 )
import Data.PLProp ( Prop(..) )

import qualified  Trees.TextBook1 as TB1
import qualified  Trees.TextBook2 as TB2
import qualified  Trees.TextBook3 as TB3
import qualified  Trees.TextBook4 as TB4
import qualified  Trees.TextBook5 as TB5
import qualified  Trees.TextBook6 as TB6
import qualified  Trees.TextBook7 as TB7
import qualified  NormalForms.PLnormalforms as NF1
import qualified  DP.DP as DP1
import qualified  DP.DPLL as DPLL1
import qualified Tables.Tables as T1

main :: IO ()
main = defaultMain [
    bgroup "testprops1"  (testblock testprops1) 
                        ,
    bgroup "testprops2"  (testblock testprops2)
                        ,
    bgroup "testprops3"  (testblock testprops3)
                        ,
    bgroup "testprops4"  (testblock testprops4)
                        ,
    bgroup "testprops5"  (testblock testprops5)
    ]

testblock :: [[Prop]] -> [Benchmark]
testblock ps = [ bench "TextBook1" $ whnf (deepmap TB1.mktreeSimple) ps
            , bench "TextBook2" $ whnf (deepmap TB2.mktreeSimple) ps
            , bench "TextBook3 - closure at end" $ whnf (deepmap TB3.mktreeSimple) ps
            , bench "TextBook4 - closure only on lits" $ whnf (deepmap TB4.mktreeSimple) ps
            , bench "TextBook5 - non-branching first" $ whnf (deepmap TB5.mktreeSimple) ps
            , bench "TextBook6 - non-branching first, closure on lits last" $ whnf (deepmap TB6.mktreeSimple) ps
            , bench "TextBook7 - native rose trees" $ whnf (deepmap TB7.mktreeSimple) ps
            , bench "DNFsat" $ whnf (deepmap NF1.dnfsat) ps
            , bench "DPsat" $ whnf (deepmap DP1.dpsat) ps
            , bench "DPLLsat" $ whnf (deepmap DPLL1.dpllsat) ps
            , bench "TableSat" $ whnf (deepmap T1.tablesat) ps
            ]


deepmap :: ([Prop] -> a) -> [[Prop]] -> [a]
deepmap f [] = []
deepmap f (x:xs) = f x `seq` f x : deepmap f xs `seq` deepmap f xs