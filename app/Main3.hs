module Main3 where

import Random.PLprops
import DP.DPLL

main :: IO ()
main = do 
    mapM_ (print . dpllsat) testprops10 
    
