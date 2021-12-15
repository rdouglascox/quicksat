module Main2 where

import Random.PLprops
import Trees.JeffreyTrees2

main :: IO ()
main = do 
    mapM_ (print . satcheckSimple) testprops10 
    
