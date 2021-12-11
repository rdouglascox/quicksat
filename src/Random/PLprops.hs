module Random.PLprops where

import System.Random
import Data.PLProp

import Data.List

testprops1 :: [[Prop]]
testprops1 = take 100 $ nrprops (mkStdGen 2) localsettings
    where localsettings = dSettings {minConstr = 2
                                    ,maxConstr = 3
                                    ,numProps = 3}

testprops2 :: [[Prop]]
testprops2 = take 100 $ nrprops (mkStdGen 3) localsettings
    where localsettings = dSettings {minConstr = 4
                                    ,maxConstr = 5
                                    ,numProps = 3}

testprops3 :: [[Prop]]
testprops3 = take 10 $ nrprops (mkStdGen 4) localsettings
    where localsettings = dSettings {minConstr = 6
                                    ,maxConstr = 7
                                    ,numProps = 3}

testprops4 :: [[Prop]]
testprops4 = take 10 $ nrprops (mkStdGen 5) localsettings
    where localsettings = dSettings {minConstr = 8
                                    ,maxConstr = 9
                                    ,numProps = 3}

testprops5 :: [[Prop]]
testprops5 = take 10 $ nrprops (mkStdGen 5) localsettings
    where localsettings = dSettings {minConstr = 3
                                    ,maxConstr = 9
                                    ,numProps = 3
                                    ,basics = "ABCDEFGHIJKLIMNOP"}


testprops6 :: [[Prop]]
testprops6 = take 10 $ nrprops (mkStdGen 5) localsettings
    where localsettings = dSettings {minConstr = 15
                                    ,maxConstr = 16
                                    ,numProps = 3}

testprops10 :: [[Prop]]
testprops10 = take 100000 $ nrprops (mkStdGen 3) localsettings
    where localsettings = dSettings {minConstr = 2
                                    ,maxConstr = 4
                                    ,numProps = 1}

props :: RandomGen g => g -> Int -> [[Prop]]
props g n = take n $ nrprops g dSettings

data Settings = Settings {minConstr :: Int -- minimum connectives in props
                         ,maxConstr :: Int -- maximum connectives in props
                         ,numProps :: Int -- how many propositions at a time
                         ,includeCons :: [Constructor] -- include connectives (possibly)
                         ,excludeCons :: [Constructor] -- exclude connectives (certainly
                         ,basics :: String -- basics
                         }

dSettings :: Settings
dSettings = Settings {minConstr = 2
                     ,maxConstr = 20
                     ,numProps = 3
                     ,includeCons = [NegConstr Negation
                                  , CondConstr Conditional
                                  , ConjConstr Conjunction
                                  , DisjConstr Disjunction
                                  , BiconConstr Biconditional]
                     ,excludeCons = []
                     ,basics = "ABC"
                     }




data Constructor = NegConstr (Prop -> Prop)
                 | ConjConstr (Prop -> Prop -> Prop)
                 | DisjConstr (Prop -> Prop -> Prop)
                 | CondConstr (Prop -> Prop -> Prop)
                 | BiconConstr (Prop -> Prop -> Prop)

instance Eq Constructor where
    NegConstr _ == NegConstr _ = True
    ConjConstr _ == ConjConstr _ = True
    DisjConstr _ == DisjConstr _ = True
    CondConstr _ == CondConstr _ = True
    BiconConstr _ == BiconConstr _ = True
    _ == _ = False


-- HELPERS

r :: RandomGen g => g -> [a] -> a
r g x = x!!fst(randomR(0,length x -1) g)

gens :: RandomGen g => g -> [g]
gens g = g : gens (snd $ next g)

rsplitAt :: RandomGen g => g -> [a] -> ([a],[a])
rsplitAt g xs = let y = (fst $ randomR (0,length xs) g) in
    splitAt y xs

-- |Functions to construct a proposition from a list of random constructors



constructors :: Settings -> [Constructor]
constructors s = includeCons s \\ excludeCons s

rconstructors :: RandomGen g => g -> Settings -> [Constructor]
rconstructors g s = rconstructor g s : rconstructors g1 s
    where g1 = snd $ next g
          rconstructor g s = r g (constructors s)

construct :: RandomGen g => g -> Settings -> [Constructor] -> Prop
construct h s (x:y:xs) = case x of NegConstr f -> f (construct (g!!1) s (y:xs))
                                   ConjConstr f -> constructlr (g!!2) s f (y:xs)
                                   DisjConstr f -> constructlr (g!!3) s f (y:xs)
                                   CondConstr f -> constructlr (g!!4) s f (y:xs)
                                   BiconConstr f -> constructlr (g!!5) s f (y:xs)
    where g = gens h
construct h s (x:xs) = case x of NegConstr f -> f (construct (g!!6) s xs)
                                 ConjConstr f -> constructlr (g!!7) s f xs
                                 DisjConstr f -> constructlr (g!!8) s f xs
                                 CondConstr f -> constructlr (g!!9) s f xs
                                 BiconConstr f -> constructlr (g!!10) s f xs
    where g = gens h
construct h s [] = rbasic' (g!!11) s
    where g = gens h

constructlr :: RandomGen g => g -> Settings -> (Prop -> Prop -> Prop) -> [Constructor] -> Prop
constructlr g s f xs = let (l,r) = rsplitAt g xs in
                       f (construct g1 s l) (construct g2 s r)
                       where (g1,g2) = split g

rbasic' :: RandomGen g => g -> Settings -> Prop
rbasic' g s = Basic (r g (basics s))

rprops' :: RandomGen g => g -> Settings -> [Prop]
rprops' g s = construct g1 s (take (r g4 [(minConstr s)..(maxConstr s)]) $ rconstructors g2 s) : rprops' g3 s
    where (g1,g2) = split g
          (g3,g4) = split g2

nrprops :: RandomGen g => g -> Settings -> [[Prop]]
nrprops g s = chop (numProps s) (rprops' g s)
    where chop m xs = take m xs : chop m (drop m xs)

-- RANDOM PROPOSITIONS

rbasic :: RandomGen g => g -> String-> Prop
rbasic g x = Basic (r g x)

rprop :: RandomGen g => g -> String -> Prop
rprop g x = r (gens g!!1) [rbasic (gens g!!2) x
                          , Negation (rprop (gens g!!3) x)
                          , Conjunction (rprop (gens g!!4) x) (rprop (gens g!!5) x)
                          , Disjunction (rprop (gens g!!6) x) (rprop (gens g!!7) x)
                          , Conditional (rprop (gens g!!8) x) (rprop (gens g!!9) x)
                          , Biconditional (rprop (gens g!!10) x) (rprop (gens g!!11) x)
                          , rbasic (gens g!!12) x
                          , rbasic (gens g!!13) x
                          , rbasic (gens g!!14) x

                          ]

-- generate a list of random props

rprops :: RandomGen g => g -> String -> [Prop]
rprops g x = rprop g x : rprops g1 x
    where g1 = snd $ next g

-- generate a list of lists consisting of one random prop

uprops :: RandomGen g => g -> String -> [[Prop]]
uprops g x = [rprop g x] : uprops g1 x
    where g1 = snd $ next g

-- generate a list of lists consisting of two random props

dprops :: RandomGen g => g -> String -> [[Prop]]
dprops g x = [rprop g1 x, rprop g2 x] : dprops g3 x
    where g1 = snd $ next g
          g2 = snd $ next g1
          g3 = snd $ next g2

-- generate a list of lists consisting of three random props

tprops :: RandomGen g => g -> String -> [[Prop]]
tprops g x = [rprop g1 x, rprop g2 x, rprop g3 x] : tprops g4 x
    where g1 = snd $ next g
          g2 = snd $ next g1
          g3 = snd $ next g2
          g4 = snd $ next g3

-- generate a list of lists consisting of four random props

qprops :: RandomGen g => g -> String -> [[Prop]]
qprops g x = [rprop g1 x, rprop g2 x, rprop g3 x, rprop g4 x] : qprops g5 x
    where g1 = snd $ next g
          g2 = snd $ next g1
          g3 = snd $ next g2
          g4 = snd $ next g3
          g5 = snd $ next g4



-- FILTERS

anyfilt :: [a -> Bool] -> (a -> Bool)
anyfilt fns el = any (\fn -> fn el) fns

allfilt :: [a -> Bool] -> (a -> Bool)
allfilt fns el = all (\fn -> fn el) fns

-- Syntactic Filters

hasnbinaries :: Int -> Prop -> Bool
hasnbinaries n p = n == (nbinary p)

maxbinaries :: Int -> Prop -> Bool
maxbinaries n p = n >= (nbinary p)

maxbinaries' :: Int -> [Prop] -> Bool
maxbinaries' n ps = all (maxbinaries n) ps

nbinary :: Prop -> Int
nbinary (Basic x) = 0
nbinary (Negation p) = nbinary p
nbinary (Conjunction l r) = 1 + nbinary l + nbinary r
nbinary (Disjunction l r) = 1 + nbinary l + nbinary r
nbinary (Conditional l r) = 1 + nbinary l + nbinary r
nbinary (Biconditional l r) = 1 + nbinary l + nbinary r

hasnbasics :: Int -> Prop -> Bool
hasnbasics n p = n == (nbasic p)

hasnbasics' :: Int -> [Prop] -> Bool
hasnbasics' n ps = and (map (\p -> (n == (nbasic p))) ps)

nbasic :: Prop -> Int
nbasic (Basic x) = 1
nbasic (Negation p) = nbasic p
nbasic (Conjunction l r) = nbasic l + nbasic r
nbasic (Disjunction l r) = nbasic l + nbasic r
nbasic (Conditional l r) = nbasic l + nbasic r
nbasic (Biconditional l r) = nbasic l + nbasic r

hasnnegs :: Int -> Prop -> Bool
hasnnegs n p = n == (nneg p)

nneg :: Prop -> Int
nneg (Basic x) = 0
nneg (Negation p) = 1 + nneg p
nneg (Conjunction l r) = nneg l + nneg r
nneg (Disjunction l r) = nneg l + nneg r
nneg (Conditional l r) = nneg l + nneg r
nneg (Biconditional l r) = nneg l + nneg r

hasnnegsnbins :: Int -> Int -> Prop -> Bool
hasnnegsnbins x y p = x == (nneg p) && y == (nbinary p)