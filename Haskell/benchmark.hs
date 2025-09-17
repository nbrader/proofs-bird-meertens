#!/usr/bin/env stack
-- stack --resolver lts-20.5 script --package QuickCheck --package criterion --package deepseq

-- run with "stack benchmark.hs"

import Criterion.Main
import Data.List
import Control.DeepSeq (NFData)

-- STANDARD tails
-- benchmarking tails/Prelude tails
-- time                 1.716 ms   (1.637 ms .. 1.786 ms)

-- Custom implementations for tails
tails' :: [a] -> [[a]]
tails' [] = [[]]
tails' xs@(_:xs') = xs : tails' xs'
-- benchmarking tails/tails'
-- time                 1.928 ms   (1.845 ms .. 2.012 ms)

tails'' :: [a] -> [[a]]
tails'' xs = if null xs then [[]] else xs : tails' (tail xs)
-- benchmarking tails/tails''
-- time                 2.021 ms   (1.941 ms .. 2.096 ms)

tails''' :: [a] -> [[a]]
tails''' = (++[[]]) . unfoldr (\xs -> if null xs then Nothing else Just (xs, tail xs))
-- benchmarking tails/tails'''
-- time                 2.116 ms   (2.030 ms .. 2.205 ms)


-- STANDARD inits
-- benchmarking inits/Prelude inits
-- time                 4.386 ms   (4.317 ms .. 4.448 ms)

-- Custom implementations for inits
inits' :: [a] -> [[a]]
inits' [] = [[]]
inits' xs = inits' (init xs) ++ [xs]
-- benchmarking inits/inits'
-- time                 43.34 ms   (42.50 ms .. 44.07 ms)

inits'' :: [a] -> [[a]]
inits'' xs = go xs []
  where go xs acc = if null xs then (xs:acc) else let new = init xs in go new (xs:acc)
-- benchmarking inits/inits''
-- time                 28.66 ms   (27.77 ms .. 29.63 ms)

inits''' :: [a] -> [[a]]
inits''' = ([]:) . reverse . unfoldr (\xs -> if null xs then Nothing else Just (xs, init xs))
-- benchmarking inits/inits'''
-- time                 28.29 ms   (27.17 ms .. 29.05 ms)


-- Main function setting up the benchmark
main :: IO ()
main = defaultMain [
  bgroup "tails"
    [ bench "Prelude tails" $ nf tails exampleList
    , bench "tails'"        $ nf tails' exampleList
    , bench "tails''"       $ nf tails'' exampleList
    , bench "tails'''"      $ nf tails''' exampleList
    ],
  bgroup "inits"
    [ bench "Prelude inits" $ nf inits exampleList
    , bench "inits'"        $ nf inits' exampleList
    , bench "inits''"       $ nf inits'' exampleList
    , bench "inits'''"      $ nf inits''' exampleList
    ]
  ]
  where
    exampleList = [1..1000] :: [Int] -- You can adjust the size and contents of the list to see how it impacts performance

