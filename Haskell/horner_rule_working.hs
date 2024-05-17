#!/usr/bin/env stack
-- stack --resolver lts-20.5 ghci

import Data.List

nonNegPlus :: (Ord a, Num a) => a -> a -> a
nonNegPlus x y = max 0 (x + y)

nonNegSum :: (Ord a, Num a) => [a] -> a
nonNegSum = foldr nonNegPlus 0

maxNonNegSumInits :: [Integer] -> Integer
maxNonNegSumInits = maximum . map nonNegSum . inits

maxNonNegSumInitsInd :: [Integer] -> Integer
maxNonNegSumInitsInd [] = 0
maxNonNegSumInitsInd (x:xs) = x `nonNegPlus` maxNonNegSumInitsInd xs

maxNonNegSumInitsInd' :: [Integer] -> Integer
maxNonNegSumInitsInd' xs = foldr nonNegPlus 0 xs

inits' :: [Integer] -> [[Integer]]
inits' [] = [[]]
inits' (x:xs) = [] : map (x:) (inits' xs)

inits'' :: [Integer] -> [[Integer]]
inits'' = foldr (\x -> ([]:) . map (x:)) [[]]

tails' :: [Integer] -> [[Integer]]
tails' [] = [[]]
tails' (x:xs) = (x:xs) : tails' xs

tails'' :: [Integer] -> [[Integer]]
tails'' = foldr (\x (xs:xss) -> (x:xs) : (xs:xss)) [[]]