#!/usr/bin/env stack
-- stack --resolver lts-20.5 ghci --package QuickCheck

import Data.List
import Test.QuickCheck

segs :: [a] -> [[a]]
segs = concat . map inits . tails

form1, form2, form3, form4, form5, form6, form7, form8 :: (Ord a, Num a) => [a] -> a
form1 = maximum . map sum . segs
form2 = maximum . map sum . concat . map inits . tails
form3 = maximum . concat . map (map sum) . map inits . tails
form4 = maximum . map maximum . map (map sum) . map inits . tails
form5 = maximum . map (maximum . map sum . inits) . tails
form6 = maximum . map (foldr (<#>) 0) . tails
form7 = maximum . scanr (<#>) 0
form8 = fst . foldr (<.>) (0,0)

x <#> y = (x + y) <|> 0
x <.> (u,v) = let w = (v+x) <|> 0 in (u <|> w, w)
x <|> y = max x y

-- Custom generator for lists with at least one negative and one non-negative
listGen :: Gen [Integer]
listGen = do
  pos <- listOf1 (arbitrary `suchThat` (>= 0))
  neg <- listOf1 (arbitrary `suchThat` (< 0))
  rest <- listOf arbitrary
  shuffle (pos ++ neg ++ rest)

-- QuickCheck property to compare all forms
prop_sameResults :: [Integer] -> Property
prop_sameResults xs = (not . null $ xs) && any (<0) xs && any (>=0) xs ==> all (== head results) results
  where results = [form1 xs, form2 xs, form3 xs, form4 xs, form5 xs, form6 xs, form7 xs, form8 xs]

-- Run QuickCheck
main :: IO ()
main = quickCheck (forAll listGen prop_sameResults)

eq2Form1 x xs = maximum (map (+) (inits (x : xs)))
eq2Form2 x xs = x + foldr (+) 0 xs

horners1, horners2 :: [Integer] -> Integer
horners1 = maximum . map sum . inits
horners2 = foldr (+) 0

test1 xs = maximum (map sum (inits (xs)))
test2 xs = sum xs