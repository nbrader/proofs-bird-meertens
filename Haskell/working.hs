#!/usr/bin/env stack
-- stack --resolver lts-20.5 ghci --package QuickCheck

import Test.QuickCheck
import Data.List

-- Custom implementations
tails' :: [a] -> [[a]]
tails' [] = [[]]  -- The tails of an empty list is a list containing the empty list.
tails' xs@(_:xs') = xs : tails' xs'

tails'' :: [a] -> [[a]]
tails'' xs = if null xs then [[]] else xs : tails' (tail xs)

tails''' :: [a] -> [[a]]
tails''' = (++[[]]) . unfoldr (\xs -> if null xs then Nothing else Just (xs, tail xs))

init' :: [a] -> Maybe [a]
init' [] = Nothing  -- Empty list case
init' [x] = Just []  -- Single element list case
init' (x:xs) =
  case init' xs of
    Nothing -> Just []  -- This case should not happen in valid inputs
    Just xs' -> Just $ x:xs'

inits' :: [a] -> [[a]]
inits' [] = [[]]  -- The inits of an empty list is a list containing the empty list.
inits' xs = inits' (init xs) ++ [xs]

inits'' :: [a] -> [[a]]
inits'' xs = go xs []
  where go xs acc = if null xs then (xs:acc) else let new = init xs in go new (xs:acc)

inits''' :: [a] -> [[a]]
inits''' = ([]:) . reverse . unfoldr (\xs -> if null xs then Nothing else Just (xs, init xs))

-- QuickCheck properties to compare default and custom implementations
prop_tails :: [Int] -> Bool
prop_tails xs = tails xs == tails' xs && tails xs == tails'' xs && tails xs == tails''' xs

prop_inits :: [Int] -> Bool
prop_inits xs = inits xs == inits' xs && inits xs == inits'' xs && inits xs == inits''' xs

main :: IO ()
main = do
  putStrLn "Testing tails implementations:"
  quickCheck prop_tails
  putStrLn "Testing inits implementations:"
  quickCheck prop_inits
