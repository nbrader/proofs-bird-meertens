#!/usr/bin/env stack
-- stack --resolver lts-20.5 ghci --package QuickCheck

import Data.List
import Test.QuickCheck

-- Basic operations matching the Coq definitions
(<#>) :: (Ord a, Num a) => a -> a -> a
x <#> y = max 0 (x + y)  -- nonNegPlus

(<|>) :: (Ord a) => a -> a -> a
x <|> y = max x y        -- maximum of two elements

-- nonNegMaximum = maximum (assuming input list is non-empty)
nonNegMaximum :: (Ord a, Num a) => [a] -> a
nonNegMaximum = maximum

-- nonNegSum = fold using nonNegPlus
nonNegSum :: (Ord a, Num a) => [a] -> a
nonNegSum = foldr (<#>) 0

-- Form definitions matching Coq
form5, form6 :: (Ord a, Num a) => [a] -> a
form5 xs = nonNegMaximum (map (nonNegMaximum . map nonNegSum . inits) (tails xs))
form6 xs = nonNegMaximum (map (foldr (<#>) 0) (tails xs))

-- Test cases
testCases :: [[Integer]]
testCases =
  [ [-3, 1, 1]        -- The counterexample from generalised_horners_rule_is_false
  , []                -- Empty list
  , [1]               -- Single element
  , [1, 1]            -- Two positive elements
  , [-1, -1]          -- Two negative elements
  , [0, 1]            -- Start with zero
  , [2, 0]            -- End with zero
  , [1, -2, 3]        -- Mixed positive/negative
  , [-5, 3, 2]        -- Start negative
  , [5, -3, -2]       -- End negative
  , [1, 2, 3, 4, 5]   -- All positive
  , [-1, -2, -3]      -- All negative
  , [0, 0, 0]         -- All zeros
  , [10, -5, 3, -2, 1] -- Longer mixed list
  ]

-- Test function to check if form5 = form6 for specific inputs
testForm5Eq6 :: [Integer] -> (Integer, Integer, Bool)
testForm5Eq6 xs =
  let f5 = form5 xs
      f6 = form6 xs
  in (f5, f6, f5 == f6)

-- Test the specific counterexample
testCounterexample :: IO ()
testCounterexample = do
  let xs = [-3, 1, 1]
  let (f5, f6, eq) = testForm5Eq6 xs
  putStrLn $ "Testing [-3, 1, 1]:"
  putStrLn $ "  form5 [-3, 1, 1] = " ++ show f5
  putStrLn $ "  form6 [-3, 1, 1] = " ++ show f6
  putStrLn $ "  form5 = form6? " ++ show eq

-- Test all predefined cases
testAllCases :: IO ()
testAllCases = do
  putStrLn "Testing form5 vs form6 on various inputs:"
  putStrLn "--------------------------------------------"
  mapM_ testAndPrint testCases
  where
    testAndPrint xs = do
      let (f5, f6, eq) = testForm5Eq6 xs
      putStrLn $ "Input: " ++ show xs
      putStrLn $ "  form5 = " ++ show f5 ++ ", form6 = " ++ show f6 ++ " => Equal: " ++ show eq

-- QuickCheck property to test if form5 = form6 always
prop_form5_eq_form6 :: [Integer] -> Property
prop_form5_eq_form6 xs = not (null xs) ==> form5 xs == form6 xs

-- Test for counterexamples using QuickCheck
findCounterexamples :: IO ()
findCounterexamples = do
  putStrLn "\nSearching for counterexamples with QuickCheck..."
  result <- quickCheckResult prop_form5_eq_form6
  case result of
    Success{} -> putStrLn "No counterexamples found - form5 appears to equal form6"
    Failure{} -> putStrLn "Counterexample found - form5 ≠ form6 for some input"
    _ -> putStrLn "Test inconclusive"

-- Manual verification of the inner difference
testInnerDifference :: IO ()
testInnerDifference = do
  let xs = [-3, 1, 1]
  let innerForm5 = nonNegMaximum (map nonNegSum (inits xs))
  let innerForm6 = foldr (<#>) 0 xs
  putStrLn $ "\nTesting inner difference for [-3, 1, 1]:"
  putStrLn $ "  nonNegMaximum (map nonNegSum (inits [-3, 1, 1])) = " ++ show innerForm5
  putStrLn $ "  foldr (<#>) 0 [-3, 1, 1] = " ++ show innerForm6
  putStrLn $ "  Inner functions equal? " ++ show (innerForm5 == innerForm6)

  -- Show step by step computation
  putStrLn $ "\nStep by step for inner computation:"
  putStrLn $ "  inits [-3, 1, 1] = " ++ show (inits xs)
  putStrLn $ "  map nonNegSum (inits [-3, 1, 1]) = " ++ show (map nonNegSum (inits xs))
  putStrLn $ "  nonNegMaximum [...] = " ++ show innerForm5
  putStrLn $ "  foldr (<#>) 0 [-3, 1, 1] step by step:"
  putStrLn $ "    1 <#> 0 = max 0 (1 + 0) = 1"
  putStrLn $ "    1 <#> 1 = max 0 (1 + 1) = 2"
  putStrLn $ "    (-3) <#> 2 = max 0 (-3 + 2) = 0"
  putStrLn $ "  So foldr (<#>) 0 [-3, 1, 1] = " ++ show innerForm6

main :: IO ()
main = do
  testCounterexample
  putStrLn ""
  testAllCases
  testInnerDifference
  findCounterexamples