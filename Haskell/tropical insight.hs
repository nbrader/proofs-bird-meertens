import Data.List

data ExtZ = NegInf | Z Integer

instance Show ExtZ where
  show (NegInf) = "NegInf"
  show (Z x) = "Z " ++ show x

instance Eq ExtZ where
  NegInf == NegInf = True
  (Z x)  == NegInf = False
  NegInf == (Z y)  = False
  (Z x)  == (Z y)  = x == y

instance Ord ExtZ where
  compare NegInf NegInf = EQ
  compare (Z x)  NegInf = GT
  compare NegInf (Z y)  = LT
  compare (Z x)  (Z y)  = compare x y

instance Num ExtZ where
  NegInf + NegInf = NegInf
  (Z x)  + NegInf = NegInf
  NegInf + (Z y)  = NegInf
  (Z x)  + (Z y)  = Z (x + y)
  
  fromInteger = Z
  
  (*) = undefined
  negate = undefined
  abs = undefined
  signum = undefined

main :: IO ()
main = do
  let xs = [Z (-10), Z (1), Z (10), Z (-10)]
  putStrLn $ "nonNegSum xs = maximum (map nonNegSum (inits xs))"
  putStrLn $ "nonNegSum xs = maximum (map nonNegSum " ++ show (inits xs) ++ ")"
  putStrLn $ "nonNegSum xs = maximum (" ++ show (map nonNegSum (inits xs)) ++ ")"
  putStrLn $ "nonNegSum xs = " ++ show (maximum (map nonNegSum (inits xs))) ++ ")"
  putStrLn $ show (nonNegSum xs) ++ " = " ++ show (maximum (map nonNegSum (inits xs)))
  putStrLn $ ""
  putStrLn $ "nonNegSum xs = maximum (map sum (inits xs))"
  putStrLn $ "nonNegSum xs = maximum (map nonNegSum " ++ show (inits xs) ++ ")"
  putStrLn $ "nonNegSum xs = maximum (" ++ show (map sum (inits xs)) ++ ")"
  putStrLn $ "nonNegSum xs = " ++ show (maximum (map sum (inits xs))) ++ ")"
  putStrLn $ show (nonNegSum xs) ++ " = " ++ show (maximum (map sum (inits xs)))

nonNegPlus' x y = max (x + y) 0
nonNegPlus NegInf NegInf = Z 0
nonNegPlus (Z x)  NegInf = Z 0
nonNegPlus NegInf (Z y)  = Z 0
nonNegPlus (Z x)  (Z y)  = Z (nonNegPlus' x y)
nonNegSum = foldr nonNegPlus NegInf