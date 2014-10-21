module Ratio

%default total

data Ratio = (&) Integer Integer
infixr 10 &

||| Take the absolute value of a `Ratio`
absRatio : Ratio -> Ratio
absRatio (n & d) = (abs n) & (abs d)

instance Show Ratio where
  show (n & d) = (show n) ++ "/" ++ (show d)


plusRatio : Ratio -> Ratio -> Ratio
plusRatio (n1 & d1) (n2 & d2) = if n1 == 0 || d1 == 0 then (n2 & d2)
                                else if n2 == 0 || d2 == 0 then (n1 & d1)
                                else ((n1 * d2) + (n2 * d1)) & (d1 * d2)

subRatio : Ratio -> Ratio -> Ratio
subRatio (n1 & d1) (n2 & d2) = if n1 == 0 || d1 == 0 then (-n2 & d2)
                               else if n2 == 0 || d2 == 0 then (n1 & d1)
                               else ((n1 * d2) - (n2 * d1)) & (d1 * d2)

multRatio : Ratio -> Ratio -> Ratio
multRatio (n1 & d1) (n2 & d2) = (n1 * n2) & (d1 * d2)

instance Eq Ratio where
  (n1 & d1) == (n2 & d2) = (n1 * d2) == (n2 * d1)

instance Ord Ratio where
  compare (n1 & d1) (n2 & d2) = compare (n1 * d2) (n2 * d1)

fromInt : Integer -> Ratio
fromInt n = n & 1

instance Num Ratio where
  (+) = plusRatio
  (-) = subRatio
  (*) = multRatio
  abs = absRatio
  fromInteger = fromInt
