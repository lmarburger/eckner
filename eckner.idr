module Timeseries

import Ratio

%default total

data Time = T Integer | Infinity

instance Eq Time where
  (==) Infinity Infinity = True
  (==) (T l)    (T r)    = l == r
  (==) _        _        = False

instance Ord Time where
  compare  Infinity  Infinity = EQ
  compare  Infinity (T _)     = GT
  compare (T _)      Infinity = LT
  compare (T x)     (T y)     = compare x y

Value : Type
Value = Integer

Observation : Type
Observation = (Time, Value)

Timeseries : Type
Timeseries = List Observation

myT : Timeseries
myT = [(T 1,1), (T 9,9), (T 3,3), (T 5,5), (T 7,7)]


||| Definition 2.3: Next available observed time.
|||
||| Examples:
|||   next myT (T Z)     --> (T 1, 11.0) : (Time, Float)
|||   next myT (T 4)     --> (T 5, 55.0) : (Time, Float)
|||   next myT (T 5)     --> (T 5, 55.0) : (Time, Float)
|||   next myT Infinity  --> (Infinity, 0.0) : (Time, Float)
next : Timeseries -> Time -> Observation
next [] _ = (T 0, 0)  -- I made this up. :shrug:
next os t with (sort $ filter (\o => fst o >= t) os)
  | []     = (Infinity, 0)
  | (o::_) = o

||| Examples:
|||   nextTime myT (T 4)     --> T 5 : Time
|||   nextTime myT (T 5)     --> T 5 : Time
|||   nextTime myT (T 6)     --> T 7 : Time
|||   nextTime myT (T Z)     --> T 1 : Time
|||   nextTime myT Infinity  --> Infinity : Time
nextTime : Timeseries -> Time -> Time
nextTime [] _ = T 0
nextTime os t = fst $ next os t

||| Definition 2.3: Most recent observed time.
|||
||| Examples:
|||   prev myT (T Z)     --> (T 1, 11.0) : (Time, Float)
|||   prev myT (T 4)     --> (T 3, 33.0) : (Time, Float)
|||   prev myT (T 5)     --> (T 5, 55.0) : (Time, Float)
|||   prev myT Infinity  --> (T 9, 99.0) : (Time, Float)
prev : Timeseries -> Time -> Observation
prev [] _ = (T 0, 0)  -- I made this up. :shrug:
prev os t with (sort $ filter (\o => fst o <= t) os)
  | []      = next os (T 0)
  | (o::os) = last (o::os)

||| Examples:
|||   prevTime myT (T 4)     --> T 3 : Time
|||   prevTime myT (T 5)     --> T 5 : Time
|||   prevTime myT (T 6)     --> T 5 : Time
|||   prevTime myT (T Z)     --> T 1 : Time
|||   prevTime myT Infinity  --> T 9 : Time
prevTime : Timeseries -> Time -> Time
prevTime [] _ = T 0
prevTime os t = fst $ prev os t

||| Definition 2.4: Last-point sampling scheme. Returns the value for the most
||| recent observed time.
|||
||| Examples:
|||   lastPoint myT (T Z)     --> 11.0 : Float
|||   lastPoint myT (T 4)     --> 33.0 : Float
|||   lastPoint myT (T 5)     --> 55.0 : Float
|||   lastPoint myT Infinity  --> 99.0 : Float
lastPoint : Timeseries -> Time -> Value
lastPoint [] _ = 0
lastPoint os t = snd $ prev os t

||| Definition 2.4: Next-point sampling scheme. Returns the value for the next
||| available observed time.
|||
||| Examples:
|||   nextPoint myT (T Z)     --> 11.0 : Float
|||   nextPoint myT (T 4)     --> 55.0 : Float
|||   nextPoint myT (T 5)     --> 55.0 : Float
|||   nextPoint myT Infinity  --> 0.0 : Float
nextPoint : Timeseries -> Time -> Value
nextPoint [] _ = 0
nextPoint os t = snd $ next os t

mutual

  ||| Definition 2.4: Linear interpolation sampling scheme. Returns the value for
  ||| the linearly interpolated time.
  |||
  ||| Examples:
  |||   linearInerpolation myT (T 0)  --> Pos 1  & Pos 1 : Ratio
  |||   linearInerpolation myT (T 4)  --> Pos 16 & Pos 4 : Ratio
  |||   linearInerpolation myT (T 5)  --> Pos 5  & Pos 1 : Ratio
  |||   linearInerpolation myT (T 6)  --> Pos 24 & Pos 4 : Ratio
  partial linearInerpolation : Timeseries -> Time -> Ratio
  linearInerpolation os t = p + n where
    p = (1 - (wxt os t)) * (fromInt (lastPoint os t))
    n = (wxt os t) * (fromInt (nextPoint os t))

  -- Not handling the Infinity case because I don't know how to write it in a
  -- way that Idris doesn't think it's an infinite loop.
  partial wxt : Timeseries -> Time -> Ratio
  wxt os (T t)    = num & denom where
    num : ZZ
    num = fromInt $ t - (lastPoint os (T t))

    denom : ZZ
    denom = fromInt $ (nextPoint os (T t)) - (lastPoint os (T t))
