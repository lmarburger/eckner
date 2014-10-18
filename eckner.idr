module Timeseries

%default total

data Time = T Nat | Infinity

instance Eq Time where
  (==) Infinity Infinity = True
  (==) (T l)    (T r)    = l == r
  (==) _        _        = False

instance Ord Time where
  compare  Infinity  Infinity = EQ
  compare  Infinity (T _)     = GT
  compare (T _)      Infinity = LT
  compare (T x)     (T y)     = compare x y

fromTime : Time -> Nat
fromTime Infinity = Z
fromTime (T n)    = n

Value : Type
Value = Float

Observation : Type
Observation = (Time, Value)

Timeseries : Type
Timeseries = List Observation

myT : Timeseries
myT = [(T 1,11), (T 9, 99), (T 3,33), (T 5,55), (T 7,77)]


||| Definition 2.3: Next available observed time.
|||
||| Examples:
|||   next myT (T Z)     --> (T 1, 11.0) : (Time, Float)
|||   next myT (T 4)     --> (T 5, 55.0) : (Time, Float)
|||   next myT (T 5)     --> (T 5, 55.0) : (Time, Float)
|||   next myT Infinity  --> (Infinity, 0.0) : (Time, Float)
next : Timeseries -> Time -> Observation
next [] _ = (T Z, 0)  -- I made this up. :shrug:
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
nextTime [] _ = T Z
nextTime os t = fst $ next os t

||| Definition 2.3: Most recent observed time.
|||
||| Examples:
|||   prev myT (T Z)     --> (T 1, 11.0) : (Time, Float)
|||   prev myT (T 4)     --> (T 3, 33.0) : (Time, Float)
|||   prev myT (T 5)     --> (T 5, 55.0) : (Time, Float)
|||   prev myT Infinity  --> (T 9, 99.0) : (Time, Float)
prev : Timeseries -> Time -> Observation
prev [] _ = (T Z, 0)  -- I made this up. :shrug:
prev os t with (sort $ filter (\o => fst o <= t) os)
  | []      = next os (T Z)
  | (o::os) = last (o::os)

||| Examples:
|||   prevTime myT (T 4)     --> T 3 : Time
|||   prevTime myT (T 5)     --> T 5 : Time
|||   prevTime myT (T 6)     --> T 5 : Time
|||   prevTime myT (T Z)     --> T 1 : Time
|||   prevTime myT Infinity  --> T 9 : Time
prevTime : Timeseries -> Time -> Time
prevTime [] _ = T Z
prevTime os t = fst $ prev os t
