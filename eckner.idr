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
Value = Int

Observation : Type
Observation = (Time, Value)

Timeseries : Type
Timeseries = List Observation

myT : Timeseries
myT = [(T 1,11), (T 9, 99), (T 3,33), (T 5,55), (T 7,77)]


||| Definition 2.3: Next available observed time.
|||
||| Examples:
|||   nextTime myT (T 4)     --> T 5 : Time
|||   nextTime myT (T 5)     --> T 5 : Time
|||   nextTime myT (T Z)     --> T 1 : Time
|||   nextTime myT Infinity  --> Infinity : Time
nextTime : Timeseries -> Time -> Time
nextTime [] _ = T Z  -- I made this up. :shrug:
nextTime os t with (sort $ filter (\o => fst o >= t) os)
  | []         = Infinity
  | ((o,_)::_) = o

||| Definition 2.3: Most recent observed time.
|||
||| Examples:
|||   prevTime myT (T 4)     --> T 3 : Time
|||   prevTime myT (T 5)     --> T 5 : Time
|||   prevTime myT (T Z)     --> T 1 : Time
|||   prevTime myT Infinity  --> T 7 : Time
prevTime : Timeseries -> Time -> Time
prevTime [] _ = T Z  -- I made this up. :shrug:
prevTime os t with (sort $ filter (\o => fst o <= t) os)
  | []      = nextTime os (T Z)
  | (o::os) = fst $ last (o::os)
