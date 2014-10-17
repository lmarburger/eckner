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
|||   next myT (T 4)     --> T 5 : Time
|||   next myT (T 5)     --> T 5 : Time
|||   next myT (T Z)     --> T 1 : Time
|||   next myT Infinity  --> Infinity : Time
next : Timeseries -> Time -> Time
next [] _ = T Z  -- I made this up. :shrug:
next os t with (sort $ filter (\o => fst o >= t) os)
  | []         = Infinity
  | ((o,_)::_) = o

||| Definition 2.3: Most recent observed time.
|||
||| Examples:
|||   prev myT (T 4)     --> T 3 : Time
|||   prev myT (T 5)     --> T 5 : Time
|||   prev myT (T Z)     --> T 1 : Time
|||   prev myT Infinity  --> T 7 : Time
prev : Timeseries -> Time -> Time
prev [] _ = T Z  -- I made this up. :shrug:
prev os t with (sort $ filter (\o => fst o <= t) os)
  | []      = next os (T Z)
  | (o::os) = fst $ last (o::os)
