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

-- Assumed to be sorted by Time. Should likely be a SortedSet not List.
Timeseries : Type
Timeseries = List Observation

myT : Timeseries
myT = [(T 1,11), (T 3,33), (T 5,55), (T 7,77)]

mutual
  prev : Timeseries -> Time -> Time
  prev [] _ = T Z  -- I made this up. :shrug:
  prev os t with (filter (\o => fst o <= t) os)
    | []      = next os (T Z)
    | (o::os) = fst $ last (o::os)

  next : Timeseries -> Time -> Time
  next [] _ = T Z  -- I made this up. :shrug:
  next os t with (filter (\o => fst o >= t) os)
    | []         = Infinity
    | ((o,_)::_) = o

-- Examples:
--   prev myT (T 4)     --> T 3 : Time
--   next myT (T 4)     --> T 5 : Time
--   prev myT (T 5)     --> T 5 : Time
--   next myT (T 5)     --> T 5 : Time
--   prev myT (T Z)     --> T 1 : Time
--   next myT (T Z)     --> T 1 : Time
--   prev myT Infinity  --> T 7 : Time
--   next myT Infinity  --> Infinity : Time
