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

||| Returns an Observation at Time `t` from the Timeseries. Returns Nothing if
||| no sampled time matches the given time.
observation : Timeseries -> Time -> Maybe Observation
observation []          t = Nothing
observation ((s,v)::os) t = if t == s then Just (s,v) else observation os t

||| (T t) isn't proven to be structurally smaller than (T (S t)) so prev as a
||| recrusive function over Time isn't known to be total. Delegate to prevNat
||| which recurses over Nat.
prevNat : Timeseries -> Nat -> Time
prevNat []          _     = T Z
prevNat ((s,v)::os) Z     = s
prevNat os          (S n) with (observation os (T (S n)))
  | Just (s,v) = s
  | Nothing    = prevNat os n

||| Returns the most recent observed Time in the Timeseries.
|||
||| Example:
|||   prev myT (T 5)  --> T 5 : Time
|||   prev myT (T 4)  --> T 3 : Time
|||   prev myT (T 0)  --> T 1 : Time
prev : Timeseries -> Time -> Time
prev os Infinity = T Z  -- TODO: Return last observed time
prev os (T t)    = prevNat os t


||| Need a way to get around the fact that this function counts up until the
||| given time is greater than the last observed time. For now it warns about
||| this function not being total.
|||   timeseries.idr:56:1:
|||   Timeseries.nextNat is possibly not total due to: with block in Timeseries.nextNat
nextNat : Timeseries -> Nat -> Time
nextNat []          _ = T Z
nextNat ((s,v)::os) Z = s
nextNat (o::os) n with (observation (o::os) (T n))
  | Just (s,v) = s
  | Nothing    = if n < lastObserved (o::os) then nextNat (o::os) (S n) else Infinity
  where
    lastObserved : Timeseries -> Nat
    lastObserved []      = Z
    lastObserved (o::os) = fromTime $ fst $ last (o::os)

||| Example:
|||   next myT (T 0)  --> T 1 : Time
|||   next myT (T 6)  --> T 7 : Time
|||   next myT (T 7)  --> T 7 : Time
|||   next myT (T 8)  --> Infinity : Time
next : Timeseries -> Time -> Time
next os Infinity = T Z
next os (T t)    = nextNat os t


