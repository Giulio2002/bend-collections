import Base
import ./common.bend as C
import ../../src/containers/types/dynamic_array.bend as E

# Independent model of a bounded growable array: a sequence of items, a
# capacity exponent `depth` (capacity 2^depth) and a fixed exponent bound
# `limit`. Capacity policy: a push into a full array doubles the capacity
# once; reserve(n) takes the least exponent k >= depth with n <= 2^k; clear
# keeps the capacity. Nothing here refers to trees, slots or Base.Array.

type Model<-T: Data> is Data:
  M{limit: Nat, depth: Nat, items: List<&2, T>}

def new(-T: Data) -> Model<T>:
  M{31n, 0n, Nil{}}

def with_limit(-T: Data, +k: Nat) -> Model<T>:
  M{Nat.min(k, 31n), 0n, Nil{}}

def item_result(-T: Data, x: Maybe<&2, T>) -> Result<&2, &2, E.Error, T>:
  match x:
    case None{}:
      Fail{E.IndexOutOfRange{}}
    case Some{v}:
      Done{v}

# Least k >= d with n <= 2^k, searching at most `fuel` doublings.
def fit(fuel: Nat, +d: Nat, +n: Nat) -> Nat:
  match fuel:
    case 0n:
      d
    case 1n+f:
      Bool.pick(Nat, Nat.is_le(n, C.pow2(d)), d, fit(f, 1n+d, n))

def ok_unit() -> Result<&2, &2, E.Error, Unit>:
  Done{Unit{}}

def pop(-T: Data, +l: Nat, +d: Nat, xs: List<&2, T>) -> Model<T> & E.Obs<T>:
  match xs:
    case Nil{}:
      (M{l, d, Nil{}}, E.OItem{Fail{E.EmptyArray{}}})
    case Con{+h, +t}:
      (M{l, d, C.init(T, Con{h, t})}, E.OItem{item_result(T, C.last(T, Con{h, t}))})

def step_parts(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +op: E.Op<T>) -> Model<T> & E.Obs<T>:
  match op:
    case E.Length{}:
      (M{l, d, xs}, E.ONat{C.length(T, xs)})
    case E.Capacity{}:
      (M{l, d, xs}, E.ONat{C.pow2(d)})
    case E.Get{i}:
      (M{l, d, xs}, E.OItem{item_result(T, C.nth(T, xs, i))})
    case E.Set{i, v}:
      Bool.pick(Model<T> & E.Obs<T>, Nat.is_lt(i, C.length(T, xs)),
        (M{l, d, C.update(T, xs, i, v)}, E.OUnit{ok_unit()}),
        (M{l, d, xs}, E.OUnit{Fail{E.IndexOutOfRange{}}}))
    case E.Push{v}:
      Bool.pick(Model<T> & E.Obs<T>, Nat.is_lt(C.length(T, xs), C.pow2(d)),
        (M{l, d, C.snoc(T, xs, v)}, E.OUnit{ok_unit()}),
        Bool.pick(Model<T> & E.Obs<T>, Nat.is_lt(d, l),
          (M{l, 1n+d, C.snoc(T, xs, v)}, E.OUnit{ok_unit()}),
          (M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}})))
    case E.Pop{}:
      pop(T, l, d, xs)
    case E.Reserve{n}:
      Bool.pick(Model<T> & E.Obs<T>, Nat.is_le(n, C.pow2(d)),
        (M{l, d, xs}, E.OUnit{ok_unit()}),
        Bool.pick(Model<T> & E.Obs<T>, Nat.is_le(n, C.pow2(l)),
          (M{l, fit(n, d, n), xs}, E.OUnit{ok_unit()}),
          (M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}})))
    case E.Clear{}:
      (M{l, d, Nil{}}, E.OUnit{ok_unit()})
    case E.ToList{}:
      (M{l, d, xs}, E.OList{xs})

# Every operation: the next model and the observation.
def step(-T: Data, m: Model<T>, op: E.Op<T>) -> Model<T> & E.Obs<T>:
  M{l, d, xs} = m
  step_parts(T, l, d, xs, op)

def cons_obs(-T: Data, o: E.Obs<T>, r: Model<T> & List<&2, E.Obs<T>>) -> Model<T> & List<&2, E.Obs<T>>:
  (m, os) = r
  (m, Con{o, os})

# Arbitrary finite traces: final model and every observation, in order.
def run(-T: Data, ops: List<&2, E.Op<T>>, +m: Model<T>) -> Model<T> & List<&2, E.Obs<T>>:
  match ops:
    case Nil{}:
      (m, Nil{})
    case Con{+op, rest}:
      cons_obs(T, Pair.snd(Model<T>, E.Obs<T>, step(T, m, op)), run(T, rest, Pair.fst(Model<T>, E.Obs<T>, step(T, m, op))))
