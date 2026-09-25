import Base
import ../lib/common.bend as C
import ../../src/containers/types/dynamic_array.bend as E
import ../lib/sequence.bend as V

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

# ---- contract (SPARK formal containers) ----
# Each `<Subprogram>.<clause>` definition below states one Post clause of
# that SPARK subprogram, as a proposition on this model; the table names the
# clauses. proofs/containers/dynamic_array/ proves every clause under its clause name,
# and its `impl` lemma carries them to the implementation.
#
# Contracts of the dynamic array in the style of SPARK's formal vectors
# (SPARKlib src/spark-containers-formal-vectors.ads, AdaCore/SPARKlib
# 46ec319; the model predicates are in spec/lib/sequence.bend). Each
# lemma is one Post clause, stated over the model step step; `impl`
# (P.step_refines) makes the implementation's step, read back through its
# abstraction, equal to step on every good array, so every clause holds
# for DA.step as well.
#
#   SPARK subprogram (.ads line)   ours          clauses
#   Length (284)                   length        length_result, length_frame
#   Capacity (322)                 capacity      capacity_result, capacity_frame
#   Empty_Vector (292)             new           new_empty, new_capacity, new_impl
#                                  with_limit    with_limit_empty, with_limit_impl
#   Reserve_Capacity (328)         reserve       reserve_equal
#   Clear (341)                    clear         clear_length, clear_capacity
#   Element (373)                  get           get_element, get_frame, get_outside
#   First_Element (913)            get 0         first_element
#   Last_Element (923)             get (len-1)   last_element
#   Replace_Element (384)          set           set_length, set_element,
#                                                set_except, set_outside
#   Append (706)                   push          push_length, push_prefix,
#                                                push_element, push_full
#   Delete_Last (866)              pop           pop_length, pop_prefix,
#                                                pop_result, pop_empty
#   iteration (Iter_Model, 1193)   to_list       to_list_model, to_list_frame
#   implementation                 DA.step       impl
# Not in this API (no such operation): Is_Empty ("=" Length 0), "=",
# To_Vector, Assign/Copy/Move (values are persistent: a copy is the value
# itself), Constant_Reference/Reference, Insert/Insert_Vector, Prepend*,
# Append_Vector, Append with Count, Delete (at an index), Delete_First,
# Delete_Last with Count, Reverse_Elements, Swap, Find_Index,
# Reverse_Find_Index, Contains, Has_Element (indices are plain Nat).
# SPARK's Pre (Index in range, Length < Capacity) is a defensive check;
# here the operation returns an error value and changes nothing, which the
# *_outside, *_full and *_empty lemmas state.

def items(-T: Data, m: Model<T>) -> List<&2, T>:
  match m:
    case M{l, d, xs}:
      xs

def depth(-T: Data, m: Model<T>) -> Nat:
  match m:
    case M{l, d, xs}:
      d

def nx(-T: Data, +m: Model<T>, +op: E.Op<T>) -> Model<T>:
  Pair.fst(Model<T>, E.Obs<T>, step(T, m, op))

def ob(-T: Data, +m: Model<T>, +op: E.Op<T>) -> E.Obs<T>:
  Pair.snd(Model<T>, E.Obs<T>, step(T, m, op))

# ---- Append: Length + 1, Equal_Prefix (Model'Old, Model), Element (Last_Index'Old + 1) = New_Item ----
# room: SPARK's Pre Length < Capacity; here the array doubles once when
# full and below its limit, so room is Length < 2^depth or depth < limit
def room(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>) -> Bool:
  Bool.or(Nat.is_lt(C.length(T, xs), C.pow2(d)), Nat.is_lt(d, l))

# Length (284)
def Length.length_result(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>) -> Type:
  {ob(T, M{l, d, xs}, E.Length{}) == E.ONat{C.length(T, xs)} : E.Obs<T>}

# Length (284)
def Length.length_frame(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>) -> Type:
  {nx(T, M{l, d, xs}, E.Length{}) == M{l, d, xs} : Model<T>}

# Capacity (322)
def Capacity.capacity_result(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>) -> Type:
  {ob(T, M{l, d, xs}, E.Capacity{}) == E.ONat{C.pow2(d)} : E.Obs<T>}

# Capacity (322)
def Capacity.capacity_frame(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>) -> Type:
  {nx(T, M{l, d, xs}, E.Capacity{}) == M{l, d, xs} : Model<T>}

# iteration (Iter_Model, 1193)
def Iteration.to_list_model(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>) -> Type:
  {ob(T, M{l, d, xs}, E.ToList{}) == E.OList{xs} : E.Obs<T>}

# iteration (Iter_Model, 1193)
def Iteration.to_list_frame(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>) -> Type:
  {nx(T, M{l, d, xs}, E.ToList{}) == M{l, d, xs} : Model<T>}

# Empty_Vector (292)
def Empty_Vector.new_empty(-T: Data) -> Type:
  {C.length(T, items(T, new(T))) == 0n : Nat}

# Empty_Vector (292)
def Empty_Vector.new_capacity(-T: Data) -> Type:
  {C.pow2(depth(T, new(T))) == 1n : Nat}

# Empty_Vector (292)
def Empty_Vector.with_limit_empty(-T: Data, +k: Nat) -> Type:
  {C.length(T, items(T, with_limit(T, k))) == 0n : Nat}

# Reserve_Capacity (328)
def Reserve_Capacity.reserve_equal(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +n: Nat) -> Type:
  {items(T, nx(T, M{l, d, xs}, E.Reserve{n})) == xs : List<&2, T>}

# Clear (341)
def Clear.clear_length(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>) -> Type:
  {C.length(T, items(T, nx(T, M{l, d, xs}, E.Clear{}))) == 0n : Nat}

# Clear (341)
def Clear.clear_capacity(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>) -> Type:
  {depth(T, nx(T, M{l, d, xs}, E.Clear{})) == d : Nat}

# Element (373)
def Element.get_element(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +i: Nat, +v: T, +h: {C.nth(T, xs, i) == Some{v} : Maybe<&2, T>}) -> Type:
  {ob(T, M{l, d, xs}, E.Get{i}) == E.OItem{Done{v}} : E.Obs<T>}

# Element (373)
def Element.get_frame(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +i: Nat) -> Type:
  {nx(T, M{l, d, xs}, E.Get{i}) == M{l, d, xs} : Model<T>}

# Element (373)
def Element.get_outside(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +i: Nat, +h: {Nat.is_le(C.length(T, xs), i) == True{} : Bool}) -> Type:
  {ob(T, M{l, d, xs}, E.Get{i}) == E.OItem{Fail{E.IndexOutOfRange{}}} : E.Obs<T>}

# First_Element (913)
def First_Element.first_element(-T: Data, +l: Nat, +d: Nat, +h: T, +t: List<&2, T>) -> Type:
  {ob(T, M{l, d, Con{h, t}}, E.Get{0n}) == E.OItem{Done{h}} : E.Obs<T>}

# Last_Element (923)
def Last_Element.last_element(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>) -> Type:
  {ob(T, M{l, d, xs}, E.Get{Nat.sub(C.length(T, xs), 1n)}) == E.OItem{item_result(T, V.last_elem(T, xs))} : E.Obs<T>}

# Replace_Element (384)
def Replace_Element.set_length(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +i: Nat, +v: T, +h: {Nat.is_lt(i, C.length(T, xs)) == True{} : Bool}) -> Type:
  {C.length(T, items(T, nx(T, M{l, d, xs}, E.Set{i, v}))) == C.length(T, xs) : Nat}

# Replace_Element (384)
def Replace_Element.set_element(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +i: Nat, +v: T, +h: {Nat.is_lt(i, C.length(T, xs)) == True{} : Bool}) -> Type:
  {C.nth(T, items(T, nx(T, M{l, d, xs}, E.Set{i, v})), i) == Some{v} : Maybe<&2, T>}

# Replace_Element (384)
def Replace_Element.set_except(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +i: Nat, +v: T, +h: {Nat.is_lt(i, C.length(T, xs)) == True{} : Bool}) -> Type:
  V.EqualExcept(T, xs, items(T, nx(T, M{l, d, xs}, E.Set{i, v})), i)

# Replace_Element (384)
def Replace_Element.set_outside(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +i: Nat, +v: T, +h: {Nat.is_lt(i, C.length(T, xs)) == False{} : Bool}) -> Type:
  {step(T, M{l, d, xs}, E.Set{i, v}) == (M{l, d, xs}, E.OUnit{Fail{E.IndexOutOfRange{}}}) : Model<T> & E.Obs<T>}

# Append (706)
def Append.push_length(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +v: T, +hr: {room(T, l, d, xs) == True{} : Bool}) -> Type:
  {C.length(T, items(T, nx(T, M{l, d, xs}, E.Push{v}))) == 1n+C.length(T, xs) : Nat}

# Append (706)
def Append.push_prefix(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +v: T, +hr: {room(T, l, d, xs) == True{} : Bool}) -> Type:
  V.EqualPrefix(T, xs, items(T, nx(T, M{l, d, xs}, E.Push{v})))

# Append (706)
def Append.push_element(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +v: T, +hr: {room(T, l, d, xs) == True{} : Bool}) -> Type:
  {C.nth(T, items(T, nx(T, M{l, d, xs}, E.Push{v})), C.length(T, xs)) == Some{v} : Maybe<&2, T>}

# Append (706)
def Append.push_full(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +v: T, +h1: {Nat.is_lt(C.length(T, xs), C.pow2(d)) == False{} : Bool}, +h2: {Nat.is_lt(d, l) == False{} : Bool}) -> Type:
  {step(T, M{l, d, xs}, E.Push{v}) == (M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}) : Model<T> & E.Obs<T>}

# Delete_Last (866)
def Delete_Last.pop_length(-T: Data, +l: Nat, +d: Nat, +h: T, +t: List<&2, T>) -> Type:
  {C.length(T, items(T, nx(T, M{l, d, Con{h, t}}, E.Pop{}))) == C.length(T, t) : Nat}

# Delete_Last (866)
def Delete_Last.pop_prefix(-T: Data, +l: Nat, +d: Nat, +h: T, +t: List<&2, T>) -> Type:
  V.EqualPrefix(T, items(T, nx(T, M{l, d, Con{h, t}}, E.Pop{})), Con{h, t})

# Delete_Last (866)
def Delete_Last.pop_result(-T: Data, +l: Nat, +d: Nat, +h: T, +t: List<&2, T>) -> Type:
  {ob(T, M{l, d, Con{h, t}}, E.Pop{}) == E.OItem{item_result(T, V.last_elem(T, Con{h, t}))} : E.Obs<T>}

# Delete_Last (866)
def Delete_Last.pop_empty(-T: Data, +l: Nat, +d: Nat) -> Type:
  {step(T, M{l, d, Nil{}}, E.Pop{}) == (M{l, d, Nil{}}, E.OItem{Fail{E.EmptyArray{}}}) : Model<T> & E.Obs<T>}
