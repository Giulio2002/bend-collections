import Base
import ../lib/common.bend as C
import ../../src/containers/types/deque.bend as E
import ../lib/sequence.bend as V

# Independent model: a deque is the finite sequence of its elements, front
# first. Nothing here refers to the two-list representation.

def item(-T: Data, x: Maybe<&2, T>) -> Result<&2, &2, E.Error, T>:
  match x:
    case None{}:
      Fail{E.EmptyDeque{}}
    case Some{v}:
      Done{v}

def pop_front(-T: Data, xs: List<&2, T>) -> List<&2, T> & E.Obs<T>:
  match xs:
    case Nil{}:
      (Nil{}, E.OItem{Fail{E.EmptyDeque{}}})
    case Con{h, t}:
      (t, E.OItem{Done{h}})

def pop_back(-T: Data, xs: List<&2, T>) -> List<&2, T> & E.Obs<T>:
  match xs:
    case Nil{}:
      (Nil{}, E.OItem{Fail{E.EmptyDeque{}}})
    case Con{+h, +t}:
      (C.init(T, Con{h, t}), E.OItem{item(T, C.last(T, Con{h, t}))})

def step(-T: Data, +xs: List<&2, T>, op: E.Op<T>) -> List<&2, T> & E.Obs<T>:
  match op:
    case E.Length{}:
      (xs, E.ONat{C.length(T, xs)})
    case E.PushFront{x}:
      (Con{x, xs}, E.OUnit{})
    case E.PushBack{x}:
      (C.snoc(T, xs, x), E.OUnit{})
    case E.PopFront{}:
      pop_front(T, xs)
    case E.PopBack{}:
      pop_back(T, xs)
    case E.PeekFront{}:
      (xs, E.OItem{item(T, C.head(T, xs))})
    case E.PeekBack{}:
      (xs, E.OItem{item(T, C.last(T, xs))})
    case E.ToList{}:
      (xs, E.OList{xs})

def cons_obs(-T: Data, o: E.Obs<T>, r: List<&2, T> & List<&2, E.Obs<T>>) -> List<&2, T> & List<&2, E.Obs<T>>:
  (m, os) = r
  (m, Con{o, os})

def run(-T: Data, ops: List<&2, E.Op<T>>, +xs: List<&2, T>) -> List<&2, T> & List<&2, E.Obs<T>>:
  match ops:
    case Nil{}:
      (xs, Nil{})
    case Con{+op, rest}:
      cons_obs(T, Pair.snd(List<&2, T>, E.Obs<T>, step(T, xs, op)), run(T, rest, Pair.fst(List<&2, T>, E.Obs<T>, step(T, xs, op))))

# ---- contract (SPARK formal containers) ----
# Each `<Subprogram>.<clause>` definition below states one Post clause of
# that SPARK subprogram, as a proposition on this model; the table names the
# clauses. proofs/containers/deque/ proves every clause under its clause name,
# and its `impl` lemma carries them to the implementation.
#
# Contracts of the deque in the style of SPARK's formal vectors
# (SPARKlib src/spark-containers-formal-vectors.ads, AdaCore/SPARKlib
# 46ec319; model predicates in spec/lib/sequence.bend). The model is the
# sequence front first. Each lemma is one Post clause of step; `impl`
# (via P.step_ok) carries every clause to the implementation: DQ.step on
# the deque of a shadow lands on the deque of a shadow whose model
# satisfies it.
#
#   SPARK subprogram (.ads line)   ours        clauses
#   Length (284)                   length      length_result, length_frame
#   Empty_Vector (292)             new         new_empty, new_impl
#   Prepend (624)                  push_front  push_front_length, push_front_first, push_front_shifted
#   Append (706)                   push_back   push_back_length, push_back_prefix, push_back_element
#   Delete_First (825)             pop_front   pop_front_length, pop_front_shifted,
#                                              pop_front_result, pop_front_empty
#   Delete_Last (866)              pop_back    pop_back_length, pop_back_prefix,
#                                              pop_back_result, pop_back_empty
#   First_Element (913)            peek_front  peek_front_first, peek_front_frame, peek_front_empty
#   Last_Element (923)             peek_back   peek_back_last, peek_back_frame, peek_back_empty
#   iteration (Iter_Model, 1193)   to_list     to_list_model, to_list_frame
#   implementation                 DQ.step     impl
# Not in this API: Capacity/Reserve_Capacity (unbounded), Is_Empty, Clear,
# "=", To_Vector, Assign/Copy/Move, Element at an index, Replace_Element,
# Reference, Insert*, Prepend/Append with Count or a vector, Delete (at an
# index or a count), Reverse_Elements, Swap, Find_Index, Reverse_Find_Index,
# Contains, Has_Element. SPARK's Pre (not Is_Empty) is a defensive check:
# on an empty deque pops and peeks return EmptyDeque and change nothing.

def nx(-T: Data, +xs: List<&2, T>, +op: E.Op<T>) -> List<&2, T>:
  Pair.fst(List<&2, T>, E.Obs<T>, step(T, xs, op))

def ob(-T: Data, +xs: List<&2, T>, +op: E.Op<T>) -> E.Obs<T>:
  Pair.snd(List<&2, T>, E.Obs<T>, step(T, xs, op))

# Length (284)
def Length.length_result(-T: Data, +xs: List<&2, T>) -> Type:
  {ob(T, xs, E.Length{}) == E.ONat{C.length(T, xs)} : E.Obs<T>}

# Length (284)
def Length.length_frame(-T: Data, +xs: List<&2, T>) -> Type:
  {nx(T, xs, E.Length{}) == xs : List<&2, T>}

# iteration (Iter_Model, 1193)
def Iteration.to_list_model(-T: Data, +xs: List<&2, T>) -> Type:
  {ob(T, xs, E.ToList{}) == E.OList{xs} : E.Obs<T>}

# iteration (Iter_Model, 1193)
def Iteration.to_list_frame(-T: Data, +xs: List<&2, T>) -> Type:
  {nx(T, xs, E.ToList{}) == xs : List<&2, T>}

# Prepend (624)
def Prepend.push_front_length(-T: Data, +xs: List<&2, T>, +v: T) -> Type:
  {C.length(T, nx(T, xs, E.PushFront{v})) == 1n+C.length(T, xs) : Nat}

# Prepend (624)
def Prepend.push_front_first(-T: Data, +xs: List<&2, T>, +v: T) -> Type:
  {C.nth(T, nx(T, xs, E.PushFront{v}), 0n) == Some{v} : Maybe<&2, T>}

# Prepend (624)
def Prepend.push_front_shifted(-T: Data, +xs: List<&2, T>, +v: T) -> Type:
  V.RangeShifted(T, xs, nx(T, xs, E.PushFront{v}), 0n, C.length(T, xs), 1n)

# Append (706)
def Append.push_back_length(-T: Data, +xs: List<&2, T>, +v: T) -> Type:
  {C.length(T, nx(T, xs, E.PushBack{v})) == 1n+C.length(T, xs) : Nat}

# Append (706)
def Append.push_back_prefix(-T: Data, +xs: List<&2, T>, +v: T) -> Type:
  V.EqualPrefix(T, xs, nx(T, xs, E.PushBack{v}))

# Append (706)
def Append.push_back_element(-T: Data, +xs: List<&2, T>, +v: T) -> Type:
  {C.nth(T, nx(T, xs, E.PushBack{v}), C.length(T, xs)) == Some{v} : Maybe<&2, T>}

# Delete_First (825)
def Delete_First.pop_front_length(-T: Data, +h: T, +t: List<&2, T>) -> Type:
  {1n+C.length(T, nx(T, Con{h, t}, E.PopFront{})) == C.length(T, Con{h, t}) : Nat}

# Delete_First (825)
def Delete_First.pop_front_shifted(-T: Data, +h: T, +t: List<&2, T>) -> Type:
  V.RangeShifted(T, nx(T, Con{h, t}, E.PopFront{}), Con{h, t}, 0n, C.length(T, nx(T, Con{h, t}, E.PopFront{})), 1n)

# Delete_First (825)
def Delete_First.pop_front_result(-T: Data, +h: T, +t: List<&2, T>) -> Type:
  {ob(T, Con{h, t}, E.PopFront{}) == E.OItem{Done{h}} : E.Obs<T>}

# Delete_First (825)
def Delete_First.pop_front_empty(-T: Data) -> Type:
  {step(T, Nil{}, E.PopFront{}) == (Nil{}, E.OItem{Fail{E.EmptyDeque{}}}) : List<&2, T> & E.Obs<T>}

# Delete_Last (866)
def Delete_Last.pop_back_length(-T: Data, +h: T, +t: List<&2, T>) -> Type:
  {C.length(T, nx(T, Con{h, t}, E.PopBack{})) == C.length(T, t) : Nat}

# Delete_Last (866)
def Delete_Last.pop_back_prefix(-T: Data, +h: T, +t: List<&2, T>) -> Type:
  V.EqualPrefix(T, nx(T, Con{h, t}, E.PopBack{}), Con{h, t})

# Delete_Last (866)
def Delete_Last.pop_back_result(-T: Data, +h: T, +t: List<&2, T>) -> Type:
  {ob(T, Con{h, t}, E.PopBack{}) == E.OItem{item(T, V.last_elem(T, Con{h, t}))} : E.Obs<T>}

# Delete_Last (866)
def Delete_Last.pop_back_empty(-T: Data) -> Type:
  {step(T, Nil{}, E.PopBack{}) == (Nil{}, E.OItem{Fail{E.EmptyDeque{}}}) : List<&2, T> & E.Obs<T>}

# First_Element (913)
def First_Element.peek_front_first(-T: Data, +h: T, +t: List<&2, T>) -> Type:
  {ob(T, Con{h, t}, E.PeekFront{}) == E.OItem{Done{h}} : E.Obs<T>} & {C.nth(T, Con{h, t}, 0n) == Some{h} : Maybe<&2, T>}

# First_Element (913)
def First_Element.peek_front_frame(-T: Data, +xs: List<&2, T>) -> Type:
  {nx(T, xs, E.PeekFront{}) == xs : List<&2, T>}

# First_Element (913)
def First_Element.peek_front_empty(-T: Data) -> Type:
  {step(T, Nil{}, E.PeekFront{}) == (Nil{}, E.OItem{Fail{E.EmptyDeque{}}}) : List<&2, T> & E.Obs<T>}

# Last_Element (923)
def Last_Element.peek_back_last(-T: Data, +h: T, +t: List<&2, T>) -> Type:
  {ob(T, Con{h, t}, E.PeekBack{}) == E.OItem{item(T, V.last_elem(T, Con{h, t}))} : E.Obs<T>}

# Last_Element (923)
def Last_Element.peek_back_frame(-T: Data, +xs: List<&2, T>) -> Type:
  {nx(T, xs, E.PeekBack{}) == xs : List<&2, T>}

# Last_Element (923)
def Last_Element.peek_back_empty(-T: Data) -> Type:
  {step(T, Nil{}, E.PeekBack{}) == (Nil{}, E.OItem{Fail{E.EmptyDeque{}}}) : List<&2, T> & E.Obs<T>}
