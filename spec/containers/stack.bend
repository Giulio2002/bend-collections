import Base
import ../lib/common.bend as C
import ../../src/containers/types/stack.bend as E
import ../lib/sequence.bend as V

# Independent LIFO sequence model; top is the first element.
def step(-T: Data, +xs: List<&2, T>, op: E.Op<T>) -> List<&2, T> & E.Obs<T>:
  match xs op:
    case +ys E.Push{x}:
      (Con{x, ys}, E.OUnit{})
    case +ys E.Length{}:
      (ys, E.ONat{C.length(T, ys)})
    case +ys E.ToList{}:
      (ys, E.OList{ys})
    case Nil{} E.Pop{}:
      (Nil{}, E.OItem{Fail{E.EmptyStack{}}})
    case Con{x, tail} E.Pop{}:
      (tail, E.OItem{Done{x}})
    case Nil{} E.Peek{}:
      (Nil{}, E.OItem{Fail{E.EmptyStack{}}})
    case Con{+x, +tail} E.Peek{}:
      (Con{x, tail}, E.OItem{Done{x}})

# ---- contract (SPARK formal containers) ----
# Each `<Subprogram>.<clause>` definition below states one Post clause of
# that SPARK subprogram, as a proposition on this model; the table names the
# clauses. proofs/containers/stack/ proves every clause under its clause name,
# and its `impl` lemma carries them to the implementation.
#
# Contracts of the stack in the style of SPARK's formal vectors
# (SPARKlib src/spark-containers-formal-vectors.ads, AdaCore/SPARKlib
# 46ec319; model predicates in spec/lib/sequence.bend). The model is the
# sequence with the top first, so push is Prepend, pop is Delete_First and
# peek is First_Element. Each lemma is one Post clause of step; `impl`
# (P.step_correct: D.step on the stack of a sequence is step lifted)
# carries every clause to the implementation.
#
#   SPARK subprogram (.ads line)   ours      clauses
#   Length (284)                   length    length_result, length_frame
#   Empty_Vector (292)             new       new_empty, new_impl
#   Prepend (624)                  push      push_length, push_first, push_shifted
#   Delete_First (825)             pop       pop_length, pop_shifted, pop_result, pop_empty
#   First_Element (913)            peek      peek_first, peek_frame, peek_empty
#   iteration (Iter_Model, 1193)   to_list   to_list_model, to_list_frame
#   implementation                 D.step    impl
# Not in this API: Capacity/Reserve_Capacity (unbounded), Is_Empty, Clear,
# "=", To_Vector, Assign/Copy/Move, Element at an index, Replace_Element,
# Reference, Insert*, Append*, Delete (at an index), Delete_Last,
# Last_Element, Reverse_Elements, Swap, Find_Index, Reverse_Find_Index,
# Contains, Has_Element. SPARK's Pre (not Is_Empty) is a defensive check:
# on an empty stack pop and peek return EmptyStack and change nothing
# (pop_empty, peek_empty).

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

# Empty_Vector (292)
def Empty_Vector.new_empty(-T: Data) -> Type:
  {C.length(T, Nil{}) == 0n : Nat}

# Prepend (624)
def Prepend.push_length(-T: Data, +xs: List<&2, T>, +v: T) -> Type:
  {C.length(T, nx(T, xs, E.Push{v})) == 1n+C.length(T, xs) : Nat}

# Prepend (624)
def Prepend.push_first(-T: Data, +xs: List<&2, T>, +v: T) -> Type:
  {C.nth(T, nx(T, xs, E.Push{v}), 0n) == Some{v} : Maybe<&2, T>}

# Prepend (624)
def Prepend.push_shifted(-T: Data, +xs: List<&2, T>, +v: T) -> Type:
  V.RangeShifted(T, xs, nx(T, xs, E.Push{v}), 0n, C.length(T, xs), 1n)

# Delete_First (825)
def Delete_First.pop_length(-T: Data, +h: T, +t: List<&2, T>) -> Type:
  {1n+C.length(T, nx(T, Con{h, t}, E.Pop{})) == C.length(T, Con{h, t}) : Nat}

# Delete_First (825)
def Delete_First.pop_shifted(-T: Data, +h: T, +t: List<&2, T>) -> Type:
  V.RangeShifted(T, nx(T, Con{h, t}, E.Pop{}), Con{h, t}, 0n, C.length(T, nx(T, Con{h, t}, E.Pop{})), 1n)

# Delete_First (825)
def Delete_First.pop_result(-T: Data, +h: T, +t: List<&2, T>) -> Type:
  {ob(T, Con{h, t}, E.Pop{}) == E.OItem{Done{h}} : E.Obs<T>}

# Delete_First (825)
def Delete_First.pop_empty(-T: Data) -> Type:
  {step(T, Nil{}, E.Pop{}) == (Nil{}, E.OItem{Fail{E.EmptyStack{}}}) : List<&2, T> & E.Obs<T>}

# First_Element (913)
def First_Element.peek_first(-T: Data, +h: T, +t: List<&2, T>) -> Type:
  {ob(T, Con{h, t}, E.Peek{}) == E.OItem{Done{h}} : E.Obs<T>} & {C.nth(T, Con{h, t}, 0n) == Some{h} : Maybe<&2, T>}

# First_Element (913)
def First_Element.peek_frame(-T: Data, +xs: List<&2, T>) -> Type:
  {nx(T, xs, E.Peek{}) == xs : List<&2, T>}

# First_Element (913)
def First_Element.peek_empty(-T: Data) -> Type:
  {step(T, Nil{}, E.Peek{}) == (Nil{}, E.OItem{Fail{E.EmptyStack{}}}) : List<&2, T> & E.Obs<T>}
