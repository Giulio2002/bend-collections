import Base
import ../lib/common.bend as C
import ../../src/containers/types/queue.bend as E
import ../lib/sequence.bend as V

# Independent model: a FIFO queue is the sequence of its elements, oldest
# first. Enqueue appends at the end; dequeue removes the first element.

def item(-T: Data, x: Maybe<&2, T>) -> Result<&2, &2, E.Error, T>:
  match x:
    case None{}:
      Fail{E.EmptyQueue{}}
    case Some{v}:
      Done{v}

def dequeue(-T: Data, xs: List<&2, T>) -> List<&2, T> & E.Obs<T>:
  match xs:
    case Nil{}:
      (Nil{}, E.OItem{Fail{E.EmptyQueue{}}})
    case Con{h, t}:
      (t, E.OItem{Done{h}})

def step(-T: Data, +xs: List<&2, T>, op: E.Op<T>) -> List<&2, T> & E.Obs<T>:
  match op:
    case E.Length{}:
      (xs, E.ONat{C.length(T, xs)})
    case E.Enqueue{x}:
      (C.snoc(T, xs, x), E.OUnit{})
    case E.Dequeue{}:
      dequeue(T, xs)
    case E.Peek{}:
      (xs, E.OItem{item(T, C.head(T, xs))})
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
# clauses. proofs/containers/queue/ proves every clause under its clause name,
# and its `impl` lemma carries them to the implementation.
#
# Contracts of the FIFO queue in the style of SPARK's formal vectors
# (SPARKlib src/spark-containers-formal-vectors.ads, AdaCore/SPARKlib
# 46ec319; model predicates in spec/lib/sequence.bend). The model is the
# sequence oldest first: enqueue is Append, dequeue is Delete_First, peek
# is First_Element. Each lemma is one Post clause of step; `impl` (via
# PS.step_ok) carries every clause to the implementation: Q.step on the
# queue of a shadow lands on the queue of a shadow whose model satisfies it.
#
#   SPARK subprogram (.ads line)   ours      clauses
#   Length (284)                   length    length_result, length_frame
#   Empty_Vector (292)             new       new_empty, new_impl
#   Append (706)                   enqueue   enqueue_length, enqueue_prefix, enqueue_element
#   Delete_First (825)             dequeue   dequeue_length, dequeue_shifted,
#                                            dequeue_result, dequeue_empty
#   First_Element (913)            peek      peek_first, peek_frame, peek_empty
#   iteration (Iter_Model, 1193)   to_list   to_list_model, to_list_frame
#   implementation                 Q.step    impl
# Not in this API: Capacity/Reserve_Capacity (unbounded), Is_Empty, Clear,
# "=", To_Vector, Assign/Copy/Move, Element at an index, Replace_Element,
# Reference, Insert*, Prepend*, Append_Vector/Count, Delete (at an index),
# Delete_Last, Last_Element, Reverse_Elements, Swap, Find_Index,
# Reverse_Find_Index, Contains, Has_Element. SPARK's Pre (not Is_Empty) is
# a defensive check: on an empty queue dequeue and peek return EmptyQueue
# and change nothing.

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

# Append (706)
def Append.enqueue_length(-T: Data, +xs: List<&2, T>, +v: T) -> Type:
  {C.length(T, nx(T, xs, E.Enqueue{v})) == 1n+C.length(T, xs) : Nat}

# Append (706)
def Append.enqueue_prefix(-T: Data, +xs: List<&2, T>, +v: T) -> Type:
  V.EqualPrefix(T, xs, nx(T, xs, E.Enqueue{v}))

# Append (706)
def Append.enqueue_element(-T: Data, +xs: List<&2, T>, +v: T) -> Type:
  {C.nth(T, nx(T, xs, E.Enqueue{v}), C.length(T, xs)) == Some{v} : Maybe<&2, T>}

# Delete_First (825)
def Delete_First.dequeue_length(-T: Data, +h: T, +t: List<&2, T>) -> Type:
  {1n+C.length(T, nx(T, Con{h, t}, E.Dequeue{})) == C.length(T, Con{h, t}) : Nat}

# Delete_First (825)
def Delete_First.dequeue_shifted(-T: Data, +h: T, +t: List<&2, T>) -> Type:
  V.RangeShifted(T, nx(T, Con{h, t}, E.Dequeue{}), Con{h, t}, 0n, C.length(T, nx(T, Con{h, t}, E.Dequeue{})), 1n)

# Delete_First (825)
def Delete_First.dequeue_result(-T: Data, +h: T, +t: List<&2, T>) -> Type:
  {ob(T, Con{h, t}, E.Dequeue{}) == E.OItem{Done{h}} : E.Obs<T>}

# Delete_First (825)
def Delete_First.dequeue_empty(-T: Data) -> Type:
  {step(T, Nil{}, E.Dequeue{}) == (Nil{}, E.OItem{Fail{E.EmptyQueue{}}}) : List<&2, T> & E.Obs<T>}

# First_Element (913)
def First_Element.peek_first(-T: Data, +h: T, +t: List<&2, T>) -> Type:
  {ob(T, Con{h, t}, E.Peek{}) == E.OItem{Done{h}} : E.Obs<T>} & {C.nth(T, Con{h, t}, 0n) == Some{h} : Maybe<&2, T>}

# First_Element (913)
def First_Element.peek_frame(-T: Data, +xs: List<&2, T>) -> Type:
  {nx(T, xs, E.Peek{}) == xs : List<&2, T>}

# First_Element (913)
def First_Element.peek_empty(-T: Data) -> Type:
  {step(T, Nil{}, E.Peek{}) == (Nil{}, E.OItem{Fail{E.EmptyQueue{}}}) : List<&2, T> & E.Obs<T>}
