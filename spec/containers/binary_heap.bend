import Base
import ../lib/common.bend as C
import ../../src/containers/types/binary_heap.bend as E
import ../lib/order.bend as SO

# Independent model: a priority queue is the finite multiset of its elements,
# represented canonically as the list sorted ascending by the comparator
# (insertion sort). Equal-comparing elements are identical under the order
# laws, so the sorted list is unique for each multiset. Nothing here refers
# to trees.

def le(~A: Data, ~cmp: A -> A -> Cmp, x: A, y: A) -> Bool:
  Cmp.is_le(cmp(x, y))

# Insert into a sorted list, before the first element not smaller than x.
def ins(~A: Data, ~cmp: A -> A -> Cmp, +x: A, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Con{x, Nil{}}
    case Con{+h, +t}:
      Bool.pick(List<&2, A>, le(~A, ~cmp, x, h), Con{x, Con{h, t}}, Con{h, ins(~A, ~cmp, x, t)})

# The multiset of a list, left to right.
def from_list(~A: Data, ~cmp: A -> A -> Cmp, xs: List<&2, A>, acc: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      from_list(~A, ~cmp, t, ins(~A, ~cmp, x, acc))

def item(-A: Data, x: Maybe<&2, A>) -> Result<&2, &2, E.Error, A>:
  match x:
    case None{}:
      Fail{E.EmptyHeap{}}
    case Some{v}:
      Done{v}

def pop(-A: Data, xs: List<&2, A>) -> List<&2, A> & E.Obs<A>:
  match xs:
    case Nil{}:
      (Nil{}, E.OItem{Fail{E.EmptyHeap{}}})
    case Con{h, t}:
      (t, E.OItem{Done{h}})

def step(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>, op: E.Op<A>) -> List<&2, A> & E.Obs<A>:
  match op:
    case E.Length{}:
      (xs, E.ONat{C.length(A, xs)})
    case E.Push{x}:
      (ins(~A, ~cmp, x, xs), E.OUnit{})
    case E.Peek{}:
      (xs, E.OItem{item(A, C.head(A, xs))})
    case E.Pop{}:
      pop(A, xs)
    case E.FromList{ys}:
      (from_list(~A, ~cmp, ys, Nil{}), E.OUnit{})
    case E.ToSortedList{}:
      (xs, E.OList{xs})

def cons_obs(-A: Data, o: E.Obs<A>, r: List<&2, A> & List<&2, E.Obs<A>>) -> List<&2, A> & List<&2, E.Obs<A>>:
  (m, os) = r
  (m, Con{o, os})

def run(~A: Data, ~cmp: A -> A -> Cmp, ops: List<&2, E.Op<A>>, +xs: List<&2, A>) -> List<&2, A> & List<&2, E.Obs<A>>:
  match ops:
    case Nil{}:
      (xs, Nil{})
    case Con{+op, rest}:
      cons_obs(A, Pair.snd(List<&2, A>, E.Obs<A>, step(~A, ~cmp, xs, op)), run(~A, ~cmp, rest, Pair.fst(List<&2, A>, E.Obs<A>, step(~A, ~cmp, xs, op))))

# ---- the sorted-multiset model: order and removal ----

def all_ge(~A: Data, ~cmp: A -> A -> Cmp, +z: A, xs: List<&2, A>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(le(~A, ~cmp, z, h), all_ge(~A, ~cmp, z, t))

def sorted(~A: Data, ~cmp: A -> A -> Cmp, xs: List<&2, A>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      Bool.and(all_ge(~A, ~cmp, h, t), sorted(~A, ~cmp, t))

def eq_head(~A: Data, ~cmp: A -> A -> Cmp, +z: A, xs: List<&2, A>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Cmp.is_eq(cmp(z, h))

def del(~A: Data, ~cmp: A -> A -> Cmp, +z: A, xs: List<&2, A>, b: Bool) -> List<&2, A>:
  match xs b:
    case Nil{} _:
      Nil{}
    case Con{h, t} True{}:
      t
    case Con{h, +t} False{}:
      Con{h, del(~A, ~cmp, z, t, eq_head(~A, ~cmp, z, t))}

def delf(~A: Data, ~cmp: A -> A -> Cmp, +z: A, +xs: List<&2, A>) -> List<&2, A>:
  del(~A, ~cmp, z, xs, eq_head(~A, ~cmp, z, xs))

# ---- contract (SPARK formal containers) ----
# Each `<Subprogram>.<clause>` definition below states one Post clause of
# that SPARK subprogram, as a proposition on this model; the table names the
# clauses. proofs/containers/binary_heap/ proves every clause under its clause name,
# and its `impl` lemma carries them to the implementation.
#
# Contracts of the binary heap. SPARKlib has no formal priority queue, so
# these are the SPARK-style contracts of the closest container: a sorted
# multiset, the model S uses (the ascending list of the elements, which is
# unique for each multiset; SPARKlib src/full/spark-containers-formal-
# ordered_sets.ads, AdaCore/SPARKlib 46ec319, with multiplicity). Each lemma
# is one Post clause of step, under a total order ~o; `impl` (via
# P.step_ok) carries every clause to the implementation.
#
#   contract (closest SPARK subprogram)       ours            lemmas
#   Length (ordered_sets 112)                 length          length_result, length_frame
#   Empty_Set (99)                            new             new_empty
#   Insert, with multiplicity (777)           push            push_length, push_bag, push_sorted
#   First_Element: the minimum (1534)         peek            peek_min, peek_frame, peek_empty
#   Delete_First (1105)                       pop             pop_length, pop_result, pop_min,
#                                                             pop_bag, pop_empty
#   To_Set (559)                              from_list       from_list_model, from_list_length,
#                                                             from_list_sorted
#   Elements / iteration (ordered)            to_sorted_list  to_sorted_result, to_sorted_frame
#   every model is ordered                                    model_sorted
#   implementation                            H.step          impl
# Pop's result is the minimum and its model is the rest: Delete_First on a
# multiset (First_Element'Old removed once, pop_bag), and push adds exactly
# one occurrence (push_bag: removing it gives the old multiset back). Not
# applicable: a heap has no keys, cursors or positions (Find, Floor,
# Ceiling, Next, Previous, Contains, Replace, Exclude of an arbitrary
# element, Last_Element), and no set algebra.

def nx(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>, +op: E.Op<A>) -> List<&2, A>:
  Pair.fst(List<&2, A>, E.Obs<A>, step(~A, ~cmp, xs, op))

def ob(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>, +op: E.Op<A>) -> E.Obs<A>:
  Pair.snd(List<&2, A>, E.Obs<A>, step(~A, ~cmp, xs, op))

# Length (ordered_sets 112)
def Length.length_result(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>) -> Type:
  {ob(~A, ~cmp, xs, E.Length{}) == E.ONat{C.length(A, xs)} : E.Obs<A>}

# Length (ordered_sets 112)
def Length.length_frame(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>) -> Type:
  {nx(~A, ~cmp, xs, E.Length{}) == xs : List<&2, A>}

# Insert, with multiplicity (777)
def Insert.push_length(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>, +x: A) -> Type:
  {C.length(A, nx(~A, ~cmp, xs, E.Push{x})) == 1n+C.length(A, xs) : Nat}

# Insert, with multiplicity (777)
def Insert.push_bag(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +xs: List<&2, A>, +x: A) -> Type:
  {delf(~A, ~cmp, x, nx(~A, ~cmp, xs, E.Push{x})) == xs : List<&2, A>}

# Insert, with multiplicity (777)
def Insert.push_sorted(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +xs: List<&2, A>, +x: A, +hs: {sorted(~A, ~cmp, xs) == True{} : Bool}) -> Type:
  {sorted(~A, ~cmp, nx(~A, ~cmp, xs, E.Push{x})) == True{} : Bool}

# First_Element: the minimum (1534)
def First_Element.peek_min(~A: Data, ~cmp: A -> A -> Cmp, +h: A, +t: List<&2, A>, +hs: {sorted(~A, ~cmp, Con{h, t}) == True{} : Bool}) -> Type:
  {ob(~A, ~cmp, Con{h, t}, E.Peek{}) == E.OItem{Done{h}} : E.Obs<A>} & {all_ge(~A, ~cmp, h, t) == True{} : Bool}

# First_Element: the minimum (1534)
def First_Element.peek_frame(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>) -> Type:
  {nx(~A, ~cmp, xs, E.Peek{}) == xs : List<&2, A>}

# First_Element: the minimum (1534)
def First_Element.peek_empty(~A: Data, ~cmp: A -> A -> Cmp) -> Type:
  {step(~A, ~cmp, Nil{}, E.Peek{}) == (Nil{}, E.OItem{Fail{E.EmptyHeap{}}}) : List<&2, A> & E.Obs<A>}

# Delete_First (1105)
def Delete_First.pop_length(~A: Data, ~cmp: A -> A -> Cmp, +h: A, +t: List<&2, A>) -> Type:
  {1n+C.length(A, nx(~A, ~cmp, Con{h, t}, E.Pop{})) == C.length(A, Con{h, t}) : Nat}

# Delete_First (1105)
def Delete_First.pop_result(~A: Data, ~cmp: A -> A -> Cmp, +h: A, +t: List<&2, A>) -> Type:
  {ob(~A, ~cmp, Con{h, t}, E.Pop{}) == E.OItem{Done{h}} : E.Obs<A>}

# Delete_First (1105)
def Delete_First.pop_min(~A: Data, ~cmp: A -> A -> Cmp, +h: A, +t: List<&2, A>, +hs: {sorted(~A, ~cmp, Con{h, t}) == True{} : Bool}) -> Type:
  {all_ge(~A, ~cmp, h, nx(~A, ~cmp, Con{h, t}, E.Pop{})) == True{} : Bool}

# Delete_First (1105)
def Delete_First.pop_bag(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +h: A, +t: List<&2, A>, +hs: {sorted(~A, ~cmp, Con{h, t}) == True{} : Bool}) -> Type:
  {ins(~A, ~cmp, h, nx(~A, ~cmp, Con{h, t}, E.Pop{})) == Con{h, t} : List<&2, A>}

# Delete_First (1105)
def Delete_First.pop_empty(~A: Data, ~cmp: A -> A -> Cmp) -> Type:
  {step(~A, ~cmp, Nil{}, E.Pop{}) == (Nil{}, E.OItem{Fail{E.EmptyHeap{}}}) : List<&2, A> & E.Obs<A>}

# To_Set (559)
def To_Set.from_list_model(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>, +ys: List<&2, A>) -> Type:
  {nx(~A, ~cmp, xs, E.FromList{ys}) == from_list(~A, ~cmp, ys, Nil{}) : List<&2, A>}

# To_Set (559)
def To_Set.from_list_length(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>, +ys: List<&2, A>) -> Type:
  {C.length(A, nx(~A, ~cmp, xs, E.FromList{ys})) == C.length(A, ys) : Nat}

# To_Set (559)
def To_Set.from_list_sorted(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +xs: List<&2, A>, +ys: List<&2, A>) -> Type:
  {sorted(~A, ~cmp, nx(~A, ~cmp, xs, E.FromList{ys})) == True{} : Bool}

# Elements / iteration (ordered)
def Elements.to_sorted_result(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>) -> Type:
  {ob(~A, ~cmp, xs, E.ToSortedList{}) == E.OList{xs} : E.Obs<A>}

# Elements / iteration (ordered)
def Elements.to_sorted_frame(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>) -> Type:
  {nx(~A, ~cmp, xs, E.ToSortedList{}) == xs : List<&2, A>}
