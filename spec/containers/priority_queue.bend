import Base
import ../lib/order.bend as SO
import ./binary_heap.bend as HS

# ---- contract (SPARK formal containers) ----
# Each `<Subprogram>.<clause>` definition below states one Post clause of
# that SPARK subprogram, as a proposition on this model; the table names the
# clauses. proofs/containers/priority_queue/ proves every clause under its clause name,
# and its `impl` lemma carries them to the implementation.
#
# The priority queue is the binary heap behind another interface; every one
# of its operations is the heap's (for every element type and order), so it
# has the heap's SPARK-style multiset contracts,
# spec/containers/binary_heap.bend (restated below):
#
#   contract                 priority_queue   binary_heap      contract lemmas (HC.)
#   Empty_Set                new              new              new_empty
#   Length                   qsize            length           length_result, length_frame
#   Insert (multiplicity)    put              push             push_length, push_bag, push_sorted
#   First_Element (minimum)  peek             peek             peek_min, peek_frame, peek_empty
#   Delete_First (minimum)   get              pop              pop_length, pop_result, pop_min,
#                                                              pop_bag, pop_empty
#   To_Set                   from_list        from_list        from_list_model, from_list_length,
#                                                              from_list_sorted
#   Elements (ordered)       to_sorted_list   to_sorted_list   to_sorted_result, to_sorted_frame
#   implementation                                             HC.impl, HC.model_sorted

# The model is the binary_heap's (HS.step) and so is every clause:

def Length.length_result(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>) -> Type:
  HS.Length.length_result(~A, ~cmp, xs)

def Length.length_frame(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>) -> Type:
  HS.Length.length_frame(~A, ~cmp, xs)

def Insert.push_length(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>, +x: A) -> Type:
  HS.Insert.push_length(~A, ~cmp, xs, x)

def Insert.push_bag(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +xs: List<&2, A>, +x: A) -> Type:
  HS.Insert.push_bag(~A, ~cmp, ~o, xs, x)

def Insert.push_sorted(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +xs: List<&2, A>, +x: A, +hs: {HS.sorted(~A, ~cmp, xs) == True{} : Bool}) -> Type:
  HS.Insert.push_sorted(~A, ~cmp, ~o, xs, x, hs)

def First_Element.peek_min(~A: Data, ~cmp: A -> A -> Cmp, +h: A, +t: List<&2, A>, +hs: {HS.sorted(~A, ~cmp, Con{h, t}) == True{} : Bool}) -> Type:
  HS.First_Element.peek_min(~A, ~cmp, h, t, hs)

def First_Element.peek_frame(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>) -> Type:
  HS.First_Element.peek_frame(~A, ~cmp, xs)

def First_Element.peek_empty(~A: Data, ~cmp: A -> A -> Cmp) -> Type:
  HS.First_Element.peek_empty(~A, ~cmp)

def Delete_First.pop_length(~A: Data, ~cmp: A -> A -> Cmp, +h: A, +t: List<&2, A>) -> Type:
  HS.Delete_First.pop_length(~A, ~cmp, h, t)

def Delete_First.pop_result(~A: Data, ~cmp: A -> A -> Cmp, +h: A, +t: List<&2, A>) -> Type:
  HS.Delete_First.pop_result(~A, ~cmp, h, t)

def Delete_First.pop_min(~A: Data, ~cmp: A -> A -> Cmp, +h: A, +t: List<&2, A>, +hs: {HS.sorted(~A, ~cmp, Con{h, t}) == True{} : Bool}) -> Type:
  HS.Delete_First.pop_min(~A, ~cmp, h, t, hs)

def Delete_First.pop_bag(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +h: A, +t: List<&2, A>, +hs: {HS.sorted(~A, ~cmp, Con{h, t}) == True{} : Bool}) -> Type:
  HS.Delete_First.pop_bag(~A, ~cmp, ~o, h, t, hs)

def Delete_First.pop_empty(~A: Data, ~cmp: A -> A -> Cmp) -> Type:
  HS.Delete_First.pop_empty(~A, ~cmp)

def To_Set.from_list_model(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>, +ys: List<&2, A>) -> Type:
  HS.To_Set.from_list_model(~A, ~cmp, xs, ys)

def To_Set.from_list_length(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>, +ys: List<&2, A>) -> Type:
  HS.To_Set.from_list_length(~A, ~cmp, xs, ys)

def To_Set.from_list_sorted(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +xs: List<&2, A>, +ys: List<&2, A>) -> Type:
  HS.To_Set.from_list_sorted(~A, ~cmp, ~o, xs, ys)

def Elements.to_sorted_result(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>) -> Type:
  HS.Elements.to_sorted_result(~A, ~cmp, xs)

def Elements.to_sorted_frame(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>) -> Type:
  HS.Elements.to_sorted_frame(~A, ~cmp, xs)

