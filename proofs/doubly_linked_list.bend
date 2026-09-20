import Base
import ../spec/doubly_linked_list.bend as DS
import ../src/doubly_linked_list.bend as D
import ../types/doubly_linked_list.bend as E
import ./doubly_linked_list/nodes.bend as NS
import ./doubly_linked_list/links.bend as LK
import ./doubly_linked_list/cut.bend as C
import ./doubly_linked_list/facts.bend as F
import ./doubly_linked_list/cores.bend as K
import ./doubly_linked_list/steps.bend as ST
import ./doubly_linked_list/trace.bend as TR

# Doubly linked list: public proof entry point (erased value type T; node
# store = the Nat instance of the checked red-black tree map).
#   abstraction  ST.abs (items obtained by walking next links from head)
#   invariant    ST.Inv (a proposition): the walked items are exactly
#                bidirectionally linked (each node's value, prev and next
#                agree with the sequence), head/tail/count agree, ids are
#                distinct and below the fresh id, every stored node is on the
#                walk (so stale ids have no node), and the store is valid.
# Every operation, including foreign- and stale-handle errors, is proven in
# ST.step_ok; traces run from the real constructor new(tag).

def new_abs(-T: Data, +tag: Nat) -> {ST.abs(T, D.new(T, tag)) == DS.new(T, tag) : DS.Model<T>}:
  ST.new_abs(T, tag)

def new_inv(-T: Data, +tag: Nat) -> ST.Inv(T, D.new(T, tag)):
  ST.new_inv(T, tag)

def step_ok(-T: Data, +s: D.DList<T>, +op: E.Op<T>, g: ST.Inv(T, s)) -> ST.StepOK(T, s, op):
  ST.step_ok(T, s, op, g)

def trace_new(-T: Data, +tag: Nat, +ops: List<&2, E.Op<T>>) -> {TR.view(T, D.run(T, ops, D.new(T, tag))) == DS.run(T, ops, DS.new(T, tag)) : DS.Model<T> & List<&2, E.Obs<T>>}:
  TR.trace_from(T, ops, D.new(T, tag), ST.new_inv(T, tag))

def trace_new_inv(-T: Data, +tag: Nat, +ops: List<&2, E.Op<T>>) -> ST.Inv(T, Pair.fst(D.DList<T>, List<&2, E.Obs<T>>, D.run(T, ops, D.new(T, tag)))):
  TR.inv_from(T, ops, D.new(T, tag), ST.new_inv(T, tag))
