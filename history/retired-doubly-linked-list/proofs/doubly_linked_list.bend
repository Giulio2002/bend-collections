import Base
import ./lib/array.bend as AR
import ../spec/common.bend as SC
import ../spec/doubly_linked_list.bend as DS
import ../src/doubly_linked_list.bend as D
import ../types/doubly_linked_list.bend as E
import ./dlist/state.bend as ST
import ./dlist/core.bend as K
import ./dlist/trace.bend as TR

# Doubly linked list: public proof entry point (values of an erased type T).
#
# Representation: parallel indexed arenas (src/doubly_linked_list.bend) --
# three linear Base.Arrays (values, prev links, next links) sharing one index
# space; a link is id + 1 and 0 is nil. As for the other array-backed
# structures the laws are stated about the list BUILT from a Data mirror
# (ST.real of a shadow: three perfect trees plus the ghost order of ids):
#   abstraction  ST.model (the (id, value) items along the order)
#   invariant    ST.good  (ids below fresh <= 2^depth <= 2^31, no id twice,
#                values present exactly at the ids in the order, prev/next
#                links agree with the order in both directions)
# Every operation, including the foreign- and stale-handle errors, is proven
# in TR.step_ok; arbitrary finite traces run from the real constructor
# new(tag) (TR.trace_new). The only premise is the capacity condition: the
# ids issued (fresh plus the insertions to come) stay below 2^q, q <= 31.
#
# The definitions are generic in T; a generic (~T) definition is checked at
# its instantiations, which END_TO_END.bend makes at T = U32 and T = String.

def new_real(~T: Data, +tag: U32) -> {D.new(~T, tag) == ST.real(~T, ST.initial(~T, tag)) : D.DList<T>}:
  ST.new_real(~T, tag)

def new_abs(~T: Data, +tag: U32) -> {ST.model(~T, ST.initial(~T, tag)) == DS.new(T, tag) : DS.Model<T>}:
  ST.new_model(~T, tag)

def new_inv(~T: Data, +tag: U32) -> {ST.good(~T, ST.initial(~T, tag)) == True{} : Bool}:
  ST.new_good(~T, tag)

def step_ok(~T: Data, +sh: ST.Shadow<T>, +op: E.Op<T>, +h: {ST.good(~T, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hroom: {Nat.is_lt(K.sfresh(~T, sh), SC.pow2(q)) == True{} : Bool}) -> K.StepOK(~T, sh, op):
  TR.step_ok(~T, sh, op, h, q, hq, hroom)

def trace_new(~T: Data, +tag: U32, +ops: List<&2, E.Op<T>>, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(TR.inserts(T, ops), SC.pow2(q)) == True{} : Bool}) -> TR.TraceNew(~T, tag, ops):
  TR.trace_new(~T, tag, ops, q, hq, room)

def trace_from(~T: Data, +ops: List<&2, E.Op<T>>, +sh: ST.Shadow<T>, +h: {ST.good(~T, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(K.sfresh(~T, sh), TR.inserts(T, ops)), SC.pow2(q)) == True{} : Bool}) -> TR.TraceOK(~T, ops, sh):
  TR.trace_from(~T, ops, sh, h, q, hq, room)
