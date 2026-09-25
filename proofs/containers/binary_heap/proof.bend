import Base
import ../../lib/logic.bend as L
import ../../lib/list.bend as LL
import ../../lib/nat.bend as N
import ../../lib/array.bend as AR
import ../../lib/order.bend as O
import ../../../spec/lib/common.bend as SC
import ../../../spec/containers/binary_heap.bend as S
import ../../../src/containers/binary_heap.bend as H
import ../../../src/containers/types/binary_heap.bend as E
import ./state.bend as ST
import ./steps.bend as SP
import ./trace.bend as TR
import ../../../spec/lib/order.bend as SO
import ./multiset.bend as M
import ./vals.bend as VL
import ./bag.bend as BG

# Binary heap: public proof entry point.
#   representation  a PACKED Base.Array block, element i with children 2i+1
#                   and 2i+2 (src/binary_heap.bend). The block is linear, so
#                   -- as in proofs/dynamic_array, proofs/bitset and
#                   proofs/deque -- every law is about the heap BUILT from a
#                   Data mirror tree (ST.real of a shadow).
#   abstraction     ST.model / ST.abs (the sorted multiset of the occupied
#                   slots; ST.abs reads an actual block through AR.freeze)
#   invariant       ST.good / ST.Inv (perfect block, elements exactly in
#                   [0, size), heap order over them, size <= 2^depth)
#   operations      SP.step_ok (every operation, errors included)
#   traces          trace_from / trace_new (arbitrary finite op lists)
#
# Laws are templates over a comparator ~cmp with total-order laws
# ~o : O.Order(~A, ~cmp); each is instantiated and thereby checked below for
# (U32, U32.cmp, O.u32_order) and (String, String.order, O.string_order), the
# instances src/ exposes.
#
# The capacity condition of the representation, in terms of the heap's
# SIZE: size + (elements the operations can add) < 2^q with q <= 31. A push
# doubles the block only when it is full, and then 2^depth = size < 2^q
# forces depth < 31, so every slot index stays a representable U32 (Base
# arrays have at most 2^31 slots). It is a premise only of the step and
# trace laws, it does not bound the length of a trace, and every other law
# holds at every state satisfying the invariant.

# ---- the constructor ----

def new_real(~A: Data, ~cmp: A -> A -> Cmp) -> {H.new(~A) == ST.real(~A, ST.initial(~A)) : H.Heap<A>}:
  ST.new_real(~A)

def new_inv(~A: Data, ~cmp: A -> A -> Cmp) -> {ST.good(~A, ~cmp, ST.initial(~A)) == True{} : Bool}:
  ST.new_good(~A, ~cmp)

def new_abs(~A: Data, ~cmp: A -> A -> Cmp) -> {ST.model(~A, ~cmp, ST.initial(~A)) == Nil{} : List<&2, A>}:
  ST.new_model(~A, ~cmp)

# ---- every operation (errors included), on every reachable representation ----

def step_ok(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), sh: ST.Shadow<A>, op: E.Op<A>, +g: {ST.good(~A, ~cmp, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(ST.sh_size(~A, sh), SP.pushcost(~A, op)), SC.pow2(q)) == True{} : Bool}) -> SP.StepOK(~A, ~cmp, sh, op):
  SP.step_ok(~A, ~cmp, ~o, sh, op, g, q, hq, room)

# The abstraction of an actual heap is the model of its shadow: the laws
# above, stated on shadows, are laws about actual heaps.
def abs_real(~A: Data, ~cmp: A -> A -> Cmp, +sh: ST.Shadow<A>) -> {ST.abs(~A, ~cmp, ST.real(~A, sh)) == ST.model(~A, ~cmp, sh) : List<&2, A>}:
  ST.abs_real(~A, ~cmp, sh)

def new_heap_inv(~A: Data, ~cmp: A -> A -> Cmp) -> ST.Inv(~A, ~cmp, H.new(~A)):
  (ST.initial(~A), (ST.new_real(~A), ST.new_good(~A, ~cmp)))

# ---- arbitrary finite traces ----

def trace_from(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ops: List<&2, E.Op<A>>, +sh0: ST.Shadow<A>, +g0: {ST.good(~A, ~cmp, sh0) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(ST.sh_size(~A, sh0), TR.pushes(~A, ops)), SC.pow2(q)) == True{} : Bool}) -> TR.TraceOK(~A, ~cmp, ops, sh0):
  TR.trace_from(~A, ~cmp, ~o, ops, sh0, g0, q, hq, room)

def trace_new(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ops: List<&2, E.Op<A>>, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(TR.pushes(~A, ops), SC.pow2(q)) == True{} : Bool}) -> TR.TraceOK(~A, ~cmp, ops, ST.initial(~A)):
  TR.trace_from(~A, ~cmp, ~o, ops, ST.initial(~A), ST.new_good(~A, ~cmp), q, hq, room)

# ---- checked instances ----

def u32_step_ok(sh: ST.Shadow<U32>, op: E.Op<U32>, +g: {ST.good(~U32, ~U32.cmp, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(ST.sh_size(~U32, sh), SP.pushcost(~U32, op)), SC.pow2(q)) == True{} : Bool}) -> SP.StepOK(~U32, ~U32.cmp, sh, op):
  step_ok(~U32, ~U32.cmp, ~O.u32_order, sh, op, g, q, hq, room)

def u32_trace(+ops: List<&2, E.Op<U32>>, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(TR.pushes(~U32, ops), SC.pow2(q)) == True{} : Bool}) -> TR.TraceOK(~U32, ~U32.cmp, ops, ST.initial(~U32)):
  trace_new(~U32, ~U32.cmp, ~O.u32_order, ops, q, hq, room)

def u32_new_inv() -> ST.Inv(~U32, ~U32.cmp, H.new(~U32)):
  new_heap_inv(~U32, ~U32.cmp)

def string_step_ok(sh: ST.Shadow<String>, op: E.Op<String>, +g: {ST.good(~String, ~String.order, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(ST.sh_size(~String, sh), SP.pushcost(~String, op)), SC.pow2(q)) == True{} : Bool}) -> SP.StepOK(~String, ~String.order, sh, op):
  step_ok(~String, ~String.order, ~O.string_order, sh, op, g, q, hq, room)

def string_trace(+ops: List<&2, E.Op<String>>, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(TR.pushes(~String, ops), SC.pow2(q)) == True{} : Bool}) -> TR.TraceOK(~String, ~String.order, ops, ST.initial(~String)):
  trace_new(~String, ~String.order, ~O.string_order, ops, q, hq, room)

def string_new_inv() -> ST.Inv(~String, ~String.order, H.new(~String)):
  new_heap_inv(~String, ~String.order)

# ==== the contract of binary_heap (stated in spec/containers/binary_heap.bend) ====================

# ascending: each element is below all the later ones
# ---- the implementation ----
def Impl(~A: Data, ~cmp: A -> A -> Cmp, sh: ST.Shadow<A>, op: E.Op<A>, Post: (List<&2, A> & E.Obs<A>) -> Type) -> Type:
  Sigma<&1, &1, ST.Shadow<A>, sh2 => Sigma<&1, &1, E.Obs<A>, o => {H.step(~A, ~cmp, ST.real(~A, sh), op) == (ST.real(~A, sh2), o) : H.Heap<A> & E.Obs<A>} & ({ST.good(~A, ~cmp, sh2) == True{} : Bool} & Post((ST.model(~A, ~cmp, sh2), o)))>>

def impl_of(~A: Data, ~cmp: A -> A -> Cmp, -sh: ST.Shadow<A>, -op: E.Op<A>, -Post: (List<&2, A> & E.Obs<A>) -> Type, k: SP.StepOK(~A, ~cmp, sh, op), pf: Post(S.step(~A, ~cmp, ST.model(~A, ~cmp, sh), op))) -> Impl(~A, ~cmp, sh, op, Post):
  match k:
    case Tuple{sh2, Tuple{o, Tuple{e1, Tuple{g2, Tuple{e3, e4}}}}}:
      (sh2, (o, (e1, (g2, L.subst(List<&2, A> & E.Obs<A>, Post, S.step(~A, ~cmp, ST.model(~A, ~cmp, sh), op), (ST.model(~A, ~cmp, sh2), o), Equal.sym(List<&2, A> & E.Obs<A>, (ST.model(~A, ~cmp, sh2), o), S.step(~A, ~cmp, ST.model(~A, ~cmp, sh), op), e3), pf)))))

# the heap must have room for a push (size + pushes < 2^q, q <= 31)
def impl(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), sh: ST.Shadow<A>, op: E.Op<A>, +g: {ST.good(~A, ~cmp, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(ST.sh_size(~A, sh), SP.pushcost(~A, op)), SC.pow2(q)) == True{} : Bool}, -Post: (List<&2, A> & E.Obs<A>) -> Type, pf: Post(S.step(~A, ~cmp, ST.model(~A, ~cmp, sh), op))) -> Impl(~A, ~cmp, sh, op, Post):
  impl_of(~A, ~cmp, sh, op, Post, step_ok(~A, ~cmp, ~o, sh, op, g, q, hq, room), pf)

# ---- ordering ----
def ag_trans(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +x: A, +h: A, +t: List<&2, A>, +hxh: {S.le(~A, ~cmp, x, h) == True{} : Bool}, +hht: {S.all_ge(~A, ~cmp, h, t) == True{} : Bool}) -> {S.all_ge(~A, ~cmp, x, t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+a, +r}:
      L.and_intro(S.le(~A, ~cmp, x, a), S.all_ge(~A, ~cmp, x, r), O.trans(~A, ~cmp, o, x, h, a, hxh, L.and_left(S.le(~A, ~cmp, h, a), S.all_ge(~A, ~cmp, h, r), hht)), ag_trans(~A, ~cmp, ~o, x, h, r, hxh, L.and_right(S.le(~A, ~cmp, h, a), S.all_ge(~A, ~cmp, h, r), hht)))

def is_c(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +x: A, +h: A, +t: List<&2, A>, +hs: {S.sorted(~A, ~cmp, Con{h, t}) == True{} : Bool}, +b: Bool, +eb: {S.le(~A, ~cmp, x, h) == b : Bool}, +ih: {S.sorted(~A, ~cmp, S.ins(~A, ~cmp, x, t)) == True{} : Bool}) -> {S.sorted(~A, ~cmp, S.ins(~A, ~cmp, x, Con{h, t})) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{h, t}), Bool.pick(List<&2, A>, True{}, Con{x, Con{h, t}}, Con{h, S.ins(~A, ~cmp, x, t)}), M.ins_cons(~A, ~cmp, x, h, t, True{}, eb)) : {S.sorted(~A, ~cmp, _) == True{} : Bool}
      L.and_intro(S.all_ge(~A, ~cmp, x, Con{h, t}), S.sorted(~A, ~cmp, Con{h, t}), L.and_intro(S.le(~A, ~cmp, x, h), S.all_ge(~A, ~cmp, x, t), eb, ag_trans(~A, ~cmp, ~o, x, h, t, eb, L.and_left(S.all_ge(~A, ~cmp, h, t), S.sorted(~A, ~cmp, t), hs))), hs)
    case False{}:
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{h, t}), Bool.pick(List<&2, A>, False{}, Con{x, Con{h, t}}, Con{h, S.ins(~A, ~cmp, x, t)}), M.ins_cons(~A, ~cmp, x, h, t, False{}, eb)) : {S.sorted(~A, ~cmp, _) == True{} : Bool}
      %Equal.sym(Bool, S.all_ge(~A, ~cmp, h, S.ins(~A, ~cmp, x, t)), Bool.and(S.le(~A, ~cmp, h, x), S.all_ge(~A, ~cmp, h, t)), M.all_ge_ins(~A, ~cmp, ~o, h, x, t)) : {Bool.and(_, S.sorted(~A, ~cmp, S.ins(~A, ~cmp, x, t))) == True{} : Bool}
      L.and_intro(Bool.and(S.le(~A, ~cmp, h, x), S.all_ge(~A, ~cmp, h, t)), S.sorted(~A, ~cmp, S.ins(~A, ~cmp, x, t)), L.and_intro(S.le(~A, ~cmp, h, x), S.all_ge(~A, ~cmp, h, t), O.total(~A, ~cmp, ~o, x, h, eb), L.and_left(S.all_ge(~A, ~cmp, h, t), S.sorted(~A, ~cmp, t), hs)), ih)

def ins_sorted(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +x: A, +xs: List<&2, A>, +hs: {S.sorted(~A, ~cmp, xs) == True{} : Bool}) -> {S.sorted(~A, ~cmp, S.ins(~A, ~cmp, x, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      is_c(~A, ~cmp, ~o, x, h, t, hs, S.le(~A, ~cmp, x, h), {==}, ins_sorted(~A, ~cmp, ~o, x, t, L.and_right(S.all_ge(~A, ~cmp, h, t), S.sorted(~A, ~cmp, t), hs)))

def msort_sorted(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +xs: List<&2, A>) -> {S.sorted(~A, ~cmp, VL.msort(~A, ~cmp, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      ins_sorted(~A, ~cmp, ~o, h, VL.msort(~A, ~cmp, t), msort_sorted(~A, ~cmp, ~o, t))

# every model (the multiset of a heap) is ascending
def model_sorted(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +sh: ST.Shadow<A>) -> {S.sorted(~A, ~cmp, ST.model(~A, ~cmp, sh)) == True{} : Bool}:
  match sh:
    case ST.Sh{+size, +depth, +t}:
      msort_sorted(~A, ~cmp, ~o, VL.vals(~A, AR.slots(Maybe<&2, A>, t), size))

def from_list_sorted_go(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +ys: List<&2, A>, +acc: List<&2, A>, +hs: {S.sorted(~A, ~cmp, acc) == True{} : Bool}) -> {S.sorted(~A, ~cmp, S.from_list(~A, ~cmp, ys, acc)) == True{} : Bool}:
  match ys:
    case Nil{}:
      hs
    case Con{+y, +t}:
      from_list_sorted_go(~A, ~cmp, ~o, t, S.ins(~A, ~cmp, y, acc), ins_sorted(~A, ~cmp, ~o, y, acc, hs))

# ---- lengths ----
def ins_len_c(~A: Data, ~cmp: A -> A -> Cmp, +x: A, +h: A, +t: List<&2, A>, +b: Bool, +eb: {S.le(~A, ~cmp, x, h) == b : Bool}, +ih: {SC.length(A, S.ins(~A, ~cmp, x, t)) == 1n+SC.length(A, t) : Nat}) -> {SC.length(A, S.ins(~A, ~cmp, x, Con{h, t})) == 1n+SC.length(A, Con{h, t}) : Nat}:
  match b:
    case True{}:
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{h, t}), Bool.pick(List<&2, A>, True{}, Con{x, Con{h, t}}, Con{h, S.ins(~A, ~cmp, x, t)}), M.ins_cons(~A, ~cmp, x, h, t, True{}, eb)) : {SC.length(A, _) == 1n+SC.length(A, Con{h, t}) : Nat}
      {==}
    case False{}:
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{h, t}), Bool.pick(List<&2, A>, False{}, Con{x, Con{h, t}}, Con{h, S.ins(~A, ~cmp, x, t)}), M.ins_cons(~A, ~cmp, x, h, t, False{}, eb)) : {SC.length(A, _) == 1n+SC.length(A, Con{h, t}) : Nat}
      N.succ_cong(SC.length(A, S.ins(~A, ~cmp, x, t)), 1n+SC.length(A, t), ih)

def ins_length(~A: Data, ~cmp: A -> A -> Cmp, +x: A, +xs: List<&2, A>) -> {SC.length(A, S.ins(~A, ~cmp, x, xs)) == 1n+SC.length(A, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      ins_len_c(~A, ~cmp, x, h, t, S.le(~A, ~cmp, x, h), {==}, ins_length(~A, ~cmp, x, t))

def succ_add(+a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == Nat.add(1n+a, b) : Nat}:
  Equal.trans(Nat, Nat.add(a, 1n+b), 1n+Nat.add(a, b), Nat.add(1n+a, b), N.add_succ(a, b),
    Equal.trans(Nat, 1n+Nat.add(a, b), 1n+Nat.add(b, a), Nat.add(1n+a, b), N.succ_cong(Nat.add(a, b), Nat.add(b, a), N.add_comm(a, b)),
      Equal.trans(Nat, 1n+Nat.add(b, a), Nat.add(b, 1n+a), Nat.add(1n+a, b), Equal.sym(Nat, Nat.add(b, 1n+a), 1n+Nat.add(b, a), N.add_succ(b, a)), N.add_comm(b, 1n+a))))

def from_list_length_go(~A: Data, ~cmp: A -> A -> Cmp, +ys: List<&2, A>, +acc: List<&2, A>) -> {SC.length(A, S.from_list(~A, ~cmp, ys, acc)) == Nat.add(SC.length(A, ys), SC.length(A, acc)) : Nat}:
  match ys:
    case Nil{}:
      Equal.sym(Nat, Nat.add(0n, SC.length(A, acc)), SC.length(A, acc), Equal.trans(Nat, Nat.add(0n, SC.length(A, acc)), Nat.add(SC.length(A, acc), 0n), SC.length(A, acc), N.add_comm(0n, SC.length(A, acc)), N.add_zero(SC.length(A, acc))))
    case Con{+y, +t}:
      %Equal.sym(Nat, SC.length(A, S.from_list(~A, ~cmp, t, S.ins(~A, ~cmp, y, acc))), Nat.add(SC.length(A, t), SC.length(A, S.ins(~A, ~cmp, y, acc))), from_list_length_go(~A, ~cmp, t, S.ins(~A, ~cmp, y, acc))) : {_ == Nat.add(1n+SC.length(A, t), SC.length(A, acc)) : Nat}
      %Equal.sym(Nat, SC.length(A, S.ins(~A, ~cmp, y, acc)), 1n+SC.length(A, acc), ins_length(~A, ~cmp, y, acc)) : {Nat.add(SC.length(A, t), _) == Nat.add(1n+SC.length(A, t), SC.length(A, acc)) : Nat}
      succ_add(SC.length(A, t), SC.length(A, acc))

# ---- Length ----
def length_result(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>) -> S.Length.length_result(~A, ~cmp, xs):
  {==}

def length_frame(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>) -> S.Length.length_frame(~A, ~cmp, xs):
  {==}

# ---- Empty_Set ----
def new_empty(~A: Data, ~cmp: A -> A -> Cmp) -> {ST.model(~A, ~cmp, ST.initial(~A)) == Nil{} : List<&2, A>}:
  new_abs(~A, ~cmp)

# ---- Insert: one more element, exactly one more occurrence of it, still ordered ----
def push_length(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>, +x: A) -> S.Insert.push_length(~A, ~cmp, xs, x):
  ins_length(~A, ~cmp, x, xs)

def push_bag(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +xs: List<&2, A>, +x: A) -> S.Insert.push_bag(~A, ~cmp, ~o, xs, x):
  BG.del_ins(~A, ~cmp, ~o, x, xs)

def push_sorted(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +xs: List<&2, A>, +x: A, +hs: {S.sorted(~A, ~cmp, xs) == True{} : Bool}) -> S.Insert.push_sorted(~A, ~cmp, ~o, xs, x, hs):
  ins_sorted(~A, ~cmp, ~o, x, xs, hs)

# ---- First_Element: the minimum; nothing changes ----
def peek_min(~A: Data, ~cmp: A -> A -> Cmp, +h: A, +t: List<&2, A>, +hs: {S.sorted(~A, ~cmp, Con{h, t}) == True{} : Bool}) -> S.First_Element.peek_min(~A, ~cmp, h, t, hs):
  ({==}, L.and_left(S.all_ge(~A, ~cmp, h, t), S.sorted(~A, ~cmp, t), hs))

def peek_frame(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>) -> S.First_Element.peek_frame(~A, ~cmp, xs):
  {==}

def peek_empty(~A: Data, ~cmp: A -> A -> Cmp) -> S.First_Element.peek_empty(~A, ~cmp):
  {==}

# ---- Delete_First: the minimum is removed once; the result is it ----
def pop_length(~A: Data, ~cmp: A -> A -> Cmp, +h: A, +t: List<&2, A>) -> S.Delete_First.pop_length(~A, ~cmp, h, t):
  {==}

def pop_result(~A: Data, ~cmp: A -> A -> Cmp, +h: A, +t: List<&2, A>) -> S.Delete_First.pop_result(~A, ~cmp, h, t):
  {==}

def pop_min(~A: Data, ~cmp: A -> A -> Cmp, +h: A, +t: List<&2, A>, +hs: {S.sorted(~A, ~cmp, Con{h, t}) == True{} : Bool}) -> S.Delete_First.pop_min(~A, ~cmp, h, t, hs):
  L.and_left(S.all_ge(~A, ~cmp, h, t), S.sorted(~A, ~cmp, t), hs)

# the old multiset is the new one with the minimum put back
def pop_bag(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +h: A, +t: List<&2, A>, +hs: {S.sorted(~A, ~cmp, Con{h, t}) == True{} : Bool}) -> S.Delete_First.pop_bag(~A, ~cmp, ~o, h, t, hs):
  M.ins_min(~A, ~cmp, ~o, h, t, L.and_left(S.all_ge(~A, ~cmp, h, t), S.sorted(~A, ~cmp, t), hs))

def pop_empty(~A: Data, ~cmp: A -> A -> Cmp) -> S.Delete_First.pop_empty(~A, ~cmp):
  {==}

# ---- To_Set: the multiset of the list, ordered ----
def from_list_model(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>, +ys: List<&2, A>) -> S.To_Set.from_list_model(~A, ~cmp, xs, ys):
  {==}

def from_list_length(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>, +ys: List<&2, A>) -> S.To_Set.from_list_length(~A, ~cmp, xs, ys):
  Equal.trans(Nat, SC.length(A, S.from_list(~A, ~cmp, ys, Nil{})), Nat.add(SC.length(A, ys), 0n), SC.length(A, ys), from_list_length_go(~A, ~cmp, ys, Nil{}), N.add_zero(SC.length(A, ys)))

def from_list_sorted(~A: Data, ~cmp: A -> A -> Cmp, ~o: SO.Order(~A, ~cmp), +xs: List<&2, A>, +ys: List<&2, A>) -> S.To_Set.from_list_sorted(~A, ~cmp, ~o, xs, ys):
  from_list_sorted_go(~A, ~cmp, ~o, ys, Nil{}, {==})

# ---- Elements: to_sorted_list returns the ordered model ----
def to_sorted_result(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>) -> S.Elements.to_sorted_result(~A, ~cmp, xs):
  {==}

def to_sorted_frame(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>) -> S.Elements.to_sorted_frame(~A, ~cmp, xs):
  {==}
