import Base
import ./lib/logic.bend as L
import ./lib/nat.bend as N
import ./lib/list.bend as LL
import ./lib/array.bend as AR
import ../spec/common.bend as SC
import ../spec/deque.bend as S
import ../src/deque.bend as DQ
import ../types/deque.bend as E
import ./dynamic_array/layout.bend as LY
import ./deque/layout.bend as WN
import ./deque/state.bend as ST
import ./deque/walk.bend as W
import ./deque/steps.bend as PS
import ./deque/init.bend as IN
import ./deque/trace.bend as FT
import ./deque/closed.bend as CL
import ./deque/budget.bend as BU

# Deque: public proof entry point.
#   abstraction  ST.model(sh)  (the elements of the window, front first)
#   invariant    ST.good(sh)   (depth <= 31, so every slot index is a
#                representable U32; the slot tree is perfect of that depth;
#                the Some slots are exactly the window [lo, lo + len))
#   shadow       ST.Sh / ST.real / ST.good / ST.model  (Base.Array is linear,
#                so every law is about the deque built from a Data mirror
#                tree, exactly as in proofs/dynamic_array and proofs/bitset)
#   layout       WN.* (the window lemmas: which slot holds which element and
#                what each end operation does to the window), W.* (the
#                indexed read walk of to_list)
#   operations   PS.step_ok (errors: pop/peek on an empty deque)
#   traces       trace_from (arbitrary op lists from any good shadow)
#   closed       CL.* (the executable `*_at` specializations compute what the
#                parametric definitions compute, so every law transfers)
#
# The capacity condition of the representation. A push doubles the block
# when the window touches the block's end on that side, so the window can
# drift and the depth is bounded by the number of pushes, not by the size.
# The amortized argument is proved: a shadow within budget for P pushes
# (proofs/deque/budget.bend: 1 + 2(lo+len) <= 2^d + 2P, 2^d <= 1 + 2(P+lo),
# len <= P) stays within budget after every operation, and 1 + 2P < 2^q with
# q <= 31 keeps every doubled block within 2^31 slots. The trace laws carry
# 1 + 2(P + pushes(ops)) < 2^q -- the representation's capacity condition,
# with no bound on the length of the trace. It is a premise only of the step
# and trace laws; every other law holds at every state satisfying the
# invariant.

def new_abs(-T: Data) -> {ST.model(T, IN.initial(T)) == Nil{} : List<&2, T>}:
  IN.new_model(T)

def new_inv(-T: Data) -> {ST.good(T, IN.initial(T)) == True{} : Bool}:
  IN.new_good(T)

def new_real(-T: Data) -> {DQ.new(T) == ST.real(T, IN.initial(T)) : DQ.Deque<T>}:
  IN.new_real(T)

def step_ok(-T: Data, +sh: ST.Shadow<T>, op: E.Op<T>, +g: {ST.good(T, sh) == True{} : Bool}, +P: Nat, +hb: {BU.bud(T, sh, P) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(1n+Nat.double(P), SC.pow2(q)) == True{} : Bool}) -> PS.StepOK(T, sh, op):
  PS.step_ok(T, sh, op, g, P, hb, q, hq, room)

# A runtime deque determines its shadow, so naming the shadow an operation
# lands on pins the abstract state.
def shadow_unique(-T: Data, +a: ST.Shadow<T>, +b: ST.Shadow<T>, +e: {ST.real(T, a) == ST.real(T, b) : DQ.Deque<T>}) -> {a == b : ST.Shadow<T>}:
  ST.real_inj(T, a, b, e)

# Arbitrary finite operation traces from the real constructor.
def trace_new(-T: Data, +ops: List<&2, E.Op<T>>, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(1n+Nat.double(FT.pushes(T, ops)), SC.pow2(q)) == True{} : Bool}) -> FT.TraceOK(T, ops, IN.initial(T)):
  FT.trace_from(T, ops, IN.initial(T), IN.new_good(T), 0n, {==}, q, hq, room)

# The same trace law for the executable specializations.
def trace_new_at(~T: Data, +ops: List<&2, E.Op<T>>, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(1n+Nat.double(FT.pushes(T, ops)), SC.pow2(q)) == True{} : Bool}) -> {DQ.run_at(~T, ops, ST.real(T, IN.initial(T))) == DQ.run(T, ops, ST.real(T, IN.initial(T))) : DQ.Deque<T> & List<&2, E.Obs<T>>}:
  CL.run_eq(~T, ops, IN.initial(T), IN.new_good(T), 0n, {==}, q, hq, room)
