import Base
import ../spec/common.bend as SC
import ../spec/union_find.bend as S
import ../src/union_find.bend as U
import ../types/union_find.bend as E
import ./union_find/cells.bend as CL
import ./union_find/model.bend as M
import ./union_find/union.bend as UN
import ./union_find/arr.bend as AR
import ./union_find/state.bend as ST
import ./union_find/steps.bend as PS
import ./union_find/init.bend as IN
import ./union_find/trace.bend as UT

# Union-find: public proof entry point.
#   abstraction  ST.model(sh)  (the representative of each element 0 .. n-1)
#   invariant    ST.good(sh)   (three perfect arenas of the depth `depth_for`
#                picks; every stored representative is a fixed point whose
#                member list is exactly its class and whose size slot is the
#                exact class size; count = number of classes)
#   shadow       ST.Sh / ST.real / ST.good / ST.model  (Base.Array is linear,
#                so every law is about the arenas built from the three Data
#                mirror trees, exactly as in proofs/bitset)
#   cells        CL.* (the cell list the mathematics talks about, zipped from
#                the three arenas)
#   union        UN.* (relinking the smaller class = the spec relabelling)
#   operations   PS.step_ok (every op; any index >= n gives OutOfRange)
#   traces       trace_new (arbitrary op lists from U.new(n))
#
# `capacity(n)` is the documented capacity condition of the arena
# representation: 2^31 slots (see src/union_find.bend). It is a premise only
# of the laws about `new`; every other law holds at every state satisfying
# the invariant, and the invariant itself implies it (ST.g_cap).

def capacity(+n: Nat) -> Type:
  {Nat.is_le(n, SC.pow2(U.depth_for(n))) == True{} : Bool}

def new_abs(+n: Nat, +h: {Nat.is_le(n, SC.pow2(U.depth_for(n))) == True{} : Bool}) -> {ST.model(IN.initial(n)) == S.new(n) : List<&2, Nat>}:
  IN.new_model(n, h)

def new_inv(+n: Nat, +h: {Nat.is_le(n, SC.pow2(U.depth_for(n))) == True{} : Bool}) -> {ST.good(IN.initial(n)) == True{} : Bool}:
  IN.new_good(n, h)

def new_real(+n: Nat) -> {U.new(n) == ST.real(IN.initial(n)) : U.UnionFind}:
  IN.new_real(n)

def step_ok(+sh: ST.Sh, op: E.Op, +g: {ST.good(sh) == True{} : Bool}) -> PS.StepOK(sh, op):
  PS.step_ok(sh, op, g)

# A runtime structure determines its shadow, so "the operation lands on the
# arenas of THIS shadow, whose model is the spec's" pins the abstract state:
# the laws above cannot be satisfied by naming a different shadow.
def shadow_unique(+a: ST.Sh, +b: ST.Sh, +e: {ST.real(a) == ST.real(b) : U.UnionFind}) -> {a == b : ST.Sh}:
  ST.real_inj(a, b, e)

# Arbitrary finite operation traces from the real constructor.
def trace_new(+n: Nat, +ops: List<&2, E.Op>, +h: {Nat.is_le(n, SC.pow2(U.depth_for(n))) == True{} : Bool}) -> UT.TraceOK(ops, IN.initial(n)):
  UT.trace_from(ops, IN.initial(n), IN.new_good(n, h))
