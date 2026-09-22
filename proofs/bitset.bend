import Base
import ./lib/array.bend as A
import ./spec/common.bend as SC
import ./spec/bitset.bend as S
import ../src/containers/bitset.bend as B
import ../src/containers/types/bitset.bend as E
import ./bitset/lists.bend as BL
import ./bitset/word.bend as W
import ./bitset/index.bend as IX
import ./bitset/depth.bend as DP
import ./bitset/arr.bend as AR
import ./bitset/state.bend as ST
import ./bitset/steps.bend as BS
import ./bitset/trace.bend as BT

# Packed bitset: public proof entry point.
#   abstraction  ST.abs(n, t)  (first n bits of the stored U32 words)
#   invariant    ST.rep(n, d, t)  (the depth is the one `depth_for` picks, the
#                word array is a perfect tree of that depth, n <= stored bits,
#                every stored bit at a position >= n is zero)
#   shadow       ST.Sh / ST.real / ST.good / ST.model  (Base.Array is linear,
#                so every law is about the array built from a Data mirror
#                tree, exactly as in proofs/dynamic_array)
#   word facts   W.*     (U32 and/or/xor/not/shifts from Base's Word defs)
#   index facts  IX.*    (i / 32 and i % 32 peel 32 bits at a time)
#   array facts  AR.*    (Base.Array get/set against the slot list)
#   operations   BS.step_ok (every op; IndexOutOfRange / LengthMismatch keep
#                the state)
#   traces       trace_new (arbitrary op lists from B.new(n))
#
# `capacity(n)` is the documented capacity condition of the packed
# representation: 2^31 words = 2^36 bits (see src/bitset.bend). It is a
# premise only of the laws about `new`; every other law holds at every state
# satisfying the invariant, and the invariant itself implies it
# (ST.rep_fits).

def capacity(+n: Nat) -> Type:
  {Nat.is_le(n, Nat.mul(SC.pow2(B.depth_for(n)), 32n)) == True{} : Bool}

def new_abs(+n: Nat, +h: {Nat.is_le(n, Nat.mul(SC.pow2(B.depth_for(n)), 32n)) == True{} : Bool}) -> {ST.model(BT.initial(n)) == S.new(n) : List<&2, Bool>}:
  BT.new_model(n, h)

def new_inv(+n: Nat, +h: {Nat.is_le(n, Nat.mul(SC.pow2(B.depth_for(n)), 32n)) == True{} : Bool}) -> {ST.good(BT.initial(n)) == True{} : Bool}:
  BT.new_good(n, h)

def new_real(+n: Nat) -> {B.new(n) == ST.real(BT.initial(n)) : B.Bitset}:
  BT.new_real(n)

def from_bools(+ys: List<&2, Bool>, +hf: {Nat.is_le(B.bool_count(ys), Nat.mul(SC.pow2(B.depth_for(B.bool_count(ys))), 32n)) == True{} : Bool}) -> BS.FromOK(ys):
  BS.from_ok(ys, hf)

def step_ok(sh: ST.Sh, op: E.Op, +g: {ST.good(sh) == True{} : Bool}) -> BS.StepOK(sh, op):
  BS.step_ok(sh, op, g)

# A runtime bitset determines its shadow, so "the operation lands on the array
# of THIS shadow, whose model is the spec's" pins the abstract state: the laws
# above cannot be satisfied by naming a different shadow.
def shadow_unique(+a: ST.Sh, +b: ST.Sh, +e: {ST.real(a) == ST.real(b) : B.Bitset}) -> {a == b : ST.Sh}:
  ST.real_inj(a, b, e)

# Arbitrary finite operation traces from the real constructor.
def trace_new(+n: Nat, +ops: List<&2, E.Op>, +h: {Nat.is_le(n, Nat.mul(SC.pow2(B.depth_for(n)), 32n)) == True{} : Bool}) -> BT.TraceOK(ops, BT.initial(n)):
  BT.trace_from(ops, BT.initial(n), BT.new_good(n, h))
