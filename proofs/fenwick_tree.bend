import Base
import ./lib/list.bend as LL
import ../spec/common.bend as SC
import ../spec/u32seq.bend as Q
import ../spec/fenwick_tree.bend as S
import ../src/fenwick_tree.bend as F
import ../types/fenwick_tree.bend as E
import ./lib/u32alg.bend as UA
import ./lib/u32seq.bend as QS
import ./fenwick_tree/model.bend as M
import ./fenwick_tree/tree.bend as T
import ./fenwick_tree/arr.bend as AR
import ./fenwick_tree/walk.bend as W
import ./fenwick_tree/depth.bend as DP
import ./fenwick_tree/state.bend as ST
import ./fenwick_tree/steps.bend as PS
import ./fenwick_tree/init.bend as IN
import ./fenwick_tree/trace.bend as FT

# Fenwick tree: public proof entry point.
#   abstraction  ST.model(sh)  (the first n values)
#   invariant    ST.good(sh)   (the cell array is a perfect tree of depth
#                d+1, so every cell index is a representable U32; n <= 2^d;
#                every internal cell holds the exact sum of its block's left
#                half)
#   shadow       ST.Sh / ST.real / ST.good / ST.model  (Base.Array is linear,
#                so every law is about the array built from a Data mirror
#                tree, exactly as in proofs/bitset and proofs/union_find)
#   model tree   M.* (the perfect tree of partial sums the flat cells
#                realise; unchanged from the tree-shaped implementation)
#   layout       W.* (which cell holds which node, the frame lemmas of the
#                split-point layout, and that the index walks of src are the
#                model's tree walks)
#   arithmetic   UA.* (U32 add associative/commutative/zero, (a+b)-a = b),
#                derived from Base's Word adder; spec sums wrap mod 2^32
#   operations   PS.step_ok (errors: IndexOutOfRange, InvalidRange)
#   traces       trace_new (arbitrary op lists from new(n))
#
# `capacity(n)` is the documented capacity condition of the flat
# representation: 2^30 values, so the cell array's depth d+1 is at most 31
# and every cell index is a representable U32 (see src/fenwick_tree.bend).
# It is a premise only of the laws about the constructors; every other law
# holds at every state satisfying the invariant, and the invariant itself
# implies it.

def capacity(+n: Nat) -> Type:
  {Nat.is_le(n, SC.pow2(F.depth_for(n))) == True{} : Bool}

def new_abs(+n: Nat, +h: {Nat.is_le(n, SC.pow2(F.depth_for(n))) == True{} : Bool}) -> {ST.model(IN.initial(n)) == S.new(n) : List<&2, U32>}:
  IN.new_model(n, h)

def new_inv(+n: Nat, +h: {Nat.is_le(n, SC.pow2(F.depth_for(n))) == True{} : Bool}) -> {ST.good(IN.initial(n)) == True{} : Bool}:
  IN.new_good(n, h)

def new_real(+n: Nat) -> {F.new(n) == ST.real(IN.initial(n)) : F.Fenwick}:
  IN.new_real(n)

def from_list_ok(+xs: List<&2, U32>, +h: {Nat.is_le(F.count(xs), SC.pow2(F.depth_for(F.count(xs)))) == True{} : Bool}) -> IN.FillOK(xs, Nil{}, IN.initial(F.count(xs))):
  IN.from_ok(xs, h)

def step_ok(+sh: ST.Sh, op: E.Op, +g: {ST.good(sh) == True{} : Bool}) -> PS.StepOK(sh, op):
  PS.step_ok(sh, op, g)

# A runtime tree determines its shadow, so "the operation lands on the array
# of THIS shadow, whose model is the spec's" pins the abstract state: the
# laws above cannot be satisfied by naming a different shadow.
def shadow_unique(+a: ST.Sh, +b: ST.Sh, +e: {ST.real(a) == ST.real(b) : F.Fenwick}) -> {a == b : ST.Sh}:
  ST.real_inj(a, b, e)

# Arbitrary finite operation traces from the real constructor.
def trace_new(+n: Nat, +ops: List<&2, E.Op>, +h: {Nat.is_le(n, SC.pow2(F.depth_for(n))) == True{} : Bool}) -> FT.TraceOK(ops, IN.initial(n)):
  FT.trace_from(ops, IN.initial(n), IN.new_good(n, h))

# ---- from_list: the shadow it builds, and traces from it ----

def from_list_shadow(+xs: List<&2, U32>, +h: {Nat.is_le(F.count(xs), SC.pow2(F.depth_for(F.count(xs)))) == True{} : Bool}) -> ST.Sh:
  IN.fo_sh(xs, Nil{}, IN.initial(F.count(xs)), IN.from_ok(xs, h))

def from_list_real(+xs: List<&2, U32>, +h: {Nat.is_le(F.count(xs), SC.pow2(F.depth_for(F.count(xs)))) == True{} : Bool}) -> {F.from_list(xs) == ST.real(from_list_shadow(xs, h)) : F.Fenwick}:
  %Equal.sym(F.Fenwick, F.new(F.count(xs)), ST.real(IN.initial(F.count(xs))), IN.new_real(F.count(xs))) : {F.fill(xs, 0n, _) == ST.real(from_list_shadow(xs, h)) : F.Fenwick}
  IN.fo_run(xs, Nil{}, IN.initial(F.count(xs)), IN.from_ok(xs, h))

def from_list_inv(+xs: List<&2, U32>, +h: {Nat.is_le(F.count(xs), SC.pow2(F.depth_for(F.count(xs)))) == True{} : Bool}) -> {ST.good(from_list_shadow(xs, h)) == True{} : Bool}:
  IN.fo_good(xs, Nil{}, IN.initial(F.count(xs)), IN.from_ok(xs, h))

def from_list_abs(+xs: List<&2, U32>, +h: {Nat.is_le(F.count(xs), SC.pow2(F.depth_for(F.count(xs)))) == True{} : Bool}) -> {ST.model(from_list_shadow(xs, h)) == S.from_list(xs) : List<&2, U32>}:
  IN.fo_model(xs, Nil{}, IN.initial(F.count(xs)), IN.from_ok(xs, h))

def trace_from_list(+xs: List<&2, U32>, +ops: List<&2, E.Op>, +h: {Nat.is_le(F.count(xs), SC.pow2(F.depth_for(F.count(xs)))) == True{} : Bool}) -> FT.TraceOK(ops, from_list_shadow(xs, h)):
  FT.trace_from(ops, from_list_shadow(xs, h), from_list_inv(xs, h))
