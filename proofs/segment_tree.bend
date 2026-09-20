import Base
import ./lib/list.bend as LL
import ../spec/common.bend as SC
import ../spec/u32seq.bend as Q
import ../spec/segment_tree.bend as S
import ../src/segment_tree.bend as F
import ../types/segment_tree.bend as E
import ./lib/u32alg.bend as UA
import ./lib/u32seq.bend as QS
import ./segment_tree/node.bend as TN
import ./segment_tree/model.bend as M
import ./segment_tree/ops.bend as O
import ./segment_tree/arr.bend as AR
import ./segment_tree/walk.bend as W
import ./segment_tree/depth.bend as DP
import ./segment_tree/state.bend as ST
import ./segment_tree/steps.bend as PS
import ./segment_tree/init.bend as IN
import ./segment_tree/trace.bend as FT

# Segment tree: public proof entry point.
#   abstraction  ST.model(sh)  (the first n values of the tree the two cell
#                arrays realise; a node's lazy tag is added to all values
#                below it)
#   invariant    ST.good(sh)   (the sum array is a perfect tree of depth d+1
#                and the tag array one of depth d, so every cell index is a
#                representable U32; n <= 2^d; every node of the realised tree
#                stores the exact sum of its subtree)
#   shadow       ST.Sh / ST.real / ST.good / ST.model  (Base.Array is linear,
#                so every law is about the structure built from Data mirror
#                trees, exactly as in proofs/fenwick_tree and proofs/bitset)
#   model tree   TN.* / M.* (the perfect tree of sums and tags the flat cells
#                realise; unchanged from the tree-shaped implementation)
#   layout       W.* (which cell holds which node, the frame lemmas of the
#                split-point layout, and that the index walks of src are the
#                model's tree walks)
#   laziness     O.padd_* (a fully covered block only gets a tag), M.tag_*
#   arithmetic   UA.* (derived from Base's Word adder); spec wraps mod 2^32
#   operations   PS.step_ok (errors: IndexOutOfRange, InvalidRange)
#   traces       trace_new (arbitrary op lists from new(n)) and
#                trace_from_list
#
# `capacity(n)` is the documented capacity condition of the flat
# representation: 2^30 values, so the sum array's depth d+1 is at most 31 and
# every cell index is a representable U32 (see src/segment_tree.bend). It is
# a premise only of the laws about the constructors; every other law holds at
# every state satisfying the invariant, and the invariant itself implies it.

def capacity(+n: Nat) -> Type:
  {Nat.is_le(n, SC.pow2(F.depth_for(n))) == True{} : Bool}

def new_abs(+n: Nat, +h: {Nat.is_le(n, SC.pow2(F.depth_for(n))) == True{} : Bool}) -> {ST.model(IN.initial(n)) == S.new(n) : List<&2, U32>}:
  IN.new_model(n, h)

def new_inv(+n: Nat, +h: {Nat.is_le(n, SC.pow2(F.depth_for(n))) == True{} : Bool}) -> {ST.good(IN.initial(n)) == True{} : Bool}:
  IN.new_good(n, h)

def new_real(+n: Nat) -> {F.new(n) == ST.real(IN.initial(n)) : F.SegTree}:
  IN.new_real(n)

def from_list_ok(+xs: List<&2, U32>, +h: {Nat.is_le(F.count(xs), SC.pow2(F.depth_for(F.count(xs)))) == True{} : Bool}) -> IN.FillOK(xs, Nil{}, IN.initial(F.count(xs))):
  IN.from_ok(xs, h)

def step_ok(+sh: ST.Sh, op: E.Op, +g: {ST.good(sh) == True{} : Bool}) -> PS.StepOK(sh, op):
  PS.step_ok(sh, op, g)

# A runtime tree determines its shadow, so "the operation lands on the arrays
# of THIS shadow, whose model is the spec's" pins the abstract state: the
# laws above cannot be satisfied by naming a different shadow.
def shadow_unique(+a: ST.Sh, +b: ST.Sh, +e: {ST.real(a) == ST.real(b) : F.SegTree}) -> {a == b : ST.Sh}:
  ST.real_inj(a, b, e)

# Arbitrary finite operation traces from the real constructor.
def trace_new(+n: Nat, +ops: List<&2, E.Op>, +h: {Nat.is_le(n, SC.pow2(F.depth_for(n))) == True{} : Bool}) -> FT.TraceOK(ops, IN.initial(n)):
  FT.trace_from(ops, IN.initial(n), IN.new_good(n, h))

# ---- from_list: the shadow it builds, and traces from it ----

def from_list_shadow(+xs: List<&2, U32>, +h: {Nat.is_le(F.count(xs), SC.pow2(F.depth_for(F.count(xs)))) == True{} : Bool}) -> ST.Sh:
  IN.fo_sh(xs, Nil{}, IN.initial(F.count(xs)), IN.from_ok(xs, h))

def from_list_real(+xs: List<&2, U32>, +h: {Nat.is_le(F.count(xs), SC.pow2(F.depth_for(F.count(xs)))) == True{} : Bool}) -> {F.from_list(xs) == ST.real(from_list_shadow(xs, h)) : F.SegTree}:
  %Equal.sym(F.SegTree, F.new(F.count(xs)), ST.real(IN.initial(F.count(xs))), IN.new_real(F.count(xs))) : {F.fill(xs, 0n, _) == ST.real(from_list_shadow(xs, h)) : F.SegTree}
  IN.fo_run(xs, Nil{}, IN.initial(F.count(xs)), IN.from_ok(xs, h))

def from_list_inv(+xs: List<&2, U32>, +h: {Nat.is_le(F.count(xs), SC.pow2(F.depth_for(F.count(xs)))) == True{} : Bool}) -> {ST.good(from_list_shadow(xs, h)) == True{} : Bool}:
  IN.fo_good(xs, Nil{}, IN.initial(F.count(xs)), IN.from_ok(xs, h))

def from_list_abs(+xs: List<&2, U32>, +h: {Nat.is_le(F.count(xs), SC.pow2(F.depth_for(F.count(xs)))) == True{} : Bool}) -> {ST.model(from_list_shadow(xs, h)) == S.from_list(xs) : List<&2, U32>}:
  IN.fo_model(xs, Nil{}, IN.initial(F.count(xs)), IN.from_ok(xs, h))

def trace_from_list(+xs: List<&2, U32>, +ops: List<&2, E.Op>, +h: {Nat.is_le(F.count(xs), SC.pow2(F.depth_for(F.count(xs)))) == True{} : Bool}) -> FT.TraceOK(ops, from_list_shadow(xs, h)):
  FT.trace_from(ops, from_list_shadow(xs, h), from_list_inv(xs, h))
