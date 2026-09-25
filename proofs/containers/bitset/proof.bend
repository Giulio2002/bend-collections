import Base
import ../../lib/array.bend as A
import ../../../spec/lib/common.bend as SC
import ../../../spec/containers/bitset.bend as S
import ../../../src/containers/bitset.bend as B
import ../../../src/containers/types/bitset.bend as E
import ./lists.bend as BL
import ./word.bend as W
import ./index.bend as IX
import ./depth.bend as DP
import ./arr.bend as AR
import ./state.bend as ST
import ./steps.bend as BS
import ./trace.bend as BT
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL

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

# ==== the contract of bitset (stated in spec/containers/bitset.bend) ====================

# ---- the implementation ----
def Impl(sh: ST.Sh, op: E.Op, Post: (List<&2, Bool> & E.Obs) -> Type) -> Type:
  Sigma<&1, &1, ST.Sh, sh2 => Sigma<&1, &1, E.Obs, o => {B.step(ST.real(sh), op) == (ST.real(sh2), o) : B.Bitset & E.Obs} & ({ST.good(sh2) == True{} : Bool} & Post((ST.model(sh2), o)))>>

def impl_of(-sh: ST.Sh, -op: E.Op, -Post: (List<&2, Bool> & E.Obs) -> Type, k: BS.StepOK(sh, op), pf: Post(S.step(ST.model(sh), op))) -> Impl(sh, op, Post):
  match k:
    case Tuple{sh2, Tuple{o, Tuple{e1, Tuple{g2, e2}}}}:
      (sh2, (o, (e1, (g2, L.subst(List<&2, Bool> & E.Obs, Post, S.step(ST.model(sh), op), (ST.model(sh2), o), Equal.sym(List<&2, Bool> & E.Obs, (ST.model(sh2), o), S.step(ST.model(sh), op), e2), pf)))))

def impl(sh: ST.Sh, op: E.Op, +g: {ST.good(sh) == True{} : Bool}, -Post: (List<&2, Bool> & E.Obs) -> Type, pf: Post(S.step(ST.model(sh), op))) -> Impl(sh, op, Post):
  impl_of(sh, op, Post, step_ok(sh, op, g), pf)

# ---- arithmetic and Boolean facts ----
def succ_ne_zero(+a: Nat, +e: {1n+a == 0n : Nat}) -> Empty:
  L.false_true(Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), 1n+a, 0n, e))

def zero_ne_succ(+a: Nat, +e: {0n == 1n+a : Nat}) -> Empty:
  L.true_false(Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), 0n, 1n+a, e))

def succ_pick(+b: Bool, +x: Nat, +y: Nat) -> {1n+Bool.pick(Nat, b, x, y) == Bool.pick(Nat, b, 1n+x, 1n+y) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def zero_add(+n: Nat) -> {Nat.add(0n, n) == n : Nat}:
  Equal.trans(Nat, Nat.add(0n, n), Nat.add(n, 0n), n, N.add_comm(0n, n), N.add_zero(n))

def succ_add(+a: Nat, +b: Nat) -> {Nat.add(1n+a, b) == Nat.add(a, 1n+b) : Nat}:
  Equal.trans(Nat, Nat.add(1n+a, b), Nat.add(b, 1n+a), Nat.add(a, 1n+b), N.add_comm(1n+a, b),
    Equal.trans(Nat, Nat.add(b, 1n+a), 1n+Nat.add(b, a), Nat.add(a, 1n+b), N.add_succ(b, a),
      Equal.trans(Nat, 1n+Nat.add(b, a), 1n+Nat.add(a, b), Nat.add(a, 1n+b), N.succ_cong(Nat.add(b, a), Nat.add(a, b), N.add_comm(b, a)), Equal.sym(Nat, Nat.add(a, 1n+b), 1n+Nat.add(a, b), N.add_succ(a, b)))))

# ---- Contains ----
def inset_nth(+xs: List<&2, Bool>, +k: Nat, +b: Bool, +h: {SC.nth(Bool, xs, k) == Some{b} : Maybe<&2, Bool>}) -> {S.inset(xs, k) == b : Bool}:
  %Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, xs, k), Some{b}, h) : {S.ins(_) == b : Bool}
  {==}

def gr_y(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}, +y: Maybe<&2, Bool>, +hy: {SC.nth(Bool, xs, i) == y : Maybe<&2, Bool>}) -> {S.ob(xs, E.Get{i}) == E.OBit{Done{S.inset(xs, i)}} : E.Obs}:
  match y:
    case None{}:
      Empty.absurd({S.ob(xs, E.Get{i}) == E.OBit{Done{S.inset(xs, i)}} : E.Obs}, LL.sc_nth_some(Bool, xs, i, h, hy))
    case Some{+b}:
      %Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, xs, i), Some{b}, hy) : {E.OBit{S.bit(_)} == E.OBit{Done{S.ins(_)}} : E.Obs}
      {==}

def get_result(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> S.Contains.get_result(xs, i, h):
  gr_y(xs, i, h, SC.nth(Bool, xs, i), {==})

def get_frame(+xs: List<&2, Bool>, +i: Nat) -> S.Contains.get_frame(xs, i):
  {==}

def get_outside(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_le(SC.length(Bool, xs), i) == True{} : Bool}) -> S.Contains.get_outside(xs, i, h):
  %Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, xs, i), None{}, LL.nth_none(Bool, xs, i, h)) : {E.OBit{S.bit(_)} == E.OBit{Fail{E.IndexOutOfRange{}}} : E.Obs}
  {==}

# ---- Length (the member count), Capacity (the universe) ----
def count_result(+xs: List<&2, Bool>) -> S.Length.count_result(xs):
  {==}

def count_frame(+xs: List<&2, Bool>) -> S.Length.count_frame(xs):
  {==}

def length_result(+xs: List<&2, Bool>) -> S.Capacity.length_result(xs):
  {==}

def length_frame(+xs: List<&2, Bool>) -> S.Capacity.length_frame(xs):
  {==}

# ---- Empty_Set: no member, Length 0, over the universe [0, n) ----
def new_contains(+n: Nat, +k: Nat) -> S.Empty_Set.new_contains(n, k):
  match n k:
    case 0n _:
      {==}
    case 1n+m 0n:
      {==}
    case 1n+ +m 1n+ +j:
      new_contains(m, j)

def new_count(+n: Nat) -> S.Empty_Set.new_count(n):
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      new_count(m)

def new_length(+n: Nat) -> S.Empty_Set.new_length(n):
  LL.length_replicate(Bool, n, False{})

# ---- the update of one bit ----
def assign_is(+xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}, +y: Maybe<&2, Bool>, +hy: {SC.nth(Bool, xs, i) == y : Maybe<&2, Bool>}) -> {S.assign(xs, i, v) == (SC.update(Bool, xs, i, v), E.OUnit{Done{Unit{}}}) : List<&2, Bool> & E.Obs}:
  match y:
    case None{}:
      Empty.absurd({S.assign(xs, i, v) == (SC.update(Bool, xs, i, v), E.OUnit{Done{Unit{}}}) : List<&2, Bool> & E.Obs}, LL.sc_nth_some(Bool, xs, i, h, hy))
    case Some{b}:
      %Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, xs, i), Some{b}, hy) : {S.assign_at(_, xs, i, v) == (SC.update(Bool, xs, i, v), E.OUnit{Done{Unit{}}}) : List<&2, Bool> & E.Obs}
      {==}

def inset_update_same(+xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> {S.inset(SC.update(Bool, xs, i, v), i) == v : Bool}:
  inset_nth(SC.update(Bool, xs, i, v), i, v, LL.nth_update_same(Bool, xs, i, v, h))

def inset_update_other(+xs: List<&2, Bool>, +i: Nat, +j: Nat, +v: Bool, +ne: {Nat.is_eq(i, j) == False{} : Bool}) -> {S.inset(SC.update(Bool, xs, i, v), j) == S.inset(xs, j) : Bool}:
  Equal.cong(Maybe<&2, Bool>, Bool, z => S.ins(z), SC.nth(Bool, SC.update(Bool, xs, i, v), j), SC.nth(Bool, xs, j), LL.nth_update_other(Bool, xs, i, j, v, ne))

# count after setting a bit: one more unless it was set
def cu_set(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> {S.count(SC.update(Bool, xs, i, True{})) == Bool.pick(Nat, S.inset(xs, i), S.count(xs), 1n+S.count(xs)) : Nat}:
  match xs i:
    case Nil{} _:
      Empty.absurd({S.count(SC.update(Bool, Nil{}, i, True{})) == Bool.pick(Nat, S.inset(Nil{}, i), S.count(Nil{}), 1n+S.count(Nil{})) : Nat}, N.lt_zero_absurd(i, h))
    case Con{True{}, t} 0n:
      {==}
    case Con{False{}, t} 0n:
      {==}
    case Con{True{}, +t} 1n+ +p:
      %Equal.sym(Nat, S.count(SC.update(Bool, t, p, True{})), Bool.pick(Nat, S.inset(t, p), S.count(t), 1n+S.count(t)), cu_set(t, p, h)) : {1n+_ == Bool.pick(Nat, S.inset(t, p), 1n+S.count(t), 1n+(1n+S.count(t))) : Nat}
      succ_pick(S.inset(t, p), S.count(t), 1n+S.count(t))
    case Con{False{}, +t} 1n+ +p:
      cu_set(t, p, h)

# count after clearing a bit: one less if it was set
def cu_clear(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> {S.count(xs) == Bool.pick(Nat, S.inset(xs, i), 1n+S.count(SC.update(Bool, xs, i, False{})), S.count(SC.update(Bool, xs, i, False{}))) : Nat}:
  match xs i:
    case Nil{} _:
      Empty.absurd({S.count(Nil{}) == Bool.pick(Nat, S.inset(Nil{}, i), 1n+S.count(SC.update(Bool, Nil{}, i, False{})), S.count(SC.update(Bool, Nil{}, i, False{}))) : Nat}, N.lt_zero_absurd(i, h))
    case Con{True{}, t} 0n:
      {==}
    case Con{False{}, t} 0n:
      {==}
    case Con{True{}, +t} 1n+ +p:
      %Equal.sym(Nat, S.count(t), Bool.pick(Nat, S.inset(t, p), 1n+S.count(SC.update(Bool, t, p, False{})), S.count(SC.update(Bool, t, p, False{}))), cu_clear(t, p, h)) : {1n+_ == Bool.pick(Nat, S.inset(t, p), 1n+(1n+S.count(SC.update(Bool, t, p, False{}))), 1n+S.count(SC.update(Bool, t, p, False{}))) : Nat}
      succ_pick(S.inset(t, p), 1n+S.count(SC.update(Bool, t, p, False{})), S.count(SC.update(Bool, t, p, False{})))
    case Con{False{}, +t} 1n+ +p:
      cu_clear(t, p, h)

# ---- Include / Insert (set) ----
def set_model(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> {S.nx(xs, E.Set{i}) == SC.update(Bool, xs, i, True{}) : List<&2, Bool>}:
  %Equal.sym(List<&2, Bool> & E.Obs, S.assign(xs, i, True{}), (SC.update(Bool, xs, i, True{}), E.OUnit{Done{Unit{}}}), assign_is(xs, i, True{}, h, SC.nth(Bool, xs, i), {==})) : {Pair.fst(List<&2, Bool>, E.Obs, _) == SC.update(Bool, xs, i, True{}) : List<&2, Bool>}
  {==}

def set_contains(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> S.Include.set_contains(xs, i, h):
  %Equal.sym(List<&2, Bool>, S.nx(xs, E.Set{i}), SC.update(Bool, xs, i, True{}), set_model(xs, i, h)) : {S.inset(_, i) == True{} : Bool}
  inset_update_same(xs, i, True{}, h)

def set_others(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}, +j: Nat, +ne: {Nat.is_eq(i, j) == False{} : Bool}) -> S.Include.set_others(xs, i, h, j, ne):
  %Equal.sym(List<&2, Bool>, S.nx(xs, E.Set{i}), SC.update(Bool, xs, i, True{}), set_model(xs, i, h)) : {S.inset(_, j) == S.inset(xs, j) : Bool}
  inset_update_other(xs, i, j, True{}, ne)

def set_universe(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> S.Include.set_universe(xs, i, h):
  %Equal.sym(List<&2, Bool>, S.nx(xs, E.Set{i}), SC.update(Bool, xs, i, True{}), set_model(xs, i, h)) : {SC.length(Bool, _) == SC.length(Bool, xs) : Nat}
  LL.length_update(Bool, xs, i, True{})

def set_outside(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_le(SC.length(Bool, xs), i) == True{} : Bool}) -> S.Include.set_outside(xs, i, h):
  %Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, xs, i), None{}, LL.nth_none(Bool, xs, i, h)) : {S.assign_at(_, xs, i, True{}) == (xs, E.OUnit{Fail{E.IndexOutOfRange{}}}) : List<&2, Bool> & E.Obs}
  {==}

# ---- Exclude / Delete (clear) ----
def clear_model(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> {S.nx(xs, E.Clear{i}) == SC.update(Bool, xs, i, False{}) : List<&2, Bool>}:
  %Equal.sym(List<&2, Bool> & E.Obs, S.assign(xs, i, False{}), (SC.update(Bool, xs, i, False{}), E.OUnit{Done{Unit{}}}), assign_is(xs, i, False{}, h, SC.nth(Bool, xs, i), {==})) : {Pair.fst(List<&2, Bool>, E.Obs, _) == SC.update(Bool, xs, i, False{}) : List<&2, Bool>}
  {==}

def clear_contains(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> S.Exclude.clear_contains(xs, i, h):
  %Equal.sym(List<&2, Bool>, S.nx(xs, E.Clear{i}), SC.update(Bool, xs, i, False{}), clear_model(xs, i, h)) : {S.inset(_, i) == False{} : Bool}
  inset_update_same(xs, i, False{}, h)

def clear_others(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}, +j: Nat, +ne: {Nat.is_eq(i, j) == False{} : Bool}) -> S.Exclude.clear_others(xs, i, h, j, ne):
  %Equal.sym(List<&2, Bool>, S.nx(xs, E.Clear{i}), SC.update(Bool, xs, i, False{}), clear_model(xs, i, h)) : {S.inset(_, j) == S.inset(xs, j) : Bool}
  inset_update_other(xs, i, j, False{}, ne)

def clear_universe(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> S.Exclude.clear_universe(xs, i, h):
  %Equal.sym(List<&2, Bool>, S.nx(xs, E.Clear{i}), SC.update(Bool, xs, i, False{}), clear_model(xs, i, h)) : {SC.length(Bool, _) == SC.length(Bool, xs) : Nat}
  LL.length_update(Bool, xs, i, False{})

def clear_outside(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_le(SC.length(Bool, xs), i) == True{} : Bool}) -> S.Exclude.clear_outside(xs, i, h):
  %Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, xs, i), None{}, LL.nth_none(Bool, xs, i, h)) : {S.assign_at(_, xs, i, False{}) == (xs, E.OUnit{Fail{E.IndexOutOfRange{}}}) : List<&2, Bool> & E.Obs}
  {==}

# Include: one more member unless it was one (Insert's Pre: it was not)
def set_count(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> S.Include.set_count(xs, i, h):
  %Equal.sym(List<&2, Bool>, S.nx(xs, E.Set{i}), SC.update(Bool, xs, i, True{}), set_model(xs, i, h)) : {S.count(_) == Bool.pick(Nat, S.inset(xs, i), S.count(xs), 1n+S.count(xs)) : Nat}
  cu_set(xs, i, h)

# Exclude: one member less if it was one (Delete's Pre: it was)
def clear_count(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> S.Exclude.clear_count(xs, i, h):
  %Equal.sym(List<&2, Bool>, S.nx(xs, E.Clear{i}), SC.update(Bool, xs, i, False{}), clear_model(xs, i, h)) : {S.count(xs) == Bool.pick(Nat, S.inset(xs, i), 1n+S.count(_), S.count(_)) : Nat}
  cu_clear(xs, i, h)

# ---- Union (1180) ----
def union_pt(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +k: Nat, +h: {SC.length(Bool, xs) == SC.length(Bool, ys) : Nat}) -> {S.inset(S.zip_or(xs, ys), k) == Bool.or(S.inset(xs, k), S.inset(ys, k)) : Bool}:
  match xs ys k:
    case Nil{} Nil{} _:
      {==}
    case Nil{} Con{b, t} _:
      Empty.absurd({S.inset(S.zip_or(Nil{}, Con{b, t}), k) == Bool.or(S.inset(Nil{}, k), S.inset(Con{b, t}, k)) : Bool}, zero_ne_succ(SC.length(Bool, t), h))
    case Con{a, s} Nil{} _:
      Empty.absurd({S.inset(S.zip_or(Con{a, s}, Nil{}), k) == Bool.or(S.inset(Con{a, s}, k), S.inset(Nil{}, k)) : Bool}, succ_ne_zero(SC.length(Bool, s), h))
    case Con{a, s} Con{b, t} 0n:
      {==}
    case Con{a, +s} Con{b, +t} 1n+ +p:
      union_pt(s, t, p, N.succ_inj(SC.length(Bool, s), SC.length(Bool, t), h))

def union_contains(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +k: Nat, +h: {SC.length(Bool, xs) == SC.length(Bool, ys) : Nat}) -> S.Union.union_contains(xs, ys, k, h):
  %h : {S.inset(Pair.fst(List<&2, Bool>, E.Obs, S.combine_if(Nat.is_eq(SC.length(Bool, xs), _), xs, S.zip_or(xs, ys))), k) == Bool.or(S.inset(xs, k), S.inset(ys, k)) : Bool}
  %Equal.sym(Bool, Nat.is_eq(SC.length(Bool, xs), SC.length(Bool, xs)), True{}, N.is_eq_refl(SC.length(Bool, xs))) : {S.inset(Pair.fst(List<&2, Bool>, E.Obs, S.combine_if(_, xs, S.zip_or(xs, ys))), k) == Bool.or(S.inset(xs, k), S.inset(ys, k)) : Bool}
  union_pt(xs, ys, k, h)

def union_mismatch(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +h: {Nat.is_eq(SC.length(Bool, xs), SC.length(Bool, ys)) == False{} : Bool}) -> S.Union.union_mismatch(xs, ys, h):
  %Equal.sym(Bool, Nat.is_eq(SC.length(Bool, xs), SC.length(Bool, ys)), False{}, h) : {S.combine_if(_, xs, S.zip_or(xs, ys)) == (xs, E.OUnit{Fail{E.LengthMismatch{}}}) : List<&2, Bool> & E.Obs}
  {==}

# ---- Intersection (1279) ----
def intersection_pt(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +k: Nat, +h: {SC.length(Bool, xs) == SC.length(Bool, ys) : Nat}) -> {S.inset(S.zip_and(xs, ys), k) == Bool.and(S.inset(xs, k), S.inset(ys, k)) : Bool}:
  match xs ys k:
    case Nil{} Nil{} _:
      {==}
    case Nil{} Con{b, t} _:
      Empty.absurd({S.inset(S.zip_and(Nil{}, Con{b, t}), k) == Bool.and(S.inset(Nil{}, k), S.inset(Con{b, t}, k)) : Bool}, zero_ne_succ(SC.length(Bool, t), h))
    case Con{a, s} Nil{} _:
      Empty.absurd({S.inset(S.zip_and(Con{a, s}, Nil{}), k) == Bool.and(S.inset(Con{a, s}, k), S.inset(Nil{}, k)) : Bool}, succ_ne_zero(SC.length(Bool, s), h))
    case Con{a, s} Con{b, t} 0n:
      {==}
    case Con{a, +s} Con{b, +t} 1n+ +p:
      intersection_pt(s, t, p, N.succ_inj(SC.length(Bool, s), SC.length(Bool, t), h))

def intersection_contains(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +k: Nat, +h: {SC.length(Bool, xs) == SC.length(Bool, ys) : Nat}) -> S.Intersection.intersection_contains(xs, ys, k, h):
  %h : {S.inset(Pair.fst(List<&2, Bool>, E.Obs, S.combine_if(Nat.is_eq(SC.length(Bool, xs), _), xs, S.zip_and(xs, ys))), k) == Bool.and(S.inset(xs, k), S.inset(ys, k)) : Bool}
  %Equal.sym(Bool, Nat.is_eq(SC.length(Bool, xs), SC.length(Bool, xs)), True{}, N.is_eq_refl(SC.length(Bool, xs))) : {S.inset(Pair.fst(List<&2, Bool>, E.Obs, S.combine_if(_, xs, S.zip_and(xs, ys))), k) == Bool.and(S.inset(xs, k), S.inset(ys, k)) : Bool}
  intersection_pt(xs, ys, k, h)

def intersection_mismatch(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +h: {Nat.is_eq(SC.length(Bool, xs), SC.length(Bool, ys)) == False{} : Bool}) -> S.Intersection.intersection_mismatch(xs, ys, h):
  %Equal.sym(Bool, Nat.is_eq(SC.length(Bool, xs), SC.length(Bool, ys)), False{}, h) : {S.combine_if(_, xs, S.zip_and(xs, ys)) == (xs, E.OUnit{Fail{E.LengthMismatch{}}}) : List<&2, Bool> & E.Obs}
  {==}

# ---- Difference (1340) ----
def difference_pt(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +k: Nat, +h: {SC.length(Bool, xs) == SC.length(Bool, ys) : Nat}) -> {S.inset(S.zip_diff(xs, ys), k) == Bool.and(S.inset(xs, k), Bool.not(S.inset(ys, k))) : Bool}:
  match xs ys k:
    case Nil{} Nil{} _:
      {==}
    case Nil{} Con{b, t} _:
      Empty.absurd({S.inset(S.zip_diff(Nil{}, Con{b, t}), k) == Bool.and(S.inset(Nil{}, k), Bool.not(S.inset(Con{b, t}, k))) : Bool}, zero_ne_succ(SC.length(Bool, t), h))
    case Con{a, s} Nil{} _:
      Empty.absurd({S.inset(S.zip_diff(Con{a, s}, Nil{}), k) == Bool.and(S.inset(Con{a, s}, k), Bool.not(S.inset(Nil{}, k))) : Bool}, succ_ne_zero(SC.length(Bool, s), h))
    case Con{a, s} Con{b, t} 0n:
      {==}
    case Con{a, +s} Con{b, +t} 1n+ +p:
      difference_pt(s, t, p, N.succ_inj(SC.length(Bool, s), SC.length(Bool, t), h))

def difference_contains(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +k: Nat, +h: {SC.length(Bool, xs) == SC.length(Bool, ys) : Nat}) -> S.Difference.difference_contains(xs, ys, k, h):
  %h : {S.inset(Pair.fst(List<&2, Bool>, E.Obs, S.combine_if(Nat.is_eq(SC.length(Bool, xs), _), xs, S.zip_diff(xs, ys))), k) == Bool.and(S.inset(xs, k), Bool.not(S.inset(ys, k))) : Bool}
  %Equal.sym(Bool, Nat.is_eq(SC.length(Bool, xs), SC.length(Bool, xs)), True{}, N.is_eq_refl(SC.length(Bool, xs))) : {S.inset(Pair.fst(List<&2, Bool>, E.Obs, S.combine_if(_, xs, S.zip_diff(xs, ys))), k) == Bool.and(S.inset(xs, k), Bool.not(S.inset(ys, k))) : Bool}
  difference_pt(xs, ys, k, h)

def difference_mismatch(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +h: {Nat.is_eq(SC.length(Bool, xs), SC.length(Bool, ys)) == False{} : Bool}) -> S.Difference.difference_mismatch(xs, ys, h):
  %Equal.sym(Bool, Nat.is_eq(SC.length(Bool, xs), SC.length(Bool, ys)), False{}, h) : {S.combine_if(_, xs, S.zip_diff(xs, ys)) == (xs, E.OUnit{Fail{E.LengthMismatch{}}}) : List<&2, Bool> & E.Obs}
  {==}

# ---- Symmetric_Difference (1404) ----
def symmetric_difference_pt(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +k: Nat, +h: {SC.length(Bool, xs) == SC.length(Bool, ys) : Nat}) -> {S.inset(S.zip_xor(xs, ys), k) == Bool.xor(S.inset(xs, k), S.inset(ys, k)) : Bool}:
  match xs ys k:
    case Nil{} Nil{} _:
      {==}
    case Nil{} Con{b, t} _:
      Empty.absurd({S.inset(S.zip_xor(Nil{}, Con{b, t}), k) == Bool.xor(S.inset(Nil{}, k), S.inset(Con{b, t}, k)) : Bool}, zero_ne_succ(SC.length(Bool, t), h))
    case Con{a, s} Nil{} _:
      Empty.absurd({S.inset(S.zip_xor(Con{a, s}, Nil{}), k) == Bool.xor(S.inset(Con{a, s}, k), S.inset(Nil{}, k)) : Bool}, succ_ne_zero(SC.length(Bool, s), h))
    case Con{a, s} Con{b, t} 0n:
      {==}
    case Con{a, +s} Con{b, +t} 1n+ +p:
      symmetric_difference_pt(s, t, p, N.succ_inj(SC.length(Bool, s), SC.length(Bool, t), h))

def symmetric_difference_contains(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +k: Nat, +h: {SC.length(Bool, xs) == SC.length(Bool, ys) : Nat}) -> S.Symmetric_Difference.symmetric_difference_contains(xs, ys, k, h):
  %h : {S.inset(Pair.fst(List<&2, Bool>, E.Obs, S.combine_if(Nat.is_eq(SC.length(Bool, xs), _), xs, S.zip_xor(xs, ys))), k) == Bool.xor(S.inset(xs, k), S.inset(ys, k)) : Bool}
  %Equal.sym(Bool, Nat.is_eq(SC.length(Bool, xs), SC.length(Bool, xs)), True{}, N.is_eq_refl(SC.length(Bool, xs))) : {S.inset(Pair.fst(List<&2, Bool>, E.Obs, S.combine_if(_, xs, S.zip_xor(xs, ys))), k) == Bool.xor(S.inset(xs, k), S.inset(ys, k)) : Bool}
  symmetric_difference_pt(xs, ys, k, h)

def xor_mismatch(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +h: {Nat.is_eq(SC.length(Bool, xs), SC.length(Bool, ys)) == False{} : Bool}) -> S.Symmetric_Difference.xor_mismatch(xs, ys, h):
  %Equal.sym(Bool, Nat.is_eq(SC.length(Bool, xs), SC.length(Bool, ys)), False{}, h) : {S.combine_if(_, xs, S.zip_xor(xs, ys)) == (xs, E.OUnit{Fail{E.LengthMismatch{}}}) : List<&2, Bool> & E.Obs}
  {==}

def to_list_result(+xs: List<&2, Bool>) -> S.Elements.to_list_result(xs):
  {==}

def to_list_frame(+xs: List<&2, Bool>) -> S.Elements.to_list_frame(xs):
  {==}

# no member below the offset
def members_above(+xs: List<&2, Bool>, +off: Nat, +j: Nat, +h: {Nat.is_lt(j, off) == True{} : Bool}) -> {S.nmem(j, S.members(xs, off)) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{False{}, +t}:
      members_above(t, 1n+off, j, N.lt_trans(j, off, 1n+off, h, N.lt_succ(off)))
    case Con{True{}, +t}:
      %Equal.sym(Bool, Nat.is_eq(off, j), False{}, N.is_eq_sym_false(j, off, N.is_eq_lt(j, off, h))) : {Bool.or(_, S.nmem(j, S.members(t, 1n+off))) == False{} : Bool}
      members_above(t, 1n+off, j, N.lt_trans(j, off, 1n+off, h, N.lt_succ(off)))

def rel_add(+off: Nat, +p: Nat) -> {Nat.add(1n+off, p) == Nat.add(1n+p, off) : Nat}:
  Equal.trans(Nat, Nat.add(1n+off, p), Nat.add(off, 1n+p), Nat.add(1n+p, off), succ_add(off, p), N.add_comm(off, 1n+p))

def ne_add_succ(+off: Nat, +p: Nat) -> {Nat.is_eq(off, Nat.add(1n+p, off)) == False{} : Bool}:
  N.is_eq_lt(off, Nat.add(1n+p, off), N.lt_le_trans(off, 1n+off, Nat.add(1n+p, off), N.lt_succ(off), L.subst(Nat, z => {Nat.is_le(1n+off, z) == True{} : Bool}, Nat.add(1n+off, p), Nat.add(1n+p, off), rel_add(off, p), N.le_add_right(1n+off, p))))

# the member at relative index k is there exactly when bit k is set
def members_pt(+xs: List<&2, Bool>, +k: Nat, +off: Nat) -> {S.nmem(Nat.add(k, off), S.members(xs, off)) == S.inset(xs, k) : Bool}:
  match xs k:
    case Nil{} _:
      {==}
    case Con{False{}, +t} 0n:
      %Equal.sym(Nat, Nat.add(0n, off), off, zero_add(off)) : {S.nmem(_, S.members(t, 1n+off)) == False{} : Bool}
      members_above(t, 1n+off, off, N.lt_succ(off))
    case Con{True{}, +t} 0n:
      %Equal.sym(Nat, Nat.add(0n, off), off, zero_add(off)) : {Bool.or(Nat.is_eq(off, _), S.nmem(_, S.members(t, 1n+off))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(off, off), True{}, N.is_eq_refl(off)) : {Bool.or(_, S.nmem(off, S.members(t, 1n+off))) == True{} : Bool}
      {==}
    case Con{False{}, +t} 1n+ +p:
      %Equal.sym(Nat, Nat.add(1n+p, off), Nat.add(p, 1n+off), succ_add(p, off)) : {S.nmem(_, S.members(t, 1n+off)) == S.inset(t, p) : Bool}
      members_pt(t, p, 1n+off)
    case Con{True{}, +t} 1n+ +p:
      %Equal.sym(Bool, Nat.is_eq(off, Nat.add(1n+p, off)), False{}, ne_add_succ(off, p)) : {Bool.or(_, S.nmem(Nat.add(1n+p, off), S.members(t, 1n+off))) == S.inset(t, p) : Bool}
      %Equal.sym(Nat, Nat.add(1n+p, off), Nat.add(p, 1n+off), succ_add(p, off)) : {Bool.or(False{}, S.nmem(_, S.members(t, 1n+off))) == S.inset(t, p) : Bool}
      members_pt(t, p, 1n+off)

def elements_contains(+xs: List<&2, Bool>, +k: Nat) -> S.Elements.elements_contains(xs, k):
  %N.add_zero(k) : {S.nmem(_, S.members(xs, 0n)) == S.inset(xs, k) : Bool}
  members_pt(xs, k, 0n)

# as many elements as members (SPARK: Length (Elements) = Length (Container))
def elements_length(+xs: List<&2, Bool>, +off: Nat) -> S.Elements.elements_length(xs, off):
  match xs:
    case Nil{}:
      {==}
    case Con{False{}, +t}:
      elements_length(t, 1n+off)
    case Con{True{}, +t}:
      N.succ_cong(SC.length(Nat, S.members(t, 1n+off)), S.count(t), elements_length(t, 1n+off))
