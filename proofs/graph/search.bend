import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/order.bend as O
import ../binary_heap/u32idx.bend as IX
import ../lib/u32half.bend as H
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../src/graph.bend as G

# The binary search of src/graph.bend is the lower bound.
#
# `G.fnd_go` narrows a window [lo, hi) of one Base.Array block. This module
# proves that, started with enough fuel on a window whose entries are sorted,
# it stops exactly at the index `lb` that splits the window into "entries
# below v" and "entries not below v" -- the lower bound. Sortedness enters
# only through the two premises hA and hB, which are what a sorted window
# gives and what the callers establish.
#
# The loop is proved against the REAL Base.Array algorithms: every read is
# `AR.get` on the array built from the Data mirror tree, and the index
# arithmetic is the real U32 one (the implementation uses sub/shr only, whose
# Nat meaning is available under a variable bound; U32.add would need a 2^32
# bound, which the checker cannot expand).

# The entry at index j is below v ("None" cannot happen inside the window).
def ltm(m: Maybe<&2, U32>, +v: U32) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+x}:
      U32.is_lt(x, v)

def ltat(xs: List<&2, U32>, +j: Nat, +v: U32) -> Bool:
  ltm(SC.nth(U32, xs, j), v)

# The midpoint at the Nat level, matching G.mid_of exactly.
def mnat(+lo: Nat, +hi: Nat) -> Nat:
  Nat.sub(hi, Nat.sub(Nat.sub(hi, lo), H.hlf(Nat.sub(hi, lo))))

# ---- Nat facts about the midpoint ----

def sub_le_self(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a b:
    case a0 0n:
      L.subst(Nat, z => {Nat.is_le(z, a0) == True{} : Bool}, a0, Nat.sub(a0, 0n), Equal.sym(Nat, Nat.sub(a0, 0n), a0, N.sub_zero(a0)), N.le_refl(a0))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      N.le_trans(Nat.sub(p, q), p, 1n+p, sub_le_self(p, q), N.le_succ(p))

# a - (a - b) = b when b <= a.
def sub_sub_cancel(+a: Nat, +b: Nat, +h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.sub(a, Nat.sub(a, b)) == b : Nat}:
  match a b:
    case a0 0n:
      L.subst(Nat, z => {Nat.sub(a0, z) == 0n : Nat}, a0, Nat.sub(a0, 0n), Equal.sym(Nat, Nat.sub(a0, 0n), a0, N.sub_zero(a0)), N.sub_self(a0))
    case 0n 1n+q:
      Empty.absurd({Nat.sub(0n, Nat.sub(0n, 1n+q)) == 1n+q : Nat}, L.false_true(h))
    case 1n+p 1n+q:
      Equal.trans(Nat, Nat.sub(1n+p, Nat.sub(p, q)), 1n+Nat.sub(p, Nat.sub(p, q)), 1n+q,
        N.sub_succ_left(p, Nat.sub(p, q), sub_le_self(p, q)),
        Equal.cong(Nat, Nat, n => 1n+n, Nat.sub(p, Nat.sub(p, q)), q, sub_sub_cancel(p, q, h)))

def zero_of_le(+x: Nat, +h: {Nat.is_le(x, 0n) == True{} : Bool}) -> {x == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, L.false_true(h))

# x <= y gives a - y <= a - x.
def sub_mono_right(+a: Nat, +x: Nat, +y: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.sub(a, y), Nat.sub(a, x)) == True{} : Bool}:
  match a x y:
    case a0 x0 0n:
      L.subst(Nat, z => {Nat.is_le(Nat.sub(a0, 0n), Nat.sub(a0, z)) == True{} : Bool}, 0n, x0, Equal.sym(Nat, x0, 0n, zero_of_le(x0, h)), N.le_refl(Nat.sub(a0, 0n)))
    case 0n x0 1n+q:
      N.zero_le(Nat.sub(0n, x0))
    case 1n+p 0n 1n+q:
      L.subst(Nat, z => {Nat.is_le(Nat.sub(1n+p, 1n+q), z) == True{} : Bool}, 1n+p, Nat.sub(1n+p, 0n), Equal.sym(Nat, Nat.sub(1n+p, 0n), 1n+p, N.sub_zero(1n+p)), N.le_trans(Nat.sub(p, q), p, 1n+p, sub_le_self(p, q), N.le_succ(p)))
    case 1n+p 1n+r 1n+q:
      sub_mono_right(p, r, q, h)

# b < a gives 0 < a - b.
def sub_pos(+a: Nat, +b: Nat, +h: {Nat.is_lt(b, a) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.sub(a, b)) == True{} : Bool}:
  match a b:
    case 0n b0:
      Empty.absurd({Nat.is_lt(0n, Nat.sub(0n, b0)) == True{} : Bool}, N.lt_zero_absurd(b0, h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      sub_pos(p, q, h)

# 0 < k and 0 < a give a - k < a.
def sub_lt_self(+a: Nat, +k: Nat, +hk: {Nat.is_lt(0n, k) == True{} : Bool}, +ha: {Nat.is_lt(0n, a) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(a, k), a) == True{} : Bool}:
  match a k:
    case 0n k0:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, k0), 0n) == True{} : Bool}, N.lt_zero_absurd(0n, ha))
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(Nat.sub(1n+p, 0n), 1n+p) == True{} : Bool}, N.lt_zero_absurd(0n, hk))
    case 1n+p 1n+q:
      N.le_lt_trans(Nat.sub(p, q), p, 1n+p, sub_le_self(p, q), N.lt_succ(p))

# d/2 < d for a positive d.
def hlf_lt_self(+d: Nat, +h: {Nat.is_lt(0n, d) == True{} : Bool}) -> {Nat.is_lt(H.hlf(d), d) == True{} : Bool}:
  match d:
    case 0n:
      Empty.absurd({Nat.is_lt(H.hlf(0n), 0n) == True{} : Bool}, N.lt_zero_absurd(0n, h))
    case 1n+q:
      N.le_lt_trans(H.hlf(1n+q), q, 1n+q, H.hlf_succ_le(q), N.lt_succ(q))

# lo <= mnat(lo, hi) whenever lo <= hi.
def mid_lower(+lo: Nat, +hi: Nat, +h: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Nat.is_le(lo, mnat(lo, hi)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(z, mnat(lo, hi)) == True{} : Bool}, Nat.sub(hi, Nat.sub(hi, lo)), lo, sub_sub_cancel(hi, lo, h),
    sub_mono_right(hi, Nat.sub(Nat.sub(hi, lo), H.hlf(Nat.sub(hi, lo))), Nat.sub(hi, lo), sub_le_self(Nat.sub(hi, lo), H.hlf(Nat.sub(hi, lo)))))

# mnat(lo, hi) < hi whenever lo < hi.
def mid_upper(+lo: Nat, +hi: Nat, +h: {Nat.is_lt(lo, hi) == True{} : Bool}) -> {Nat.is_lt(mnat(lo, hi), hi) == True{} : Bool}:
  sub_lt_self(hi, Nat.sub(Nat.sub(hi, lo), H.hlf(Nat.sub(hi, lo))),
    sub_pos(Nat.sub(hi, lo), H.hlf(Nat.sub(hi, lo)), hlf_lt_self(Nat.sub(hi, lo), sub_pos(hi, lo, h))),
    N.le_lt_trans(0n, lo, hi, N.zero_le(lo), h))

# ---- the midpoint of the implementation is mnat ----

def hlf_le_le(+d: Nat) -> {Nat.is_le(H.hlf(d), d) == True{} : Bool}:
  H.hlf_le(d)

def mid_bridge(+lo: Nat, +hi: Nat, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +hhi: {Nat.is_lt(hi, SC.pow2(k)) == True{} : Bool}, +hle: {Nat.is_le(lo, hi) == True{} : Bool}) -> {G.mid_of(U32.from_nat(lo), U32.from_nat(hi)) == U32.from_nat(mnat(lo, hi)) : U32}:
  +d = Nat.sub(hi, lo)
  +hd = N.le_lt_trans(d, hi, SC.pow2(k), sub_le_self(hi, lo), hhi)
  +e1 = H.sub_bridge(hi, lo, k, hk, hhi, hle)
  +e2 = H.shr_bridge(d, k, hk, hd)
  +e3 = H.sub_bridge(d, H.hlf(d), k, hk, hd, hlf_le_le(d))
  +e4 = H.sub_bridge(hi, Nat.sub(d, H.hlf(d)), k, hk, hhi, N.le_trans(Nat.sub(d, H.hlf(d)), d, hi, sub_le_self(d, H.hlf(d)), sub_le_self(hi, lo)))
  %Equal.sym(U32, U32.sub(U32.from_nat(hi), U32.from_nat(lo)), U32.from_nat(d), e1) : {G.mid_sub(U32.from_nat(hi), _) == U32.from_nat(mnat(lo, hi)) : U32}
  %Equal.sym(U32, U32.shr(U32.from_nat(d)), U32.from_nat(H.hlf(d)), e2) : {U32.sub(U32.from_nat(hi), U32.sub(U32.from_nat(d), _)) == U32.from_nat(mnat(lo, hi)) : U32}
  %Equal.sym(U32, U32.sub(U32.from_nat(d), U32.from_nat(H.hlf(d))), U32.from_nat(Nat.sub(d, H.hlf(d))), e3) : {U32.sub(U32.from_nat(hi), _) == U32.from_nat(mnat(lo, hi)) : U32}
  e4

# hlf(d) <= d, as a `le` (the `lt` version needs d > 0).
# ---- the window predicates ----
#
# `alllt(xs, from, k, v)`: every entry of [from, from + k) is below v.
# `allge(xs, from, k, v)`: no entry of [from, from + k) is below v.
# A sorted window gives exactly these two around its lower bound, and they
# are what the narrowing step needs.

def alllt(+k: Nat, +xs: List<&2, U32>, +from: Nat, +v: U32) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+m:
      Bool.and(ltat(xs, from, v), alllt(m, xs, 1n+from, v))

def allge(+k: Nat, +xs: List<&2, U32>, +from: Nat, +v: U32) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+m:
      Bool.and(Bool.not(ltat(xs, from, v)), allge(m, xs, 1n+from, v))

# Extraction: an index inside the range satisfies the predicate. The split is
# on whether the index is the first one of the range; the induction hypothesis
# is threaded as a parameter (Bend allows no mutual recursion).
def lt_head(+xs: List<&2, U32>, +from: Nat, +m: Nat, +v: U32, +j: Nat, +h: {alllt(1n+m, xs, from, v) == True{} : Bool}, +he: {j == from : Nat}) -> {ltat(xs, j, v) == True{} : Bool}:
  L.subst(Nat, z => {ltat(xs, z, v) == True{} : Bool}, from, j, Equal.sym(Nat, j, from, he),
    L.and_left(ltat(xs, from, v), alllt(m, xs, 1n+from, v), h))

def ge_head(+xs: List<&2, U32>, +from: Nat, +m: Nat, +v: U32, +j: Nat, +h: {allge(1n+m, xs, from, v) == True{} : Bool}, +he: {j == from : Nat}) -> {ltat(xs, j, v) == False{} : Bool}:
  L.subst(Nat, z => {ltat(xs, z, v) == False{} : Bool}, from, j, Equal.sym(Nat, j, from, he),
    L.not_true(ltat(xs, from, v), L.and_left(Bool.not(ltat(xs, from, v)), allge(m, xs, 1n+from, v), h)))

# from <= j and from /= j give 1 + from <= j.
def succ_le(+from: Nat, +j: Nat, +h1: {Nat.is_le(from, j) == True{} : Bool}, +hne: {Nat.is_eq(from, j) == False{} : Bool}) -> {Nat.is_le(1n+from, j) == True{} : Bool}:
  match from j:
    case 0n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, L.true_false(hne))
    case 0n 1n+i:
      N.zero_le(i)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(2n+p, 0n) == True{} : Bool}, L.false_true(h1))
    case 1n+p 1n+i:
      succ_le(p, i, h1, hne)

def shift_lt(+from: Nat, +m: Nat, +j: Nat, +h2: {Nat.is_lt(j, Nat.add(from, 1n+m)) == True{} : Bool}) -> {Nat.is_lt(j, Nat.add(1n+from, m)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, Nat.add(from, 1n+m), Nat.add(1n+from, m), N.add_succ(from, m), h2)

# j < from + 0 is j < from.
def empty_range(+from: Nat, +j: Nat, +h: {Nat.is_lt(j, Nat.add(from, 0n)) == True{} : Bool}) -> {Nat.is_lt(j, from) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, Nat.add(from, 0n), from, N.add_zero(from), h)

def lt_at_split(+xs: List<&2, U32>, +from: Nat, +m: Nat, +v: U32, +j: Nat, +h: {alllt(1n+m, xs, from, v) == True{} : Bool}, +h1: {Nat.is_le(from, j) == True{} : Bool}, +h2: {Nat.is_lt(j, Nat.add(from, 1n+m)) == True{} : Bool}, same: Bool, +hs: {Nat.is_eq(from, j) == same : Bool}, ih: @+ha: {alllt(m, xs, 1n+from, v) == True{} : Bool} -> @+hb: {Nat.is_le(1n+from, j) == True{} : Bool} -> @+hc: {Nat.is_lt(j, Nat.add(1n+from, m)) == True{} : Bool} -> {ltat(xs, j, v) == True{} : Bool}) -> {ltat(xs, j, v) == True{} : Bool}:
  match same:
    case True{}:
      lt_head(xs, from, m, v, j, h, Equal.sym(Nat, from, j, N.eq_from_is_eq(from, j, hs)))
    case False{}:
      ih(L.and_right(ltat(xs, from, v), alllt(m, xs, 1n+from, v), h), succ_le(from, j, h1, hs), shift_lt(from, m, j, h2))

def lt_at(+k: Nat, +xs: List<&2, U32>, +from: Nat, +v: U32, +j: Nat, +h: {alllt(k, xs, from, v) == True{} : Bool}, +h1: {Nat.is_le(from, j) == True{} : Bool}, +h2: {Nat.is_lt(j, Nat.add(from, k)) == True{} : Bool}) -> {ltat(xs, j, v) == True{} : Bool}:
  match k:
    case 0n:
      Empty.absurd({ltat(xs, j, v) == True{} : Bool}, L.true_not_false(Nat.is_le(from, j), h1, N.lt_not_le(j, from, empty_range(from, j, h2))))
    case 1n+m:
      lt_at_split(xs, from, m, v, j, h, h1, h2, Nat.is_eq(from, j), {==},
        ha => hb => hc => lt_at(m, xs, 1n+from, v, j, ha, hb, hc))

def ge_at_split(+xs: List<&2, U32>, +from: Nat, +m: Nat, +v: U32, +j: Nat, +h: {allge(1n+m, xs, from, v) == True{} : Bool}, +h1: {Nat.is_le(from, j) == True{} : Bool}, +h2: {Nat.is_lt(j, Nat.add(from, 1n+m)) == True{} : Bool}, same: Bool, +hs: {Nat.is_eq(from, j) == same : Bool}, ih: @+ha: {allge(m, xs, 1n+from, v) == True{} : Bool} -> @+hb: {Nat.is_le(1n+from, j) == True{} : Bool} -> @+hc: {Nat.is_lt(j, Nat.add(1n+from, m)) == True{} : Bool} -> {ltat(xs, j, v) == False{} : Bool}) -> {ltat(xs, j, v) == False{} : Bool}:
  match same:
    case True{}:
      ge_head(xs, from, m, v, j, h, Equal.sym(Nat, from, j, N.eq_from_is_eq(from, j, hs)))
    case False{}:
      ih(L.and_right(Bool.not(ltat(xs, from, v)), allge(m, xs, 1n+from, v), h), succ_le(from, j, h1, hs), shift_lt(from, m, j, h2))

def ge_at(+k: Nat, +xs: List<&2, U32>, +from: Nat, +v: U32, +j: Nat, +h: {allge(k, xs, from, v) == True{} : Bool}, +h1: {Nat.is_le(from, j) == True{} : Bool}, +h2: {Nat.is_lt(j, Nat.add(from, k)) == True{} : Bool}) -> {ltat(xs, j, v) == False{} : Bool}:
  match k:
    case 0n:
      Empty.absurd({ltat(xs, j, v) == False{} : Bool}, L.true_not_false(Nat.is_le(from, j), h1, N.lt_not_le(j, from, empty_range(from, j, h2))))
    case 1n+m:
      ge_at_split(xs, from, m, v, j, h, h1, h2, Nat.is_eq(from, j), {==},
        ha => hb => hc => ge_at(m, xs, 1n+from, v, j, ha, hb, hc))

# ---- the loop ----

def lt_irr(+x: U32) -> {U32.is_lt(x, x) == False{} : Bool}:
  Equal.cong(Cmp, Bool, c => Cmp.is_lt(c), U32.cmp(x, x), EQ{}, O.refl(~U32, ~U32.cmp, ~O.u32_order, x))

# An empty window is a fixed point of the loop.
def settle(+f: Nat, +v: U32, +t: AR.Tree<U32>, +x: U32) -> {G.fnd_go(f, v, G.FD{AR.thaw(U32, t), x, x}) == G.FD{AR.thaw(U32, t), x, x} : G.Fnd}:
  match f:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Bool, U32.is_lt(x, x), False{}, lt_irr(x)) : {G.fnd_go(p, v, G.fnd_live(v, x, x, AR.thaw(U32, t), _)) == G.FD{AR.thaw(U32, t), x, x} : G.Fnd}
      settle(p, v, t, x)

# ---- reading the midpoint ----

# The value stored at an index inside the block, as a Some.
def slot_some(+d: Nat, +t: AR.Tree<U32>, +j: Nat, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(j, SC.length(U32, AR.slots(U32, t))) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, SC.pow2(d), SC.length(U32, AR.slots(U32, t)),
    Equal.sym(Nat, SC.length(U32, AR.slots(U32, t)), SC.pow2(d), AR.slots_length(U32, d, t, pf)), hj)

# `ltat` at an index whose slot value is x.
def ltat_value(+xs: List<&2, U32>, +j: Nat, +v: U32, +x: U32, +hx: {SC.nth(U32, xs, j) == Some{x} : Maybe<&2, U32>}) -> {ltat(xs, j, v) == U32.is_lt(x, v) : Bool}:
  Equal.cong(Maybe<&2, U32>, Bool, m => ltm(m, v), SC.nth(U32, xs, j), Some{x}, hx)

# The loop invariant, as a statement: started on [lo, hi) with fuel f, where
# the lower bound lb of v in the whole window [w0, w1) lies in [lo, hi] and
# the window is split at lb (hA/hB), the loop stops at lb.
def LoopOK(+f: Nat, +d: Nat, +t: AR.Tree<U32>, +v: U32, +lo: Nat, +hi: Nat, +lb: Nat) -> Type:
  {G.fnd_go(f, v, G.FD{AR.thaw(U32, t), U32.from_nat(lo), U32.from_nat(hi)}) == G.FD{AR.thaw(U32, t), U32.from_nat(lb), U32.from_nat(lb)} : G.Fnd}

# lo = lb = hi when the range is empty.
def pinch_lo(+lo: Nat, +hi: Nat, +lb: Nat, +h1: {Nat.is_le(lo, lb) == True{} : Bool}, +h2: {Nat.is_le(lb, hi) == True{} : Bool}, +h3: {Nat.is_le(hi, lo) == True{} : Bool}) -> {lo == lb : Nat}:
  N.le_antisym(lo, lb, h1, N.le_trans(lb, hi, lo, h2, h3))

def pinch_hi(+lo: Nat, +hi: Nat, +lb: Nat, +h1: {Nat.is_le(lo, lb) == True{} : Bool}, +h2: {Nat.is_le(lb, hi) == True{} : Bool}, +h3: {Nat.is_le(hi, lo) == True{} : Bool}) -> {hi == lb : Nat}:
  N.le_antisym(hi, lb, N.le_trans(hi, lo, lb, h3, h1), h2)

def empty_case(+f: Nat, +d: Nat, +t: AR.Tree<U32>, +v: U32, +lo: Nat, +hi: Nat, +lb: Nat, +e1: {lo == lb : Nat}, +e2: {hi == lb : Nat}) -> LoopOK(f, d, t, v, lo, hi, lb):
  L.subst(Nat, z => LoopOK(f, d, t, v, z, hi, lb), lb, lo, Equal.sym(Nat, lo, lb, e1),
    L.subst(Nat, z => LoopOK(f, d, t, v, lb, z, lb), lb, hi, Equal.sym(Nat, hi, lb, e2),
      settle(f, v, t, U32.from_nat(lb))))

# ---- Nat facts for the narrowing step ----

def sub_eq_zero_le(+a: Nat, +b: Nat, +h: {Nat.sub(a, b) == 0n : Nat}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n b0:
      N.zero_le(b0)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, N.succ_zero(p, L.subst(Nat, z => {z == 0n : Nat}, Nat.sub(1n+p, 0n), 1n+p, N.sub_zero(1n+p), h)))
    case 1n+p 1n+q:
      sub_eq_zero_le(p, q, h)

def lt_one_zero(+n: Nat, +h: {Nat.is_lt(n, 1n) == True{} : Bool}) -> {n == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, N.lt_zero_absurd(p, h))

# a - (1 + b) = (a - b) - 1
def size_zero_le(+hi: Nat, +lo: Nat, +h: {Nat.is_lt(Nat.sub(hi, lo), 1n) == True{} : Bool}) -> {Nat.is_le(hi, lo) == True{} : Bool}:
  sub_eq_zero_le(hi, lo, lt_one_zero(Nat.sub(hi, lo), h))

def zero_sub(+b: Nat) -> {Nat.sub(0n, b) == 0n : Nat}:
  match b:
    case 0n:
      {==}
    case 1n+q:
      {==}

def pred_succ(+x: Nat) -> {Nat.sub(1n+x, 1n) == x : Nat}:
  N.sub_zero(x)

# (a - 1) <= b gives a <= 1 + b.
def le_of_pred_le(+a: Nat, +b: Nat, +h: {Nat.is_le(Nat.sub(a, 1n), b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a:
    case 0n:
      N.zero_le(1n+b)
    case 1n+p:
      L.subst(Nat, z => {Nat.is_le(z, b) == True{} : Bool}, Nat.sub(1n+p, 1n), p, pred_succ(p), h)

# (d - d/2) - 1 <= d/2
def sub_succ_right(+a: Nat, +b: Nat) -> {Nat.sub(a, 1n+b) == Nat.sub(Nat.sub(a, b), 1n) : Nat}:
  match a b:
    case 0n b0:
      Equal.sym(Nat, Nat.sub(Nat.sub(0n, b0), 1n), 0n,
        Equal.trans(Nat, Nat.sub(Nat.sub(0n, b0), 1n), Nat.sub(0n, 1n), 0n,
          Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), Nat.sub(0n, b0), 0n, zero_sub(b0)), {==}))
    case 1n+p 0n:
      %N.sub_zero(1n+p) : {Nat.sub(1n+p, 1n) == Nat.sub(_, 1n) : Nat}
      {==}
    case 1n+p 1n+q:
      sub_succ_right(p, q)

def gap_le(+d: Nat) -> {Nat.is_le(Nat.sub(Nat.sub(d, H.hlf(d)), 1n), H.hlf(d)) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+0n:
      {==}
    case 1n+1n+r:
      L.subst(Nat, z => {Nat.is_le(Nat.sub(z, 1n), 1n+H.hlf(r)) == True{} : Bool}, 1n+Nat.sub(r, H.hlf(r)), Nat.sub(1n+r, H.hlf(r)),
        Equal.sym(Nat, Nat.sub(1n+r, H.hlf(r)), 1n+Nat.sub(r, H.hlf(r)), N.sub_succ_left(r, H.hlf(r), H.hlf_le(r))),
        L.subst(Nat, z => {Nat.is_le(z, 1n+H.hlf(r)) == True{} : Bool}, Nat.sub(r, H.hlf(r)), Nat.sub(1n+Nat.sub(r, H.hlf(r)), 1n),
          Equal.sym(Nat, Nat.sub(1n+Nat.sub(r, H.hlf(r)), 1n), Nat.sub(r, H.hlf(r)), pred_succ(Nat.sub(r, H.hlf(r)))),
          le_of_pred_le(Nat.sub(r, H.hlf(r)), H.hlf(r), gap_le(r))))

# ---- the narrowing step ----
#
# `IH` is the induction hypothesis of the loop, passed as a parameter
# (Bend has no mutual recursion): the same statement one fuel step smaller,
# for any narrower window that still contains the lower bound.
def IH(+f2: Nat, +d: Nat, +t: AR.Tree<U32>, +v: U32, +lb: Nat, +w0: Nat, +w1: Nat) -> Type:
  @+lo2: Nat -> @+hi2: Nat ->
  @+p1: {Nat.is_le(w0, lo2) == True{} : Bool} ->
  @+p2: {Nat.is_le(lo2, lb) == True{} : Bool} ->
  @+p3: {Nat.is_le(lb, hi2) == True{} : Bool} ->
  @+p4: {Nat.is_le(hi2, w1) == True{} : Bool} ->
  @+p5: {Nat.is_lt(Nat.sub(hi2, lo2), SC.pow2(f2)) == True{} : Bool} ->
  LoopOK(f2, d, t, v, lo2, hi2, lb)

# index bound: everything in the window is below the block capacity, and one
# level of headroom keeps the U32 bridges applicable (2^(d+1) <= 2^32).
def in_cap(+d: Nat, +w1: Nat, +x: Nat, +hcap: {Nat.is_le(w1, SC.pow2(d)) == True{} : Bool}, +hx: {Nat.is_le(x, w1) == True{} : Bool}) -> {Nat.is_lt(x, SC.pow2(1n+d)) == True{} : Bool}:
  N.le_lt_trans(x, SC.pow2(d), SC.pow2(1n+d), N.le_trans(x, w1, SC.pow2(d), hx, hcap), N.pow2_lt_succ(d))

def cap_ok(+d: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {Nat.is_le(1n+d, 32n) == True{} : Bool}:
  N.lt_succ_le_succ(d, 32n, hd)

# m < lb, from the two halves of the window split.
def mid_below_go(+t: AR.Tree<U32>, +v: U32, +m: Nat, +lb: Nat, +w1: Nat, +hm: {ltat(AR.slots(U32, t), m, v) == True{} : Bool}, +hmw: {Nat.is_lt(m, w1) == True{} : Bool}, +hB: {allge(Nat.sub(w1, lb), AR.slots(U32, t), lb, v) == True{} : Bool}, +hlbw: {Nat.is_le(lb, w1) == True{} : Bool}, le: Bool, +ele: {Nat.is_le(lb, m) == le : Bool}) -> {Nat.is_lt(m, lb) == True{} : Bool}:
  match le:
    case False{}:
      N.not_le_lt(lb, m, ele)
    case True{}:
      Empty.absurd({Nat.is_lt(m, lb) == True{} : Bool},
        L.true_not_false(ltat(AR.slots(U32, t), m, v), hm,
          ge_at(Nat.sub(w1, lb), AR.slots(U32, t), lb, v, m, hB, ele,
            L.subst(Nat, z => {Nat.is_lt(m, z) == True{} : Bool}, w1, Nat.add(lb, Nat.sub(w1, lb)), Equal.sym(Nat, Nat.add(lb, Nat.sub(w1, lb)), w1, N.sub_add(w1, lb, hlbw)), hmw))))

# The value at the midpoint is NOT below v: the lower bound is at or below it.
def mid_below_lb(+t: AR.Tree<U32>, +v: U32, +m: Nat, +lb: Nat, +w1: Nat, +hm: {ltat(AR.slots(U32, t), m, v) == True{} : Bool}, +hmw: {Nat.is_lt(m, w1) == True{} : Bool}, +hB: {allge(Nat.sub(w1, lb), AR.slots(U32, t), lb, v) == True{} : Bool}, +hlbw: {Nat.is_le(lb, w1) == True{} : Bool}) -> {Nat.is_lt(m, lb) == True{} : Bool}:
  mid_below_go(t, v, m, lb, w1, hm, hmw, hB, hlbw, Nat.is_le(lb, m), {==})

def mid_above_go(+t: AR.Tree<U32>, +v: U32, +m: Nat, +lb: Nat, +w0: Nat, +hm: {ltat(AR.slots(U32, t), m, v) == False{} : Bool}, +hmw: {Nat.is_le(w0, m) == True{} : Bool}, +hA: {alllt(Nat.sub(lb, w0), AR.slots(U32, t), w0, v) == True{} : Bool}, +hlbw: {Nat.is_le(w0, lb) == True{} : Bool}, lt: Bool, +elt: {Nat.is_lt(m, lb) == lt : Bool}) -> {Nat.is_le(lb, m) == True{} : Bool}:
  match lt:
    case False{}:
      N.not_lt_le(m, lb, elt)
    case True{}:
      Empty.absurd({Nat.is_le(lb, m) == True{} : Bool},
        L.true_not_false(ltat(AR.slots(U32, t), m, v),
          lt_at(Nat.sub(lb, w0), AR.slots(U32, t), w0, v, m, hA, hmw,
            L.subst(Nat, z => {Nat.is_lt(m, z) == True{} : Bool}, lb, Nat.add(w0, Nat.sub(lb, w0)), Equal.sym(Nat, Nat.add(w0, Nat.sub(lb, w0)), lb, N.sub_add(lb, w0, hlbw)), elt)),
          hm))

def mid_at_or_above(+t: AR.Tree<U32>, +v: U32, +m: Nat, +lb: Nat, +w0: Nat, +hm: {ltat(AR.slots(U32, t), m, v) == False{} : Bool}, +hmw: {Nat.is_le(w0, m) == True{} : Bool}, +hA: {alllt(Nat.sub(lb, w0), AR.slots(U32, t), w0, v) == True{} : Bool}, +hlbw: {Nat.is_le(w0, lb) == True{} : Bool}) -> {Nat.is_le(lb, m) == True{} : Bool}:
  mid_above_go(t, v, m, lb, w0, hm, hmw, hA, hlbw, Nat.is_lt(m, lb), {==})

# (a - b) - c = a - (b + c)
def sub_zero_both(+x: Nat, +y: Nat) -> {Nat.sub(0n, x) == Nat.sub(0n, y) : Nat}:
  Equal.trans(Nat, Nat.sub(0n, x), 0n, Nat.sub(0n, y), zero_sub(x), Equal.sym(Nat, Nat.sub(0n, y), 0n, zero_sub(y)))

# (a - b) - c = (a - c) - b
def sub_add_eq(+a: Nat, +b: Nat, +c: Nat) -> {Nat.sub(Nat.sub(a, b), c) == Nat.sub(a, Nat.add(b, c)) : Nat}:
  match a b:
    case a0 0n:
      L.subst(Nat, z => {Nat.sub(z, c) == Nat.sub(a0, Nat.add(0n, c)) : Nat}, a0, Nat.sub(a0, 0n), Equal.sym(Nat, Nat.sub(a0, 0n), a0, N.sub_zero(a0)), {==})
    case 0n 1n+q:
      L.subst(Nat, z => {Nat.sub(z, c) == Nat.sub(0n, Nat.add(1n+q, c)) : Nat}, 0n, Nat.sub(0n, 1n+q), Equal.sym(Nat, Nat.sub(0n, 1n+q), 0n, zero_sub(1n+q)),
        Equal.sym(Nat, Nat.sub(0n, Nat.add(1n+q, c)), Nat.sub(0n, c), sub_zero_both(Nat.add(1n+q, c), c)))
    case 1n+p 1n+q:
      sub_add_eq(p, q, c)

def sub_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.sub(Nat.sub(a, b), c) == Nat.sub(Nat.sub(a, c), b) : Nat}:
  Equal.trans(Nat, Nat.sub(Nat.sub(a, b), c), Nat.sub(a, Nat.add(b, c)), Nat.sub(Nat.sub(a, c), b),
    sub_add_eq(a, b, c),
    Equal.trans(Nat, Nat.sub(a, Nat.add(b, c)), Nat.sub(a, Nat.add(c, b)), Nat.sub(Nat.sub(a, c), b),
      Equal.cong(Nat, Nat, z => Nat.sub(a, z), Nat.add(b, c), Nat.add(c, b), N.add_comm(b, c)),
      Equal.sym(Nat, Nat.sub(Nat.sub(a, c), b), Nat.sub(a, Nat.add(c, b)), sub_add_eq(a, c, b))))

# The midpoint sits exactly d/2 above lo.
def mid_gap(+lo: Nat, +hi: Nat, +h: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Nat.sub(mnat(lo, hi), lo) == H.hlf(Nat.sub(hi, lo)) : Nat}:
  Equal.trans(Nat, Nat.sub(mnat(lo, hi), lo), Nat.sub(Nat.sub(hi, lo), Nat.sub(Nat.sub(hi, lo), H.hlf(Nat.sub(hi, lo)))), H.hlf(Nat.sub(hi, lo)),
    sub_swap(hi, Nat.sub(Nat.sub(hi, lo), H.hlf(Nat.sub(hi, lo))), lo),
    sub_sub_cancel(Nat.sub(hi, lo), H.hlf(Nat.sub(hi, lo)), H.hlf_le(Nat.sub(hi, lo))))

# hi - (1 + m) = (d - d/2) - 1 for the midpoint m.
def gap_right(+lo: Nat, +hi: Nat, +h: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Nat.sub(hi, 1n+mnat(lo, hi)) == Nat.sub(Nat.sub(Nat.sub(hi, lo), H.hlf(Nat.sub(hi, lo))), 1n) : Nat}:
  Equal.trans(Nat, Nat.sub(hi, 1n+mnat(lo, hi)), Nat.sub(Nat.sub(hi, mnat(lo, hi)), 1n), Nat.sub(Nat.sub(Nat.sub(hi, lo), H.hlf(Nat.sub(hi, lo))), 1n),
    sub_succ_right(hi, mnat(lo, hi)),
    Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), Nat.sub(hi, mnat(lo, hi)), Nat.sub(Nat.sub(hi, lo), H.hlf(Nat.sub(hi, lo))),
      sub_sub_cancel(hi, Nat.sub(Nat.sub(hi, lo), H.hlf(Nat.sub(hi, lo))),
        N.le_trans(Nat.sub(Nat.sub(hi, lo), H.hlf(Nat.sub(hi, lo))), Nat.sub(hi, lo), hi, sub_le_self(Nat.sub(hi, lo), H.hlf(Nat.sub(hi, lo))), sub_le_self(hi, lo)))))

# ---- one narrowing step ----

# The window shrinks to [m+1, hi): the entry at the midpoint is below v.
def go_right(+f2: Nat, +d: Nat, +t: AR.Tree<U32>, +v: U32, +lo: Nat, +hi: Nat, +lb: Nat, +w0: Nat, +w1: Nat, +m: Nat, +hlt: {Nat.is_lt(lo, hi) == True{} : Bool}, +hml: {Nat.is_le(lo, m) == True{} : Bool}, +hmu: {Nat.is_lt(m, hi) == True{} : Bool}, +hem: {m == mnat(lo, hi) : Nat}, +h01: {Nat.is_le(w0, lo) == True{} : Bool}, +hlb2: {Nat.is_le(lb, hi) == True{} : Bool}, +hw1: {Nat.is_le(hi, w1) == True{} : Bool}, +hsize: {Nat.is_lt(Nat.sub(hi, lo), SC.pow2(1n+f2)) == True{} : Bool}, +hmlb: {Nat.is_lt(m, lb) == True{} : Bool}, ih: IH(f2, d, t, v, lb, w0, w1)) -> LoopOK(f2, d, t, v, 1n+m, hi, lb):
  ih(1n+m, hi,
     N.le_trans(w0, m, 1n+m, N.le_trans(w0, lo, m, h01, hml), N.le_succ(m)),
     N.lt_succ_le_succ(m, lb, hmlb),
     hlb2,
     hw1,
     H.step_bound(Nat.sub(hi, 1n+m), Nat.sub(hi, lo), SC.pow2(f2),
       L.subst(Nat, z => {Nat.is_le(z, H.hlf(Nat.sub(hi, lo))) == True{} : Bool}, Nat.sub(Nat.sub(Nat.sub(hi, lo), H.hlf(Nat.sub(hi, lo))), 1n), Nat.sub(hi, 1n+m),
         Equal.sym(Nat, Nat.sub(hi, 1n+m), Nat.sub(Nat.sub(Nat.sub(hi, lo), H.hlf(Nat.sub(hi, lo))), 1n),
           L.subst(Nat, z => {Nat.sub(hi, 1n+z) == Nat.sub(Nat.sub(Nat.sub(hi, lo), H.hlf(Nat.sub(hi, lo))), 1n) : Nat}, mnat(lo, hi), m, Equal.sym(Nat, m, mnat(lo, hi), hem),
             gap_right(lo, hi, N.lt_le(lo, hi, hlt)))),
         gap_le(Nat.sub(hi, lo))),
       hsize))

# The window shrinks to [lo, m): the entry at the midpoint is not below v.
def go_left(+f2: Nat, +d: Nat, +t: AR.Tree<U32>, +v: U32, +lo: Nat, +hi: Nat, +lb: Nat, +w0: Nat, +w1: Nat, +m: Nat, +hlt: {Nat.is_lt(lo, hi) == True{} : Bool}, +hml: {Nat.is_le(lo, m) == True{} : Bool}, +hmu: {Nat.is_lt(m, hi) == True{} : Bool}, +hem: {m == mnat(lo, hi) : Nat}, +h01: {Nat.is_le(w0, lo) == True{} : Bool}, +hlb1: {Nat.is_le(lo, lb) == True{} : Bool}, +hw1: {Nat.is_le(hi, w1) == True{} : Bool}, +hsize: {Nat.is_lt(Nat.sub(hi, lo), SC.pow2(1n+f2)) == True{} : Bool}, +hlbm: {Nat.is_le(lb, m) == True{} : Bool}, ih: IH(f2, d, t, v, lb, w0, w1)) -> LoopOK(f2, d, t, v, lo, m, lb):
  ih(lo, m,
     h01,
     hlb1,
     hlbm,
     N.le_trans(m, hi, w1, N.lt_le(m, hi, hmu), hw1),
     H.step_bound(Nat.sub(m, lo), Nat.sub(hi, lo), SC.pow2(f2),
       L.subst(Nat, z => {Nat.is_le(z, H.hlf(Nat.sub(hi, lo))) == True{} : Bool}, H.hlf(Nat.sub(hi, lo)), Nat.sub(m, lo),
         Equal.sym(Nat, Nat.sub(m, lo), H.hlf(Nat.sub(hi, lo)),
           L.subst(Nat, z => {Nat.sub(z, lo) == H.hlf(Nat.sub(hi, lo)) : Nat}, mnat(lo, hi), m, Equal.sym(Nat, m, mnat(lo, hi), hem),
             mid_gap(lo, hi, N.lt_le(lo, hi, hlt)))),
         N.le_refl(H.hlf(Nat.sub(hi, lo)))),
       hsize))

# ---- the step, with the midpoint value read from the block ----

def split_side(+f2: Nat, +d: Nat, +t: AR.Tree<U32>, +v: U32, +lo: Nat, +hi: Nat, +lb: Nat, +w0: Nat, +w1: Nat, +m: Nat, +x: U32, +hx: {SC.nth(U32, AR.slots(U32, t), m) == Some{x} : Maybe<&2, U32>}, +hlt: {Nat.is_lt(lo, hi) == True{} : Bool}, +hml: {Nat.is_le(lo, m) == True{} : Bool}, +hmu: {Nat.is_lt(m, hi) == True{} : Bool}, +hem: {m == mnat(lo, hi) : Nat}, +h01: {Nat.is_le(w0, lo) == True{} : Bool}, +hlb1: {Nat.is_le(lo, lb) == True{} : Bool}, +hlb2: {Nat.is_le(lb, hi) == True{} : Bool}, +hw1: {Nat.is_le(hi, w1) == True{} : Bool}, +hsize: {Nat.is_lt(Nat.sub(hi, lo), SC.pow2(1n+f2)) == True{} : Bool}, +hA: {alllt(Nat.sub(lb, w0), AR.slots(U32, t), w0, v) == True{} : Bool}, +hB: {allge(Nat.sub(w1, lb), AR.slots(U32, t), lb, v) == True{} : Bool}, ih: IH(f2, d, t, v, lb, w0, w1), less: Bool, +eless: {U32.is_lt(x, v) == less : Bool}) -> {G.fnd_go(f2, v, G.fnd_side(U32.from_nat(lo), U32.from_nat(hi), U32.from_nat(m), AR.thaw(U32, t), less)) == G.FD{AR.thaw(U32, t), U32.from_nat(lb), U32.from_nat(lb)} : G.Fnd}:
  match less:
    case True{}:
      go_right(f2, d, t, v, lo, hi, lb, w0, w1, m, hlt, hml, hmu, hem, h01, hlb2, hw1, hsize,
        mid_below_lb(t, v, m, lb, w1,
          Equal.trans(Bool, ltat(AR.slots(U32, t), m, v), U32.is_lt(x, v), True{}, ltat_value(AR.slots(U32, t), m, v, x, hx), eless),
          N.lt_le_trans(m, hi, w1, hmu, hw1), hB, N.le_trans(lb, hi, w1, hlb2, hw1)),
        ih)
    case False{}:
      go_left(f2, d, t, v, lo, hi, lb, w0, w1, m, hlt, hml, hmu, hem, h01, hlb1, hw1, hsize,
        mid_at_or_above(t, v, m, lb, w0,
          Equal.trans(Bool, ltat(AR.slots(U32, t), m, v), U32.is_lt(x, v), False{}, ltat_value(AR.slots(U32, t), m, v, x, hx), eless),
          N.le_trans(w0, lo, m, h01, hml), hA, N.le_trans(w0, lo, lb, h01, hlb1)),
        ih)

# The narrowing step: rewrite the U32 test, the midpoint and the block read
# into their Nat meanings, then split on the comparison.
def step_x(+f2: Nat, +d: Nat, +t: AR.Tree<U32>, +v: U32, +lo: Nat, +hi: Nat, +lb: Nat, +w0: Nat, +w1: Nat, +m: Nat, +x: U32, +hx: {SC.nth(U32, AR.slots(U32, t), m) == Some{x} : Maybe<&2, U32>}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hlt: {Nat.is_lt(lo, hi) == True{} : Bool}, +hml: {Nat.is_le(lo, m) == True{} : Bool}, +hmu: {Nat.is_lt(m, hi) == True{} : Bool}, +hem: {m == mnat(lo, hi) : Nat}, +h01: {Nat.is_le(w0, lo) == True{} : Bool}, +hlb1: {Nat.is_le(lo, lb) == True{} : Bool}, +hlb2: {Nat.is_le(lb, hi) == True{} : Bool}, +hw1: {Nat.is_le(hi, w1) == True{} : Bool}, +hcap: {Nat.is_le(w1, SC.pow2(d)) == True{} : Bool}, +hsize: {Nat.is_lt(Nat.sub(hi, lo), SC.pow2(1n+f2)) == True{} : Bool}, +hA: {alllt(Nat.sub(lb, w0), AR.slots(U32, t), w0, v) == True{} : Bool}, +hB: {allge(Nat.sub(w1, lb), AR.slots(U32, t), lb, v) == True{} : Bool}, ih: IH(f2, d, t, v, lb, w0, w1)) -> LoopOK(1n+f2, d, t, v, lo, hi, lb):
  +hk = cap_ok(d, hd)
  +hlok = in_cap(d, w1, lo, hcap, N.le_trans(lo, hi, w1, N.lt_le(lo, hi, hlt), hw1))
  +hhik = in_cap(d, w1, hi, hcap, hw1)
  +hmk = in_cap(d, w1, m, hcap, N.le_trans(m, hi, w1, N.lt_le(m, hi, hmu), hw1))
  +hmd = N.lt_le_trans(m, w1, SC.pow2(d), N.lt_le_trans(m, hi, w1, hmu, hw1), hcap)
  +rm = IX.nat_round(m, 1n+d, hk, hmk)
  # the loop test
  %Equal.sym(Bool, U32.is_lt(U32.from_nat(lo), U32.from_nat(hi)), True{},
    Equal.trans(Bool, U32.is_lt(U32.from_nat(lo), U32.from_nat(hi)), Nat.is_lt(lo, hi), True{}, IX.lt_bridge(lo, hi, 1n+d, hk, hlok, hhik), hlt)) : {G.fnd_go(f2, v, G.fnd_live(v, U32.from_nat(lo), U32.from_nat(hi), AR.thaw(U32, t), _)) == G.FD{AR.thaw(U32, t), U32.from_nat(lb), U32.from_nat(lb)} : G.Fnd}
  # the midpoint
  %Equal.sym(U32, G.mid_of(U32.from_nat(lo), U32.from_nat(hi)), U32.from_nat(m),
    L.subst(Nat, z => {G.mid_of(U32.from_nat(lo), U32.from_nat(hi)) == U32.from_nat(z) : U32}, mnat(lo, hi), m, Equal.sym(Nat, m, mnat(lo, hi), hem),
      mid_bridge(lo, hi, 1n+d, hk, hhik, N.lt_le(lo, hi, hlt)))) : {G.fnd_go(f2, v, G.fnd_mid(v, U32.from_nat(lo), U32.from_nat(hi), AR.thaw(U32, t), _)) == G.FD{AR.thaw(U32, t), U32.from_nat(lb), U32.from_nat(lb)} : G.Fnd}
  # the block read
  %Equal.sym(Array<U32> & U32, Array.get(U32, AR.thaw(U32, t), U32.from_nat(m)), (AR.thaw(U32, t), x),
    AR.get(U32, d, t, U32.from_nat(m), x, hd,
      L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, m, U32.to_nat(U32.from_nat(m)), Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, rm), hmd),
      L.subst(Nat, z => {SC.nth(U32, AR.slots(U32, t), z) == Some{x} : Maybe<&2, U32>}, m, U32.to_nat(U32.from_nat(m)), Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, rm), hx),
      pf)) : {G.fnd_go(f2, v, G.fnd_at(v, U32.from_nat(lo), U32.from_nat(hi), U32.from_nat(m), _)) == G.FD{AR.thaw(U32, t), U32.from_nat(lb), U32.from_nat(lb)} : G.Fnd}
  split_side(f2, d, t, v, lo, hi, lb, w0, w1, m, x, hx, hlt, hml, hmu, hem, h01, hlb1, hlb2, hw1, hsize, hA, hB, ih, U32.is_lt(x, v), {==})

def step_read(+f2: Nat, +d: Nat, +t: AR.Tree<U32>, +v: U32, +lo: Nat, +hi: Nat, +lb: Nat, +w0: Nat, +w1: Nat, +m: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hlt: {Nat.is_lt(lo, hi) == True{} : Bool}, +hml: {Nat.is_le(lo, m) == True{} : Bool}, +hmu: {Nat.is_lt(m, hi) == True{} : Bool}, +hem: {m == mnat(lo, hi) : Nat}, +h01: {Nat.is_le(w0, lo) == True{} : Bool}, +hlb1: {Nat.is_le(lo, lb) == True{} : Bool}, +hlb2: {Nat.is_le(lb, hi) == True{} : Bool}, +hw1: {Nat.is_le(hi, w1) == True{} : Bool}, +hcap: {Nat.is_le(w1, SC.pow2(d)) == True{} : Bool}, +hsize: {Nat.is_lt(Nat.sub(hi, lo), SC.pow2(1n+f2)) == True{} : Bool}, +hA: {alllt(Nat.sub(lb, w0), AR.slots(U32, t), w0, v) == True{} : Bool}, +hB: {allge(Nat.sub(w1, lb), AR.slots(U32, t), lb, v) == True{} : Bool}, ih: IH(f2, d, t, v, lb, w0, w1), mb: Maybe<&2, U32>, +hmb: {SC.nth(U32, AR.slots(U32, t), m) == mb : Maybe<&2, U32>}) -> LoopOK(1n+f2, d, t, v, lo, hi, lb):
  match mb:
    case None{}:
      Empty.absurd(LoopOK(1n+f2, d, t, v, lo, hi, lb),
        LL.sc_nth_some(U32, AR.slots(U32, t), m,
          slot_some(d, t, m, pf, N.lt_le_trans(m, w1, SC.pow2(d), N.lt_le_trans(m, hi, w1, hmu, hw1), hcap)),
          hmb))
    case Some{+x}:
      step_x(f2, d, t, v, lo, hi, lb, w0, w1, m, x, hmb, hd, pf, hlt, hml, hmu, hem, h01, hlb1, hlb2, hw1, hcap, hsize, hA, hB, ih)

def step_live(+f2: Nat, +d: Nat, +t: AR.Tree<U32>, +v: U32, +lo: Nat, +hi: Nat, +lb: Nat, +w0: Nat, +w1: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +h01: {Nat.is_le(w0, lo) == True{} : Bool}, +hlb1: {Nat.is_le(lo, lb) == True{} : Bool}, +hlb2: {Nat.is_le(lb, hi) == True{} : Bool}, +hw1: {Nat.is_le(hi, w1) == True{} : Bool}, +hcap: {Nat.is_le(w1, SC.pow2(d)) == True{} : Bool}, +hsize: {Nat.is_lt(Nat.sub(hi, lo), SC.pow2(1n+f2)) == True{} : Bool}, +hA: {alllt(Nat.sub(lb, w0), AR.slots(U32, t), w0, v) == True{} : Bool}, +hB: {allge(Nat.sub(w1, lb), AR.slots(U32, t), lb, v) == True{} : Bool}, ih: IH(f2, d, t, v, lb, w0, w1), live: Bool, +elive: {Nat.is_lt(lo, hi) == live : Bool}) -> LoopOK(1n+f2, d, t, v, lo, hi, lb):
  match live:
    case False{}:
      empty_case(1n+f2, d, t, v, lo, hi, lb,
        pinch_lo(lo, hi, lb, hlb1, hlb2, N.not_lt_le(lo, hi, elive)),
        pinch_hi(lo, hi, lb, hlb1, hlb2, N.not_lt_le(lo, hi, elive)))
    case True{}:
      step_read(f2, d, t, v, lo, hi, lb, w0, w1, mnat(lo, hi), hd, pf, elive,
        mid_lower(lo, hi, N.lt_le(lo, hi, elive)), mid_upper(lo, hi, elive), {==},
        h01, hlb1, hlb2, hw1, hcap, hsize, hA, hB, ih,
        SC.nth(U32, AR.slots(U32, t), mnat(lo, hi)), {==})

# The loop finds the lower bound.
def loop(+f: Nat, +d: Nat, +t: AR.Tree<U32>, +v: U32, +lo: Nat, +hi: Nat, +lb: Nat, +w0: Nat, +w1: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +h01: {Nat.is_le(w0, lo) == True{} : Bool}, +hlb1: {Nat.is_le(lo, lb) == True{} : Bool}, +hlb2: {Nat.is_le(lb, hi) == True{} : Bool}, +hw1: {Nat.is_le(hi, w1) == True{} : Bool}, +hcap: {Nat.is_le(w1, SC.pow2(d)) == True{} : Bool}, +hsize: {Nat.is_lt(Nat.sub(hi, lo), SC.pow2(f)) == True{} : Bool}, +hA: {alllt(Nat.sub(lb, w0), AR.slots(U32, t), w0, v) == True{} : Bool}, +hB: {allge(Nat.sub(w1, lb), AR.slots(U32, t), lb, v) == True{} : Bool}) -> LoopOK(f, d, t, v, lo, hi, lb):
  match f:
    case 0n:
      empty_case(0n, d, t, v, lo, hi, lb,
        pinch_lo(lo, hi, lb, hlb1, hlb2, size_zero_le(hi, lo, hsize)),
        pinch_hi(lo, hi, lb, hlb1, hlb2, size_zero_le(hi, lo, hsize)))
    case 1n+f2:
      step_live(f2, d, t, v, lo, hi, lb, w0, w1, hd, pf, h01, hlb1, hlb2, hw1, hcap, hsize, hA, hB,
        lo2 => hi2 => p1 => p2 => p3 => p4 => p5 => loop(f2, d, t, v, lo2, hi2, lb, w0, w1, hd, pf, p1, p2, p3, p4, hcap, p5, hA, hB),
        Nat.is_lt(lo, hi), {==})

# ---- locate ----

def eqm(m: Maybe<&2, U32>, +v: U32) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+x}:
      U32.is_eq(x, v)

def eqat(xs: List<&2, U32>, +j: Nat, +v: U32) -> Bool:
  eqm(SC.nth(U32, xs, j), v)

def pick(b: Bool, e: Bool) -> Bool:
  match b:
    case True{}:
      e
    case False{}:
      False{}

# `found` as the implementation reports it: the lower bound is inside the
# window and the entry there is v.
def found_of(+t: AR.Tree<U32>, +lb: Nat, +hi: Nat, +v: U32) -> Bool:
  pick(Nat.is_lt(lb, hi), eqat(AR.slots(U32, t), lb, v))

def loc_read(+d: Nat, +t: AR.Tree<U32>, +v: U32, +hi: Nat, +lb: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hcap: {Nat.is_le(hi, SC.pow2(d)) == True{} : Bool}, +ein: {Nat.is_lt(lb, hi) == True{} : Bool}, mb: Maybe<&2, U32>, +hmb: {SC.nth(U32, AR.slots(U32, t), lb) == mb : Maybe<&2, U32>}) -> {G.loc_chk(U32.from_nat(lb), v, Array.get(U32, AR.thaw(U32, t), U32.from_nat(lb))) == G.LC{AR.thaw(U32, t), U32.from_nat(lb), pick(True{}, eqat(AR.slots(U32, t), lb, v))} : G.Loc}:
  match mb:
    case None{}:
      Empty.absurd({G.loc_chk(U32.from_nat(lb), v, Array.get(U32, AR.thaw(U32, t), U32.from_nat(lb))) == G.LC{AR.thaw(U32, t), U32.from_nat(lb), pick(True{}, eqat(AR.slots(U32, t), lb, v))} : G.Loc},
        LL.sc_nth_some(U32, AR.slots(U32, t), lb, slot_some(d, t, lb, pf, N.lt_le_trans(lb, hi, SC.pow2(d), ein, hcap)), hmb))
    case Some{+x}:
      +rb = IX.nat_round(lb, 1n+d, cap_ok(d, hd), in_cap(d, hi, lb, hcap, N.lt_le(lb, hi, ein)))
      %Equal.sym(Bool, eqat(AR.slots(U32, t), lb, v), U32.is_eq(x, v), Equal.cong(Maybe<&2, U32>, Bool, mm => eqm(mm, v), SC.nth(U32, AR.slots(U32, t), lb), Some{x}, hmb)) : {G.loc_chk(U32.from_nat(lb), v, Array.get(U32, AR.thaw(U32, t), U32.from_nat(lb))) == G.LC{AR.thaw(U32, t), U32.from_nat(lb), _} : G.Loc}
      %Equal.sym(Array<U32> & U32, Array.get(U32, AR.thaw(U32, t), U32.from_nat(lb)), (AR.thaw(U32, t), x),
        AR.get(U32, d, t, U32.from_nat(lb), x, hd,
          L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, lb, U32.to_nat(U32.from_nat(lb)), Equal.sym(Nat, U32.to_nat(U32.from_nat(lb)), lb, rb), N.lt_le_trans(lb, hi, SC.pow2(d), ein, hcap)),
          L.subst(Nat, z => {SC.nth(U32, AR.slots(U32, t), z) == Some{x} : Maybe<&2, U32>}, lb, U32.to_nat(U32.from_nat(lb)), Equal.sym(Nat, U32.to_nat(U32.from_nat(lb)), lb, rb), hmb),
          pf)) : {G.loc_chk(U32.from_nat(lb), v, _) == G.LC{AR.thaw(U32, t), U32.from_nat(lb), U32.is_eq(x, v)} : G.Loc}
      {==}

# `locate` returns the lower bound and whether the entry there is v.
def loc_in_ok(+d: Nat, +t: AR.Tree<U32>, +v: U32, +hi: Nat, +lb: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hcap: {Nat.is_le(hi, SC.pow2(d)) == True{} : Bool}, inside: Bool, +ein: {Nat.is_lt(lb, hi) == inside : Bool}) -> {G.loc_in(v, AR.thaw(U32, t), U32.from_nat(lb), inside) == G.LC{AR.thaw(U32, t), U32.from_nat(lb), pick(inside, eqat(AR.slots(U32, t), lb, v))} : G.Loc}:
  match inside:
    case False{}:
      {==}
    case True{}:
      loc_read(d, t, v, hi, lb, hd, pf, hcap, ein, SC.nth(U32, AR.slots(U32, t), lb), {==})

def locate_ok(+d: Nat, +t: AR.Tree<U32>, +v: U32, +lo: Nat, +hi: Nat, +lb: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hlb1: {Nat.is_le(lo, lb) == True{} : Bool}, +hlb2: {Nat.is_le(lb, hi) == True{} : Bool}, +hcap: {Nat.is_le(hi, SC.pow2(d)) == True{} : Bool}, +hA: {alllt(Nat.sub(lb, lo), AR.slots(U32, t), lo, v) == True{} : Bool}, +hB: {allge(Nat.sub(hi, lb), AR.slots(U32, t), lb, v) == True{} : Bool}) -> {G.locate(d, v, U32.from_nat(lo), U32.from_nat(hi), AR.thaw(U32, t)) == G.LC{AR.thaw(U32, t), U32.from_nat(lb), found_of(t, lb, hi, v)} : G.Loc}:
  %Equal.sym(G.Fnd, G.fnd_go(1n+d, v, G.FD{AR.thaw(U32, t), U32.from_nat(lo), U32.from_nat(hi)}), G.FD{AR.thaw(U32, t), U32.from_nat(lb), U32.from_nat(lb)},
    loop(1n+d, d, t, v, lo, hi, lb, lo, hi, hd, pf, N.le_refl(lo), hlb1, hlb2, N.le_refl(hi), hcap,
      N.le_lt_trans(Nat.sub(hi, lo), hi, SC.pow2(1n+d), sub_le_self(hi, lo), N.le_lt_trans(hi, SC.pow2(d), SC.pow2(1n+d), hcap, N.pow2_lt_succ(d))),
      hA, hB)) : {G.loc_end(v, U32.from_nat(hi), _) == G.LC{AR.thaw(U32, t), U32.from_nat(lb), found_of(t, lb, hi, v)} : G.Loc}
  %Equal.sym(Bool, U32.is_lt(U32.from_nat(lb), U32.from_nat(hi)), Nat.is_lt(lb, hi),
    IX.lt_bridge(lb, hi, 1n+d, cap_ok(d, hd), in_cap(d, hi, lb, hcap, hlb2), in_cap(d, hi, hi, hcap, N.le_refl(hi)))) : {G.loc_in(v, AR.thaw(U32, t), U32.from_nat(lb), _) == G.LC{AR.thaw(U32, t), U32.from_nat(lb), found_of(t, lb, hi, v)} : G.Loc}
  loc_in_ok(d, t, v, hi, lb, hd, pf, hcap, Nat.is_lt(lb, hi), {==})
