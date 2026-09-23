import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../lib/order.bend as O
import ../../lib/array.bend as AR
import ../../lib/u32.bend as U
import ../../lib/spec_common.bend as SC
import ./spec.bend as S
import ../../../src/containers/binary_heap.bend as H
import ./idx.bend as IX
import ./u32idx.bend as UX
import ./slots.bend as SL
import ./vals.bend as V
import ./bag.bend as BG
import ./multiset.bend as M
import ./up.bend as UPS

# The sift-down loop, mirrored on the shadow tree.
#
# The invariant is the mirror image of the sift-up one. With the hole at i and
# the sifted value x (the logical array is `UPS.ulog(t, i, x)`):
#   D1  every pair holds except the two whose parent is the hole
#   D2  the pair INTO the hole holds (its parent is not larger than x)
#   D3  the value physically at the hole's parent is not larger than the
#       hole's children -- stated on the block, so that it also says the right
#       thing at the root, where the hole's "parent" is the stale slot 0
# and the loop moves the hole to the smaller child while that child is
# smaller than x.

type DownS<-A: Data> is Data:
  DStp{t: AR.Tree<Maybe<&2, A>>, i: Nat}
  DMv{t: AR.Tree<Maybe<&2, A>>, i: Nat, cv: A, ci: Nat}

def dreal(~A: Data, s: DownS<A>) -> H.Down<A>:
  match s:
    case DStp{t, i}:
      H.DStop{AR.thaw(Maybe<&2, A>, t), U32.from_nat(i)}
    case DMv{t, i, cv, ci}:
      H.DMove{AR.thaw(Maybe<&2, A>, t), U32.from_nat(i), cv, U32.from_nat(ci)}

# ---- the mirror of `H.down_probe` ----

def ddec(~A: Data, t: AR.Tree<Maybe<&2, A>>, +i: Nat, cv: A, ci: Nat, ok: Bool) -> DownS<A>:
  match ok:
    case True{}:
      DStp{t, i}
    case False{}:
      DMv{t, i, cv, ci}

def dcmp(~A: Data, ~cmp: A -> A -> Cmp, t: AR.Tree<Maybe<&2, A>>, +i: Nat, x: A, +cv: A, ci: Nat) -> DownS<A>:
  ddec(~A, t, i, cv, ci, S.le(~A, ~cmp, x, cv))

def dtwo(~A: Data, ~cmp: A -> A -> Cmp, t: AR.Tree<Maybe<&2, A>>, +i: Nat, x: A, l: Nat, +lv: A, r: Nat, +rv: A, left: Bool) -> DownS<A>:
  match left:
    case True{}:
      dcmp(~A, ~cmp, t, i, x, lv, l)
    case False{}:
      dcmp(~A, ~cmp, t, i, x, rv, r)

def drmb(~A: Data, ~cmp: A -> A -> Cmp, t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, l: Nat, +lv: A, r: Nat, m: Maybe<&2, A>) -> DownS<A>:
  match m:
    case None{}:
      dcmp(~A, ~cmp, t, i, x, lv, l)
    case Some{+rv}:
      dtwo(~A, ~cmp, t, i, x, l, lv, r, rv, S.le(~A, ~cmp, lv, rv))

def dlmb(~A: Data, ~cmp: A -> A -> Cmp, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +l: Nat, two: Bool, m: Maybe<&2, A>) -> DownS<A>:
  match two m:
    case _ None{}:
      DStp{t, i}
    case True{} Some{+lv}:
      drmb(~A, ~cmp, t, i, x, l, lv, 1n+l, SL.slot(~A, AR.slots(Maybe<&2, A>, t), 1n+l))
    case False{} Some{+lv}:
      dcmp(~A, ~cmp, t, i, x, lv, l)

def dhas(~A: Data, ~cmp: A -> A -> Cmp, +n: Nat, +i: Nat, +x: A, +t: AR.Tree<Maybe<&2, A>>, +l: Nat, has_left: Bool) -> DownS<A>:
  match has_left:
    case True{}:
      dlmb(~A, ~cmp, t, i, x, l, Nat.is_lt(l, Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t), l))
    case False{}:
      DStp{t, i}

def dprobe(~A: Data, ~cmp: A -> A -> Cmp, +n: Nat, +i: Nat, +x: A, +t: AR.Tree<Maybe<&2, A>>) -> DownS<A>:
  dhas(~A, ~cmp, n, i, x, t, IX.kidl(i), Nat.is_lt(IX.kidl(i), n))

# ---- the bridge ----

def double_gt(+v: Nat, +h: {Nat.is_lt(0n, v) == True{} : Bool}) -> {Nat.is_lt(v, Nat.double(v)) == True{} : Bool}:
  match v:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, L.true_not_false(Nat.is_lt(0n, 0n), h, N.lt_irrefl(0n)))
    case 1n+k:
      N.le_lt_succ(1n+k, 1n+Nat.double(k), N.lt_succ_le_succ(k, 1n+Nat.double(k), N.le_lt_trans(k, Nat.double(k), 1n+Nat.double(k), IX.double_le(k), N.lt_succ(Nat.double(k)))))

def pow2_up(+d: Nat) -> {Nat.is_lt(SC.pow2(d), SC.pow2(1n+d)) == True{} : Bool}:
  double_gt(SC.pow2(d), UPS.pow2_pos(d))

def double_lt_pow(+i: Nat, +d: Nat, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(Nat.double(i), SC.pow2(1n+d)) == True{} : Bool}:
  IX.double_lt(i, SC.pow2(d), hi)

def kidl_bridge(+i: Nat, +d: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}) -> {U32.inc(U32.shl(U32.from_nat(i))) == U32.from_nat(IX.kidl(i)) : U32}:
  Equal.cong(U32, U32, y => U32.inc(y), U32.shl(U32.from_nat(i)), U32.from_nat(Nat.double(i)),
    UX.shl_bridge(i, 1n+d, N.lt_succ_le_succ(d, 32n, hd), N.lt_trans(i, SC.pow2(d), SC.pow2(1n+d), hi, pow2_up(d)), double_lt_pow(i, d, hi)))

def ddec_ok(~A: Data, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +cv: A, +ci: Nat, b: Bool) -> {H.down_dec(~A, AR.thaw(Maybe<&2, A>, t), U32.from_nat(i), cv, U32.from_nat(ci), b) == dreal(~A, ddec(~A, t, i, cv, ci, b)) : H.Down<A>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def dcmp_ok(~A: Data, ~cmp: A -> A -> Cmp, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat) -> {H.down_dec(~A, AR.thaw(Maybe<&2, A>, t), U32.from_nat(i), cv, U32.from_nat(ci), S.le(~A, ~cmp, x, cv)) == dreal(~A, dcmp(~A, ~cmp, t, i, x, cv, ci)) : H.Down<A>}:
  ddec_ok(~A, t, i, cv, ci, S.le(~A, ~cmp, x, cv))

def dtwo_ok(~A: Data, ~cmp: A -> A -> Cmp, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +l: Nat, +lv: A, +r: Nat, +rv: A, b: Bool) -> {H.down_two(~A, ~cmp, AR.thaw(Maybe<&2, A>, t), U32.from_nat(i), x, U32.from_nat(l), lv, U32.from_nat(r), rv, b) == dreal(~A, dtwo(~A, ~cmp, t, i, x, l, lv, r, rv, b)) : H.Down<A>}:
  match b:
    case True{}:
      dcmp_ok(~A, ~cmp, t, i, x, lv, l)
    case False{}:
      dcmp_ok(~A, ~cmp, t, i, x, rv, r)

def drmb_ok(~A: Data, ~cmp: A -> A -> Cmp, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +l: Nat, +lv: A, +r: Nat, m: Maybe<&2, A>) -> {H.down_rmb(~A, ~cmp, AR.thaw(Maybe<&2, A>, t), U32.from_nat(i), x, U32.from_nat(l), lv, U32.from_nat(r), m) == dreal(~A, drmb(~A, ~cmp, t, i, x, l, lv, r, m)) : H.Down<A>}:
  match m:
    case None{}:
      dcmp_ok(~A, ~cmp, t, i, x, lv, l)
    case Some{+rv}:
      dtwo_ok(~A, ~cmp, t, i, x, l, lv, r, rv, S.le(~A, ~cmp, lv, rv))

# l < n - 1 gives l + 1 < n

def right_in(+l: Nat, +n: Nat, +e: {Nat.is_lt(l, Nat.sub(n, 1n)) == True{} : Bool}) -> {Nat.is_lt(1n+l, n) == True{} : Bool}:
  L.subst(Bool, b => {b == True{} : Bool}, Nat.is_lt(l, Nat.sub(n, 1n)), Nat.is_lt(1n+l, n), Equal.sym(Bool, Nat.is_lt(1n+l, n), Nat.is_lt(l, Nat.sub(n, 1n)), IX.succ_lt_sub(l, n)), e)

# the right child is read only when it is inside the heap, so its index is
# below the block

def dlmb_ok(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +l: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hn: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, two: Bool, m: Maybe<&2, A>, +etwo: {Nat.is_lt(l, Nat.sub(n, 1n)) == two : Bool}, +hl: {l == IX.kidl(i) : Nat}) -> {H.down_lmb(~A, ~cmp, AR.thaw(Maybe<&2, A>, t), U32.from_nat(i), x, U32.from_nat(l), two, m) == dreal(~A, dlmb(~A, ~cmp, t, i, x, l, two, m)) : H.Down<A>}:
  match two m:
    case True{} None{}:
      {==}
    case False{} None{}:
      {==}
    case False{} Some{lv}:
      dcmp_ok(~A, ~cmp, t, i, x, lv, l)
    case True{} Some{+lv}:
      +hr = right_in(l, n, etwo)
      %Equal.sym(Array<Maybe<&2, A>> & Maybe<&2, A>, Array.get(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), U32.from_nat(1n+l)), (AR.thaw(Maybe<&2, A>, t), SL.slot(~A, AR.slots(Maybe<&2, A>, t), 1n+l)), UPS.get_slot(~A, d, t, 1n+l, hd, N.lt_le_trans(1n+l, n, SC.pow2(d), hr, hn), pf)) : {H.down_rslot(~A, ~cmp, U32.from_nat(i), x, U32.from_nat(l), lv, U32.inc(U32.from_nat(l)), _) == dreal(~A, dlmb(~A, ~cmp, t, i, x, l, True{}, Some{lv})) : H.Down<A>}
      drmb_ok(~A, ~cmp, t, i, x, l, lv, 1n+l, SL.slot(~A, AR.slots(Maybe<&2, A>, t), 1n+l))

# the "there is a right child" test, in Nat

def two_bridge(+l: Nat, +n: Nat, +d: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hl: {Nat.is_lt(l, SC.pow2(d)) == True{} : Bool}, +hln: {Nat.is_lt(l, n) == True{} : Bool}, +hn: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}) -> {U32.is_lt(U32.from_nat(l), U32.sub(U32.from_nat(n), 1)) == Nat.is_lt(l, Nat.sub(n, 1n)) : Bool}:
  +hnd = N.le_lt_trans(n, SC.pow2(d), SC.pow2(1n+d), hn, pow2_up(d))
  +hpos = N.lt_succ_le_succ(0n, n, N.le_lt_trans(0n, l, n, N.zero_le(l), hln))
  %Equal.sym(U32, U32.sub(U32.from_nat(n), 1), U32.from_nat(Nat.sub(n, 1n)), UX.sub_one(n, 1n+d, N.lt_succ_le_succ(d, 32n, hd), hnd, hpos)) : {U32.is_lt(U32.from_nat(l), _) == Nat.is_lt(l, Nat.sub(n, 1n)) : Bool}
  UX.lt_bridge(l, Nat.sub(n, 1n), 1n+d, N.lt_succ_le_succ(d, 32n, hd), N.lt_trans(l, SC.pow2(d), SC.pow2(1n+d), hl, pow2_up(d)), N.le_lt_trans(Nat.sub(n, 1n), n, SC.pow2(1n+d), UX.sub_le(n), hnd))

def dhas_ok(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hn: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, b: Bool, +eb: {Nat.is_lt(IX.kidl(i), n) == b : Bool}) -> {H.down_has(~A, ~cmp, U32.from_nat(n), U32.from_nat(i), x, AR.thaw(Maybe<&2, A>, t), U32.from_nat(IX.kidl(i)), b) == dreal(~A, dhas(~A, ~cmp, n, i, x, t, IX.kidl(i), b)) : H.Down<A>}:
  match b:
    case False{}:
      {==}
    case True{}:
      +hl = N.lt_le_trans(IX.kidl(i), n, SC.pow2(d), eb, hn)
      %Equal.sym(Bool, U32.is_lt(U32.from_nat(IX.kidl(i)), U32.sub(U32.from_nat(n), 1)), Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), two_bridge(IX.kidl(i), n, d, hd, hl, eb, hn)) : {H.down_lslot(~A, ~cmp, U32.from_nat(i), x, U32.from_nat(IX.kidl(i)), _, Array.get(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), U32.from_nat(IX.kidl(i)))) == dreal(~A, dhas(~A, ~cmp, n, i, x, t, IX.kidl(i), True{})) : H.Down<A>}
      %Equal.sym(Array<Maybe<&2, A>> & Maybe<&2, A>, Array.get(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), U32.from_nat(IX.kidl(i))), (AR.thaw(Maybe<&2, A>, t), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i))), UPS.get_slot(~A, d, t, IX.kidl(i), hd, hl, pf)) : {H.down_lslot(~A, ~cmp, U32.from_nat(i), x, U32.from_nat(IX.kidl(i)), Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), _) == dreal(~A, dhas(~A, ~cmp, n, i, x, t, IX.kidl(i), True{})) : H.Down<A>}
      dlmb_ok(~A, ~cmp, d, n, t, i, x, IX.kidl(i), hd, hn, pf, Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), {==}, {==})

def dprobe_ok(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hn: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {H.down_probe(~A, ~cmp, U32.from_nat(n), U32.from_nat(i), x, AR.thaw(Maybe<&2, A>, t)) == dreal(~A, dprobe(~A, ~cmp, n, i, x, t)) : H.Down<A>}:
  %Equal.sym(U32, U32.inc(U32.shl(U32.from_nat(i))), U32.from_nat(IX.kidl(i)), kidl_bridge(i, d, hd, hi)) : {H.down_has(~A, ~cmp, U32.from_nat(n), U32.from_nat(i), x, AR.thaw(Maybe<&2, A>, t), _, U32.is_lt(_, U32.from_nat(n))) == dreal(~A, dprobe(~A, ~cmp, n, i, x, t)) : H.Down<A>}
  %Equal.sym(Bool, U32.is_lt(U32.from_nat(IX.kidl(i)), U32.from_nat(n)), Nat.is_lt(IX.kidl(i), n), UX.lt_bridge(IX.kidl(i), n, 1n+d, N.lt_succ_le_succ(d, 32n, hd), IX.kidl_bound(i, d, hi), N.le_lt_trans(n, SC.pow2(d), SC.pow2(1n+d), hn, pow2_up(d)))) : {H.down_has(~A, ~cmp, U32.from_nat(n), U32.from_nat(i), x, AR.thaw(Maybe<&2, A>, t), U32.from_nat(IX.kidl(i)), _) == dreal(~A, dprobe(~A, ~cmp, n, i, x, t)) : H.Down<A>}
  dhas_ok(~A, ~cmp, d, n, t, i, x, hd, hn, pf, Nat.is_lt(IX.kidl(i), n), {==})

# ---- one step of the sift-down loop ----
#
# The hole moves from i to the child ci (whose value cv is the smaller of the
# children and is smaller than x). `s` is the other child. The step writes cv
# into slot i, so the block becomes `t2` and the logical array is `d2`.

def t2_of(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +cv: A) -> AR.Tree<Maybe<&2, A>>:
  UPS.set_tree(~A, d, t, i, cv)

def d2_of(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat) -> List<&2, Maybe<&2, A>>:
  UPS.ulog(~A, t2_of(~A, d, t, i, cv), ci, x)

def d2_at_c(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +hc: {Nat.is_lt(ci, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), ci) == Some{x} : Maybe<&2, A>}:
  UPS.ulog_at(~A, d, t2_of(~A, d, t, i, cv), ci, x, hc, UPS.t2_perfect(~A, d, t, i, cv, pf))

def d2_at_i(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +hne: {Nat.is_eq(ci, i) == False{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), i) == Some{cv} : Maybe<&2, A>}:
  Equal.trans(Maybe<&2, A>, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), i), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), i), Some{cv},
    UPS.ulog_off(~A, t2_of(~A, d, t, i, cv), ci, x, i, hne),
    Equal.trans(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), i), SL.slot(~A, UPS.ulog(~A, t, i, cv), i), Some{cv},
      Equal.cong(List<&2, Maybe<&2, A>>, Maybe<&2, A>, ss => SL.slot(~A, ss, i), AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), UPS.ulog(~A, t, i, cv), UPS.set_slots(~A, d, t, i, cv, hi, pf)),
      UPS.ulog_at(~A, d, t, i, cv, hi, pf)))

def d2_off(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +j: Nat, +hji: {Nat.is_eq(i, j) == False{} : Bool}, +hjc: {Nat.is_eq(ci, j) == False{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), j) == SL.slot(~A, AR.slots(Maybe<&2, A>, t), j) : Maybe<&2, A>}:
  Equal.trans(Maybe<&2, A>, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), j), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), j), SL.slot(~A, AR.slots(Maybe<&2, A>, t), j),
    UPS.ulog_off(~A, t2_of(~A, d, t, i, cv), ci, x, j, hjc),
    Equal.trans(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), j), SL.slot(~A, UPS.ulog(~A, t, i, cv), j), SL.slot(~A, AR.slots(Maybe<&2, A>, t), j),
      Equal.cong(List<&2, Maybe<&2, A>>, Maybe<&2, A>, ss => SL.slot(~A, ss, j), AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), UPS.ulog(~A, t, i, cv), UPS.set_slots(~A, d, t, i, cv, hi, pf)),
      UPS.ulog_off(~A, t, i, cv, j, hji)))

# the current logical array, for reference: x sits at the hole

def d1_at_i(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {SL.slot(~A, UPS.ulog(~A, t, i, x), i) == Some{x} : Maybe<&2, A>}:
  UPS.ulog_at(~A, d, t, i, x, hi, pf)

def kid_pick_of(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +n: Nat, +i: Nat, +ci: Nat, +hkids: {SL.kids_le(~A, ~cmp, ss, n, IX.par(i), i) == True{} : Bool}, e: {ci == IX.kidl(i) : Nat} | {ci == IX.kidr(i) : Nat}) -> {SL.kid_le(~A, ~cmp, ss, n, IX.par(i), ci) == True{} : Bool}:
  match e:
    case Inl{ec}:
      L.subst(Nat, z => {SL.kid_le(~A, ~cmp, ss, n, IX.par(i), z) == True{} : Bool}, IX.kidl(i), ci, Equal.sym(Nat, ci, IX.kidl(i), ec), L.and_left(SL.kid_le(~A, ~cmp, ss, n, IX.par(i), IX.kidl(i)), SL.kid_le(~A, ~cmp, ss, n, IX.par(i), IX.kidr(i)), hkids))
    case Inr{ec}:
      L.subst(Nat, z => {SL.kid_le(~A, ~cmp, ss, n, IX.par(i), z) == True{} : Bool}, IX.kidr(i), ci, Equal.sym(Nat, ci, IX.kidr(i), ec), L.and_right(SL.kid_le(~A, ~cmp, ss, n, IX.par(i), IX.kidl(i)), SL.kid_le(~A, ~cmp, ss, n, IX.par(i), IX.kidr(i)), hkids))

def kid_pick(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +n: Nat, +i: Nat, +ci: Nat, +epc: {IX.par(ci) == i : Nat}, +hcpos: {Nat.is_le(1n, ci) == True{} : Bool}, +hkids: {SL.kids_le(~A, ~cmp, ss, n, IX.par(i), i) == True{} : Bool}) -> {SL.kid_le(~A, ~cmp, ss, n, IX.par(i), ci) == True{} : Bool}:
  kid_pick_of(~A, ~cmp, ss, n, i, ci, hkids, UPS.kid_at(i, ci, epc, IX.kid_split(ci, N.succ_le_lt(0n, ci, hcpos))))

def d1n_i_mle(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +hcn: {Nat.is_lt(ci, n) == True{} : Bool}, +hcv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), ci) == Some{cv} : Maybe<&2, A>}, +epc: {IX.par(ci) == i : Nat}, +hcpos: {Nat.is_le(1n, ci) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hkids: {SL.kids_le(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, IX.par(i), i) == True{} : Bool}) -> {SL.mle(~A, ~cmp, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), IX.par(i)), SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), i)) == True{} : Bool}:
  +hgrand = SL.ne_sym(ci, IX.par(i), N.is_eq_lt(IX.par(i), ci, N.lt_trans(IX.par(i), i, ci, IX.par_lt(i, N.succ_le_lt(0n, i, hpos)), L.subst(Nat, z => {Nat.is_lt(z, ci) == True{} : Bool}, IX.par(ci), i, epc, IX.par_lt(ci, N.succ_le_lt(0n, ci, hcpos))))))
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), IX.par(i)), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)), d2_off(~A, d, t, i, x, cv, ci, IX.par(i), SL.ne_sym(i, IX.par(i), UPS.par_ne(i, hpos)), hgrand, hi, pf)) : {SL.mle(~A, ~cmp, _, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), i)) == True{} : Bool}
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), i), Some{cv}, d2_at_i(~A, d, t, i, x, cv, ci, SL.ne_sym(ci, i, N.is_eq_lt(i, ci, L.subst(Nat, z => {Nat.is_lt(z, ci) == True{} : Bool}, IX.par(ci), i, epc, IX.par_lt(ci, N.succ_le_lt(0n, ci, hcpos))))), hi, pf)) : {SL.mle(~A, ~cmp, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)), _) == True{} : Bool}
  %hcv : {SL.mle(~A, ~cmp, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)), _) == True{} : Bool}
  SL.kid_le_at(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, IX.par(i), ci, hcn, kid_pick(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, i, ci, epc, hcpos, hkids))

def d1n_i(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +j: Nat, +ej: {Nat.is_eq(j, i) == True{} : Bool}, +hcn: {Nat.is_lt(ci, n) == True{} : Bool}, +hcv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), ci) == Some{cv} : Maybe<&2, A>}, +epc: {IX.par(ci) == i : Nat}, +hcpos: {Nat.is_le(1n, ci) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hkids: {SL.kids_le(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, IX.par(i), i) == True{} : Bool}, b: Bool, +eb: {Nat.is_eq(i, 0n) == b : Bool}) -> {SL.pair_ok(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), j) == True{} : Bool}:
  match b:
    case True{}:
      L.subst(Nat, z => {SL.pair_ok(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), z) == True{} : Bool}, i, j, Equal.sym(Nat, j, i, N.eq_from_is_eq(j, i, ej)),
        UPS.pair_ok_zero(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), i, eb))
    case False{}:
      L.subst(Nat, z => {SL.pair_ok(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), z) == True{} : Bool}, i, j, Equal.sym(Nat, j, i, N.eq_from_is_eq(j, i, ej)),
        UPS.pair_ok_pos(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), i, UPS.pos_of_ne(i, eb),
          d1n_i_mle(~A, ~cmp, d, n, t, i, x, cv, ci, hcn, hcv, epc, hcpos, UPS.pos_of_ne(i, eb), hi, pf, hkids)))


def d1n_c_mle(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +epc: {IX.par(ci) == i : Nat}, +hcpos: {Nat.is_le(1n, ci) == True{} : Bool}, +hc: {Nat.is_lt(ci, SC.pow2(d)) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hnle: {S.le(~A, ~cmp, x, cv) == False{} : Bool}) -> {SL.mle(~A, ~cmp, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), IX.par(ci)), SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), ci)) == True{} : Bool}:
  +hne = SL.ne_sym(ci, i, N.is_eq_lt(i, ci, L.subst(Nat, z => {Nat.is_lt(z, ci) == True{} : Bool}, IX.par(ci), i, epc, IX.par_lt(ci, N.succ_le_lt(0n, ci, hcpos)))))
  %Equal.sym(Nat, IX.par(ci), i, epc) : {SL.mle(~A, ~cmp, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), _), SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), ci)) == True{} : Bool}
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), i), Some{cv}, d2_at_i(~A, d, t, i, x, cv, ci, hne, hi, pf)) : {SL.mle(~A, ~cmp, _, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), ci)) == True{} : Bool}
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), ci), Some{x}, d2_at_c(~A, d, t, i, x, cv, ci, hc, pf)) : {SL.mle(~A, ~cmp, Some{cv}, _) == True{} : Bool}
  O.total(~A, ~cmp, ~o, x, cv, hnle)

def d1n_c(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +j: Nat, +ej: {Nat.is_eq(j, ci) == True{} : Bool}, +epc: {IX.par(ci) == i : Nat}, +hcpos: {Nat.is_le(1n, ci) == True{} : Bool}, +hc: {Nat.is_lt(ci, SC.pow2(d)) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hnle: {S.le(~A, ~cmp, x, cv) == False{} : Bool}) -> {SL.pair_ok(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), j) == True{} : Bool}:
  L.subst(Nat, z => {SL.pair_ok(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), z) == True{} : Bool}, ci, j, Equal.sym(Nat, j, ci, N.eq_from_is_eq(j, ci, ej)),
    UPS.pair_ok_pos(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), ci, hcpos,
      d1n_c_mle(~A, ~cmp, ~o, d, t, i, x, cv, ci, epc, hcpos, hc, hi, pf, hnle)))

def d1n_s_mle(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +s: Nat, +hsn: {Nat.is_lt(s, n) == True{} : Bool}, +hsc: {Nat.is_eq(ci, s) == False{} : Bool}, +eps: {IX.par(s) == i : Nat}, +hspos: {Nat.is_le(1n, s) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hcpos: {Nat.is_le(1n, ci) == True{} : Bool}, +epc: {IX.par(ci) == i : Nat}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hsib: {SL.kid_le(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, ci, s) == True{} : Bool}, +hcv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), ci) == Some{cv} : Maybe<&2, A>}) -> {SL.mle(~A, ~cmp, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), IX.par(s)), SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), s)) == True{} : Bool}:
  +hne = SL.ne_sym(ci, i, N.is_eq_lt(i, ci, L.subst(Nat, z => {Nat.is_lt(z, ci) == True{} : Bool}, IX.par(ci), i, epc, IX.par_lt(ci, N.succ_le_lt(0n, ci, hcpos)))))
  +hsi = N.is_eq_lt(i, s, L.subst(Nat, z => {Nat.is_lt(z, s) == True{} : Bool}, IX.par(s), i, eps, IX.par_lt(s, N.succ_le_lt(0n, s, hspos))))
  %Equal.sym(Nat, IX.par(s), i, eps) : {SL.mle(~A, ~cmp, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), _), SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), s)) == True{} : Bool}
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), i), Some{cv}, d2_at_i(~A, d, t, i, x, cv, ci, hne, hi, pf)) : {SL.mle(~A, ~cmp, _, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), s)) == True{} : Bool}
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), s), SL.slot(~A, AR.slots(Maybe<&2, A>, t), s), d2_off(~A, d, t, i, x, cv, ci, s, hsi, hsc, hi, pf)) : {SL.mle(~A, ~cmp, Some{cv}, _) == True{} : Bool}
  %hcv : {SL.mle(~A, ~cmp, _, SL.slot(~A, AR.slots(Maybe<&2, A>, t), s)) == True{} : Bool}
  SL.kid_le_at(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, ci, s, hsn, hsib)

def d1n_s(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +s: Nat, +j: Nat, +ej: {Nat.is_eq(j, s) == True{} : Bool}, +hjn: {Nat.is_lt(j, n) == True{} : Bool}, +hsc: {Nat.is_eq(ci, s) == False{} : Bool}, +eps: {IX.par(s) == i : Nat}, +hspos: {Nat.is_le(1n, s) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hcpos: {Nat.is_le(1n, ci) == True{} : Bool}, +epc: {IX.par(ci) == i : Nat}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hsib: {SL.kid_le(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, ci, s) == True{} : Bool}, +hcv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), ci) == Some{cv} : Maybe<&2, A>}) -> {SL.pair_ok(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), j) == True{} : Bool}:
  L.subst(Nat, z => {SL.pair_ok(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), z) == True{} : Bool}, s, j, Equal.sym(Nat, j, s, N.eq_from_is_eq(j, s, ej)),
    UPS.pair_ok_pos(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), s, hspos,
      d1n_s_mle(~A, ~cmp, d, n, t, i, x, cv, ci, s, L.subst(Nat, z => {Nat.is_lt(z, n) == True{} : Bool}, j, s, N.eq_from_is_eq(j, s, ej), hjn), hsc, eps, hspos, hi, hcpos, epc, pf, hsib, hcv)))

def eq_of_eq(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_eq(a, z) == True{} : Bool}, a, b, e, N.is_eq_refl(a))

def or_left(a: Bool, b: Bool, +ea: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.or(_, b) == True{} : Bool}
  {==}

def or_right(a: Bool, b: Bool, +eb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      eb

def par_not_absurd(+j: Nat, +u: Nat, +hkf: {SL.kid_of(j, u) == False{} : Bool}, e: {j == IX.kidl(IX.par(j)) : Nat} | {j == IX.kidr(IX.par(j)) : Nat}, +ep: {IX.par(j) == u : Nat}) -> Empty:
  match e:
    case Inl{ej}:
      L.true_not_false(SL.kid_of(j, u), or_left(Nat.is_eq(j, IX.kidl(u)), Nat.is_eq(j, IX.kidr(u)), eq_of_eq(j, IX.kidl(u), L.subst(Nat, z => {j == IX.kidl(z) : Nat}, IX.par(j), u, ep, ej))), hkf)
    case Inr{ej}:
      L.true_not_false(SL.kid_of(j, u), or_right(Nat.is_eq(j, IX.kidl(u)), Nat.is_eq(j, IX.kidr(u)), eq_of_eq(j, IX.kidr(u), L.subst(Nat, z => {j == IX.kidr(z) : Nat}, IX.par(j), u, ep, ej))), hkf)

def par_not_of(+j: Nat, +u: Nat, +hkf: {SL.kid_of(j, u) == False{} : Bool}, e: {j == IX.kidl(IX.par(j)) : Nat} | {j == IX.kidr(IX.par(j)) : Nat}, b: Bool, +eb: {Nat.is_eq(IX.par(j), u) == b : Bool}) -> {Nat.is_eq(IX.par(j), u) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      Empty.absurd({Nat.is_eq(IX.par(j), u) == False{} : Bool}, par_not_absurd(j, u, hkf, e, N.eq_from_is_eq(IX.par(j), u, eb)))

def par_not(+j: Nat, +u: Nat, +hjpos: {Nat.is_le(1n, j) == True{} : Bool}, +hkf: {SL.kid_of(j, u) == False{} : Bool}) -> {Nat.is_eq(IX.par(j), u) == False{} : Bool}:
  par_not_of(j, u, hkf, IX.kid_split(j, N.succ_le_lt(0n, j, hjpos)), Nat.is_eq(IX.par(j), u), {==})

def d1n_far_mle(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +j: Nat, +hji: {Nat.is_eq(j, i) == False{} : Bool}, +hjc: {Nat.is_eq(j, ci) == False{} : Bool}, +hpi: {Nat.is_eq(IX.par(j), i) == False{} : Bool}, +hpc: {Nat.is_eq(IX.par(j), ci) == False{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hm: {SL.mle(~A, ~cmp, SL.slot(~A, UPS.ulog(~A, t, i, x), IX.par(j)), SL.slot(~A, UPS.ulog(~A, t, i, x), j)) == True{} : Bool}) -> {SL.mle(~A, ~cmp, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), IX.par(j)), SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), j)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), IX.par(j)), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(j)), d2_off(~A, d, t, i, x, cv, ci, IX.par(j), SL.ne_sym(i, IX.par(j), hpi), SL.ne_sym(ci, IX.par(j), hpc), hi, pf)) : {SL.mle(~A, ~cmp, _, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), j)) == True{} : Bool}
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), j), SL.slot(~A, AR.slots(Maybe<&2, A>, t), j), d2_off(~A, d, t, i, x, cv, ci, j, SL.ne_sym(i, j, hji), SL.ne_sym(ci, j, hjc), hi, pf)) : {SL.mle(~A, ~cmp, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(j)), _) == True{} : Bool}
  %UPS.ulog_off(~A, t, i, x, IX.par(j), SL.ne_sym(i, IX.par(j), hpi)) : {SL.mle(~A, ~cmp, _, SL.slot(~A, AR.slots(Maybe<&2, A>, t), j)) == True{} : Bool}
  %UPS.ulog_off(~A, t, i, x, j, SL.ne_sym(i, j, hji)) : {SL.mle(~A, ~cmp, SL.slot(~A, UPS.ulog(~A, t, i, x), IX.par(j)), _) == True{} : Bool}
  hm

def d1n_far(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +j: Nat, +hji: {Nat.is_eq(j, i) == False{} : Bool}, +hjc: {Nat.is_eq(j, ci) == False{} : Bool}, +hjn: {Nat.is_lt(j, n) == True{} : Bool}, +hkf: {SL.kid_of(j, i) == False{} : Bool}, +hkf2: {SL.kid_of(j, ci) == False{} : Bool}, +hjpos: {Nat.is_le(1n, j) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hexc: {SL.ho_exc2(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i) == True{} : Bool}) -> {SL.pair_ok(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), j) == True{} : Bool}:
  +hpi = par_not(j, i, hjpos, hkf)
  +hpc = par_not(j, ci, hjpos, hkf2)
  +hm = UPS.pair_ok_val(~A, ~cmp, UPS.ulog(~A, t, i, x), j, hjpos, SL.exc2_at(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i, j, hexc, hjn, hkf))
  UPS.pair_ok_pos(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), j, hjpos,
    d1n_far_mle(~A, ~cmp, d, t, i, x, cv, ci, j, hji, hjc, hpi, hpc, hi, pf, hm))

# ---- the four cases, dispatched on the index ----

def eq_false_of(+j: Nat, +a: Nat, +b: Nat, +e: {a == b : Nat}, +h: {Nat.is_eq(j, b) == False{} : Bool}) -> {Nat.is_eq(j, a) == False{} : Bool}:
  L.subst(Nat, z => {Nat.is_eq(j, z) == False{} : Bool}, b, a, Equal.sym(Nat, a, b, e), h)

def side_false(+j: Nat, +u: Nat, +ci: Nat, +s: Nat, +hjc: {Nat.is_eq(j, ci) == False{} : Bool}, +hjs: {Nat.is_eq(j, s) == False{} : Bool}, e: Either<&2, &2, {u == ci : Nat}, {u == s : Nat}>) -> {Nat.is_eq(j, u) == False{} : Bool}:
  match e:
    case Inl{eu}:
      eq_false_of(j, u, ci, eu, hjc)
    case Inr{eu}:
      eq_false_of(j, u, s, eu, hjs)

def or_false(a: Bool, b: Bool, +ea: {a == False{} : Bool}, +eb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, ea) : {Bool.or(_, b) == False{} : Bool}
  eb

def kid_of_false(+j: Nat, +i: Nat, +ci: Nat, +s: Nat, +hjc: {Nat.is_eq(j, ci) == False{} : Bool}, +hjs: {Nat.is_eq(j, s) == False{} : Bool}, ecl: Either<&2, &2, {IX.kidl(i) == ci : Nat}, {IX.kidl(i) == s : Nat}>, ecr: Either<&2, &2, {IX.kidr(i) == ci : Nat}, {IX.kidr(i) == s : Nat}>) -> {SL.kid_of(j, i) == False{} : Bool}:
  or_false(Nat.is_eq(j, IX.kidl(i)), Nat.is_eq(j, IX.kidr(i)), side_false(j, IX.kidl(i), ci, s, hjc, hjs, ecl), side_false(j, IX.kidr(i), ci, s, hjc, hjs, ecr))

def d1_next_s(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +s: Nat, +j: Nat, +hji: {Nat.is_eq(j, i) == False{} : Bool}, +hjc: {Nat.is_eq(j, ci) == False{} : Bool}, +hjn: {Nat.is_lt(j, n) == True{} : Bool}, +hjpos: {Nat.is_le(1n, j) == True{} : Bool}, +hkf2: {SL.kid_of(j, ci) == False{} : Bool}, +hsc: {Nat.is_eq(ci, s) == False{} : Bool}, +eps: {IX.par(s) == i : Nat}, +hspos: {Nat.is_le(1n, s) == True{} : Bool}, +epc: {IX.par(ci) == i : Nat}, +hcpos: {Nat.is_le(1n, ci) == True{} : Bool}, +ecl: Either<&2, &2, {IX.kidl(i) == ci : Nat}, {IX.kidl(i) == s : Nat}>, +ecr: Either<&2, &2, {IX.kidr(i) == ci : Nat}, {IX.kidr(i) == s : Nat}>, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hexc: {SL.ho_exc2(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i) == True{} : Bool}, +hsib: {SL.kid_le(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, ci, s) == True{} : Bool}, +hcv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), ci) == Some{cv} : Maybe<&2, A>}, b: Bool, +eb: {Nat.is_eq(j, s) == b : Bool}) -> {SL.pair_ok(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), j) == True{} : Bool}:
  match b:
    case True{}:
      d1n_s(~A, ~cmp, d, n, t, i, x, cv, ci, s, j, eb, hjn, hsc, eps, hspos, hi, hcpos, epc, pf, hsib, hcv)
    case False{}:
      d1n_far(~A, ~cmp, d, n, t, i, x, cv, ci, j, hji, hjc, hjn, kid_of_false(j, i, ci, s, hjc, eb, ecl, ecr), hkf2, hjpos, hi, pf, hexc)

def d1_next_c(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +s: Nat, +j: Nat, +hji: {Nat.is_eq(j, i) == False{} : Bool}, +hjn: {Nat.is_lt(j, n) == True{} : Bool}, +hjpos: {Nat.is_le(1n, j) == True{} : Bool}, +hkf2: {SL.kid_of(j, ci) == False{} : Bool}, +hsc: {Nat.is_eq(ci, s) == False{} : Bool}, +eps: {IX.par(s) == i : Nat}, +hspos: {Nat.is_le(1n, s) == True{} : Bool}, +epc: {IX.par(ci) == i : Nat}, +hcpos: {Nat.is_le(1n, ci) == True{} : Bool}, +hc: {Nat.is_lt(ci, SC.pow2(d)) == True{} : Bool}, +ecl: Either<&2, &2, {IX.kidl(i) == ci : Nat}, {IX.kidl(i) == s : Nat}>, +ecr: Either<&2, &2, {IX.kidr(i) == ci : Nat}, {IX.kidr(i) == s : Nat}>, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hexc: {SL.ho_exc2(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i) == True{} : Bool}, +hsib: {SL.kid_le(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, ci, s) == True{} : Bool}, +hcv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), ci) == Some{cv} : Maybe<&2, A>}, +hnle: {S.le(~A, ~cmp, x, cv) == False{} : Bool}, b: Bool, +eb: {Nat.is_eq(j, ci) == b : Bool}) -> {SL.pair_ok(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), j) == True{} : Bool}:
  match b:
    case True{}:
      d1n_c(~A, ~cmp, ~o, d, t, i, x, cv, ci, j, eb, epc, hcpos, hc, hi, pf, hnle)
    case False{}:
      d1_next_s(~A, ~cmp, ~o, d, n, t, i, x, cv, ci, s, j, hji, eb, hjn, hjpos, hkf2, hsc, eps, hspos, epc, hcpos, ecl, ecr, hi, pf, hexc, hsib, hcv, Nat.is_eq(j, s), {==})

def d1_next_pos(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +s: Nat, +j: Nat, +hjn: {Nat.is_lt(j, n) == True{} : Bool}, +hjpos: {Nat.is_le(1n, j) == True{} : Bool}, +hkf2: {SL.kid_of(j, ci) == False{} : Bool}, +hcn: {Nat.is_lt(ci, n) == True{} : Bool}, +hsc: {Nat.is_eq(ci, s) == False{} : Bool}, +eps: {IX.par(s) == i : Nat}, +hspos: {Nat.is_le(1n, s) == True{} : Bool}, +epc: {IX.par(ci) == i : Nat}, +hcpos: {Nat.is_le(1n, ci) == True{} : Bool}, +hc: {Nat.is_lt(ci, SC.pow2(d)) == True{} : Bool}, +ecl: Either<&2, &2, {IX.kidl(i) == ci : Nat}, {IX.kidl(i) == s : Nat}>, +ecr: Either<&2, &2, {IX.kidr(i) == ci : Nat}, {IX.kidr(i) == s : Nat}>, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hexc: {SL.ho_exc2(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i) == True{} : Bool}, +hkids: {SL.kids_le(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, IX.par(i), i) == True{} : Bool}, +hsib: {SL.kid_le(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, ci, s) == True{} : Bool}, +hcv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), ci) == Some{cv} : Maybe<&2, A>}, +hnle: {S.le(~A, ~cmp, x, cv) == False{} : Bool}, b: Bool, +eb: {Nat.is_eq(j, i) == b : Bool}) -> {SL.pair_ok(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), j) == True{} : Bool}:
  match b:
    case True{}:
      d1n_i(~A, ~cmp, d, n, t, i, x, cv, ci, j, eb, hcn, hcv, epc, hcpos, hi, pf, hkids, Nat.is_eq(i, 0n), {==})
    case False{}:
      d1_next_c(~A, ~cmp, ~o, d, n, t, i, x, cv, ci, s, j, eb, hjn, hjpos, hkf2, hsc, eps, hspos, epc, hcpos, hc, ecl, ecr, hi, pf, hexc, hsib, hcv, hnle, Nat.is_eq(j, ci), {==})

def d1_next_at(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +s: Nat, j: Nat, +hjn: {Nat.is_lt(j, n) == True{} : Bool}, +hkf2: {SL.kid_of(j, ci) == False{} : Bool}, +hcn: {Nat.is_lt(ci, n) == True{} : Bool}, +hsc: {Nat.is_eq(ci, s) == False{} : Bool}, +eps: {IX.par(s) == i : Nat}, +hspos: {Nat.is_le(1n, s) == True{} : Bool}, +epc: {IX.par(ci) == i : Nat}, +hcpos: {Nat.is_le(1n, ci) == True{} : Bool}, +hc: {Nat.is_lt(ci, SC.pow2(d)) == True{} : Bool}, +ecl: Either<&2, &2, {IX.kidl(i) == ci : Nat}, {IX.kidl(i) == s : Nat}>, +ecr: Either<&2, &2, {IX.kidr(i) == ci : Nat}, {IX.kidr(i) == s : Nat}>, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hexc: {SL.ho_exc2(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i) == True{} : Bool}, +hkids: {SL.kids_le(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, IX.par(i), i) == True{} : Bool}, +hsib: {SL.kid_le(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, ci, s) == True{} : Bool}, +hcv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), ci) == Some{cv} : Maybe<&2, A>}, +hnle: {S.le(~A, ~cmp, x, cv) == False{} : Bool}) -> {SL.pair_ok(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), j) == True{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+ +m:
      d1_next_pos(~A, ~cmp, ~o, d, n, t, i, x, cv, ci, s, 1n+m, hjn, N.zero_le(m), hkf2, hcn, hsc, eps, hspos, epc, hcpos, hc, ecl, ecr, hi, pf, hexc, hkids, hsib, hcv, hnle, Nat.is_eq(1n+m, i), {==})


def par_of_kid_go(+k: Nat, +i: Nat, +eb: {SL.kid_of(k, i) == True{} : Bool}, b: Bool, +ebl: {Nat.is_eq(k, IX.kidl(i)) == b : Bool}, c: Bool, +ebr: {Nat.is_eq(k, IX.kidr(i)) == c : Bool}) -> {IX.par(k) == i : Nat}:
  match b c:
    case True{} _:
      L.subst(Nat, z => {IX.par(z) == i : Nat}, IX.kidl(i), k, Equal.sym(Nat, k, IX.kidl(i), N.eq_from_is_eq(k, IX.kidl(i), ebl)), IX.par_kidl(i))
    case False{} True{}:
      L.subst(Nat, z => {IX.par(z) == i : Nat}, IX.kidr(i), k, Equal.sym(Nat, k, IX.kidr(i), N.eq_from_is_eq(k, IX.kidr(i), ebr)), IX.par_kidr(i))
    case False{} False{}:
      Empty.absurd({IX.par(k) == i : Nat}, L.true_not_false(SL.kid_of(k, i), eb, or_false(Nat.is_eq(k, IX.kidl(i)), Nat.is_eq(k, IX.kidr(i)), ebl, ebr)))

def par_of_kid(+k: Nat, +i: Nat, +eb: {SL.kid_of(k, i) == True{} : Bool}, e: {k == IX.kidl(IX.par(k)) : Nat} | {k == IX.kidr(IX.par(k)) : Nat}) -> {IX.par(k) == i : Nat}:
  par_of_kid_go(k, i, eb, Nat.is_eq(k, IX.kidl(i)), {==}, Nat.is_eq(k, IX.kidr(i)), {==})

def kid_of_grand_go(+k: Nat, +i: Nat, +ci: Nat, +epk: {IX.par(k) == ci : Nat}, +hne: {Nat.is_eq(ci, i) == False{} : Bool}, b: Bool, +eb: {SL.kid_of(k, i) == b : Bool}, +hkpos: {Nat.is_le(1n, k) == True{} : Bool}) -> {SL.kid_of(k, i) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      Empty.absurd({SL.kid_of(k, i) == False{} : Bool},
        L.true_not_false(Nat.is_eq(ci, i), eq_of_eq(ci, i, Equal.trans(Nat, ci, IX.par(k), i, Equal.sym(Nat, IX.par(k), ci, epk), par_of_kid(k, i, eb, IX.kid_split(k, N.succ_le_lt(0n, k, hkpos))))), hne))

def kid_of_grand(+k: Nat, +i: Nat, +ci: Nat, +epk: {IX.par(k) == ci : Nat}, +hkpos: {Nat.is_le(1n, k) == True{} : Bool}, +hne: {Nat.is_eq(ci, i) == False{} : Bool}) -> {SL.kid_of(k, i) == False{} : Bool}:
  kid_of_grand_go(k, i, ci, epk, hne, SL.kid_of(k, i), {==}, hkpos)

def k_gt_i(+k: Nat, +i: Nat, +ci: Nat, +epk: {IX.par(k) == ci : Nat}, +hkpos: {Nat.is_le(1n, k) == True{} : Bool}, +epc: {IX.par(ci) == i : Nat}, +hcpos: {Nat.is_le(1n, ci) == True{} : Bool}) -> {Nat.is_lt(i, k) == True{} : Bool}:
  N.lt_trans(i, ci, k,
    L.subst(Nat, z => {Nat.is_lt(z, ci) == True{} : Bool}, IX.par(ci), i, epc, IX.par_lt(ci, N.succ_le_lt(0n, ci, hcpos))),
    L.subst(Nat, z => {Nat.is_lt(z, k) == True{} : Bool}, IX.par(k), ci, epk, IX.par_lt(k, N.succ_le_lt(0n, k, hkpos))))

def t2_at_i(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +cv: A, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), i) == Some{cv} : Maybe<&2, A>}:
  Equal.trans(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), i), SL.slot(~A, UPS.ulog(~A, t, i, cv), i), Some{cv},
    Equal.cong(List<&2, Maybe<&2, A>>, Maybe<&2, A>, ss => SL.slot(~A, ss, i), AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), UPS.ulog(~A, t, i, cv), UPS.set_slots(~A, d, t, i, cv, hi, pf)),
    UPS.ulog_at(~A, d, t, i, cv, hi, pf))

def t2_off(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +cv: A, +j: Nat, +hij: {Nat.is_eq(i, j) == False{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), j) == SL.slot(~A, AR.slots(Maybe<&2, A>, t), j) : Maybe<&2, A>}:
  Equal.trans(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), j), SL.slot(~A, UPS.ulog(~A, t, i, cv), j), SL.slot(~A, AR.slots(Maybe<&2, A>, t), j),
    Equal.cong(List<&2, Maybe<&2, A>>, Maybe<&2, A>, ss => SL.slot(~A, ss, j), AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), UPS.ulog(~A, t, i, cv), UPS.set_slots(~A, d, t, i, cv, hi, pf)),
    UPS.ulog_off(~A, t, i, cv, j, hij))

def kid_next_mle(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +k: Nat, +epk: {IX.par(k) == ci : Nat}, +hkpos: {Nat.is_le(1n, k) == True{} : Bool}, +epc: {IX.par(ci) == i : Nat}, +hcpos: {Nat.is_le(1n, ci) == True{} : Bool}, +hcne: {Nat.is_eq(ci, i) == False{} : Bool}, +hkn: {Nat.is_lt(k, n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hexc: {SL.ho_exc2(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i) == True{} : Bool}, +hcv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), ci) == Some{cv} : Maybe<&2, A>}) -> {SL.mle(~A, ~cmp, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), i), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), k)) == True{} : Bool}:
  +hki = N.is_eq_lt(i, k, k_gt_i(k, i, ci, epk, hkpos, epc, hcpos))
  +hm = UPS.pair_ok_val(~A, ~cmp, UPS.ulog(~A, t, i, x), k, hkpos, SL.exc2_at(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i, k, hexc, hkn, kid_of_grand(k, i, ci, epk, hkpos, hcne)))
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), i), Some{cv}, t2_at_i(~A, d, t, i, cv, hi, pf)) : {SL.mle(~A, ~cmp, _, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), k)) == True{} : Bool}
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), k), SL.slot(~A, AR.slots(Maybe<&2, A>, t), k), t2_off(~A, d, t, i, cv, k, hki, hi, pf)) : {SL.mle(~A, ~cmp, Some{cv}, _) == True{} : Bool}
  %hcv : {SL.mle(~A, ~cmp, _, SL.slot(~A, AR.slots(Maybe<&2, A>, t), k)) == True{} : Bool}
  %UPS.ulog_off(~A, t, i, x, k, hki) : {SL.mle(~A, ~cmp, SL.slot(~A, AR.slots(Maybe<&2, A>, t), ci), _) == True{} : Bool}
  %epk : {SL.mle(~A, ~cmp, SL.slot(~A, AR.slots(Maybe<&2, A>, t), _), SL.slot(~A, UPS.ulog(~A, t, i, x), k)) == True{} : Bool}
  %UPS.ulog_off(~A, t, i, x, IX.par(k), SL.ne_sym(i, IX.par(k), par_not(k, i, hkpos, kid_of_grand(k, i, ci, epk, hkpos, hcne)))) : {SL.mle(~A, ~cmp, _, SL.slot(~A, UPS.ulog(~A, t, i, x), k)) == True{} : Bool}
  hm

def kid_next_one(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +k: Nat, +epk: {IX.par(k) == ci : Nat}, +hkpos: {Nat.is_le(1n, k) == True{} : Bool}, +epc: {IX.par(ci) == i : Nat}, +hcpos: {Nat.is_le(1n, ci) == True{} : Bool}, +hcne: {Nat.is_eq(ci, i) == False{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hexc: {SL.ho_exc2(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i) == True{} : Bool}, +hcv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), ci) == Some{cv} : Maybe<&2, A>}, b: Bool, +eb: {Nat.is_lt(k, n) == b : Bool}) -> {SL.kid_le(~A, ~cmp, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), n, i, k) == True{} : Bool}:
  match b:
    case False{}:
      SL.kid_le_out(~A, ~cmp, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), n, i, k, eb)
    case True{}:
      SL.kid_le_in(~A, ~cmp, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), n, i, k, eb,
        kid_next_mle(~A, ~cmp, d, n, t, i, x, cv, ci, k, epk, hkpos, epc, hcpos, hcne, eb, hi, pf, hexc, hcv))

def kids_next_d(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +epc: {IX.par(ci) == i : Nat}, +hcpos: {Nat.is_le(1n, ci) == True{} : Bool}, +hcne: {Nat.is_eq(ci, i) == False{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hexc: {SL.ho_exc2(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i) == True{} : Bool}, +hcv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), ci) == Some{cv} : Maybe<&2, A>}) -> {SL.kids_le(~A, ~cmp, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), n, IX.par(ci), ci) == True{} : Bool}:
  %Equal.sym(Nat, IX.par(ci), i, epc) : {SL.kids_le(~A, ~cmp, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), n, _, ci) == True{} : Bool}
  L.and_intro(SL.kid_le(~A, ~cmp, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), n, i, IX.kidl(ci)), SL.kid_le(~A, ~cmp, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), n, i, IX.kidr(ci)),
    kid_next_one(~A, ~cmp, d, n, t, i, x, cv, ci, IX.kidl(ci), IX.par_kidl(ci), IX.kidl_pos1(ci), epc, hcpos, hcne, hi, pf, hexc, hcv, Nat.is_lt(IX.kidl(ci), n), {==}),
    kid_next_one(~A, ~cmp, d, n, t, i, x, cv, ci, IX.kidr(ci), IX.par_kidr(ci), IX.kidr_pos1(ci), epc, hcpos, hcne, hi, pf, hexc, hcv, Nat.is_lt(IX.kidr(ci), n), {==}))

# D1 for the next state, built index by index
def skip2_next(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +s: Nat, +m: Nat, +hmn: {Nat.is_lt(m, n) == True{} : Bool}, +hcn: {Nat.is_lt(ci, n) == True{} : Bool}, +hsc: {Nat.is_eq(ci, s) == False{} : Bool}, +eps: {IX.par(s) == i : Nat}, +hspos: {Nat.is_le(1n, s) == True{} : Bool}, +epc: {IX.par(ci) == i : Nat}, +hcpos: {Nat.is_le(1n, ci) == True{} : Bool}, +hc: {Nat.is_lt(ci, SC.pow2(d)) == True{} : Bool}, +ecl: Either<&2, &2, {IX.kidl(i) == ci : Nat}, {IX.kidl(i) == s : Nat}>, +ecr: Either<&2, &2, {IX.kidr(i) == ci : Nat}, {IX.kidr(i) == s : Nat}>, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hexc: {SL.ho_exc2(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i) == True{} : Bool}, +hkids: {SL.kids_le(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, IX.par(i), i) == True{} : Bool}, +hsib: {SL.kid_le(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, ci, s) == True{} : Bool}, +hcv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), ci) == Some{cv} : Maybe<&2, A>}, +hnle: {S.le(~A, ~cmp, x, cv) == False{} : Bool}, b: Bool, +eb: {SL.kid_of(m, ci) == b : Bool}) -> {SL.pair_skip2(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), m, ci) == True{} : Bool}:
  match b:
    case True{}:
      SL.skip2_eq(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), m, ci, eb)
    case False{}:
      SL.skip2_ne(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), m, ci, eb,
        d1_next_at(~A, ~cmp, ~o, d, n, t, i, x, cv, ci, s, m, hmn, eb, hcn, hsc, eps, hspos, epc, hcpos, hc, ecl, ecr, hi, pf, hexc, hkids, hsib, hcv, hnle))

def exc2_next(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +s: Nat, k: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}, +hcn: {Nat.is_lt(ci, n) == True{} : Bool}, +hsc: {Nat.is_eq(ci, s) == False{} : Bool}, +eps: {IX.par(s) == i : Nat}, +hspos: {Nat.is_le(1n, s) == True{} : Bool}, +epc: {IX.par(ci) == i : Nat}, +hcpos: {Nat.is_le(1n, ci) == True{} : Bool}, +hc: {Nat.is_lt(ci, SC.pow2(d)) == True{} : Bool}, +ecl: Either<&2, &2, {IX.kidl(i) == ci : Nat}, {IX.kidl(i) == s : Nat}>, +ecr: Either<&2, &2, {IX.kidr(i) == ci : Nat}, {IX.kidr(i) == s : Nat}>, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hexc: {SL.ho_exc2(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i) == True{} : Bool}, +hkids: {SL.kids_le(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, IX.par(i), i) == True{} : Bool}, +hsib: {SL.kid_le(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, ci, s) == True{} : Bool}, +hcv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), ci) == Some{cv} : Maybe<&2, A>}, +hnle: {S.le(~A, ~cmp, x, cv) == False{} : Bool}) -> {SL.ho_exc2(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), k, ci) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +m:
      L.and_intro(SL.pair_skip2(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), m, ci), SL.ho_exc2(~A, ~cmp, d2_of(~A, d, t, i, x, cv, ci), m, ci),
        skip2_next(~A, ~cmp, ~o, d, n, t, i, x, cv, ci, s, m, N.lt_le_trans(m, 1n+m, n, N.lt_succ(m), hk), hcn, hsc, eps, hspos, epc, hcpos, hc, ecl, ecr, hi, pf, hexc, hkids, hsib, hcv, hnle, SL.kid_of(m, ci), {==}),
        exc2_next(~A, ~cmp, ~o, d, n, t, i, x, cv, ci, s, m, N.le_trans(m, 1n+m, n, N.le_succ(m), hk), hcn, hsc, eps, hspos, epc, hcpos, hc, ecl, ecr, hi, pf, hexc, hkids, hsib, hcv, hnle))

# the layout and the multiset of the next state
def some_next_d(~A: Data, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +m: Nat, +hmn: {Nat.is_lt(m, n) == True{} : Bool}, +hcne: {Nat.is_eq(ci, i) == False{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hc: {Nat.is_lt(ci, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hlay: {SL.lay(~A, UPS.ulog(~A, t, i, x), n) == True{} : Bool}, b: Bool, +eb: {Nat.is_eq(m, ci) == b : Bool}, c: Bool, +ec: {Nat.is_eq(m, i) == c : Bool}) -> {Maybe.is_some(&2, A, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), m)) == True{} : Bool}:
  match b c:
    case True{} _:
      L.subst(Nat, z => {Maybe.is_some(&2, A, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), z)) == True{} : Bool}, ci, m, Equal.sym(Nat, m, ci, N.eq_from_is_eq(m, ci, eb)),
        UPS.some_of_eq(~A, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), ci), x, d2_at_c(~A, d, t, i, x, cv, ci, hc, pf)))
    case False{} True{}:
      L.subst(Nat, z => {Maybe.is_some(&2, A, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), z)) == True{} : Bool}, i, m, Equal.sym(Nat, m, i, N.eq_from_is_eq(m, i, ec)),
        UPS.some_of_eq(~A, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), i), cv, d2_at_i(~A, d, t, i, x, cv, ci, hcne, hi, pf)))
    case False{} False{}:
      L.subst(Maybe<&2, A>, w => {Maybe.is_some(&2, A, w) == True{} : Bool}, SL.slot(~A, UPS.ulog(~A, t, i, x), m), SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), m),
        Equal.trans(Maybe<&2, A>, SL.slot(~A, UPS.ulog(~A, t, i, x), m), SL.slot(~A, AR.slots(Maybe<&2, A>, t), m), SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), m),
          UPS.ulog_off(~A, t, i, x, m, SL.ne_sym(i, m, ec)),
          Equal.sym(Maybe<&2, A>, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), m), SL.slot(~A, AR.slots(Maybe<&2, A>, t), m), d2_off(~A, d, t, i, x, cv, ci, m, SL.ne_sym(i, m, ec), SL.ne_sym(ci, m, eb), hi, pf))),
        SL.lay_at(~A, UPS.ulog(~A, t, i, x), n, m, hlay, hmn))

def lay_next_d(~A: Data, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, k: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}, +hcne: {Nat.is_eq(ci, i) == False{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hc: {Nat.is_lt(ci, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hlay: {SL.lay(~A, UPS.ulog(~A, t, i, x), n) == True{} : Bool}) -> {SL.lay(~A, d2_of(~A, d, t, i, x, cv, ci), k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +m:
      L.and_intro(Maybe.is_some(&2, A, SL.slot(~A, d2_of(~A, d, t, i, x, cv, ci), m)), SL.lay(~A, d2_of(~A, d, t, i, x, cv, ci), m),
        some_next_d(~A, d, n, t, i, x, cv, ci, m, N.lt_le_trans(m, 1n+m, n, N.lt_succ(m), hk), hcne, hi, hc, pf, hlay, Nat.is_eq(m, ci), {==}, Nat.is_eq(m, i), {==}),
        lay_next_d(~A, d, n, t, i, x, cv, ci, m, N.le_trans(m, 1n+m, n, N.le_succ(m), hk), hcne, hi, hc, pf, hlay))

def d2_swap_form(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {d2_of(~A, d, t, i, x, cv, ci) == SC.update(Maybe<&2, A>, SC.update(Maybe<&2, A>, UPS.ulog(~A, t, i, x), i, Some{cv}), ci, Some{x}) : List<&2, Maybe<&2, A>>}:
  Equal.cong(List<&2, Maybe<&2, A>>, List<&2, Maybe<&2, A>>, ss => SC.update(Maybe<&2, A>, ss, ci, Some{x}), AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), SC.update(Maybe<&2, A>, UPS.ulog(~A, t, i, x), i, Some{cv}),
    Equal.trans(List<&2, Maybe<&2, A>>, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), UPS.ulog(~A, t, i, cv), SC.update(Maybe<&2, A>, UPS.ulog(~A, t, i, x), i, Some{cv}),
      UPS.set_slots(~A, d, t, i, cv, hi, pf),
      Equal.sym(List<&2, Maybe<&2, A>>, SC.update(Maybe<&2, A>, UPS.ulog(~A, t, i, x), i, Some{cv}), UPS.ulog(~A, t, i, cv), BG.upd_upd_same(~A, AR.slots(Maybe<&2, A>, t), i, Some{x}, Some{cv}))))

def ms_next_d(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +tgt: List<&2, A>, +hin: {Nat.is_lt(i, n) == True{} : Bool}, +hcn: {Nat.is_lt(ci, n) == True{} : Bool}, +hcne: {Nat.is_eq(ci, i) == False{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hcv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), ci) == Some{cv} : Maybe<&2, A>}, +hms: {V.msort(~A, ~cmp, V.vals(~A, UPS.ulog(~A, t, i, x), n)) == tgt : List<&2, A>}) -> {V.msort(~A, ~cmp, V.vals(~A, d2_of(~A, d, t, i, x, cv, ci), n)) == tgt : List<&2, A>}:
  %Equal.sym(List<&2, Maybe<&2, A>>, d2_of(~A, d, t, i, x, cv, ci), SC.update(Maybe<&2, A>, SC.update(Maybe<&2, A>, UPS.ulog(~A, t, i, x), i, Some{cv}), ci, Some{x}), d2_swap_form(~A, d, t, i, x, cv, ci, hi, pf)) : {V.msort(~A, ~cmp, V.vals(~A, _, n)) == tgt : List<&2, A>}
  Equal.trans(List<&2, A>, V.msort(~A, ~cmp, V.vals(~A, SC.update(Maybe<&2, A>, SC.update(Maybe<&2, A>, UPS.ulog(~A, t, i, x), i, Some{cv}), ci, Some{x}), n)), V.msort(~A, ~cmp, V.vals(~A, UPS.ulog(~A, t, i, x), n)), tgt,
    BG.vals_swap(~A, ~cmp, ~o, UPS.ulog(~A, t, i, x), n, i, ci, x, cv, hin, hcn, SL.ne_sym(i, ci, hcne),
      UPS.ulog_at(~A, d, t, i, x, hi, pf),
      Equal.trans(Maybe<&2, A>, SL.slot(~A, UPS.ulog(~A, t, i, x), ci), SL.slot(~A, AR.slots(Maybe<&2, A>, t), ci), Some{cv}, UPS.ulog_off(~A, t, i, x, ci, SL.ne_sym(i, ci, hcne)), hcv)),
    hms)

# ---- what the loop delivers ----

def DownOK(~A: Data, ~cmp: A -> A -> Cmp, d: Nat, n: Nat, tgt: List<&2, A>, fuel: Nat, x: A, s: DownS<A>) -> Type:
  Sigma<&1, &1, AR.Tree<Maybe<&2, A>>, t2 => {H.down_go(~A, ~cmp, fuel, U32.from_nat(n), x, dreal(~A, s)) == AR.thaw(Maybe<&2, A>, t2) : Array<Maybe<&2, A>>} & ({AR.perfect(Maybe<&2, A>, d, t2) == True{} : Bool} & ({SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t2), n) == True{} : Bool} & ({SL.lay(~A, AR.slots(Maybe<&2, A>, t2), n) == True{} : Bool} & {V.msort(~A, ~cmp, V.vals(~A, AR.slots(Maybe<&2, A>, t2), n)) == tgt : List<&2, A>})))>

# the loop stops: x is written at the hole and the two pairs below it hold
def down_stop_mk(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +tgt: List<&2, A>, +fuel: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +eq: {H.down_go(~A, ~cmp, fuel, U32.from_nat(n), x, dreal(~A, DStp{t, i})) == AR.thaw(Maybe<&2, A>, UPS.set_tree(~A, d, t, i, x)) : Array<Maybe<&2, A>>}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hn: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hexc: {SL.ho_exc2(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i) == True{} : Bool}, +hkids: {SL.kids_le(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i, i) == True{} : Bool}, +hlay: {SL.lay(~A, UPS.ulog(~A, t, i, x), n) == True{} : Bool}, +hms: {V.msort(~A, ~cmp, V.vals(~A, UPS.ulog(~A, t, i, x), n)) == tgt : List<&2, A>}) -> DownOK(~A, ~cmp, d, n, tgt, fuel, x, DStp{t, i}):
  +es = UPS.set_slots(~A, d, t, i, x, hi, pf)
  (UPS.set_tree(~A, d, t, i, x),
   (eq,
    (AR.upd_perfect(Maybe<&2, A>, d, t, i, Some{x}, pf),
     (L.subst(List<&2, Maybe<&2, A>>, ss => {SL.ho_upto(~A, ~cmp, ss, n) == True{} : Bool}, UPS.ulog(~A, t, i, x), AR.slots(Maybe<&2, A>, UPS.set_tree(~A, d, t, i, x)), Equal.sym(List<&2, Maybe<&2, A>>, AR.slots(Maybe<&2, A>, UPS.set_tree(~A, d, t, i, x)), UPS.ulog(~A, t, i, x), es),
        SL.ho_of_exc2(~A, ~cmp, UPS.ulog(~A, t, i, x), n, n, i, N.le_refl(n), hexc, hkids)),
      (L.subst(List<&2, Maybe<&2, A>>, ss => {SL.lay(~A, ss, n) == True{} : Bool}, UPS.ulog(~A, t, i, x), AR.slots(Maybe<&2, A>, UPS.set_tree(~A, d, t, i, x)), Equal.sym(List<&2, Maybe<&2, A>>, AR.slots(Maybe<&2, A>, UPS.set_tree(~A, d, t, i, x)), UPS.ulog(~A, t, i, x), es), hlay),
       L.subst(List<&2, Maybe<&2, A>>, ss => {V.msort(~A, ~cmp, V.vals(~A, ss, n)) == tgt : List<&2, A>}, UPS.ulog(~A, t, i, x), AR.slots(Maybe<&2, A>, UPS.set_tree(~A, d, t, i, x)), Equal.sym(List<&2, Maybe<&2, A>>, AR.slots(Maybe<&2, A>, UPS.set_tree(~A, d, t, i, x)), UPS.ulog(~A, t, i, x), es), hms))))))

def down_stop_ok(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +tgt: List<&2, A>, fuel: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hn: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hexc: {SL.ho_exc2(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i) == True{} : Bool}, +hkids: {SL.kids_le(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i, i) == True{} : Bool}, +hlay: {SL.lay(~A, UPS.ulog(~A, t, i, x), n) == True{} : Bool}, +hms: {V.msort(~A, ~cmp, V.vals(~A, UPS.ulog(~A, t, i, x), n)) == tgt : List<&2, A>}) -> DownOK(~A, ~cmp, d, n, tgt, fuel, x, DStp{t, i}):
  match fuel:
    case 0n:
      down_stop_mk(~A, ~cmp, d, n, tgt, 0n, t, i, x, UPS.set_eq(~A, d, t, i, x, hd, hi, pf), hi, hn, pf, hexc, hkids, hlay, hms)
    case 1n+f:
      down_stop_mk(~A, ~cmp, d, n, tgt, 1n+f, t, i, x, UPS.set_eq(~A, d, t, i, x, hd, hi, pf), hi, hn, pf, hexc, hkids, hlay, hms)

# ---- the facts each shape of the probe gives ----

# a slot inside the heap is occupied, so a probe that reads None there is
# impossible
def slot_some_at(~A: Data, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +n: Nat, +j: Nat, +hjn: {Nat.is_lt(j, n) == True{} : Bool}, +hji: {Nat.is_eq(i, j) == False{} : Bool}, +hlay: {SL.lay(~A, UPS.ulog(~A, t, i, x), n) == True{} : Bool}, +em: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), j) == None{} : Maybe<&2, A>}) -> Empty:
  L.true_not_false(Maybe.is_some(&2, A, SL.slot(~A, UPS.ulog(~A, t, i, x), j)), SL.lay_at(~A, UPS.ulog(~A, t, i, x), n, j, hlay, hjn),
    L.subst(Maybe<&2, A>, w => {Maybe.is_some(&2, A, w) == False{} : Bool}, None{}, SL.slot(~A, UPS.ulog(~A, t, i, x), j),
      Equal.sym(Maybe<&2, A>, SL.slot(~A, UPS.ulog(~A, t, i, x), j), None{}, Equal.trans(Maybe<&2, A>, SL.slot(~A, UPS.ulog(~A, t, i, x), j), SL.slot(~A, AR.slots(Maybe<&2, A>, t), j), None{}, UPS.ulog_off(~A, t, i, x, j, hji), em)), {==}))

# kidl i >= n implies kidr i >= n
def kidr_out(+i: Nat, +n: Nat, +e: {Nat.is_lt(IX.kidl(i), n) == False{} : Bool}) -> {Nat.is_lt(IX.kidr(i), n) == False{} : Bool}:
  N.le_not_lt(IX.kidr(i), n, N.le_trans(n, IX.kidl(i), IX.kidr(i), N.not_lt_le(IX.kidl(i), n, e), N.le_succ(IX.kidl(i))))

# the right child is out of range exactly when the `two` test fails
def kidr_out2(+i: Nat, +n: Nat, +e: {Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)) == False{} : Bool}) -> {Nat.is_lt(IX.kidr(i), n) == False{} : Bool}:
  L.subst(Bool, b => {b == False{} : Bool}, Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), Nat.is_lt(IX.kidr(i), n), Equal.sym(Bool, Nat.is_lt(IX.kidr(i), n), Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), IX.succ_lt_sub(IX.kidl(i), n)), e)

def kidr_in2(+i: Nat, +n: Nat, +e: {Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)) == True{} : Bool}) -> {Nat.is_lt(IX.kidr(i), n) == True{} : Bool}:
  L.subst(Bool, b => {b == True{} : Bool}, Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), Nat.is_lt(IX.kidr(i), n), Equal.sym(Bool, Nat.is_lt(IX.kidr(i), n), Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), IX.succ_lt_sub(IX.kidl(i), n)), e)

def kidl_ne_kidr(+i: Nat) -> {Nat.is_eq(IX.kidl(i), IX.kidr(i)) == False{} : Bool}:
  N.is_eq_lt(IX.kidl(i), IX.kidr(i), N.lt_succ(IX.kidl(i)))

def kid_le_x_mle(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +c: Nat, +cv: A, +hci: {Nat.is_eq(i, c) == False{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hcv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), c) == Some{cv} : Maybe<&2, A>}, +hle: {S.le(~A, ~cmp, x, cv) == True{} : Bool}) -> {SL.mle(~A, ~cmp, SL.slot(~A, UPS.ulog(~A, t, i, x), i), SL.slot(~A, UPS.ulog(~A, t, i, x), c)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, UPS.ulog(~A, t, i, x), i), Some{x}, UPS.ulog_at(~A, d, t, i, x, hi, pf)) : {SL.mle(~A, ~cmp, _, SL.slot(~A, UPS.ulog(~A, t, i, x), c)) == True{} : Bool}
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, UPS.ulog(~A, t, i, x), c), SL.slot(~A, AR.slots(Maybe<&2, A>, t), c), UPS.ulog_off(~A, t, i, x, c, hci)) : {SL.mle(~A, ~cmp, Some{x}, _) == True{} : Bool}
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), c), Some{cv}, hcv) : {SL.mle(~A, ~cmp, Some{x}, _) == True{} : Bool}
  hle

# "x is not larger than that child", as the kid_le conjunct
def kid_le_x(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +n: Nat, +c: Nat, +cv: A, +hcn: {Nat.is_lt(c, n) == True{} : Bool}, +hci: {Nat.is_eq(i, c) == False{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hcv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), c) == Some{cv} : Maybe<&2, A>}, +hle: {S.le(~A, ~cmp, x, cv) == True{} : Bool}) -> {SL.kid_le(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i, c) == True{} : Bool}:
  SL.kid_le_in(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i, c, hcn, kid_le_x_mle(~A, ~cmp, d, t, i, x, c, cv, hci, hi, pf, hcv, hle))

# ---- the loop ----

# the value the probe compares x with, as a function of its three reads
def pick_cv2(~A: Data, +x: A, +lv: A, two: Bool, mr: Maybe<&2, A>, left: Bool) -> A:
  match two mr left:
    case False{} _ _:
      lv
    case True{} None{} _:
      lv
    case True{} Some{rv} True{}:
      lv
    case True{} Some{rv} False{}:
      rv

def pick_cv(~A: Data, +x: A, ml: Maybe<&2, A>, two: Bool, mr: Maybe<&2, A>, left: Bool) -> A:
  match ml:
    case None{}:
      x
    case Some{+lv}:
      pick_cv2(~A, x, lv, two, mr, left)

def down_carry_go(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +tgt: List<&2, A>, +f: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +t3: AR.Tree<Maybe<&2, A>>, +eq: {H.down_go(~A, ~cmp, 1n+f, U32.from_nat(n), x, dreal(~A, DMv{t, i, cv, ci})) == H.down_go(~A, ~cmp, f, U32.from_nat(n), x, dreal(~A, dprobe(~A, ~cmp, n, ci, x, t2_of(~A, d, t, i, cv)))) : Array<Maybe<&2, A>>}, rest: {H.down_go(~A, ~cmp, f, U32.from_nat(n), x, dreal(~A, dprobe(~A, ~cmp, n, ci, x, t2_of(~A, d, t, i, cv)))) == AR.thaw(Maybe<&2, A>, t3) : Array<Maybe<&2, A>>} & ({AR.perfect(Maybe<&2, A>, d, t3) == True{} : Bool} & ({SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t3), n) == True{} : Bool} & ({SL.lay(~A, AR.slots(Maybe<&2, A>, t3), n) == True{} : Bool} & {V.msort(~A, ~cmp, V.vals(~A, AR.slots(Maybe<&2, A>, t3), n)) == tgt : List<&2, A>}))) ) -> DownOK(~A, ~cmp, d, n, tgt, 1n+f, x, DMv{t, i, cv, ci}):
  (e1, more) = rest
  (t3, (Equal.trans(Array<Maybe<&2, A>>, H.down_go(~A, ~cmp, 1n+f, U32.from_nat(n), x, dreal(~A, DMv{t, i, cv, ci})), H.down_go(~A, ~cmp, f, U32.from_nat(n), x, dreal(~A, dprobe(~A, ~cmp, n, ci, x, t2_of(~A, d, t, i, cv)))), AR.thaw(Maybe<&2, A>, t3), eq, e1), more))

def down_carry(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +tgt: List<&2, A>, +f: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +eq: {H.down_go(~A, ~cmp, 1n+f, U32.from_nat(n), x, dreal(~A, DMv{t, i, cv, ci})) == H.down_go(~A, ~cmp, f, U32.from_nat(n), x, dreal(~A, dprobe(~A, ~cmp, n, ci, x, t2_of(~A, d, t, i, cv)))) : Array<Maybe<&2, A>>}, rec: DownOK(~A, ~cmp, d, n, tgt, f, x, dprobe(~A, ~cmp, n, ci, x, t2_of(~A, d, t, i, cv)))) -> DownOK(~A, ~cmp, d, n, tgt, 1n+f, x, DMv{t, i, cv, ci}):
  (t3, rest) = rec
  down_carry_go(~A, ~cmp, d, n, tgt, f, t, i, x, cv, ci, t3, eq, rest)

def down_step_eq(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +f: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +cv: A, +ci: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hc: {Nat.is_lt(ci, SC.pow2(d)) == True{} : Bool}, +hn: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {H.down_go(~A, ~cmp, 1n+f, U32.from_nat(n), x, dreal(~A, DMv{t, i, cv, ci})) == H.down_go(~A, ~cmp, f, U32.from_nat(n), x, dreal(~A, dprobe(~A, ~cmp, n, ci, x, t2_of(~A, d, t, i, cv)))) : Array<Maybe<&2, A>>}:
  %Equal.sym(Array<Maybe<&2, A>>, Array.set(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), U32.from_nat(i), Some{cv}), AR.thaw(Maybe<&2, A>, t2_of(~A, d, t, i, cv)), UPS.set_eq(~A, d, t, i, cv, hd, hi, pf)) : {H.down_go(~A, ~cmp, f, U32.from_nat(n), x, H.down_probe(~A, ~cmp, U32.from_nat(n), U32.from_nat(ci), x, _)) == H.down_go(~A, ~cmp, f, U32.from_nat(n), x, dreal(~A, dprobe(~A, ~cmp, n, ci, x, t2_of(~A, d, t, i, cv)))) : Array<Maybe<&2, A>>}
  Equal.cong(H.Down<A>, Array<Maybe<&2, A>>, s => H.down_go(~A, ~cmp, f, U32.from_nat(n), x, s), H.down_probe(~A, ~cmp, U32.from_nat(n), U32.from_nat(ci), x, AR.thaw(Maybe<&2, A>, t2_of(~A, d, t, i, cv))), dreal(~A, dprobe(~A, ~cmp, n, ci, x, t2_of(~A, d, t, i, cv))),
    dprobe_ok(~A, ~cmp, d, n, t2_of(~A, d, t, i, cv), ci, x, hd, hc, hn, UPS.t2_perfect(~A, d, t, i, cv, pf)))

# the probe's result as a function of its three reads and two comparisons
def pick_state2(~A: Data, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +lv: A, two: Bool, mr: Maybe<&2, A>, left: Bool, ok: Bool) -> DownS<A>:
  match two mr left ok:
    case False{} _ _ True{}:
      DStp{t, i}
    case False{} _ _ False{}:
      DMv{t, i, lv, IX.kidl(i)}
    case True{} None{} _ True{}:
      DStp{t, i}
    case True{} None{} _ False{}:
      DMv{t, i, lv, IX.kidl(i)}
    case True{} Some{rv} True{} True{}:
      DStp{t, i}
    case True{} Some{rv} True{} False{}:
      DMv{t, i, lv, IX.kidl(i)}
    case True{} Some{rv} False{} True{}:
      DStp{t, i}
    case True{} Some{+rv} False{} False{}:
      DMv{t, i, rv, IX.kidr(i)}

def pick_state(~A: Data, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, hasl: Bool, ml: Maybe<&2, A>, two: Bool, mr: Maybe<&2, A>, left: Bool, ok: Bool) -> DownS<A>:
  match hasl ml:
    case False{} _:
      DStp{t, i}
    case True{} None{}:
      DStp{t, i}
    case True{} Some{+lv}:
      pick_state2(~A, t, i, lv, two, mr, left, ok)

def probe_shape(~A: Data, ~cmp: A -> A -> Cmp, +n: Nat, +i: Nat, +x: A, +t: AR.Tree<Maybe<&2, A>>, hasl: Bool, +ehasl: {Nat.is_lt(IX.kidl(i), n) == hasl : Bool}, ml: Maybe<&2, A>, +eml: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)) == ml : Maybe<&2, A>}, two: Bool, +etwo: {Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)) == two : Bool}, mr: Maybe<&2, A>, +emr: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)) == mr : Maybe<&2, A>}, left: Bool, +eleft: {S.le(~A, ~cmp, UPS.mval(~A, ml, x), UPS.mval(~A, mr, x)) == left : Bool}, ok: Bool, +eok: {S.le(~A, ~cmp, x, pick_cv(~A, x, ml, two, mr, left)) == ok : Bool}) -> {dprobe(~A, ~cmp, n, i, x, t) == pick_state(~A, t, i, hasl, ml, two, mr, left, ok) : DownS<A>}:
  match hasl ml two mr left ok:
    case False{} _ _ _ _ _:
      %Equal.sym(Bool, Nat.is_lt(IX.kidl(i), n), False{}, ehasl) : {dhas(~A, ~cmp, n, i, x, t, IX.kidl(i), _) == DStp{t, i} : DownS<A>}
      {==}
    case True{} None{} True{} _ _ _:
      %Equal.sym(Bool, Nat.is_lt(IX.kidl(i), n), True{}, ehasl) : {dhas(~A, ~cmp, n, i, x, t, IX.kidl(i), _) == DStp{t, i} : DownS<A>}
      %Equal.sym(Bool, Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), True{}, etwo) : {dlmb(~A, ~cmp, t, i, x, IX.kidl(i), _, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i))) == DStp{t, i} : DownS<A>}
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), None{}, eml) : {dlmb(~A, ~cmp, t, i, x, IX.kidl(i), True{}, _) == DStp{t, i} : DownS<A>}
      {==}
    case True{} None{} False{} _ _ _:
      %Equal.sym(Bool, Nat.is_lt(IX.kidl(i), n), True{}, ehasl) : {dhas(~A, ~cmp, n, i, x, t, IX.kidl(i), _) == DStp{t, i} : DownS<A>}
      %Equal.sym(Bool, Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), False{}, etwo) : {dlmb(~A, ~cmp, t, i, x, IX.kidl(i), _, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i))) == DStp{t, i} : DownS<A>}
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), None{}, eml) : {dlmb(~A, ~cmp, t, i, x, IX.kidl(i), False{}, _) == DStp{t, i} : DownS<A>}
      {==}
    case True{} Some{lv} False{} _ _ True{}:
      %Equal.sym(Bool, Nat.is_lt(IX.kidl(i), n), True{}, ehasl) : {dhas(~A, ~cmp, n, i, x, t, IX.kidl(i), _) == DStp{t, i} : DownS<A>}
      %Equal.sym(Bool, Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), False{}, etwo) : {dlmb(~A, ~cmp, t, i, x, IX.kidl(i), _, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i))) == DStp{t, i} : DownS<A>}
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), Some{lv}, eml) : {dlmb(~A, ~cmp, t, i, x, IX.kidl(i), False{}, _) == DStp{t, i} : DownS<A>}
      %Equal.sym(Bool, S.le(~A, ~cmp, x, lv), True{}, eok) : {ddec(~A, t, i, lv, IX.kidl(i), _) == DStp{t, i} : DownS<A>}
      {==}
    case True{} Some{lv} False{} _ _ False{}:
      %Equal.sym(Bool, Nat.is_lt(IX.kidl(i), n), True{}, ehasl) : {dhas(~A, ~cmp, n, i, x, t, IX.kidl(i), _) == DMv{t, i, lv, IX.kidl(i)} : DownS<A>}
      %Equal.sym(Bool, Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), False{}, etwo) : {dlmb(~A, ~cmp, t, i, x, IX.kidl(i), _, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i))) == DMv{t, i, lv, IX.kidl(i)} : DownS<A>}
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), Some{lv}, eml) : {dlmb(~A, ~cmp, t, i, x, IX.kidl(i), False{}, _) == DMv{t, i, lv, IX.kidl(i)} : DownS<A>}
      %Equal.sym(Bool, S.le(~A, ~cmp, x, lv), False{}, eok) : {ddec(~A, t, i, lv, IX.kidl(i), _) == DMv{t, i, lv, IX.kidl(i)} : DownS<A>}
      {==}
    case True{} Some{lv} True{} None{} _ True{}:
      %Equal.sym(Bool, Nat.is_lt(IX.kidl(i), n), True{}, ehasl) : {dhas(~A, ~cmp, n, i, x, t, IX.kidl(i), _) == DStp{t, i} : DownS<A>}
      %Equal.sym(Bool, Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), True{}, etwo) : {dlmb(~A, ~cmp, t, i, x, IX.kidl(i), _, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i))) == DStp{t, i} : DownS<A>}
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), Some{lv}, eml) : {dlmb(~A, ~cmp, t, i, x, IX.kidl(i), True{}, _) == DStp{t, i} : DownS<A>}
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), None{}, emr) : {drmb(~A, ~cmp, t, i, x, IX.kidl(i), lv, IX.kidr(i), _) == DStp{t, i} : DownS<A>}
      %Equal.sym(Bool, S.le(~A, ~cmp, x, lv), True{}, eok) : {ddec(~A, t, i, lv, IX.kidl(i), _) == DStp{t, i} : DownS<A>}
      {==}
    case True{} Some{lv} True{} None{} _ False{}:
      %Equal.sym(Bool, Nat.is_lt(IX.kidl(i), n), True{}, ehasl) : {dhas(~A, ~cmp, n, i, x, t, IX.kidl(i), _) == DMv{t, i, lv, IX.kidl(i)} : DownS<A>}
      %Equal.sym(Bool, Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), True{}, etwo) : {dlmb(~A, ~cmp, t, i, x, IX.kidl(i), _, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i))) == DMv{t, i, lv, IX.kidl(i)} : DownS<A>}
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), Some{lv}, eml) : {dlmb(~A, ~cmp, t, i, x, IX.kidl(i), True{}, _) == DMv{t, i, lv, IX.kidl(i)} : DownS<A>}
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), None{}, emr) : {drmb(~A, ~cmp, t, i, x, IX.kidl(i), lv, IX.kidr(i), _) == DMv{t, i, lv, IX.kidl(i)} : DownS<A>}
      %Equal.sym(Bool, S.le(~A, ~cmp, x, lv), False{}, eok) : {ddec(~A, t, i, lv, IX.kidl(i), _) == DMv{t, i, lv, IX.kidl(i)} : DownS<A>}
      {==}
    case True{} Some{lv} True{} Some{rv} True{} True{}:
      %Equal.sym(Bool, Nat.is_lt(IX.kidl(i), n), True{}, ehasl) : {dhas(~A, ~cmp, n, i, x, t, IX.kidl(i), _) == DStp{t, i} : DownS<A>}
      %Equal.sym(Bool, Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), True{}, etwo) : {dlmb(~A, ~cmp, t, i, x, IX.kidl(i), _, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i))) == DStp{t, i} : DownS<A>}
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), Some{lv}, eml) : {dlmb(~A, ~cmp, t, i, x, IX.kidl(i), True{}, _) == DStp{t, i} : DownS<A>}
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), Some{rv}, emr) : {drmb(~A, ~cmp, t, i, x, IX.kidl(i), lv, IX.kidr(i), _) == DStp{t, i} : DownS<A>}
      %Equal.sym(Bool, S.le(~A, ~cmp, lv, rv), True{}, eleft) : {dtwo(~A, ~cmp, t, i, x, IX.kidl(i), lv, IX.kidr(i), rv, _) == DStp{t, i} : DownS<A>}
      %Equal.sym(Bool, S.le(~A, ~cmp, x, lv), True{}, eok) : {ddec(~A, t, i, lv, IX.kidl(i), _) == DStp{t, i} : DownS<A>}
      {==}
    case True{} Some{lv} True{} Some{rv} True{} False{}:
      %Equal.sym(Bool, Nat.is_lt(IX.kidl(i), n), True{}, ehasl) : {dhas(~A, ~cmp, n, i, x, t, IX.kidl(i), _) == DMv{t, i, lv, IX.kidl(i)} : DownS<A>}
      %Equal.sym(Bool, Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), True{}, etwo) : {dlmb(~A, ~cmp, t, i, x, IX.kidl(i), _, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i))) == DMv{t, i, lv, IX.kidl(i)} : DownS<A>}
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), Some{lv}, eml) : {dlmb(~A, ~cmp, t, i, x, IX.kidl(i), True{}, _) == DMv{t, i, lv, IX.kidl(i)} : DownS<A>}
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), Some{rv}, emr) : {drmb(~A, ~cmp, t, i, x, IX.kidl(i), lv, IX.kidr(i), _) == DMv{t, i, lv, IX.kidl(i)} : DownS<A>}
      %Equal.sym(Bool, S.le(~A, ~cmp, lv, rv), True{}, eleft) : {dtwo(~A, ~cmp, t, i, x, IX.kidl(i), lv, IX.kidr(i), rv, _) == DMv{t, i, lv, IX.kidl(i)} : DownS<A>}
      %Equal.sym(Bool, S.le(~A, ~cmp, x, lv), False{}, eok) : {ddec(~A, t, i, lv, IX.kidl(i), _) == DMv{t, i, lv, IX.kidl(i)} : DownS<A>}
      {==}
    case True{} Some{lv} True{} Some{rv} False{} True{}:
      %Equal.sym(Bool, Nat.is_lt(IX.kidl(i), n), True{}, ehasl) : {dhas(~A, ~cmp, n, i, x, t, IX.kidl(i), _) == DStp{t, i} : DownS<A>}
      %Equal.sym(Bool, Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), True{}, etwo) : {dlmb(~A, ~cmp, t, i, x, IX.kidl(i), _, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i))) == DStp{t, i} : DownS<A>}
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), Some{lv}, eml) : {dlmb(~A, ~cmp, t, i, x, IX.kidl(i), True{}, _) == DStp{t, i} : DownS<A>}
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), Some{rv}, emr) : {drmb(~A, ~cmp, t, i, x, IX.kidl(i), lv, IX.kidr(i), _) == DStp{t, i} : DownS<A>}
      %Equal.sym(Bool, S.le(~A, ~cmp, lv, rv), False{}, eleft) : {dtwo(~A, ~cmp, t, i, x, IX.kidl(i), lv, IX.kidr(i), rv, _) == DStp{t, i} : DownS<A>}
      %Equal.sym(Bool, S.le(~A, ~cmp, x, rv), True{}, eok) : {ddec(~A, t, i, rv, IX.kidr(i), _) == DStp{t, i} : DownS<A>}
      {==}
    case True{} Some{lv} True{} Some{rv} False{} False{}:
      %Equal.sym(Bool, Nat.is_lt(IX.kidl(i), n), True{}, ehasl) : {dhas(~A, ~cmp, n, i, x, t, IX.kidl(i), _) == DMv{t, i, rv, IX.kidr(i)} : DownS<A>}
      %Equal.sym(Bool, Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), True{}, etwo) : {dlmb(~A, ~cmp, t, i, x, IX.kidl(i), _, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i))) == DMv{t, i, rv, IX.kidr(i)} : DownS<A>}
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), Some{lv}, eml) : {dlmb(~A, ~cmp, t, i, x, IX.kidl(i), True{}, _) == DMv{t, i, rv, IX.kidr(i)} : DownS<A>}
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), Some{rv}, emr) : {drmb(~A, ~cmp, t, i, x, IX.kidl(i), lv, IX.kidr(i), _) == DMv{t, i, rv, IX.kidr(i)} : DownS<A>}
      %Equal.sym(Bool, S.le(~A, ~cmp, lv, rv), False{}, eleft) : {dtwo(~A, ~cmp, t, i, x, IX.kidl(i), lv, IX.kidr(i), rv, _) == DMv{t, i, rv, IX.kidr(i)} : DownS<A>}
      %Equal.sym(Bool, S.le(~A, ~cmp, x, rv), False{}, eok) : {ddec(~A, t, i, rv, IX.kidr(i), _) == DMv{t, i, rv, IX.kidr(i)} : DownS<A>}
      {==}

# ---- what the stop cases have to show: x is not larger than its children ----

def g_no_left(~A: Data, ~cmp: A -> A -> Cmp, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +n: Nat, +e: {Nat.is_lt(IX.kidl(i), n) == False{} : Bool}) -> {SL.kids_le(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i, i) == True{} : Bool}:
  L.and_intro(SL.kid_le(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i, IX.kidl(i)), SL.kid_le(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i, IX.kidr(i)),
    SL.kid_le_out(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i, IX.kidl(i), e),
    SL.kid_le_out(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i, IX.kidr(i), kidr_out(i, n, e)))

def g_left_only(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +n: Nat, +lv: A, +ehasl: {Nat.is_lt(IX.kidl(i), n) == True{} : Bool}, +etwo: {Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)) == False{} : Bool}, +eml: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)) == Some{lv} : Maybe<&2, A>}, +eok: {S.le(~A, ~cmp, x, lv) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {SL.kids_le(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i, i) == True{} : Bool}:
  L.and_intro(SL.kid_le(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i, IX.kidl(i)), SL.kid_le(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i, IX.kidr(i)),
    kid_le_x(~A, ~cmp, d, t, i, x, n, IX.kidl(i), lv, ehasl, N.is_eq_lt(i, IX.kidl(i), IX.kidl_gt(i)), hi, pf, eml, eok),
    SL.kid_le_out(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i, IX.kidr(i), kidr_out2(i, n, etwo)))

def g_both(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +n: Nat, +lv: A, +rv: A, +ehasl: {Nat.is_lt(IX.kidl(i), n) == True{} : Bool}, +etwo: {Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)) == True{} : Bool}, +eml: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)) == Some{lv} : Maybe<&2, A>}, +emr: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)) == Some{rv} : Maybe<&2, A>}, +hxl: {S.le(~A, ~cmp, x, lv) == True{} : Bool}, +hxr: {S.le(~A, ~cmp, x, rv) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {SL.kids_le(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i, i) == True{} : Bool}:
  L.and_intro(SL.kid_le(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i, IX.kidl(i)), SL.kid_le(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i, IX.kidr(i)),
    kid_le_x(~A, ~cmp, d, t, i, x, n, IX.kidl(i), lv, ehasl, N.is_eq_lt(i, IX.kidl(i), IX.kidl_gt(i)), hi, pf, eml, hxl),
    kid_le_x(~A, ~cmp, d, t, i, x, n, IX.kidr(i), rv, kidr_in2(i, n, etwo), N.is_eq_lt(i, IX.kidr(i), IX.kidr_gt(i)), hi, pf, emr, hxr))

# with no fuel left the hole has no children: n <= 1 + i and kidl i < n force
# 2i + 1 < 1 + i
def fuel_out(+i: Nat, +n: Nat, +ehasl: {Nat.is_lt(IX.kidl(i), n) == True{} : Bool}, +hfuel: {Nat.is_le(n, IX.scale(0n, 1n+i)) == True{} : Bool}) -> Empty:
  L.true_not_false(Nat.is_lt(IX.kidl(i), 1n+i), N.lt_le_trans(IX.kidl(i), n, 1n+i, ehasl, hfuel), N.le_not_lt(IX.kidl(i), 1n+i, IX.double_le(i)))

def sib_mle(~A: Data, ~cmp: A -> A -> Cmp, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +lv: A, +rv: A, +eml: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)) == Some{lv} : Maybe<&2, A>}, +emr: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)) == Some{rv} : Maybe<&2, A>}, +hle: {S.le(~A, ~cmp, lv, rv) == True{} : Bool}) -> {SL.mle(~A, ~cmp, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i))) == True{} : Bool}:
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), Some{lv}, eml) : {SL.mle(~A, ~cmp, _, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i))) == True{} : Bool}
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), Some{rv}, emr) : {SL.mle(~A, ~cmp, Some{lv}, _) == True{} : Bool}
  hle

def sib_mle_r(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +lv: A, +rv: A, +eml: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)) == Some{lv} : Maybe<&2, A>}, +emr: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)) == Some{rv} : Maybe<&2, A>}, +hnle: {S.le(~A, ~cmp, lv, rv) == False{} : Bool}) -> {SL.mle(~A, ~cmp, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i))) == True{} : Bool}:
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), Some{rv}, emr) : {SL.mle(~A, ~cmp, _, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i))) == True{} : Bool}
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), Some{lv}, eml) : {SL.mle(~A, ~cmp, Some{rv}, _) == True{} : Bool}
  O.total(~A, ~cmp, ~o, lv, rv, hnle)


def down_loop_go(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), fuel: Nat, +d: Nat, +n: Nat, +tgt: List<&2, A>, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hin: {Nat.is_lt(i, n) == True{} : Bool}, +hn: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}, +hfuel: {Nat.is_le(n, IX.scale(fuel, 1n+i)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hexc: {SL.ho_exc2(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i) == True{} : Bool}, +hpair: {SL.pair_ok(~A, ~cmp, UPS.ulog(~A, t, i, x), i) == True{} : Bool}, +hkids: {SL.kids_le(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, IX.par(i), i) == True{} : Bool}, +hlay: {SL.lay(~A, UPS.ulog(~A, t, i, x), n) == True{} : Bool}, +hms: {V.msort(~A, ~cmp, V.vals(~A, UPS.ulog(~A, t, i, x), n)) == tgt : List<&2, A>}, hasl: Bool, +ehasl: {Nat.is_lt(IX.kidl(i), n) == hasl : Bool}, ml: Maybe<&2, A>, +eml: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)) == ml : Maybe<&2, A>}, two: Bool, +etwo: {Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)) == two : Bool}, mr: Maybe<&2, A>, +emr: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)) == mr : Maybe<&2, A>}, left: Bool, +eleft: {S.le(~A, ~cmp, UPS.mval(~A, ml, x), UPS.mval(~A, mr, x)) == left : Bool}, ok: Bool, +eok: {S.le(~A, ~cmp, x, pick_cv(~A, x, ml, two, mr, left)) == ok : Bool}) -> DownOK(~A, ~cmp, d, n, tgt, fuel, x, pick_state(~A, t, i, hasl, ml, two, mr, left, ok)):
  match fuel hasl ml two mr left ok:
    case _ False{} _ _ _ _ _:
      down_stop_ok(~A, ~cmp, d, n, tgt, fuel, t, i, x, hd, hi, hn, pf, hexc, g_no_left(~A, ~cmp, t, i, x, n, ehasl), hlay, hms)
    case _ True{} None{} True{} _ _ _:
      Empty.absurd(DownOK(~A, ~cmp, d, n, tgt, fuel, x, DStp{t, i}), slot_some_at(~A, t, i, x, n, IX.kidl(i), ehasl, N.is_eq_lt(i, IX.kidl(i), IX.kidl_gt(i)), hlay, eml))
    case _ True{} None{} False{} _ _ _:
      Empty.absurd(DownOK(~A, ~cmp, d, n, tgt, fuel, x, DStp{t, i}), slot_some_at(~A, t, i, x, n, IX.kidl(i), ehasl, N.is_eq_lt(i, IX.kidl(i), IX.kidl_gt(i)), hlay, eml))
    case _ True{} Some{lv} False{} _ _ True{}:
      down_stop_ok(~A, ~cmp, d, n, tgt, fuel, t, i, x, hd, hi, hn, pf, hexc, g_left_only(~A, ~cmp, d, t, i, x, n, lv, ehasl, etwo, eml, eok, hi, pf), hlay, hms)
    case 0n True{} Some{lv} False{} _ _ False{}:
      Empty.absurd(DownOK(~A, ~cmp, d, n, tgt, 0n, x, DMv{t, i, lv, IX.kidl(i)}), fuel_out(i, n, ehasl, hfuel))
    case 1n+ +f True{} Some{+lv} False{} _ _ False{}:
      down_carry(~A, ~cmp, d, n, tgt, f, t, i, x, lv, IX.kidl(i),
        down_step_eq(~A, ~cmp, d, n, f, t, i, x, lv, IX.kidl(i), hd, hi, N.lt_le_trans(IX.kidl(i), n, SC.pow2(d), ehasl, hn), hn, pf),
        L.subst(DownS<A>, st => DownOK(~A, ~cmp, d, n, tgt, f, x, st), pick_state(~A, t2_of(~A, d, t, i, lv), IX.kidl(i), Nat.is_lt(IX.kidl(IX.kidl(i)), n), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), Nat.is_lt(IX.kidl(IX.kidl(i)), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), x)), S.le(~A, ~cmp, x, pick_cv(~A, x, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), Nat.is_lt(IX.kidl(IX.kidl(i)), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), x))))), dprobe(~A, ~cmp, n, IX.kidl(i), x, t2_of(~A, d, t, i, lv)),
          Equal.sym(DownS<A>, dprobe(~A, ~cmp, n, IX.kidl(i), x, t2_of(~A, d, t, i, lv)), pick_state(~A, t2_of(~A, d, t, i, lv), IX.kidl(i), Nat.is_lt(IX.kidl(IX.kidl(i)), n), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), Nat.is_lt(IX.kidl(IX.kidl(i)), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), x)), S.le(~A, ~cmp, x, pick_cv(~A, x, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), Nat.is_lt(IX.kidl(IX.kidl(i)), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), x))))), probe_shape(~A, ~cmp, n, IX.kidl(i), x, t2_of(~A, d, t, i, lv), Nat.is_lt(IX.kidl(IX.kidl(i)), n), {==}, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), {==}, Nat.is_lt(IX.kidl(IX.kidl(i)), Nat.sub(n, 1n)), {==}, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), {==}, S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), x)), {==}, S.le(~A, ~cmp, x, pick_cv(~A, x, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), Nat.is_lt(IX.kidl(IX.kidl(i)), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), x)))), {==})),
          down_loop_go(~A, ~cmp, ~o, f, d, n, tgt, t2_of(~A, d, t, i, lv), IX.kidl(i), x, hd, N.lt_le_trans(IX.kidl(i), n, SC.pow2(d), ehasl, hn), ehasl, hn,
            N.le_trans(n, IX.scale(f, Nat.double(1n+i)), IX.scale(f, 1n+IX.kidl(i)), hfuel, IX.scale_mono(f, Nat.double(1n+i), 1n+IX.kidl(i), IX.kid_double(i, IX.kidl(i), IX.par_kidl(i), IX.kidl_pos1(i)))),
            UPS.t2_perfect(~A, d, t, i, lv, pf),
            exc2_next(~A, ~cmp, ~o, d, n, t, i, x, lv, IX.kidl(i), IX.kidr(i), n, N.le_refl(n), ehasl, kidl_ne_kidr(i), IX.par_kidr(i), IX.kidr_pos1(i), IX.par_kidl(i), IX.kidl_pos1(i), N.lt_le_trans(IX.kidl(i), n, SC.pow2(d), ehasl, hn), Inl{{==}}, Inr{{==}}, hi, pf, hexc, hkids, SL.kid_le_out(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, IX.kidl(i), IX.kidr(i), kidr_out2(i, n, etwo)), eml, eok),
            d1n_c(~A, ~cmp, ~o, d, t, i, x, lv, IX.kidl(i), IX.kidl(i), N.is_eq_refl(IX.kidl(i)), IX.par_kidl(i), IX.kidl_pos1(i), N.lt_le_trans(IX.kidl(i), n, SC.pow2(d), ehasl, hn), hi, pf, eok),
            kids_next_d(~A, ~cmp, d, n, t, i, x, lv, IX.kidl(i), IX.par_kidl(i), IX.kidl_pos1(i), SL.ne_sym(IX.kidl(i), i, N.is_eq_lt(i, IX.kidl(i), IX.kidl_gt(i))), hi, pf, hexc, eml),
            lay_next_d(~A, d, n, t, i, x, lv, IX.kidl(i), n, N.le_refl(n), SL.ne_sym(IX.kidl(i), i, N.is_eq_lt(i, IX.kidl(i), IX.kidl_gt(i))), hi, N.lt_le_trans(IX.kidl(i), n, SC.pow2(d), ehasl, hn), pf, hlay),
            ms_next_d(~A, ~cmp, ~o, d, n, t, i, x, lv, IX.kidl(i), tgt, hin, ehasl, SL.ne_sym(IX.kidl(i), i, N.is_eq_lt(i, IX.kidl(i), IX.kidl_gt(i))), hi, pf, eml, hms),
            Nat.is_lt(IX.kidl(IX.kidl(i)), n), {==}, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), {==}, Nat.is_lt(IX.kidl(IX.kidl(i)), Nat.sub(n, 1n)), {==}, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), {==}, S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), x)), {==}, S.le(~A, ~cmp, x, pick_cv(~A, x, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), Nat.is_lt(IX.kidl(IX.kidl(i)), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), x)))), {==})))
    case _ True{} Some{lv} True{} None{} _ True{}:
      Empty.absurd(DownOK(~A, ~cmp, d, n, tgt, fuel, x, pick_state2(~A, t, i, lv, True{}, None{}, left, True{})), slot_some_at(~A, t, i, x, n, IX.kidr(i), kidr_in2(i, n, etwo), N.is_eq_lt(i, IX.kidr(i), IX.kidr_gt(i)), hlay, emr))
    case _ True{} Some{lv} True{} None{} _ False{}:
      Empty.absurd(DownOK(~A, ~cmp, d, n, tgt, fuel, x, pick_state2(~A, t, i, lv, True{}, None{}, left, False{})), slot_some_at(~A, t, i, x, n, IX.kidr(i), kidr_in2(i, n, etwo), N.is_eq_lt(i, IX.kidr(i), IX.kidr_gt(i)), hlay, emr))
    case _ True{} Some{+lv} True{} Some{+rv} True{} True{}:
      down_stop_ok(~A, ~cmp, d, n, tgt, fuel, t, i, x, hd, hi, hn, pf, hexc, g_both(~A, ~cmp, ~o, d, t, i, x, n, lv, rv, ehasl, etwo, eml, emr, eok, O.trans(~A, ~cmp, o, x, lv, rv, eok, eleft), hi, pf), hlay, hms)
    case 0n True{} Some{lv} True{} Some{rv} True{} False{}:
      Empty.absurd(DownOK(~A, ~cmp, d, n, tgt, 0n, x, DMv{t, i, lv, IX.kidl(i)}), fuel_out(i, n, ehasl, hfuel))
    case 1n+ +f True{} Some{+lv} True{} Some{rv} True{} False{}:
      down_carry(~A, ~cmp, d, n, tgt, f, t, i, x, lv, IX.kidl(i),
        down_step_eq(~A, ~cmp, d, n, f, t, i, x, lv, IX.kidl(i), hd, hi, N.lt_le_trans(IX.kidl(i), n, SC.pow2(d), ehasl, hn), hn, pf),
        L.subst(DownS<A>, st => DownOK(~A, ~cmp, d, n, tgt, f, x, st), pick_state(~A, t2_of(~A, d, t, i, lv), IX.kidl(i), Nat.is_lt(IX.kidl(IX.kidl(i)), n), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), Nat.is_lt(IX.kidl(IX.kidl(i)), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), x)), S.le(~A, ~cmp, x, pick_cv(~A, x, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), Nat.is_lt(IX.kidl(IX.kidl(i)), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), x))))), dprobe(~A, ~cmp, n, IX.kidl(i), x, t2_of(~A, d, t, i, lv)),
          Equal.sym(DownS<A>, dprobe(~A, ~cmp, n, IX.kidl(i), x, t2_of(~A, d, t, i, lv)), pick_state(~A, t2_of(~A, d, t, i, lv), IX.kidl(i), Nat.is_lt(IX.kidl(IX.kidl(i)), n), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), Nat.is_lt(IX.kidl(IX.kidl(i)), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), x)), S.le(~A, ~cmp, x, pick_cv(~A, x, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), Nat.is_lt(IX.kidl(IX.kidl(i)), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), x))))), probe_shape(~A, ~cmp, n, IX.kidl(i), x, t2_of(~A, d, t, i, lv), Nat.is_lt(IX.kidl(IX.kidl(i)), n), {==}, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), {==}, Nat.is_lt(IX.kidl(IX.kidl(i)), Nat.sub(n, 1n)), {==}, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), {==}, S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), x)), {==}, S.le(~A, ~cmp, x, pick_cv(~A, x, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), Nat.is_lt(IX.kidl(IX.kidl(i)), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), x)))), {==})),
          down_loop_go(~A, ~cmp, ~o, f, d, n, tgt, t2_of(~A, d, t, i, lv), IX.kidl(i), x, hd, N.lt_le_trans(IX.kidl(i), n, SC.pow2(d), ehasl, hn), ehasl, hn,
            N.le_trans(n, IX.scale(f, Nat.double(1n+i)), IX.scale(f, 1n+IX.kidl(i)), hfuel, IX.scale_mono(f, Nat.double(1n+i), 1n+IX.kidl(i), IX.kid_double(i, IX.kidl(i), IX.par_kidl(i), IX.kidl_pos1(i)))),
            UPS.t2_perfect(~A, d, t, i, lv, pf),
            exc2_next(~A, ~cmp, ~o, d, n, t, i, x, lv, IX.kidl(i), IX.kidr(i), n, N.le_refl(n), ehasl, kidl_ne_kidr(i), IX.par_kidr(i), IX.kidr_pos1(i), IX.par_kidl(i), IX.kidl_pos1(i), N.lt_le_trans(IX.kidl(i), n, SC.pow2(d), ehasl, hn), Inl{{==}}, Inr{{==}}, hi, pf, hexc, hkids, SL.kid_le_in(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, IX.kidl(i), IX.kidr(i), kidr_in2(i, n, etwo), sib_mle(~A, ~cmp, t, i, lv, rv, eml, emr, eleft)), eml, eok),
            d1n_c(~A, ~cmp, ~o, d, t, i, x, lv, IX.kidl(i), IX.kidl(i), N.is_eq_refl(IX.kidl(i)), IX.par_kidl(i), IX.kidl_pos1(i), N.lt_le_trans(IX.kidl(i), n, SC.pow2(d), ehasl, hn), hi, pf, eok),
            kids_next_d(~A, ~cmp, d, n, t, i, x, lv, IX.kidl(i), IX.par_kidl(i), IX.kidl_pos1(i), SL.ne_sym(IX.kidl(i), i, N.is_eq_lt(i, IX.kidl(i), IX.kidl_gt(i))), hi, pf, hexc, eml),
            lay_next_d(~A, d, n, t, i, x, lv, IX.kidl(i), n, N.le_refl(n), SL.ne_sym(IX.kidl(i), i, N.is_eq_lt(i, IX.kidl(i), IX.kidl_gt(i))), hi, N.lt_le_trans(IX.kidl(i), n, SC.pow2(d), ehasl, hn), pf, hlay),
            ms_next_d(~A, ~cmp, ~o, d, n, t, i, x, lv, IX.kidl(i), tgt, hin, ehasl, SL.ne_sym(IX.kidl(i), i, N.is_eq_lt(i, IX.kidl(i), IX.kidl_gt(i))), hi, pf, eml, hms),
            Nat.is_lt(IX.kidl(IX.kidl(i)), n), {==}, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), {==}, Nat.is_lt(IX.kidl(IX.kidl(i)), Nat.sub(n, 1n)), {==}, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), {==}, S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), x)), {==}, S.le(~A, ~cmp, x, pick_cv(~A, x, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), Nat.is_lt(IX.kidl(IX.kidl(i)), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidl(IX.kidl(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, lv)), IX.kidr(IX.kidl(i))), x)))), {==})))
    case _ True{} Some{+lv} True{} Some{+rv} False{} True{}:
      down_stop_ok(~A, ~cmp, d, n, tgt, fuel, t, i, x, hd, hi, hn, pf, hexc, g_both(~A, ~cmp, ~o, d, t, i, x, n, lv, rv, ehasl, etwo, eml, emr, O.trans(~A, ~cmp, o, x, rv, lv, eok, O.total(~A, ~cmp, ~o, lv, rv, eleft)), eok, hi, pf), hlay, hms)
    case 0n True{} Some{lv} True{} Some{rv} False{} False{}:
      Empty.absurd(DownOK(~A, ~cmp, d, n, tgt, 0n, x, DMv{t, i, rv, IX.kidr(i)}), fuel_out(i, n, ehasl, hfuel))
    case 1n+ +f True{} Some{lv} True{} Some{+rv} False{} False{}:
      down_carry(~A, ~cmp, d, n, tgt, f, t, i, x, rv, IX.kidr(i),
        down_step_eq(~A, ~cmp, d, n, f, t, i, x, rv, IX.kidr(i), hd, hi, N.lt_le_trans(IX.kidr(i), n, SC.pow2(d), kidr_in2(i, n, etwo), hn), hn, pf),
        L.subst(DownS<A>, st => DownOK(~A, ~cmp, d, n, tgt, f, x, st), pick_state(~A, t2_of(~A, d, t, i, rv), IX.kidr(i), Nat.is_lt(IX.kidl(IX.kidr(i)), n), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidl(IX.kidr(i))), Nat.is_lt(IX.kidl(IX.kidr(i)), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidr(IX.kidr(i))), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidl(IX.kidr(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidr(IX.kidr(i))), x)), S.le(~A, ~cmp, x, pick_cv(~A, x, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidl(IX.kidr(i))), Nat.is_lt(IX.kidl(IX.kidr(i)), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidr(IX.kidr(i))), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidl(IX.kidr(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidr(IX.kidr(i))), x))))), dprobe(~A, ~cmp, n, IX.kidr(i), x, t2_of(~A, d, t, i, rv)),
          Equal.sym(DownS<A>, dprobe(~A, ~cmp, n, IX.kidr(i), x, t2_of(~A, d, t, i, rv)), pick_state(~A, t2_of(~A, d, t, i, rv), IX.kidr(i), Nat.is_lt(IX.kidl(IX.kidr(i)), n), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidl(IX.kidr(i))), Nat.is_lt(IX.kidl(IX.kidr(i)), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidr(IX.kidr(i))), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidl(IX.kidr(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidr(IX.kidr(i))), x)), S.le(~A, ~cmp, x, pick_cv(~A, x, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidl(IX.kidr(i))), Nat.is_lt(IX.kidl(IX.kidr(i)), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidr(IX.kidr(i))), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidl(IX.kidr(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidr(IX.kidr(i))), x))))), probe_shape(~A, ~cmp, n, IX.kidr(i), x, t2_of(~A, d, t, i, rv), Nat.is_lt(IX.kidl(IX.kidr(i)), n), {==}, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidl(IX.kidr(i))), {==}, Nat.is_lt(IX.kidl(IX.kidr(i)), Nat.sub(n, 1n)), {==}, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidr(IX.kidr(i))), {==}, S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidl(IX.kidr(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidr(IX.kidr(i))), x)), {==}, S.le(~A, ~cmp, x, pick_cv(~A, x, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidl(IX.kidr(i))), Nat.is_lt(IX.kidl(IX.kidr(i)), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidr(IX.kidr(i))), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidl(IX.kidr(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidr(IX.kidr(i))), x)))), {==})),
          down_loop_go(~A, ~cmp, ~o, f, d, n, tgt, t2_of(~A, d, t, i, rv), IX.kidr(i), x, hd, N.lt_le_trans(IX.kidr(i), n, SC.pow2(d), kidr_in2(i, n, etwo), hn), kidr_in2(i, n, etwo), hn,
            N.le_trans(n, IX.scale(f, Nat.double(1n+i)), IX.scale(f, 1n+IX.kidr(i)), hfuel, IX.scale_mono(f, Nat.double(1n+i), 1n+IX.kidr(i), IX.kid_double(i, IX.kidr(i), IX.par_kidr(i), IX.kidr_pos1(i)))),
            UPS.t2_perfect(~A, d, t, i, rv, pf),
            exc2_next(~A, ~cmp, ~o, d, n, t, i, x, rv, IX.kidr(i), IX.kidl(i), n, N.le_refl(n), kidr_in2(i, n, etwo), SL.ne_sym(IX.kidr(i), IX.kidl(i), kidl_ne_kidr(i)), IX.par_kidl(i), IX.kidl_pos1(i), IX.par_kidr(i), IX.kidr_pos1(i), N.lt_le_trans(IX.kidr(i), n, SC.pow2(d), kidr_in2(i, n, etwo), hn), Inr{{==}}, Inl{{==}}, hi, pf, hexc, hkids, SL.kid_le_in(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, IX.kidr(i), IX.kidl(i), ehasl, sib_mle_r(~A, ~cmp, ~o, t, i, lv, rv, eml, emr, eleft)), emr, eok),
            d1n_c(~A, ~cmp, ~o, d, t, i, x, rv, IX.kidr(i), IX.kidr(i), N.is_eq_refl(IX.kidr(i)), IX.par_kidr(i), IX.kidr_pos1(i), N.lt_le_trans(IX.kidr(i), n, SC.pow2(d), kidr_in2(i, n, etwo), hn), hi, pf, eok),
            kids_next_d(~A, ~cmp, d, n, t, i, x, rv, IX.kidr(i), IX.par_kidr(i), IX.kidr_pos1(i), SL.ne_sym(IX.kidr(i), i, N.is_eq_lt(i, IX.kidr(i), IX.kidr_gt(i))), hi, pf, hexc, emr),
            lay_next_d(~A, d, n, t, i, x, rv, IX.kidr(i), n, N.le_refl(n), SL.ne_sym(IX.kidr(i), i, N.is_eq_lt(i, IX.kidr(i), IX.kidr_gt(i))), hi, N.lt_le_trans(IX.kidr(i), n, SC.pow2(d), kidr_in2(i, n, etwo), hn), pf, hlay),
            ms_next_d(~A, ~cmp, ~o, d, n, t, i, x, rv, IX.kidr(i), tgt, hin, kidr_in2(i, n, etwo), SL.ne_sym(IX.kidr(i), i, N.is_eq_lt(i, IX.kidr(i), IX.kidr_gt(i))), hi, pf, emr, hms),
            Nat.is_lt(IX.kidl(IX.kidr(i)), n), {==}, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidl(IX.kidr(i))), {==}, Nat.is_lt(IX.kidl(IX.kidr(i)), Nat.sub(n, 1n)), {==}, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidr(IX.kidr(i))), {==}, S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidl(IX.kidr(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidr(IX.kidr(i))), x)), {==}, S.le(~A, ~cmp, x, pick_cv(~A, x, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidl(IX.kidr(i))), Nat.is_lt(IX.kidl(IX.kidr(i)), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidr(IX.kidr(i))), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidl(IX.kidr(i))), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, rv)), IX.kidr(IX.kidr(i))), x)))), {==})))

# ---- the entry point ----

def SiftDownOK(~A: Data, ~cmp: A -> A -> Cmp, d: Nat, n: Nat, tgt: List<&2, A>, fuel: Nat, t: AR.Tree<Maybe<&2, A>>, i: Nat, x: A) -> Type:
  Sigma<&1, &1, AR.Tree<Maybe<&2, A>>, t2 => {H.sift_down(~A, ~cmp, fuel, U32.from_nat(n), U32.from_nat(i), x, AR.thaw(Maybe<&2, A>, t)) == AR.thaw(Maybe<&2, A>, t2) : Array<Maybe<&2, A>>} & ({AR.perfect(Maybe<&2, A>, d, t2) == True{} : Bool} & ({SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t2), n) == True{} : Bool} & ({SL.lay(~A, AR.slots(Maybe<&2, A>, t2), n) == True{} : Bool} & {V.msort(~A, ~cmp, V.vals(~A, AR.slots(Maybe<&2, A>, t2), n)) == tgt : List<&2, A>})))>

def dsift_from_go(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +tgt: List<&2, A>, +fuel: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +t2: AR.Tree<Maybe<&2, A>>, +eq: {H.sift_down(~A, ~cmp, fuel, U32.from_nat(n), U32.from_nat(i), x, AR.thaw(Maybe<&2, A>, t)) == H.down_go(~A, ~cmp, fuel, U32.from_nat(n), x, dreal(~A, dprobe(~A, ~cmp, n, i, x, t))) : Array<Maybe<&2, A>>}, rest: {H.down_go(~A, ~cmp, fuel, U32.from_nat(n), x, dreal(~A, dprobe(~A, ~cmp, n, i, x, t))) == AR.thaw(Maybe<&2, A>, t2) : Array<Maybe<&2, A>>} & ({AR.perfect(Maybe<&2, A>, d, t2) == True{} : Bool} & ({SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t2), n) == True{} : Bool} & ({SL.lay(~A, AR.slots(Maybe<&2, A>, t2), n) == True{} : Bool} & {V.msort(~A, ~cmp, V.vals(~A, AR.slots(Maybe<&2, A>, t2), n)) == tgt : List<&2, A>})))) -> SiftDownOK(~A, ~cmp, d, n, tgt, fuel, t, i, x):
  (e1, more) = rest
  (t2, (Equal.trans(Array<Maybe<&2, A>>, H.sift_down(~A, ~cmp, fuel, U32.from_nat(n), U32.from_nat(i), x, AR.thaw(Maybe<&2, A>, t)), H.down_go(~A, ~cmp, fuel, U32.from_nat(n), x, dreal(~A, dprobe(~A, ~cmp, n, i, x, t))), AR.thaw(Maybe<&2, A>, t2), eq, e1), more))

def dsift_from_loop(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +tgt: List<&2, A>, +fuel: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +eq: {H.sift_down(~A, ~cmp, fuel, U32.from_nat(n), U32.from_nat(i), x, AR.thaw(Maybe<&2, A>, t)) == H.down_go(~A, ~cmp, fuel, U32.from_nat(n), x, dreal(~A, dprobe(~A, ~cmp, n, i, x, t))) : Array<Maybe<&2, A>>}, r: DownOK(~A, ~cmp, d, n, tgt, fuel, x, dprobe(~A, ~cmp, n, i, x, t))) -> SiftDownOK(~A, ~cmp, d, n, tgt, fuel, t, i, x):
  (t2, rest) = r
  dsift_from_go(~A, ~cmp, d, n, tgt, fuel, t, i, x, t2, eq, rest)

# The hole at i is below the parent pair it inherits, every other pair holds,
# the two pairs below the hole are the only ones the loop has to fix, and the
# loop has enough fuel for n <= 2^fuel * (1 + i).
def sift_down_ok(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +fuel: Nat, +d: Nat, +n: Nat, +tgt: List<&2, A>, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hin: {Nat.is_lt(i, n) == True{} : Bool}, +hn: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}, +hfuel: {Nat.is_le(n, IX.scale(fuel, 1n+i)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hexc: {SL.ho_exc2(~A, ~cmp, UPS.ulog(~A, t, i, x), n, i) == True{} : Bool}, +hpair: {SL.pair_ok(~A, ~cmp, UPS.ulog(~A, t, i, x), i) == True{} : Bool}, +hkids: {SL.kids_le(~A, ~cmp, AR.slots(Maybe<&2, A>, t), n, IX.par(i), i) == True{} : Bool}, +hlay: {SL.lay(~A, UPS.ulog(~A, t, i, x), n) == True{} : Bool}, +hms: {V.msort(~A, ~cmp, V.vals(~A, UPS.ulog(~A, t, i, x), n)) == tgt : List<&2, A>}) -> SiftDownOK(~A, ~cmp, d, n, tgt, fuel, t, i, x):
  dsift_from_loop(~A, ~cmp, d, n, tgt, fuel, t, i, x,
    Equal.cong(H.Down<A>, Array<Maybe<&2, A>>, s => H.down_go(~A, ~cmp, fuel, U32.from_nat(n), x, s), H.down_probe(~A, ~cmp, U32.from_nat(n), U32.from_nat(i), x, AR.thaw(Maybe<&2, A>, t)), dreal(~A, dprobe(~A, ~cmp, n, i, x, t)), dprobe_ok(~A, ~cmp, d, n, t, i, x, hd, hi, hn, pf)),
    L.subst(DownS<A>, st => DownOK(~A, ~cmp, d, n, tgt, fuel, x, st), pick_state(~A, t, i, Nat.is_lt(IX.kidl(i), n), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), x)), S.le(~A, ~cmp, x, pick_cv(~A, x, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), x))))), dprobe(~A, ~cmp, n, i, x, t),
      Equal.sym(DownS<A>, dprobe(~A, ~cmp, n, i, x, t), pick_state(~A, t, i, Nat.is_lt(IX.kidl(i), n), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), x)), S.le(~A, ~cmp, x, pick_cv(~A, x, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), x))))),
        probe_shape(~A, ~cmp, n, i, x, t, Nat.is_lt(IX.kidl(i), n), {==}, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), {==}, Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), {==}, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), {==}, S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), x)), {==}, S.le(~A, ~cmp, x, pick_cv(~A, x, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), x)))), {==})),
      down_loop_go(~A, ~cmp, ~o, fuel, d, n, tgt, t, i, x, hd, hi, hin, hn, hfuel, pf, hexc, hpair, hkids, hlay, hms, Nat.is_lt(IX.kidl(i), n), {==}, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), {==}, Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), {==}, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), {==}, S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), x)), {==}, S.le(~A, ~cmp, x, pick_cv(~A, x, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), Nat.is_lt(IX.kidl(i), Nat.sub(n, 1n)), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), S.le(~A, ~cmp, UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidl(i)), x), UPS.mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.kidr(i)), x)))), {==})))
