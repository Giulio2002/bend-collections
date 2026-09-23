import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/array.bend as AR
import ../spec/common.bend as SC
import ../spec/lru.bend as SP
import ../math/u32div.bend as UD
import ../../src/math/u64.bend as W
import ../../src/containers/lru.bend as LR
import ./state.bend as ST
import ./meta.bend as MT
import ./basic.bend as BA
import ../lib/list.bend as LL
import ../lib/words32.bend as W32
import ../lib/u32_tree.bend as UT

# bump: a counter's 64-bit increment in the meta words.


def BumpOK(+mT: AR.Tree<U32>, +i: Nat, r: Array<U32>) -> Type:
  Sigma<&1, &1, AR.Tree<U32>, m2 => {r == AR.thaw(U32, m2) : Array<U32>} & ({AR.perfect(U32, 5n, m2) == True{} : Bool} & ({ST.w64(AR.slots(U32, m2), i) == SP.inc64(ST.w64(AR.slots(U32, mT), i)) : W.U64} & Sigma<&1, &1, U32, x => Sigma<&1, &1, U32, y => {AR.slots(U32, m2) == SC.update(U32, SC.update(U32, AR.slots(U32, mT), i, x), 1n+i, y) : List<&2, U32>}>>))>


def lt_i(+i: Nat, +hi: {Nat.is_lt(1n+i, 32n) == True{} : Bool}) -> {Nat.is_lt(i, 32n) == True{} : Bool}:
  N.lt_trans(i, 1n+i, 32n, N.lt_succ(i), hi)

def vlt(+x: U32, +i: Nat, +h: {UD.v(x) == i : Nat}, +hi: {Nat.is_lt(i, 32n) == True{} : Bool}) -> {Nat.is_lt(UD.v(x), SC.pow2(5n)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(z, 32n) == True{} : Bool}, i, UD.v(x), Equal.sym(Nat, UD.v(x), i, h), hi)

def ne_si(+i: Nat) -> {Nat.is_eq(i, 1n+i) == False{} : Bool}:
  N.is_eq_lt(i, 1n+i, N.lt_succ(i))

def s1_of(+mT: AR.Tree<U32>, +pm: {AR.perfect(U32, 5n, mT) == True{} : Bool}, +c: U32, +i: Nat, +hi: {Nat.is_lt(1n+i, 32n) == True{} : Bool}, +hI: {UD.v(U32.add(16, U32.shl(c))) == i : Nat}, +hJ: {UD.v(U32.add(17, U32.shl(c))) == 1n+i : Nat}) -> {AR.slots(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))) == SC.update(U32, AR.slots(U32, mT), i, U32.inc(W32.nth0(AR.slots(U32, mT), i))) : List<&2, U32>}:
  +hIb = vlt(U32.add(16, U32.shl(c)), i, hI, lt_i(i, hi))
  Equal.trans(List<&2, U32>, AR.slots(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), SC.update(U32, AR.slots(U32, mT), UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i))), SC.update(U32, AR.slots(U32, mT), i, U32.inc(W32.nth0(AR.slots(U32, mT), i))), UT.uset_s(5n, mT, pm, UD.v(U32.add(16, U32.shl(c))), hIb, U32.inc(W32.nth0(AR.slots(U32, mT), i))), Equal.cong(Nat, List<&2, U32>, z => SC.update(U32, AR.slots(U32, mT), z, U32.inc(W32.nth0(AR.slots(U32, mT), i))), UD.v(U32.add(16, U32.shl(c))), i, hI))

# writing a word's own value changes nothing
def upd_id(+xs: List<&2, U32>, +j: Nat) -> {SC.update(U32, xs, j, W32.nth0(xs, j)) == xs : List<&2, U32>}:
  match xs j:
    case Nil{} _:
      {==}
    case Con{+h, +t} 0n:
      {==}
    case Con{+h, +t} 1n+p:
      LL.cons_cong(U32, h, SC.update(U32, t, p, W32.nth0(t, p)), t, upd_id(t, p))

# no wrap of the low word
def bump_nw(+mT: AR.Tree<U32>, +pm: {AR.perfect(U32, 5n, mT) == True{} : Bool}, +c: U32, +i: Nat, +hi: {Nat.is_lt(1n+i, 32n) == True{} : Bool}, +hI: {UD.v(U32.add(16, U32.shl(c))) == i : Nat}, +hJ: {UD.v(U32.add(17, U32.shl(c))) == 1n+i : Nat}, +hz: {U32.is_eq(U32.inc(W32.nth0(AR.slots(U32, mT), i)), 0) == False{} : Bool}) -> BumpOK(mT, i, LR.bump_hi(Array.set(U32, AR.thaw(U32, mT), U32.add(16, U32.shl(c)), U32.inc(W32.nth0(AR.slots(U32, mT), i))), c, False{})):
  +hIb = vlt(U32.add(16, U32.shl(c)), i, hI, lt_i(i, hi))
  +a1 = UT.uset_a(5n, {==}, mT, pm, U32.add(16, U32.shl(c)), hIb, U32.inc(W32.nth0(AR.slots(U32, mT), i)))
  +p1 = UT.uset_p(5n, mT, pm, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))
  +s1 = s1_of(mT, pm, c, i, hi, hI, hJ)
  +e0 = MT.nth_same(5n, mT, pm, i, lt_i(i, hi), U32.inc(W32.nth0(AR.slots(U32, mT), i)), AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i))), s1)
  +e1 = MT.nth_other(mT, i, U32.inc(W32.nth0(AR.slots(U32, mT), i)), AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i))), s1, 1n+i, ne_si(i))
  +r = L.subst(Bool, z => {W.U64{U32.inc(W32.nth0(AR.slots(U32, mT), i)), W32.nth0(AR.slots(U32, mT), 1n+i)} == SP.inc_hi(U32.inc(W32.nth0(AR.slots(U32, mT), i)), W32.nth0(AR.slots(U32, mT), 1n+i), z) : W.U64}, False{}, U32.is_eq(U32.inc(W32.nth0(AR.slots(U32, mT), i)), 0), Equal.sym(Bool, U32.is_eq(U32.inc(W32.nth0(AR.slots(U32, mT), i)), 0), False{}, hz), {==})
  +ew = Equal.trans(W.U64, ST.w64(AR.slots(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), i), W.U64{U32.inc(W32.nth0(AR.slots(U32, mT), i)), W32.nth0(AR.slots(U32, mT), 1n+i)}, SP.inc64(ST.w64(AR.slots(U32, mT), i)), BA.w64_eq_l(AR.slots(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), i, U32.inc(W32.nth0(AR.slots(U32, mT), i)), W32.nth0(AR.slots(U32, mT), 1n+i), e0, e1), r)
  +U = SC.update(U32, AR.slots(U32, mT), i, U32.inc(W32.nth0(AR.slots(U32, mT), i)))
  +eu = Equal.trans(List<&2, U32>, SC.update(U32, U, 1n+i, W32.nth0(AR.slots(U32, mT), 1n+i)), SC.update(U32, U, 1n+i, W32.nth0(U, 1n+i)), U, Equal.cong(U32, List<&2, U32>, z => SC.update(U32, U, 1n+i, z), W32.nth0(AR.slots(U32, mT), 1n+i), W32.nth0(U, 1n+i), Equal.sym(U32, W32.nth0(U, 1n+i), W32.nth0(AR.slots(U32, mT), 1n+i), W32.nth0_upd_other(AR.slots(U32, mT), i, 1n+i, U32.inc(W32.nth0(AR.slots(U32, mT), i)), ne_si(i)))), upd_id(U, 1n+i))
  (AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i))), (a1, (p1, (ew, (U32.inc(W32.nth0(AR.slots(U32, mT), i)), (W32.nth0(AR.slots(U32, mT), 1n+i), Equal.trans(List<&2, U32>, AR.slots(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), U, SC.update(U32, U, 1n+i, W32.nth0(AR.slots(U32, mT), 1n+i)), s1, Equal.sym(List<&2, U32>, SC.update(U32, U, 1n+i, W32.nth0(AR.slots(U32, mT), 1n+i)), U, eu))))))))

# the low word wraps: the high word is incremented too
def bump_w(+mT: AR.Tree<U32>, +pm: {AR.perfect(U32, 5n, mT) == True{} : Bool}, +c: U32, +i: Nat, +hi: {Nat.is_lt(1n+i, 32n) == True{} : Bool}, +hI: {UD.v(U32.add(16, U32.shl(c))) == i : Nat}, +hJ: {UD.v(U32.add(17, U32.shl(c))) == 1n+i : Nat}, +hz: {U32.is_eq(U32.inc(W32.nth0(AR.slots(U32, mT), i)), 0) == True{} : Bool}) -> BumpOK(mT, i, LR.bump_hi(Array.set(U32, AR.thaw(U32, mT), U32.add(16, U32.shl(c)), U32.inc(W32.nth0(AR.slots(U32, mT), i))), c, True{})):
  +hIb = vlt(U32.add(16, U32.shl(c)), i, hI, lt_i(i, hi))
  +hJb = vlt(U32.add(17, U32.shl(c)), 1n+i, hJ, hi)
  +a1 = UT.uset_a(5n, {==}, mT, pm, U32.add(16, U32.shl(c)), hIb, U32.inc(W32.nth0(AR.slots(U32, mT), i)))
  +p1 = UT.uset_p(5n, mT, pm, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))
  +s1 = s1_of(mT, pm, c, i, hi, hI, hJ)
  +g1 = L.subst(Nat, z => {Array.get(U32, AR.thaw(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), U32.add(17, U32.shl(c))) == (AR.thaw(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), W32.nth0(AR.slots(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), z)) : Array<U32> & U32}, UD.v(U32.add(17, U32.shl(c))), 1n+i, hJ, UT.uget(5n, {==}, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i))), p1, U32.add(17, U32.shl(c)), hJb))
  +eh = MT.nth_other(mT, i, U32.inc(W32.nth0(AR.slots(U32, mT), i)), AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i))), s1, 1n+i, ne_si(i))
  +g2 = Equal.trans(Array<U32> & U32, Array.get(U32, AR.thaw(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), U32.add(17, U32.shl(c))), (AR.thaw(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), W32.nth0(AR.slots(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), 1n+i)), (AR.thaw(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), W32.nth0(AR.slots(U32, mT), 1n+i)), g1, Equal.cong(U32, Array<U32> & U32, z => (AR.thaw(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), z), W32.nth0(AR.slots(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), 1n+i), W32.nth0(AR.slots(U32, mT), 1n+i), eh))
  +a2 = UT.uset_a(5n, {==}, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i))), p1, U32.add(17, U32.shl(c)), hJb, U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i)))
  +p2 = UT.uset_p(5n, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i))), p1, UD.v(U32.add(17, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i)))
  +s2 = Equal.trans(List<&2, U32>, AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i))), UD.v(U32.add(17, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i)))), SC.update(U32, AR.slots(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), UD.v(U32.add(17, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i))), SC.update(U32, AR.slots(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), 1n+i, U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i))), UT.uset_s(5n, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i))), p1, UD.v(U32.add(17, U32.shl(c))), hJb, U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i))), Equal.cong(Nat, List<&2, U32>, z => SC.update(U32, AR.slots(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), z, U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i))), UD.v(U32.add(17, U32.shl(c))), 1n+i, hJ))
  +ea = Equal.trans(Array<U32>, LR.bump_hi_go(U32.add(17, U32.shl(c)), Array.get(U32, Array.set(U32, AR.thaw(U32, mT), U32.add(16, U32.shl(c)), U32.inc(W32.nth0(AR.slots(U32, mT), i))), U32.add(17, U32.shl(c)))), LR.bump_hi_go(U32.add(17, U32.shl(c)), (AR.thaw(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), W32.nth0(AR.slots(U32, mT), 1n+i))), AR.thaw(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i))), UD.v(U32.add(17, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i)))), Equal.trans(Array<U32>, LR.bump_hi_go(U32.add(17, U32.shl(c)), Array.get(U32, Array.set(U32, AR.thaw(U32, mT), U32.add(16, U32.shl(c)), U32.inc(W32.nth0(AR.slots(U32, mT), i))), U32.add(17, U32.shl(c)))), LR.bump_hi_go(U32.add(17, U32.shl(c)), Array.get(U32, AR.thaw(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), U32.add(17, U32.shl(c)))), LR.bump_hi_go(U32.add(17, U32.shl(c)), (AR.thaw(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), W32.nth0(AR.slots(U32, mT), 1n+i))), Equal.cong(Array<U32>, Array<U32>, z => LR.bump_hi_go(U32.add(17, U32.shl(c)), Array.get(U32, z, U32.add(17, U32.shl(c)))), Array.set(U32, AR.thaw(U32, mT), U32.add(16, U32.shl(c)), U32.inc(W32.nth0(AR.slots(U32, mT), i))), AR.thaw(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), a1), Equal.cong(Array<U32> & U32, Array<U32>, z => LR.bump_hi_go(U32.add(17, U32.shl(c)), z), Array.get(U32, AR.thaw(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), U32.add(17, U32.shl(c))), (AR.thaw(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), W32.nth0(AR.slots(U32, mT), 1n+i)), g2)), a2)
  +e0 = Equal.trans(U32, W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i))), UD.v(U32.add(17, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i)))), i), W32.nth0(AR.slots(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), i), U32.inc(W32.nth0(AR.slots(U32, mT), i)), MT.nth_other(AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i))), 1n+i, U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i)), AR.upd(U32, 5n, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i))), UD.v(U32.add(17, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i))), s2, i, N.is_eq_sym_false(i, 1n+i, ne_si(i))), MT.nth_same(5n, mT, pm, i, lt_i(i, hi), U32.inc(W32.nth0(AR.slots(U32, mT), i)), AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i))), s1))
  +e1 = MT.nth_same(5n, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i))), p1, 1n+i, hi, U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i)), AR.upd(U32, 5n, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i))), UD.v(U32.add(17, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i))), s2)
  +r = L.subst(Bool, z => {W.U64{U32.inc(W32.nth0(AR.slots(U32, mT), i)), U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i))} == SP.inc_hi(U32.inc(W32.nth0(AR.slots(U32, mT), i)), W32.nth0(AR.slots(U32, mT), 1n+i), z) : W.U64}, True{}, U32.is_eq(U32.inc(W32.nth0(AR.slots(U32, mT), i)), 0), Equal.sym(Bool, U32.is_eq(U32.inc(W32.nth0(AR.slots(U32, mT), i)), 0), True{}, hz), {==})
  +ew = Equal.trans(W.U64, ST.w64(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i))), UD.v(U32.add(17, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i)))), i), W.U64{U32.inc(W32.nth0(AR.slots(U32, mT), i)), U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i))}, SP.inc64(ST.w64(AR.slots(U32, mT), i)), BA.w64_eq_l(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i))), UD.v(U32.add(17, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i)))), i, U32.inc(W32.nth0(AR.slots(U32, mT), i)), U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i)), e0, e1), r)
  (AR.upd(U32, 5n, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i))), UD.v(U32.add(17, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i))), (ea, (p2, (ew, (U32.inc(W32.nth0(AR.slots(U32, mT), i)), (U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i)), Equal.trans(List<&2, U32>, AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i))), UD.v(U32.add(17, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i)))), SC.update(U32, AR.slots(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), 1n+i, U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i))), SC.update(U32, SC.update(U32, AR.slots(U32, mT), i, U32.inc(W32.nth0(AR.slots(U32, mT), i))), 1n+i, U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i))), s2, Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.update(U32, z, 1n+i, U32.inc(W32.nth0(AR.slots(U32, mT), 1n+i))), AR.slots(U32, AR.upd(U32, 5n, mT, UD.v(U32.add(16, U32.shl(c))), U32.inc(W32.nth0(AR.slots(U32, mT), i)))), SC.update(U32, AR.slots(U32, mT), i, U32.inc(W32.nth0(AR.slots(U32, mT), i))), s1))))))))

def bump_c(+mT: AR.Tree<U32>, +pm: {AR.perfect(U32, 5n, mT) == True{} : Bool}, +c: U32, +i: Nat, +hi: {Nat.is_lt(1n+i, 32n) == True{} : Bool}, +hI: {UD.v(U32.add(16, U32.shl(c))) == i : Nat}, +hJ: {UD.v(U32.add(17, U32.shl(c))) == 1n+i : Nat}, +z: Bool, +hz: {U32.is_eq(U32.inc(W32.nth0(AR.slots(U32, mT), i)), 0) == z : Bool}) -> BumpOK(mT, i, LR.bump_hi(Array.set(U32, AR.thaw(U32, mT), U32.add(16, U32.shl(c)), U32.inc(W32.nth0(AR.slots(U32, mT), i))), c, z)):
  match z:
    case False{}:
      bump_nw(mT, pm, c, i, hi, hI, hJ, hz)
    case True{}:
      bump_w(mT, pm, c, i, hi, hI, hJ, hz)

# THEOREM (bump): counter c's words i, i + 1 become the 64-bit increment of
# their value; every other meta word is kept.
def bump_ok(+mT: AR.Tree<U32>, +pm: {AR.perfect(U32, 5n, mT) == True{} : Bool}, +c: U32, +i: Nat, +hi: {Nat.is_lt(1n+i, 32n) == True{} : Bool}, +hI: {UD.v(U32.add(16, U32.shl(c))) == i : Nat}, +hJ: {UD.v(U32.add(17, U32.shl(c))) == 1n+i : Nat}) -> BumpOK(mT, i, LR.bump(c, AR.thaw(U32, mT))):
  +hIb = vlt(U32.add(16, U32.shl(c)), i, hI, lt_i(i, hi))
  +g = L.subst(Nat, z => {Array.get(U32, AR.thaw(U32, mT), U32.add(16, U32.shl(c))) == (AR.thaw(U32, mT), W32.nth0(AR.slots(U32, mT), z)) : Array<U32> & U32}, UD.v(U32.add(16, U32.shl(c))), i, hI, UT.uget(5n, {==}, mT, pm, U32.add(16, U32.shl(c)), hIb))
  +E = Equal.cong(Array<U32> & U32, Array<U32>, r => LR.bump_lo(c, r), Array.get(U32, AR.thaw(U32, mT), U32.add(16, U32.shl(c))), (AR.thaw(U32, mT), W32.nth0(AR.slots(U32, mT), i)), g)
  L.subst(Array<U32>, r => BumpOK(mT, i, r), LR.bump_lo(c, (AR.thaw(U32, mT), W32.nth0(AR.slots(U32, mT), i))), LR.bump(c, AR.thaw(U32, mT)), Equal.sym(Array<U32>, LR.bump(c, AR.thaw(U32, mT)), LR.bump_lo(c, (AR.thaw(U32, mT), W32.nth0(AR.slots(U32, mT), i))), E), bump_c(mT, pm, c, i, hi, hI, hJ, U32.is_eq(U32.inc(W32.nth0(AR.slots(U32, mT), i)), 0), {==}))
