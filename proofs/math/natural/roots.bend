import Base
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../../spec/lib/common.bend as SC
import ../../lib/lemmas/proofs/nat_algebra.bend as A
import ../../lib/lemmas/proofs/natural_products.bend as PR
import ../../../src/math/natural.bend as M
import ../../../src/math/pow2.bend as P2
import ../pow2/pow2.bend as PP
import ./arith.bend as R
import ./lcm.bend as LC
import ./fact.bend as F
import ./bits.bend as B

# iroot is the exact integer root: r^k <= n < (r + 1)^k for
# r = iroot(n, k), k >= 1, so r is the floor of the k-th root. Statement
# shape of Lean 4 Mathlib Mathlib/Data/Nat/Sqrt (Nat.sqrt_le',
# Nat.lt_succ_sqrt'), for every k; the binary-search proof follows the Why3 gallery's
# isqrt (loop invariant lo^2 <= n < hi^2 with a shrinking interval).

# ---- the power test r^k <= n ----

def pow_pos(+rp: Nat, +j: Nat) -> {Nat.is_lt(0n, Nat.pow(1n+rp, j)) == True{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+ +jp:
      F.pos_mul(rp, Nat.pow(1n+rp, jp), pow_pos(rp, jp))

# x <= x y for y > 0
def le_mul_pos(+x: Nat, +y: Nat, +hy: {Nat.is_lt(0n, y) == True{} : Bool}) -> {Nat.is_le(x, Nat.mul(x, y)) == True{} : Bool}:
  match y:
    case 0n:
      Empty.absurd({Nat.is_le(x, Nat.mul(x, 0n)) == True{} : Bool}, L.false_true(hy))
    case 1n+ +yp:
      %Equal.sym(Nat, Nat.mul(x, 1n+yp), Nat.add(x, Nat.mul(x, yp)), A.mul_succ(x, yp)) : {Nat.is_le(x, _) == True{} : Bool}
      N.le_add_right(x, Nat.mul(x, yp))

# the division-guarded loop computes (acc r) r^j <= n
def pow_le_case(+j: Nat, +rp: Nat, +acc: Nat, +n: Nat, +ok: Bool, +hk: {ok == Nat.is_le(Nat.mul(acc, 1n+rp), n) : Bool}) -> {M.pow_le_go(1n+j, 1n+rp, acc, n, ok) == Nat.is_le(Nat.mul(Nat.mul(acc, 1n+rp), Nat.pow(1n+rp, j)), n) : Bool}:
  match j ok:
    case 0n False{}:
      Equal.sym(Bool, Nat.is_le(Nat.mul(Nat.mul(acc, 1n+rp), 1n), n), False{}, Equal.trans(Bool, Nat.is_le(Nat.mul(Nat.mul(acc, 1n+rp), 1n), n), Nat.is_le(Nat.mul(acc, 1n+rp), n), False{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, n), Nat.mul(Nat.mul(acc, 1n+rp), 1n), Nat.mul(acc, 1n+rp), A.mul_one(Nat.mul(acc, 1n+rp))), Equal.sym(Bool, False{}, Nat.is_le(Nat.mul(acc, 1n+rp), n), hk)))
    case 1n+ +jp False{}:
      +big = N.not_le_lt(Nat.mul(acc, 1n+rp), n, Equal.sym(Bool, False{}, Nat.is_le(Nat.mul(acc, 1n+rp), n), hk))
      Equal.sym(Bool, Nat.is_le(Nat.mul(Nat.mul(acc, 1n+rp), Nat.pow(1n+rp, 1n+jp)), n), False{}, N.lt_not_le(n, Nat.mul(Nat.mul(acc, 1n+rp), Nat.pow(1n+rp, 1n+jp)), N.lt_le_trans(n, Nat.mul(acc, 1n+rp), Nat.mul(Nat.mul(acc, 1n+rp), Nat.pow(1n+rp, 1n+jp)), big, le_mul_pos(Nat.mul(acc, 1n+rp), Nat.pow(1n+rp, 1n+jp), pow_pos(rp, 1n+jp)))))
    case 0n True{}:
      Equal.trans(Bool, True{}, Nat.is_le(Nat.mul(acc, 1n+rp), n), Nat.is_le(Nat.mul(Nat.mul(acc, 1n+rp), 1n), n), hk, Equal.cong(Nat, Bool, z => Nat.is_le(z, n), Nat.mul(acc, 1n+rp), Nat.mul(Nat.mul(acc, 1n+rp), 1n), Equal.sym(Nat, Nat.mul(Nat.mul(acc, 1n+rp), 1n), Nat.mul(acc, 1n+rp), A.mul_one(Nat.mul(acc, 1n+rp)))))
    case 1n+ +jp True{}:
      +ar = Nat.mul(acc, 1n+rp)
      %Equal.sym(Nat, Nat.mul(ar, Nat.mul(1n+rp, Nat.pow(1n+rp, jp))), Nat.mul(Nat.mul(ar, 1n+rp), Nat.pow(1n+rp, jp)), Equal.sym(Nat, Nat.mul(Nat.mul(ar, 1n+rp), Nat.pow(1n+rp, jp)), Nat.mul(ar, Nat.mul(1n+rp, Nat.pow(1n+rp, jp))), A.mul_assoc(ar, 1n+rp, Nat.pow(1n+rp, jp)))) : {M.pow_le_go(1n+jp, 1n+rp, ar, n, Nat.is_le(ar, Nat.div(n, 1n+rp))) == Nat.is_le(_, n) : Bool}
      pow_le_case(jp, rp, ar, n, Nat.is_le(ar, Nat.div(n, 1n+rp)), R.le_div(rp, ar, n))

# root_le(n, k, r) is r^k <= n
def root_le_ok(+n: Nat, +k: Nat, +r: Nat) -> {M.root_le(n, k, r) == Nat.is_le(Nat.pow(r, k), n) : Bool}:
  match k r:
    case 0n r0:
      {==}
    case 1n+ +kp 0n:
      Equal.sym(Bool, Nat.is_le(0n, n), True{}, N.zero_le(n))
    case 1n+ +kp 1n+ +rp:
      +c = pow_le_case(kp, rp, 1n, n, Nat.is_le(1n, Nat.div(n, 1n+rp)), R.le_div(rp, 1n, n))
      %Equal.sym(Nat, Nat.pow(1n+rp, 1n+kp), Nat.mul(Nat.mul(1n, 1n+rp), Nat.pow(1n+rp, kp)), Equal.cong(Nat, Nat, z => Nat.mul(z, Nat.pow(1n+rp, kp)), 1n+rp, Nat.mul(1n, 1n+rp), Equal.sym(Nat, Nat.mul(1n, 1n+rp), 1n+rp, LC.one_mul(1n+rp)))) : {M.root_le(n, 1n+kp, 1n+rp) == Nat.is_le(_, n) : Bool}
      c

# ---- the search interval ----

# x 2 == x + x
def two_mul(+x: Nat) -> {Nat.mul(x, 2n) == Nat.add(x, x) : Nat}:
  Equal.trans(Nat, Nat.mul(x, 2n), Nat.mul(2n, x), Nat.add(x, x), A.mul_comm(x, 2n), Equal.cong(Nat, Nat, z => Nat.add(x, z), Nat.add(x, 0n), x, A.add_zero(x)))

# lo + 1 < hi gives lo < (lo + hi) / 2
def lo_lt_mid(+lo: Nat, +hi: Nat, +h: {Nat.is_lt(1n+lo, hi) == True{} : Bool}) -> {Nat.is_lt(lo, M.mid(lo, hi)) == True{} : Bool}:
  +e = Equal.trans(Bool, Nat.is_le(1n+lo, M.mid(lo, hi)), Nat.is_le(Nat.mul(1n+lo, 2n), Nat.add(lo, hi)), Nat.is_le(Nat.add(2n, lo), hi), R.le_div(1n, 1n+lo, Nat.add(lo, hi)),
    Equal.trans(Bool, Nat.is_le(Nat.mul(1n+lo, 2n), Nat.add(lo, hi)), Nat.is_le(Nat.add(lo, Nat.add(2n, lo)), Nat.add(lo, hi)), Nat.is_le(Nat.add(2n, lo), hi),
      Equal.cong(Nat, Bool, z => Nat.is_le(z, Nat.add(lo, hi)), Nat.mul(1n+lo, 2n), Nat.add(lo, Nat.add(2n, lo)), Equal.trans(Nat, Nat.mul(1n+lo, 2n), Nat.add(2n, Nat.add(lo, lo)), Nat.add(lo, Nat.add(2n, lo)), Equal.cong(Nat, Nat, z => Nat.add(2n, z), Nat.mul(lo, 2n), Nat.add(lo, lo), two_mul(lo)), A.add_swap(2n, lo, lo))),
      R.le_add_cancel(lo, Nat.add(2n, lo), hi)))
  N.succ_le_lt(lo, M.mid(lo, hi), Equal.trans(Bool, Nat.is_le(1n+lo, M.mid(lo, hi)), Nat.is_le(Nat.add(2n, lo), hi), True{}, e, N.lt_succ_le_succ(1n+lo, hi, h)))

# lo < hi gives (lo + hi) / 2 < hi
def mid_lt_hi(+lo: Nat, +hi: Nat, +h: {Nat.is_lt(lo, hi) == True{} : Bool}) -> {Nat.is_lt(M.mid(lo, hi), hi) == True{} : Bool}:
  +e = Equal.trans(Bool, Nat.is_le(hi, M.mid(lo, hi)), Nat.is_le(Nat.mul(hi, 2n), Nat.add(lo, hi)), False{}, R.le_div(1n, hi, Nat.add(lo, hi)),
    Equal.trans(Bool, Nat.is_le(Nat.mul(hi, 2n), Nat.add(lo, hi)), Nat.is_le(Nat.add(hi, hi), Nat.add(hi, lo)), False{},
      Equal.trans(Bool, Nat.is_le(Nat.mul(hi, 2n), Nat.add(lo, hi)), Nat.is_le(Nat.add(hi, hi), Nat.add(lo, hi)), Nat.is_le(Nat.add(hi, hi), Nat.add(hi, lo)), Equal.cong(Nat, Bool, z => Nat.is_le(z, Nat.add(lo, hi)), Nat.mul(hi, 2n), Nat.add(hi, hi), two_mul(hi)), Equal.cong(Nat, Bool, z => Nat.is_le(Nat.add(hi, hi), z), Nat.add(lo, hi), Nat.add(hi, lo), A.add_comm(lo, hi))),
      Equal.trans(Bool, Nat.is_le(Nat.add(hi, hi), Nat.add(hi, lo)), Nat.is_le(hi, lo), False{}, R.le_add_cancel(hi, hi, lo), N.lt_not_le(lo, hi, h))))
  N.not_le_lt(hi, M.mid(lo, hi), e)

# b < c <= a gives a - c < a - b
def lt_sub(+a: Nat, +b: Nat, +c: Nat, +h1: {Nat.is_lt(b, c) == True{} : Bool}, +h2: {Nat.is_le(c, a) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(a, c), Nat.sub(a, b)) == True{} : Bool}:
  match a b c:
    case 0n 0n 0n:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, 0n), Nat.sub(0n, 0n)) == True{} : Bool}, L.false_true(h1))
    case 0n 0n 1n+cp:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, 1n+cp), Nat.sub(0n, 0n)) == True{} : Bool}, L.false_true(h2))
    case 0n 1n+bp 0n:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, 0n), Nat.sub(0n, 1n+bp)) == True{} : Bool}, L.false_true(h1))
    case 0n 1n+bp 1n+cp:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, 1n+cp), Nat.sub(0n, 1n+bp)) == True{} : Bool}, L.false_true(h2))
    case 1n+ap 0n 0n:
      Empty.absurd({Nat.is_lt(Nat.sub(1n+ap, 0n), Nat.sub(1n+ap, 0n)) == True{} : Bool}, L.false_true(h1))
    case 1n+ +ap 0n 1n+ +cp:
      N.le_lt_succ(Nat.sub(ap, cp), ap, F.sub_le_self(ap, cp))
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.is_lt(Nat.sub(1n+ap, 0n), Nat.sub(1n+ap, 1n+bp)) == True{} : Bool}, L.false_true(h1))
    case 1n+ +ap 1n+ +bp 1n+ +cp:
      lt_sub(ap, bp, cp, h1, h2)

# a < b and c <= a give a - c < b - c
def lt_sub2(+a: Nat, +b: Nat, +c: Nat, +h1: {Nat.is_lt(a, b) == True{} : Bool}, +h2: {Nat.is_le(c, a) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(a, c), Nat.sub(b, c)) == True{} : Bool}:
  match a b c:
    case 0n 0n c0:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, c0), Nat.sub(0n, c0)) == True{} : Bool}, L.false_true(h1))
    case 0n 1n+bp 0n:
      {==}
    case 0n 1n+bp 1n+cp:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, 1n+cp), Nat.sub(1n+bp, 1n+cp)) == True{} : Bool}, L.false_true(h2))
    case 1n+ap 0n c0:
      Empty.absurd({Nat.is_lt(Nat.sub(1n+ap, c0), Nat.sub(0n, c0)) == True{} : Bool}, L.false_true(h1))
    case 1n+ap 1n+bp 0n:
      h1
    case 1n+ +ap 1n+ +bp 1n+ +cp:
      lt_sub2(ap, bp, cp, h1, h2)

# lo < hi gives 0 < hi - lo
def sub_pos(+lo: Nat, +hi: Nat, +h: {Nat.is_lt(lo, hi) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.sub(hi, lo)) == True{} : Bool}:
  match lo hi:
    case lo0 0n:
      Empty.absurd({Nat.is_lt(0n, Nat.sub(0n, lo0)) == True{} : Bool}, N.lt_zero_absurd(lo0, h))
    case 0n 1n+hp:
      {==}
    case 1n+ +lp 1n+ +hp:
      sub_pos(lp, hp, h)

# ---- the search ----

# the answer r: r^k <= n < (r + 1)^k, through root_le
def root_ok(+n: Nat, +k: Nat, +r: Nat) -> Type:
  {M.root_le(n, k, r) == True{} : Bool} & {M.root_le(n, k, 1n+r) == False{} : Bool}

def no_fuel(+lo: Nat, +hi: Nat, +hlt: {Nat.is_lt(lo, hi) == True{} : Bool}, +hf: {Nat.is_le(Nat.sub(hi, lo), 0n) == True{} : Bool}) -> Empty:
  N.lt_zero_absurd(0n, N.lt_le_trans(0n, Nat.sub(hi, lo), 0n, sub_pos(lo, hi, hlt), hf))

# lo + 1 >= hi with lo < hi: the interval is [lo, lo + 1)
def done_ok(+n: Nat, +k: Nat, +lo: Nat, +hi: Nat, +hlo: {M.root_le(n, k, lo) == True{} : Bool}, +hhi: {M.root_le(n, k, hi) == False{} : Bool}, +hlt: {Nat.is_lt(lo, hi) == True{} : Bool}, +hm: {False{} == Nat.is_lt(1n+lo, hi) : Bool}) -> root_ok(n, k, lo):
  +e = N.le_antisym(hi, 1n+lo, N.not_lt_le(1n+lo, hi, Equal.sym(Bool, False{}, Nat.is_lt(1n+lo, hi), hm)), N.lt_succ_le_succ(lo, hi, hlt))
  (hlo, Equal.trans(Bool, M.root_le(n, k, 1n+lo), M.root_le(n, k, hi), False{}, Equal.cong(Nat, Bool, z => M.root_le(n, k, z), 1n+lo, hi, Equal.sym(Nat, hi, 1n+lo, e)), hhi))

# the interval shrinks: a step fits in the remaining fuel
def shrink(+x: Nat, +y: Nat, +f: Nat, +h: {Nat.is_lt(x, y) == True{} : Bool}, +hf: {Nat.is_le(y, 1n+f) == True{} : Bool}) -> {Nat.is_le(x, f) == True{} : Bool}:
  N.lt_succ_le(x, f, N.lt_le_trans(x, y, 1n+f, h, hf))

def search_ok(fuel: Nat, +n: Nat, +k: Nat, +lo: Nat, +hi: Nat, +more: Bool, +ok: Bool, +hlo: {M.root_le(n, k, lo) == True{} : Bool}, +hhi: {M.root_le(n, k, hi) == False{} : Bool}, +hlt: {Nat.is_lt(lo, hi) == True{} : Bool}, +hf: {Nat.is_le(Nat.sub(hi, lo), fuel) == True{} : Bool}, +hm: {more == Nat.is_lt(1n+lo, hi) : Bool}, +hok: {ok == M.root_le(n, k, M.mid(lo, hi)) : Bool}) -> root_ok(n, k, M.search_go(fuel, n, k, lo, hi, more, ok)):
  match fuel more ok:
    case 0n False{} False{}:
      Empty.absurd(root_ok(n, k, M.search_go(0n, n, k, lo, hi, False{}, False{})), no_fuel(lo, hi, hlt, hf))
    case 0n False{} True{}:
      Empty.absurd(root_ok(n, k, M.search_go(0n, n, k, lo, hi, False{}, True{})), no_fuel(lo, hi, hlt, hf))
    case 0n True{} False{}:
      Empty.absurd(root_ok(n, k, M.search_go(0n, n, k, lo, hi, True{}, False{})), no_fuel(lo, hi, hlt, hf))
    case 0n True{} True{}:
      Empty.absurd(root_ok(n, k, M.search_go(0n, n, k, lo, hi, True{}, True{})), no_fuel(lo, hi, hlt, hf))
    case 1n+f False{} False{}:
      done_ok(n, k, lo, hi, hlo, hhi, hlt, hm)
    case 1n+f False{} True{}:
      done_ok(n, k, lo, hi, hlo, hhi, hlt, hm)
    case 1n+ +f True{} True{}:
      +m = M.mid(lo, hi)
      +hml = lo_lt_mid(lo, hi, Equal.sym(Bool, True{}, Nat.is_lt(1n+lo, hi), hm))
      +hmh = mid_lt_hi(lo, hi, hlt)
      search_ok(f, n, k, m, hi, Nat.is_lt(1n+m, hi), M.root_le(n, k, M.mid(m, hi)), Equal.sym(Bool, True{}, M.root_le(n, k, m), hok), hhi, hmh, shrink(Nat.sub(hi, m), Nat.sub(hi, lo), f, lt_sub(hi, lo, m, hml, N.lt_le(m, hi, hmh)), hf), {==}, {==})
    case 1n+ +f True{} False{}:
      +m = M.mid(lo, hi)
      +hml = lo_lt_mid(lo, hi, Equal.sym(Bool, True{}, Nat.is_lt(1n+lo, hi), hm))
      +hmh = mid_lt_hi(lo, hi, hlt)
      search_ok(f, n, k, lo, m, Nat.is_lt(1n+lo, m), M.root_le(n, k, M.mid(lo, m)), hlo, Equal.sym(Bool, False{}, M.root_le(n, k, m), hok), hml, shrink(Nat.sub(m, lo), Nat.sub(hi, lo), f, lt_sub2(m, hi, lo, hmh, N.lt_le(lo, m, hml)), hf), {==}, {==})

def search_top(+n: Nat, +k: Nat, +lo: Nat, +hi: Nat, +hlo: {M.root_le(n, k, lo) == True{} : Bool}, +hhi: {M.root_le(n, k, hi) == False{} : Bool}, +hlt: {Nat.is_lt(lo, hi) == True{} : Bool}) -> root_ok(n, k, M.search(n, k, lo, hi)):
  search_ok(Nat.sub(hi, lo), n, k, lo, hi, Nat.is_lt(1n+lo, hi), M.root_le(n, k, M.mid(lo, hi)), hlo, hhi, hlt, N.le_refl(Nat.sub(hi, lo)), {==}, {==})

# ---- the initial bound hi = 2^(1 + L/k), L = bit_length(n) ----

# 2^(x + y) == 2^x 2^y
def pow2_add(+x: Nat, +y: Nat) -> {SC.pow2(Nat.add(x, y)) == Nat.mul(SC.pow2(x), SC.pow2(y)) : Nat}:
  match x:
    case 0n:
      Equal.sym(Nat, Nat.mul(1n, SC.pow2(y)), SC.pow2(y), LC.one_mul(SC.pow2(y)))
    case 1n+ +xp:
      Equal.trans(Nat, Nat.double(SC.pow2(Nat.add(xp, y))), Nat.double(Nat.mul(SC.pow2(xp), SC.pow2(y))), Nat.mul(Nat.double(SC.pow2(xp)), SC.pow2(y)),
        Equal.cong(Nat, Nat, z => Nat.double(z), SC.pow2(Nat.add(xp, y)), Nat.mul(SC.pow2(xp), SC.pow2(y)), pow2_add(xp, y)),
        Equal.sym(Nat, Nat.mul(Nat.double(SC.pow2(xp)), SC.pow2(y)), Nat.double(Nat.mul(SC.pow2(xp), SC.pow2(y))), PR.double_product(SC.pow2(xp), SC.pow2(y))))

# (2^a)^k == 2^(k a)
def pow_pow2(+a: Nat, +k: Nat) -> {Nat.pow(SC.pow2(a), k) == SC.pow2(Nat.mul(k, a)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +kp:
      Equal.trans(Nat, Nat.mul(SC.pow2(a), Nat.pow(SC.pow2(a), kp)), Nat.mul(SC.pow2(a), SC.pow2(Nat.mul(kp, a))), SC.pow2(Nat.add(a, Nat.mul(kp, a))),
        Equal.cong(Nat, Nat, z => Nat.mul(SC.pow2(a), z), Nat.pow(SC.pow2(a), kp), SC.pow2(Nat.mul(kp, a)), pow_pow2(a, kp)),
        Equal.sym(Nat, SC.pow2(Nat.add(a, Nat.mul(kp, a))), Nat.mul(SC.pow2(a), SC.pow2(Nat.mul(kp, a))), pow2_add(a, Nat.mul(kp, a))))

# L <= k (1 + L / k)
def bl_le(+kp: Nat, +bl: Nat) -> {Nat.is_le(bl, Nat.mul(1n+kp, 1n+Nat.div(bl, 1n+kp))) == True{} : Bool}:
  +k = {1n+kp : Nat}
  +q = Nat.div(bl, k)
  +r = Nat.mod(bl, k)
  %Equal.sym(Nat, bl, Nat.add(Nat.mul(q, k), r), R.dm_eq(kp, bl)) : {Nat.is_le(_, Nat.mul(k, 1n+q)) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(k, 1n+q), Nat.add(k, Nat.mul(k, q)), A.mul_succ(k, q)) : {Nat.is_le(Nat.add(Nat.mul(q, k), r), _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(k, Nat.mul(k, q)), Nat.add(Nat.mul(q, k), k), Equal.trans(Nat, Nat.add(k, Nat.mul(k, q)), Nat.add(Nat.mul(k, q), k), Nat.add(Nat.mul(q, k), k), A.add_comm(k, Nat.mul(k, q)), Equal.cong(Nat, Nat, z => Nat.add(z, k), Nat.mul(k, q), Nat.mul(q, k), A.mul_comm(k, q)))) : {Nat.is_le(Nat.add(Nat.mul(q, k), r), _) == True{} : Bool}
  N.lt_le(Nat.add(Nat.mul(q, k), r), Nat.add(Nat.mul(q, k), k), N.lt_add_left(r, k, Nat.mul(q, k), R.dm_lt(kp, bl)))

# n < (2^(1 + L/k))^k
def hi_bound(+n: Nat, +kp: Nat) -> {M.root_le(n, 1n+kp, P2.pow2t(1n+Nat.div(M.bit_length(n), 1n+kp))) == False{} : Bool}:
  +k = {1n+kp : Nat}
  +a = {1n+Nat.div(M.bit_length(n), k) : Nat}
  +big = N.lt_le_trans(n, SC.pow2(M.bit_length(n)), SC.pow2(Nat.mul(k, a)), B.bit_length_lt(n), N.pow2_mono(M.bit_length(n), Nat.mul(k, a), bl_le(kp, M.bit_length(n))))
  %Equal.sym(Nat, P2.pow2t(a), SC.pow2(a), PP.same(a)) : {M.root_le(n, k, _) == False{} : Bool}
  %Equal.sym(Bool, M.root_le(n, k, SC.pow2(a)), Nat.is_le(Nat.pow(SC.pow2(a), k), n), root_le_ok(n, k, SC.pow2(a))) : {_ == False{} : Bool}
  %Equal.sym(Nat, Nat.pow(SC.pow2(a), k), SC.pow2(Nat.mul(k, a)), pow_pow2(a, k)) : {Nat.is_le(_, n) == False{} : Bool}
  N.lt_not_le(n, SC.pow2(Nat.mul(k, a)), big)

def hi_pos(+a: Nat) -> {Nat.is_lt(0n, P2.pow2t(a)) == True{} : Bool}:
  %Equal.sym(Nat, P2.pow2t(a), SC.pow2(a), PP.same(a)) : {Nat.is_lt(0n, _) == True{} : Bool}
  N.succ_le_lt(0n, SC.pow2(a), N.pow2_pos(a))

def root_top(+n: Nat, +kp: Nat) -> root_ok(n, 1n+kp, M.search(n, 1n+kp, 0n, P2.pow2t(1n+Nat.div(M.bit_length(n), 1n+kp)))):
  search_top(n, 1n+kp, 0n, P2.pow2t(1n+Nat.div(M.bit_length(n), 1n+kp)), {==}, hi_bound(n, kp), hi_pos(1n+Nat.div(M.bit_length(n), 1n+kp)))

# ---- the theorems ----

def ok_le(+n: Nat, +k: Nat, +r: Nat, p: root_ok(n, k, r)) -> {Nat.is_le(Nat.pow(r, k), n) == True{} : Bool}:
  (a, b) = p
  Equal.trans(Bool, Nat.is_le(Nat.pow(r, k), n), M.root_le(n, k, r), True{}, Equal.sym(Bool, M.root_le(n, k, r), Nat.is_le(Nat.pow(r, k), n), root_le_ok(n, k, r)), a)

def ok_lt(+n: Nat, +k: Nat, +r: Nat, p: root_ok(n, k, r)) -> {Nat.is_lt(n, Nat.pow(1n+r, k)) == True{} : Bool}:
  (a, b) = p
  N.not_le_lt(Nat.pow(1n+r, k), n, Equal.trans(Bool, Nat.is_le(Nat.pow(1n+r, k), n), M.root_le(n, k, 1n+r), False{}, Equal.sym(Bool, M.root_le(n, k, 1n+r), Nat.is_le(Nat.pow(1n+r, k), n), root_le_ok(n, k, 1n+r)), b))

def iroot_k_ok(+n: Nat, +kp: Nat) -> root_ok(n, 1n+kp, M.iroot_k(n, 1n+kp)):
  match kp:
    case 0n:
      (Equal.trans(Bool, M.root_le(n, 1n, n), Nat.is_le(Nat.mul(n, 1n), n), True{}, root_le_ok(n, 1n, n), Equal.trans(Bool, Nat.is_le(Nat.mul(n, 1n), n), Nat.is_le(n, n), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, n), Nat.mul(n, 1n), n, A.mul_one(n)), N.le_refl(n))),
       Equal.trans(Bool, M.root_le(n, 1n, 1n+n), Nat.is_le(Nat.mul(1n+n, 1n), n), False{}, root_le_ok(n, 1n, 1n+n), Equal.trans(Bool, Nat.is_le(Nat.mul(1n+n, 1n), n), Nat.is_le(1n+n, n), False{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, n), Nat.mul(1n+n, 1n), 1n+n, A.mul_one(1n+n)), N.lt_not_le(n, 1n+n, N.lt_succ(n)))))
    case 1n+ +kq:
      root_top(n, 1n+kq)

# iroot(n, k) == Done{r} with r^k <= n < (r + 1)^k for k >= 1, Domain for k == 0
def iroot_done(+n: Nat, +kp: Nat) -> {M.iroot(n, 1n+kp) == Done{M.iroot_k(n, 1n+kp)} : Result<&2, &2, M.MathError, Nat>}:
  {==}

def iroot_zero(+n: Nat) -> {M.iroot(n, 0n) == Fail{M.Domain{}} : Result<&2, &2, M.MathError, Nat>}:
  {==}

def iroot_le(+n: Nat, +kp: Nat) -> {Nat.is_le(Nat.pow(M.iroot_k(n, 1n+kp), 1n+kp), n) == True{} : Bool}:
  ok_le(n, 1n+kp, M.iroot_k(n, 1n+kp), iroot_k_ok(n, kp))

def lt_succ_iroot(+n: Nat, +kp: Nat) -> {Nat.is_lt(n, Nat.pow(1n+M.iroot_k(n, 1n+kp), 1n+kp)) == True{} : Bool}:
  ok_lt(n, 1n+kp, M.iroot_k(n, 1n+kp), iroot_k_ok(n, kp))
