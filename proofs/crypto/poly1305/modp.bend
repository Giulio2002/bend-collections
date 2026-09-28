import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/poly1305.bend as R
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/arith.bend as AR
import ../../lib/u32alg.bend as UA
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/typed/width.bend as WW
import ../../math/typed/w64mul.bend as WM
import ../../math/typed/w64sh.bend as SH
import ../../math/natural/arith.bend as NR
import ./arith.bend as A

# spec/crypto/poly1305.bend's modp(x) is x mod p. The modulus is written
# 1 + bp with 1 + bp + 5 == 2^130 == C.shift(130n, one), one == 1 (the checker
# expands a closed 2^130 in unary, so neither is ever closed).

law bigp:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +bp: Nat
  for +h5: {Nat.add(1n+bp, 5n) == C.shift(130n, one) : Nat}
  for +x: Nat
  {C.shift(130n, x) == Nat.add(Nat.mul(x, 1n+bp), Nat.mul(x, 5n)) : Nat}

def bigp(one, h1, bp, h5, x):
  A.tr(C.shift(130n, x), Nat.mul(x, C.shift(130n, one)), Nat.add(Nat.mul(x, 1n+bp), Nat.mul(x, 5n)), WW.shift_mul_one(130n, one, h1, x),
    A.tr(Nat.mul(x, C.shift(130n, one)), Nat.mul(x, Nat.add(1n+bp, 5n)), Nat.add(Nat.mul(x, 1n+bp), Nat.mul(x, 5n)),
      Equal.cong(Nat, Nat, t => Nat.mul(x, t), C.shift(130n, one), Nat.add(1n+bp, 5n), A.sy(Nat.add(1n+bp, 5n), C.shift(130n, one), h5)),
      NA.mul_add_left(x, 1n+bp, 5n)))

# x == hi p + fold(x)
law fold_eq:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +bp: Nat
  for +h5: {Nat.add(1n+bp, 5n) == C.shift(130n, one) : Nat}
  for +x: Nat
  {x == Nat.add(Nat.mul(C.high(130n, x), 1n+bp), R.fold(x)) : Nat}

def fold_eq(one, h1, bp, h5, x):
  +lo = C.low(130n, x)
  +hi = C.high(130n, x)
  A.tr(x, Nat.add(lo, C.shift(130n, hi)), Nat.add(Nat.mul(hi, 1n+bp), Nat.add(lo, Nat.mul(hi, 5n))), WW.low_high(130n, x),
    A.tr(Nat.add(lo, C.shift(130n, hi)), Nat.add(lo, Nat.add(Nat.mul(hi, 1n+bp), Nat.mul(hi, 5n))), Nat.add(Nat.mul(hi, 1n+bp), Nat.add(lo, Nat.mul(hi, 5n))),
      WM.cong_r(lo, C.shift(130n, hi), Nat.add(Nat.mul(hi, 1n+bp), Nat.mul(hi, 5n)), bigp(one, h1, bp, h5, hi)),
      NA.add_swap(lo, Nat.mul(hi, 1n+bp), Nat.mul(hi, 5n))))

law fold_mod:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +bp: Nat
  for +h5: {Nat.add(1n+bp, 5n) == C.shift(130n, one) : Nat}
  for +x: Nat
  {Nat.mod(R.fold(x), 1n+bp) == Nat.mod(x, 1n+bp) : Nat}

def fold_mod(one, h1, bp, h5, x):
  +hi = C.high(130n, x)
  A.sy(Nat.mod(x, 1n+bp), Nat.mod(R.fold(x), 1n+bp),
    A.tr(Nat.mod(x, 1n+bp), Nat.mod(Nat.add(Nat.mul(hi, 1n+bp), R.fold(x)), 1n+bp), Nat.mod(R.fold(x), 1n+bp),
      Equal.cong(Nat, Nat, t => Nat.mod(t, 1n+bp), x, Nat.add(Nat.mul(hi, 1n+bp), R.fold(x)), fold_eq(one, h1, bp, h5, x)),
      NR.absorb(bp, hi, R.fold(x))))

law folds_mod:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +bp: Nat
  for +h5: {Nat.add(1n+bp, 5n) == C.shift(130n, one) : Nat}
  for +n: Nat
  for +x: Nat
  {Nat.mod(R.folds(n, x), 1n+bp) == Nat.mod(x, 1n+bp) : Nat}

def folds_mod(one, h1, bp, h5, n, x):
  match n:
    case 0n: {==}
    case 1n+k: A.tr(Nat.mod(R.folds(k, R.fold(x)), 1n+bp), Nat.mod(R.fold(x), 1n+bp), Nat.mod(x, 1n+bp), folds_mod(one, h1, bp, h5, k, R.fold(x)), fold_mod(one, h1, bp, h5, x))

# a fold on x < k + 1 + 2^130 gives a value below k + 2^130
def fold_lt_c(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +h5: {Nat.add(1n+bp, 5n) == C.shift(130n, one) : Nat}, +k: Nat, +x: Nat, +h: {Nat.is_lt(x, Nat.add(1n+k, C.shift(130n, one))) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(C.high(130n, x), 0n) == c : Bool}) -> {Nat.is_lt(R.fold(x), Nat.add(k, C.shift(130n, one))) == True{} : Bool}:
  match c:
    case True{}:
      +s = C.shift(130n, one)
      +hi = C.high(130n, x)
      +lo = C.low(130n, x)
      +h0 = N.eq_from_is_eq(hi, 0n, hc)
      +ef = A.tr(R.fold(x), Nat.add(lo, Nat.mul(0n, 5n)), x, WM.cong_r(lo, Nat.mul(hi, 5n), Nat.mul(0n, 5n), Equal.cong(Nat, Nat, t => Nat.mul(t, 5n), hi, 0n, h0)),
        A.tr(Nat.add(lo, 0n), lo, x, N.add_zero(lo), WW.low_fit(130n, x, hc)))
      A.lt_substl(x, R.fold(x), Nat.add(k, s), A.sy(R.fold(x), x, ef), N.lt_le_trans(x, s, Nat.add(k, s), WW.lt_one(130n, one, h1, x, hc), A.le_add_l(k, s)))
    case False{}:
      +s = C.shift(130n, one)
      +hi = C.high(130n, x)
      +lo = C.low(130n, x)
      +f = R.fold(x)
      +hp = Nat.mul(hi, 1n+bp)
      +h1h = N.lt_succ_le_succ(0n, hi, N.lt_or_eq(0n, hi, N.zero_le(hi), N.is_eq_sym_false(hi, 0n, hc)))
      +hp1b = A.le_substl(Nat.mul(1n, 1n+bp), 1n+bp, hp, AR.one_mul(1n+bp), AR.mul_le(1n, hi, 1n+bp, h1h))
      +lx = A.le_subst(1n+f, Nat.add(hp, f), x, A.sy(x, Nat.add(hp, f), fold_eq(one, h1, bp, h5, x)), WW.le_add_r(1n, hp, f, N.le_trans(1n, 1n+bp, hp, N.zero_le(bp), hp1b)))
      N.lt_le_trans(f, x, Nat.add(k, s), N.succ_le_lt(f, x, lx), N.lt_succ_le(x, Nat.add(k, s), h))

law folds_fit:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +bp: Nat
  for +h5: {Nat.add(1n+bp, 5n) == C.shift(130n, one) : Nat}
  for +n: Nat
  for +x: Nat
  for +h: {Nat.is_lt(x, Nat.add(n, C.shift(130n, one))) == True{} : Bool}
  {C.fits(130n, R.folds(n, x)) == True{} : Bool}

def folds_fit(one, h1, bp, h5, n, x, h):
  match n:
    case 0n: WW.fits_one(130n, one, h1, x, h)
    case 1n+k: folds_fit(one, h1, bp, h5, k, R.fold(x), fold_lt_c(one, h1, bp, h5, k, x, h, Nat.is_eq(C.high(130n, x), 0n), {==}))

# y < 2^130: canon(y) == y mod p
def canon_c(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +h5: {Nat.add(1n+bp, 5n) == C.shift(130n, one) : Nat}, +y: Nat, +hy: {C.fits(130n, y) == True{} : Bool}, +b: Bool, +hb: {C.fits(130n, Nat.add(y, 5n)) == b : Bool}) -> {R.pick(b, y, C.low(130n, Nat.add(y, 5n))) == Nat.mod(y, 1n+bp) : Nat}:
  match b:
    case True{}:
      +s = C.shift(130n, one)
      +pp = {1n+bp : Nat}
      +l1 = A.lt_subst(Nat.add(y, 5n), s, Nat.add(pp, 5n), A.sy(Nat.add(pp, 5n), s, h5), WW.lt_one(130n, one, h1, Nat.add(y, 5n), hb))
      +l2 = A.btrue(Nat.is_lt(y, pp), Nat.is_lt(Nat.add(y, 5n), Nat.add(pp, 5n)), Equal.sym(Bool, Nat.is_lt(Nat.add(y, 5n), Nat.add(pp, 5n)), Nat.is_lt(y, pp), WW.lt_cancel_r(y, pp, 5n)), l1)
      A.sy(Nat.mod(y, pp), y, NR.mod_of(0n, bp, y, l2))
    case False{}:
      +s = C.shift(130n, one)
      +pp = {1n+bp : Nat}
      +x = Nat.add(y, 5n)
      +lo = C.low(130n, x)
      +hi = C.high(130n, x)
      # 5 <= 2^130 and 16 <= 2^130
      +h16 = N.le_trans(16n, C.shift(4n, one), s, L.subst(Nat, z => {Nat.is_le(16n, C.shift(4n, z)) == True{} : Bool}, 1n, one, A.sy(one, 1n, h1), {==}), WW.shift_ge(126n, C.shift(4n, one)))
      +ly = WW.lt_one(130n, one, h1, y, hy)
      +lx = A.lt_add2(y, 5n, s, s, ly, N.lt_le_trans(5n, 16n, s, {==}, h16))
      +f131 = WW.fits_one(131n, one, h1, x, A.lt_subst(x, Nat.add(s, s), Nat.double(s), A.sy(Nat.double(s), Nat.add(s, s), NA.double_self(s)), lx))
      +h2 = WW.lt_of_fits(1n, hi, SH.fits_high(130n, 1n, x, f131))
      +hne = N.is_eq_sym_false(hi, 0n, hb)
      +h1h = N.lt_succ_le_succ(0n, hi, N.lt_or_eq(0n, hi, N.zero_le(hi), hne))
      +ehi = N.le_antisym(hi, 1n, N.lt_succ_le(hi, 1n, h2), h1h)
      # x == lo + 2^130 hi == lo + s
      +ex = A.tr(x, Nat.add(lo, C.shift(130n, hi)), Nat.add(lo, s), WW.low_high(130n, x),
        WM.cong_r(lo, C.shift(130n, hi), s, A.tr(C.shift(130n, hi), Nat.mul(hi, s), s, WW.shift_mul_one(130n, one, h1, hi),
          A.tr(Nat.mul(hi, s), Nat.mul(1n, s), s, Equal.cong(Nat, Nat, t => Nat.mul(t, s), hi, 1n, ehi), AR.one_mul(s)))))
      # y == lo + p
      +e2 = A.tr(Nat.add(y, 5n), Nat.add(lo, Nat.add(pp, 5n)), Nat.add(Nat.add(lo, pp), 5n),
        A.tr(Nat.add(y, 5n), Nat.add(lo, s), Nat.add(lo, Nat.add(pp, 5n)), ex, WM.cong_r(lo, s, Nat.add(pp, 5n), A.sy(Nat.add(pp, 5n), s, h5))),
        A.sy(Nat.add(Nat.add(lo, pp), 5n), Nat.add(lo, Nat.add(pp, 5n)), N.add_assoc(lo, pp, 5n)))
      +ey = UA.add_cancel_r(y, Nat.add(lo, pp), 5n, e2)
      # lo < 5 <= p
      +l5a = A.lt_subst(Nat.add(lo, s), Nat.add(s, 5n), Nat.add(5n, s), N.add_comm(s, 5n), A.lt_substl(Nat.add(y, 5n), Nat.add(lo, s), Nat.add(s, 5n), ex, N.lt_add_r2(y, s, 5n, ly)))
      +l5b = A.btrue(Nat.is_lt(lo, 5n), Nat.is_lt(Nat.add(lo, s), Nat.add(5n, s)), Equal.sym(Bool, Nat.is_lt(Nat.add(lo, s), Nat.add(5n, s)), Nat.is_lt(lo, 5n), WW.lt_cancel_r(lo, 5n, s)), l5a)
      +h10 = A.le_subst(10n, s, Nat.add(pp, 5n), A.sy(Nat.add(pp, 5n), s, h5), N.le_trans(10n, 16n, s, {==}, h16))
      +h9 = N.succ_le_lt(9n, Nat.add(pp, 5n), h10)
      +h4 = A.btrue(Nat.is_lt(4n, pp), Nat.is_lt(Nat.add(4n, 5n), Nat.add(pp, 5n)), Equal.sym(Bool, Nat.is_lt(Nat.add(4n, 5n), Nat.add(pp, 5n)), Nat.is_lt(4n, pp), WW.lt_cancel_r(4n, pp, 5n)), h9)
      +hp5 = N.lt_succ_le_succ(4n, pp, h4)
      +llo = N.lt_le_trans(lo, 5n, pp, l5b, hp5)
      A.sy(Nat.mod(y, pp), lo, A.tr(Nat.mod(y, pp), Nat.mod(Nat.add(Nat.mul(1n, pp), lo), pp), lo,
        Equal.cong(Nat, Nat, t => Nat.mod(t, pp), y, Nat.add(Nat.mul(1n, pp), lo), A.tr(y, Nat.add(lo, pp), Nat.add(Nat.mul(1n, pp), lo), ey, A.tr(Nat.add(lo, pp), Nat.add(pp, lo), Nat.add(Nat.mul(1n, pp), lo), N.add_comm(lo, pp), WM.cong_l(pp, Nat.mul(1n, pp), lo, A.sy(Nat.mul(1n, pp), pp, AR.one_mul(pp)))))),
        NR.mod_of(1n, bp, lo, llo)))

law canon_mod:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +bp: Nat
  for +h5: {Nat.add(1n+bp, 5n) == C.shift(130n, one) : Nat}
  for +y: Nat
  for +hy: {C.fits(130n, y) == True{} : Bool}
  {R.canon(y) == Nat.mod(y, 1n+bp) : Nat}

def canon_mod(one, h1, bp, h5, y, hy):
  match y:
    case 0n: {==}
    case 1n+z: canon_c(one, h1, bp, h5, 1n+z, hy, C.fits(130n, Nat.add(1n+z, 5n)), {==})

# modp(x) is x mod p, for every x
law modp_mod:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +bp: Nat
  for +h5: {Nat.add(1n+bp, 5n) == C.shift(130n, one) : Nat}
  for +x: Nat
  {R.modp(x) == Nat.mod(x, 1n+bp) : Nat}

def modp_mod(one, h1, bp, h5, x):
  +s = C.shift(130n, one)
  +hs = N.succ_le_lt(0n, s, A.one_le_shift(130n, one, h1))
  +hx = A.lt_substl(Nat.add(x, 0n), x, Nat.add(x, s), N.add_zero(x), N.lt_add_left(0n, s, x, hs))
  +y = R.folds(x, x)
  A.tr(R.canon(y), Nat.mod(y, 1n+bp), Nat.mod(x, 1n+bp), canon_mod(one, h1, bp, h5, y, folds_fit(one, h1, bp, h5, x, x, hx)), folds_mod(one, h1, bp, h5, x, x))
