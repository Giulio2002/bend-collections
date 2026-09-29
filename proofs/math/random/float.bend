import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/random.bend as SR
import ../../../src/math/random/rand.bend as R
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../../src/math/f64.bend as F
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/u32.bend as U
import ../natural/bits.bend as NB
import ../typed/width.bend as WW
import ../typed/u32laws.bend as LW
import ../typed/w64sh.bend as SH
import ../typed/w64clz.bend as WC
import ../typed/w64add.bend as WA
import ../typed/f64bits.bend as FB
import ../typed/f64round.bend as FR
import ../typed/f64rtools.bend as RT

# Float64.value and Float64.lt_one of spec/math/random.bend: Go's Float64,
# float64(x << 11 >> 11) / 2^53, built by src/math/random/rand.bend's
# to_float as the bit pattern of m * 2^-53 (m the low 53 bits of x), is the
# double spec/math/f64.bend's round gives for m * 2^-53, and is below 1.
# For m > 0 with bit length 1 + j (j <= 52), the significand is
# q = m * 2^(52 - j) in [2^52, 2^53) and the exponent field 970 + j <= 1022.
# No constant 2^k is ever expanded: widths stay symbolic (C.fits, C.low,
# C.high, C.shift) and U32 constants are read through their words.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# ---- natural-number arithmetic ----

# 63 - j = 11 + (52 - j)
def sub63(+j: Nat, +hj: {Nat.is_le(j, 52n) == True{} : Bool}) -> {Nat.sub(63n, j) == Nat.add(11n, Nat.sub(52n, j)) : Nat}:
  +r = Nat.sub(52n, j)
  +e1 = N.sub_add(52n, j, hj)
  +e2 = Equal.trans(Nat, Nat.add(j, Nat.add(11n, r)), Nat.add(Nat.add(11n, r), j), 63n, N.add_comm(j, Nat.add(11n, r)), Equal.cong(Nat, Nat, z => Nat.add(11n, z), Nat.add(r, j), 52n, Equal.trans(Nat, Nat.add(r, j), Nat.add(j, r), 52n, N.add_comm(r, j), e1)))
  %e2 : {Nat.sub(_, j) == Nat.add(11n, r) : Nat}
  N.add_sub_cancel(j, Nat.add(11n, r))

# the shift of the implementation: clz - 11 = 52 - j
def shift_amt(+j: Nat, +hj: {Nat.is_le(j, 52n) == True{} : Bool}) -> {Nat.sub(Nat.sub(63n, j), 11n) == Nat.sub(52n, j) : Nat}:
  %Equal.sym(Nat, Nat.sub(63n, j), Nat.add(11n, Nat.sub(52n, j)), sub63(j, hj)) : {Nat.sub(_, 11n) == Nat.sub(52n, j) : Nat}
  N.sub_zero(Nat.sub(52n, j))

# the exponent field of the implementation: 1033 - clz = 970 + j
def exp_amt0(+j: Nat, +hj: {Nat.is_le(j, 52n) == True{} : Bool}) -> {Nat.sub(1033n, Nat.sub(63n, j)) == Nat.add(970n, j) : Nat}:
  +r = Nat.sub(52n, j)
  +e1 = N.sub_add(52n, j, hj)
  +e3 = Equal.trans(Nat, Nat.add(r, Nat.add(970n, j)), Nat.add(Nat.add(970n, j), r), 1022n, N.add_comm(r, Nat.add(970n, j)), Equal.cong(Nat, Nat, z => Nat.add(970n, z), Nat.add(j, r), 52n, e1))
  %Equal.sym(Nat, Nat.sub(63n, j), Nat.add(11n, r), sub63(j, hj)) : {Nat.sub(1033n, _) == Nat.add(970n, j) : Nat}
  %e3 : {Nat.sub(_, r) == Nat.add(970n, j) : Nat}
  N.add_sub_cancel(r, Nat.add(970n, j))

def exp_amt(+j: Nat, +hj: {Nat.is_le(j, 52n) == True{} : Bool}) -> {Nat.sub(1033n, Nat.sub(63n, j)) == Nat.add(j, 970n) : Nat}:
  Equal.trans(Nat, Nat.sub(1033n, Nat.sub(63n, j)), Nat.add(970n, j), Nat.add(j, 970n), exp_amt0(j, hj), N.add_comm(970n, j))

# ---- widths ----

def fits0(+a: Nat) -> {C.fits(a, 0n) == True{} : Bool}:
  %Equal.sym(Nat, C.high(a, 0n), 0n, WC.high0(a)) : {Nat.is_eq(_, 0n) == True{} : Bool}
  {==}

def fits_up(+a: Nat, +d: Nat, +x: Nat, +h: {C.fits(a, x) == True{} : Bool}) -> {C.fits(Nat.add(a, d), x) == True{} : Bool}:
  +e = N.eq_from_is_eq(C.high(a, x), 0n, h)
  %Equal.sym(Nat, C.high(Nat.add(a, d), x), C.high(d, C.high(a, x)), WW.high_comp(d, a, x)) : {Nat.is_eq(_, 0n) == True{} : Bool}
  %Equal.sym(Nat, C.high(a, x), 0n, e) : {Nat.is_eq(C.high(d, _), 0n) == True{} : Bool}
  fits0(d)

# x < 2^k gives x 2^a < 2^(a + k)
def fits_shift(+a: Nat, +k: Nat, +x: Nat, +h: {C.fits(k, x) == True{} : Bool}) -> {C.fits(Nat.add(a, k), C.shift(a, x)) == True{} : Bool}:
  WW.limbs_fit(a, k, 0n, x, fits0(a), h)

def fits_lt11(+e: Nat, +h: {Nat.is_lt(e, 2048n) == True{} : Bool}) -> {C.fits(11n, e) == True{} : Bool}:
  WW.fits_of_lt(11n, e, h)

# ---- the high word ----

# the high word the implementation builds: exponent field e, and the top 20
# fraction bits of qh
def hw(+e: Nat, +qh: U32) -> U32:
  U32.add(U32.mul(U32.from_nat(e), 1048576), U32.and(qh, 1048575))

def bits(+q: WU.U64, +e: Nat) -> F.F64:
  F.Bits{X.lo(q), hw(e, X.hi(q))}

def f12(+e: Nat, +he: {Nat.is_lt(e, 2048n) == True{} : Bool}) -> {C.fits(12n, e) == True{} : Bool}:
  fits_up(11n, 1n, e, fits_lt11(e, he))

# its value: 2^20 e + (qh mod 2^20), for e < 2^11
def hw_value(+one: Nat, +h1: {one == 1n : Nat}, +e: Nat, +qh: U32, +he: {Nat.is_lt(e, 2048n) == True{} : Bool}) -> {v(hw(e, qh)) == Nat.add(C.low(20n, v(qh)), C.shift(20n, e)) : Nat}:
  +a = U32.mul(U32.from_nat(e), 1048576)
  +b = U32.and(qh, 1048575)
  +lq = C.low(20n, v(qh))
  +se = C.shift(20n, e)
  +ve = U.to_nat_from_nat(e, 11n, {==}, he)
  +f32 = fits_shift(20n, 12n, e, f12(e, he))
  +va = Equal.trans(Nat, v(a), C.low(32n, C.shift(20n, v(U32.from_nat(e)))), se, SH.mul_p2(U32.from_nat(e), 20n, {==}),
    Equal.trans(Nat, C.low(32n, C.shift(20n, v(U32.from_nat(e)))), C.low(32n, se), se, Equal.cong(Nat, Nat, z => C.low(32n, C.shift(20n, z)), v(U32.from_nat(e)), e, ve), WW.low_fit(32n, se, f32)))
  +vb = FB.andm(qh, 20n, 1048575, {==})
  +e12 = Equal.trans(Nat, Nat.add(v(a), v(b)), Nat.add(se, v(b)), Nat.add(se, lq), Equal.cong(Nat, Nat, z => Nat.add(z, v(b)), v(a), se, va), Equal.cong(Nat, Nat, z => Nat.add(se, z), v(b), lq, vb))
  +e13 = Equal.trans(Nat, Nat.add(v(a), v(b)), Nat.add(se, lq), Nat.add(lq, se), e12, N.add_comm(se, lq))
  +fs3 = WW.limbs_fit(20n, 12n, lq, e, WW.low_fits(20n, v(qh)), f12(e, he))
  +fs1 = L.subst(Nat, z => {C.fits(32n, z) == True{} : Bool}, Nat.add(lq, se), Nat.add(v(a), v(b)), Equal.sym(Nat, Nat.add(v(a), v(b)), Nat.add(lq, se), e13), fs3)
  Equal.trans(Nat, v(U32.add(a, b)), Nat.add(v(a), v(b)), Nat.add(lq, se), FB.addv(one, h1, a, b, WW.lt_one(32n, one, h1, Nat.add(v(a), v(b)), fs1)), e13)

def value_eta(+q: WU.U64) -> {SW.value(q) == Nat.add(v(X.lo(q)), C.shift(32n, v(X.hi(q)))) : Nat}:
  match q:
    case WU.U64{l, h}:
      {==}

# the implementation's bits are encode(False, e, q mod 2^52) for the value
# q < 2^53 of the shifted significand
def enc(+one: Nat, +h1: {one == 1n : Nat}, +Q: WU.U64, +e: Nat, +he: {Nat.is_lt(e, 2048n) == True{} : Bool}, +q: Nat, +hq: {SW.value(Q) == q : Nat}, +f53: {C.fits(53n, q) == True{} : Bool}) -> {bits(Q, e) == SF.encode(False{}, e, C.low(52n, q)) : F.F64}:
  +ql = X.lo(Q)
  +qh = X.hi(Q)
  +lq = C.low(20n, v(qh))
  +hq2 = Equal.trans(Nat, q, SW.value(Q), Nat.add(v(ql), C.shift(32n, v(qh))), Equal.sym(Nat, SW.value(Q), q, hq), value_eta(Q))
  +f = C.low(52n, q)
  +F1 = Nat.add(v(ql), C.shift(32n, lq))
  +s1 = FB.low_split(32n, 20n, q)
  +el = Equal.trans(Nat, C.low(32n, q), C.low(32n, Nat.add(v(ql), C.shift(32n, v(qh)))), v(ql), Equal.cong(Nat, Nat, z => C.low(32n, z), q, Nat.add(v(ql), C.shift(32n, v(qh))), hq2), WW.low_u(32n, v(ql), v(qh), LW.vb(ql)))
  +eh = Equal.trans(Nat, C.high(32n, q), C.high(32n, Nat.add(v(ql), C.shift(32n, v(qh)))), v(qh), Equal.cong(Nat, Nat, z => C.high(32n, z), q, Nat.add(v(ql), C.shift(32n, v(qh))), hq2), WW.high_u(32n, v(ql), v(qh), LW.vb(ql)))
  +ef1 = Equal.trans(Nat, f, Nat.add(C.low(32n, q), C.shift(32n, C.low(20n, C.high(32n, q)))), F1, s1,
    Equal.trans(Nat, Nat.add(C.low(32n, q), C.shift(32n, C.low(20n, C.high(32n, q)))), Nat.add(v(ql), C.shift(32n, C.low(20n, C.high(32n, q)))), F1, Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(32n, C.low(20n, C.high(32n, q)))), C.low(32n, q), v(ql), el),
      Equal.cong(Nat, Nat, z => Nat.add(v(ql), C.shift(32n, C.low(20n, z))), C.high(32n, q), v(qh), eh)))
  +elo = Equal.trans(Nat, C.low(32n, f), C.low(32n, F1), v(ql), Equal.cong(Nat, Nat, z => C.low(32n, z), f, F1, ef1), WW.low_u(32n, v(ql), lq, LW.vb(ql)))
  +ehi0 = Equal.trans(Nat, C.high(32n, f), C.high(32n, F1), lq, Equal.cong(Nat, Nat, z => C.high(32n, z), f, F1, ef1), WW.high_u(32n, v(ql), lq, LW.vb(ql)))
  +T = Nat.add(e, C.shift(11n, SF.b2n(False{})))
  +ehi1 = Equal.trans(Nat, Nat.add(C.high(32n, f), C.shift(20n, T)), Nat.add(lq, C.shift(20n, T)), Nat.add(lq, C.shift(20n, e)), Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(20n, T)), C.high(32n, f), lq, ehi0), Equal.cong(Nat, Nat, z => Nat.add(lq, C.shift(20n, z)), T, e, N.add_zero(e)))
  +ehi2 = Equal.trans(Nat, Nat.add(C.high(32n, f), C.shift(20n, T)), Nat.add(lq, C.shift(20n, e)), v(hw(e, qh)), ehi1, Equal.sym(Nat, v(hw(e, qh)), Nat.add(lq, C.shift(20n, e)), hw_value(one, h1, e, qh, he)))
  +wlo = Equal.trans(U32, U32.from_nat(C.low(32n, f)), U32.from_nat(v(ql)), ql, Equal.cong(Nat, U32, z => U32.from_nat(z), C.low(32n, f), v(ql), elo), LW.rt(ql))
  +whi = Equal.trans(U32, U32.from_nat(Nat.add(C.high(32n, f), C.shift(20n, T))), U32.from_nat(v(hw(e, qh))), hw(e, qh), Equal.cong(Nat, U32, z => U32.from_nat(z), Nat.add(C.high(32n, f), C.shift(20n, T)), v(hw(e, qh)), ehi2), LW.rt(hw(e, qh)))
  +lo_s = U32.from_nat(C.low(32n, f))
  +hi_s = U32.from_nat(Nat.add(C.high(32n, f), C.shift(20n, T)))
  Equal.sym(F.F64, F.Bits{lo_s, hi_s}, F.Bits{ql, hw(e, qh)}, Equal.trans(F.F64, F.Bits{lo_s, hi_s}, F.Bits{ql, hi_s}, F.Bits{ql, hw(e, qh)}, Equal.cong(U32, F.F64, z => F.Bits{z, hi_s}, lo_s, ql, wlo), Equal.cong(U32, F.F64, z => F.Bits{ql, z}, hi_s, hw(e, qh), whi)))

# ---- bit lengths ----

def bl_le(+k: Nat, +n: Nat, +h: {C.fits(k, n) == True{} : Bool}) -> {Nat.is_le(M.bit_length(n), k) == True{} : Bool}:
  match k:
    case 0n:
      +en = N.eq_from_is_eq(n, 0n, h)
      %Equal.sym(Nat, n, 0n, en) : {Nat.is_le(M.bit_length(_), 0n) == True{} : Bool}
      {==}
    case 1n+ +kp:
      match n:
        case 0n:
          {==}
        case 1n+ +np:
          %Equal.sym(Nat, M.bit_length(1n+np), 1n+M.bit_length(C.half(1n+np)), WC.bl_succ(np)) : {Nat.is_le(_, 1n+kp) == True{} : Bool}
          bl_le(kp, C.half(1n+np), h)


# ---- the rounding of spec/math/f64.bend ----
# Exponents are kept as j + c (the variable first), so the checker never
# unfolds them into long successor chains.

def x0() -> Nat:
  Nat.sub(SF.zb(), 53n)

def max_l(+a: Nat, +b: Nat, +h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.max(a, b) == a : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({Nat.max(0n, 1n+bp) == 0n : Nat}, L.false_true(h))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.max(ap, bp), ap, max_l(ap, bp, h))

def sub_add53(+X: Nat) -> {Nat.sub(Nat.add(X, 53n), 53n) == X : Nat}:
  %Equal.sym(Nat, Nat.add(X, 53n), Nat.add(53n, X), N.add_comm(X, 53n)) : {Nat.sub(_, 53n) == X : Nat}
  N.sub_zero(X)

# X + r = 2947 for X = j + 2895, r = 52 - j
def ex(+j: Nat, +hj: {Nat.is_le(j, 52n) == True{} : Bool}) -> {Nat.add(Nat.add(j, 2895n), Nat.sub(52n, j)) == x0() : Nat}:
  +r = Nat.sub(52n, j)
  +e1 = N.sub_add(52n, j, hj)
  +a1 = N.add_assoc(j, 2895n, r)
  +a2 = Equal.cong(Nat, Nat, z => Nat.add(j, z), Nat.add(2895n, r), Nat.add(r, 2895n), N.add_comm(2895n, r))
  +a3 = Equal.sym(Nat, Nat.add(Nat.add(j, r), 2895n), Nat.add(j, Nat.add(r, 2895n)), N.add_assoc(j, r, 2895n))
  +a4 = Equal.cong(Nat, Nat, z => Nat.add(z, 2895n), Nat.add(j, r), 52n, e1)
  Equal.trans(Nat, Nat.add(Nat.add(j, 2895n), r), Nat.add(j, Nat.add(2895n, r)), x0(), a1,
    Equal.trans(Nat, Nat.add(j, Nat.add(2895n, r)), Nat.add(j, Nat.add(r, 2895n)), x0(), a2,
      Equal.trans(Nat, Nat.add(j, Nat.add(r, 2895n)), Nat.add(Nat.add(j, r), 2895n), x0(), a3, a4)))

# round(q, X) for 2^52 <= q < 2^53 at the scale X = j + 2895 is pack(q, X)
def round_q(+q: Nat, +j: Nat, +bq: {M.bit_length(q) == 53n : Nat}, +hz: {Nat.is_eq(q, 0n) == False{} : Bool}) -> {SF.round(False{}, q, Nat.add(j, 2895n)) == SF.pack(False{}, q, Nat.add(j, 2895n)) : F.F64}:
  +X = Nat.add(j, 2895n)
  +U = Nat.max(Nat.sub(Nat.add(X, M.bit_length(q)), 53n), Nat.sub(SF.zb(), 1074n))
  +hle = Equal.trans(Bool, Nat.is_le(1926n, X), Nat.is_le(1926n, Nat.add(2895n, j)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(1926n, z), X, Nat.add(2895n, j), N.add_comm(j, 2895n)), {==})
  +eU = Equal.trans(Nat, U, Nat.max(Nat.sub(Nat.add(X, 53n), 53n), 1926n), X, Equal.cong(Nat, Nat, z => Nat.max(Nat.sub(Nat.add(X, z), 53n), Nat.sub(SF.zb(), 1074n)), M.bit_length(q), 53n, bq),
    Equal.trans(Nat, Nat.max(Nat.sub(Nat.add(X, 53n), 53n), 1926n), Nat.max(X, 1926n), X, Equal.cong(Nat, Nat, z => Nat.max(z, 1926n), Nat.sub(Nat.add(X, 53n), 53n), X, sub_add53(X)), max_l(X, 1926n, hle)))
  +r1 = Equal.cong(Bool, F.F64, c => SF.pick(F.F64, c, SF.zero(False{}), SF.round_u(False{}, q, X, U)), Nat.is_eq(q, 0n), False{}, hz)
  +r2 = Equal.cong(Nat, F.F64, z => SF.round_u(False{}, q, X, z), U, X, eU)
  +r3 = Equal.cong(Bool, F.F64, c => SF.pack(False{}, SF.pick(Nat, c, SF.rne(q, Nat.sub(X, X)), C.shift(Nat.sub(X, X), q)), X), Nat.is_le(X, X), True{}, N.le_refl(X))
  +r4 = Equal.cong(Nat, F.F64, z => SF.pack(False{}, SF.rne(q, z), X), Nat.sub(X, X), 0n, N.sub_self(X))
  Equal.trans(F.F64, SF.round(False{}, q, X), SF.round_u(False{}, q, X, U), SF.pack(False{}, q, X), r1,
    Equal.trans(F.F64, SF.round_u(False{}, q, X, U), SF.round_u(False{}, q, X, X), SF.pack(False{}, q, X), r2,
      Equal.trans(F.F64, SF.round_u(False{}, q, X, X), SF.pack(False{}, SF.rne(q, Nat.sub(X, X)), X), SF.pack(False{}, q, X), r3, r4)))

# pack(q, X) is the pattern with exponent field j + 970 and fraction q mod 2^52
def pack_q(+one: Nat, +h1: {one == 1n : Nat}, +q: Nat, +j: Nat, +hj: {Nat.is_le(j, 52n) == True{} : Bool}, +f53: {C.fits(53n, q) == True{} : Bool}, +n52: {C.fits(52n, q) == False{} : Bool}) -> {SF.pack(False{}, q, Nat.add(j, 2895n)) == SF.encode(False{}, Nat.add(j, 970n), C.low(52n, q)) : F.F64}:
  +X = Nat.add(j, 2895n)
  +EF = Nat.add(j, 969n)
  +E = Nat.add(j, 970n)
  +l52 = C.low(52n, q)
  +hEF = N.add_assoc(j, 969n, 1926n)
  +hq = N.lt_le(q, C.shift(53n, one), WW.lt_one(53n, one, h1, q, f53))
  +h0 = Equal.cong(Bool, Bool, c => Bool.or(Bool.not(c), Nat.is_eq(EF, 0n)), C.fits(52n, q), False{}, n52)
  +eA = Equal.trans(Nat, Nat.add(Nat.add(j, 969n), 1n), Nat.add(j, 970n), Nat.add(970n, j), N.add_assoc(j, 969n, 1n), N.add_comm(j, 970n))
  +ev2 = L.subst(Nat, z => {Nat.is_lt(z, 2047n) == True{} : Bool}, Nat.add(970n, j), Nat.add(Nat.add(j, 969n), 1n), Equal.sym(Nat, Nat.add(Nat.add(j, 969n), 1n), Nat.add(970n, j), eA), N.le_lt_trans(j, 52n, 1077n, hj, {==}))
  +hov = Equal.trans(Bool, Nat.is_lt(Nat.add(EF, SF.pick(Nat, C.fits(53n, q), 1n, 2n)), 2047n), Nat.is_lt(Nat.add(EF, 1n), 2047n), True{}, Equal.cong(Bool, Bool, c => Nat.is_lt(Nat.add(EF, SF.pick(Nat, c, 1n, 2n)), 2047n), C.fits(53n, q), True{}, f53), ev2)
  +p1 = FR.pkg(one, h1, False{}, q, X, EF, hEF, hq, h0, hov)
  +p2 = FR.enc_bits(False{}, E, l52)
  +eH = FR.hi_one(C.high(52n, q), Equal.trans(Bool, Nat.is_eq(C.half(C.high(52n, q)), 0n), C.fits(53n, q), True{}, Equal.sym(Bool, C.fits(53n, q), Nat.is_eq(C.half(C.high(52n, q)), 0n), FR.f53h(q)), f53), n52)
  +eHo = Equal.trans(Nat, C.high(52n, q), 1n, one, eH, Equal.sym(Nat, one, 1n, h1))
  +eq = Equal.trans(Nat, q, Nat.add(l52, C.shift(52n, C.high(52n, q))), Nat.add(l52, C.shift(52n, one)), WW.low_high(52n, q), Equal.cong(Nat, Nat, z => Nat.add(l52, C.shift(52n, z)), C.high(52n, q), one, eHo))
  +eE = Equal.trans(Nat, E, 1n+EF, Nat.add(one, EF), N.add_succ(j, 969n), Equal.cong(Nat, Nat, z => Nat.add(z, EF), 1n, one, Equal.sym(Nat, one, 1n, h1)))
  +n1 = Equal.cong(Nat, Nat, z => Nat.add(l52, C.shift(52n, z)), E, Nat.add(one, EF), eE)
  +n2 = Equal.cong(Nat, Nat, z => Nat.add(l52, z), C.shift(52n, Nat.add(one, EF)), Nat.add(C.shift(52n, one), C.shift(52n, EF)), WW.shift_add(52n, one, EF))
  +n3 = Equal.sym(Nat, Nat.add(Nat.add(l52, C.shift(52n, one)), C.shift(52n, EF)), Nat.add(l52, Nat.add(C.shift(52n, one), C.shift(52n, EF))), N.add_assoc(l52, C.shift(52n, one), C.shift(52n, EF)))
  +n4 = Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(52n, EF)), Nat.add(l52, C.shift(52n, one)), q, Equal.sym(Nat, q, Nat.add(l52, C.shift(52n, one)), eq))
  +nn = Equal.trans(Nat, Nat.add(l52, C.shift(52n, E)), Nat.add(l52, C.shift(52n, Nat.add(one, EF))), Nat.add(q, C.shift(52n, EF)), n1,
    Equal.trans(Nat, Nat.add(l52, C.shift(52n, Nat.add(one, EF))), Nat.add(l52, Nat.add(C.shift(52n, one), C.shift(52n, EF))), Nat.add(q, C.shift(52n, EF)), n2,
      Equal.trans(Nat, Nat.add(l52, Nat.add(C.shift(52n, one), C.shift(52n, EF))), Nat.add(Nat.add(l52, C.shift(52n, one)), C.shift(52n, EF)), Nat.add(q, C.shift(52n, EF)), n3, n4)))
  +p3 = Equal.cong(Nat, F.F64, z => FR.bits(False{}, z), Nat.add(l52, C.shift(52n, E)), Nat.add(q, C.shift(52n, EF)), nn)
  Equal.trans(F.F64, SF.pack(False{}, q, X), FR.bits(False{}, Nat.add(q, C.shift(52n, EF))), SF.encode(False{}, E, l52), p1,
    Equal.sym(F.F64, SF.encode(False{}, E, l52), FR.bits(False{}, Nat.add(q, C.shift(52n, EF))), Equal.trans(F.F64, SF.encode(False{}, E, l52), FR.bits(False{}, Nat.add(l52, C.shift(52n, E))), FR.bits(False{}, Nat.add(q, C.shift(52n, EF))), p2, p3)))

# ---- the value: m * 2^-53 for 0 < m < 2^53 ----

# the bit length of 1 + np is 1 + J(np)
def J(+np: Nat) -> Nat:
  M.bit_length(C.half(1n+np))

def j52(+np: Nat, +hf: {C.fits(53n, 1n+np) == True{} : Bool}) -> {Nat.is_le(J(np), 52n) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(z, 53n) == True{} : Bool}, M.bit_length(1n+np), 1n+J(np), WC.bl_succ(np), bl_le(53n, 1n+np, hf))

def r52(+j: Nat, +hj: {Nat.is_le(j, 52n) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(52n, j), 64n) == True{} : Bool}:
  +r = Nat.sub(52n, j)
  +e = Equal.trans(Nat, Nat.add(r, j), Nat.add(j, r), 52n, N.add_comm(r, j), N.sub_add(52n, j, hj))
  N.le_lt_trans(r, 52n, 64n, L.subst(Nat, z => {Nat.is_le(r, z) == True{} : Bool}, Nat.add(r, j), 52n, e, N.le_add_right(r, j)), {==})

# the implementation: shift by 52 - j, exponent field j + 970, for the bit
# length 1 + j of the significand (j a variable, so no bit length is ever
# evaluated inside a comparison)
def impl_eq(+m: WU.U64, +np: Nat, +hM: {SW.value(m) == 1n+np : Nat}, +j: Nat, +hj: {Nat.is_le(j, 52n) == True{} : Bool}, +hbl: {M.bit_length(1n+np) == 1n+j : Nat}) -> {R.f53(m, X.clz(m)) == bits(X.shl(m, Nat.sub(52n, j)), Nat.add(j, 970n)) : F.F64}:
  +r = Nat.sub(52n, j)
  +E = Nat.add(j, 970n)
  +c = X.clz(m)
  +hclz = Equal.trans(Nat, c, Nat.sub(64n, M.bit_length(SW.value(m))), Nat.sub(63n, j), WC.clz_value(m),
    Equal.trans(Nat, Nat.sub(64n, M.bit_length(SW.value(m))), Nat.sub(64n, M.bit_length(1n+np)), Nat.sub(63n, j), Equal.cong(Nat, Nat, z => Nat.sub(64n, M.bit_length(z)), SW.value(m), 1n+np, hM), Equal.cong(Nat, Nat, z => Nat.sub(64n, z), M.bit_length(1n+np), 1n+j, hbl)))
  +es = Equal.trans(Nat, Nat.sub(c, 11n), Nat.sub(Nat.sub(63n, j), 11n), r, Equal.cong(Nat, Nat, z => Nat.sub(z, 11n), c, Nat.sub(63n, j), hclz), shift_amt(j, hj))
  +ee = Equal.trans(Nat, Nat.sub(1033n, c), Nat.sub(1033n, Nat.sub(63n, j)), E, Equal.cong(Nat, Nat, z => Nat.sub(1033n, z), c, Nat.sub(63n, j), hclz), exp_amt(j, hj))
  +i2 = Equal.cong(Nat, F.F64, z => bits(X.shl(m, z), Nat.sub(1033n, c)), Nat.sub(c, 11n), r, es)
  +i3 = Equal.cong(Nat, F.F64, z => bits(X.shl(m, r), z), Nat.sub(1033n, c), E, ee)
  Equal.trans(F.F64, R.f53(m, c), bits(X.shl(m, Nat.sub(c, 11n)), Nat.sub(1033n, c)), bits(X.shl(m, r), E), {==},
    Equal.trans(F.F64, bits(X.shl(m, Nat.sub(c, 11n)), Nat.sub(1033n, c)), bits(X.shl(m, r), Nat.sub(1033n, c)), bits(X.shl(m, r), E), i2, i3))

# j <= 52 from the bit length 1 + j <= 53
def hj_of(+np: Nat, +j: Nat, +hf: {C.fits(53n, 1n+np) == True{} : Bool}, +hbl: {M.bit_length(1n+np) == 1n+j : Nat}) -> {Nat.is_le(j, 52n) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(z, 53n) == True{} : Bool}, M.bit_length(1n+np), 1n+j, hbl, bl_le(53n, 1n+np, hf))

def main_g(+one: Nat, +h1: {one == 1n : Nat}, +xv: Nat, +hx: {Nat.sub(SF.zb(), 53n) == xv : Nat}, +m: WU.U64, +np: Nat, +hM: {SW.value(m) == 1n+np : Nat}, +j: Nat, +hj: {Nat.is_le(j, 52n) == True{} : Bool}, +hbl: {M.bit_length(1n+np) == 1n+j : Nat}) -> {bits(X.shl(m, Nat.sub(52n, j)), Nat.add(j, 970n)) == SF.round(False{}, 1n+np, xv) : F.F64}:
  +r = Nat.sub(52n, j)
  +q = C.shift(r, 1n+np)
  +e1 = N.sub_add(52n, j, hj)
  +bq = Equal.trans(Nat, M.bit_length(q), Nat.add(M.bit_length(1n+np), r), 53n, RT.bl_shift(r, 1n+np, {==}),
    Equal.trans(Nat, Nat.add(M.bit_length(1n+np), r), Nat.add(1n+j, r), 53n, Equal.cong(Nat, Nat, z => Nat.add(z, r), M.bit_length(1n+np), 1n+j, hbl), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(j, r), 52n, e1)))
  +hzq = WW.shift_eq0(r, 1n+np)
  +f53 = L.subst(Nat, z => {C.fits(z, q) == True{} : Bool}, M.bit_length(q), 53n, bq, RT.bl_fit(q))
  +n52 = L.subst(Nat, z => {C.fits(z, q) == False{} : Bool}, Nat.sub(M.bit_length(q), 1n), 52n, Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), M.bit_length(q), 53n, bq), RT.bl_nfit(q, hzq))
  sv = SH.shl_value(m, r, r52(j, hj))
  +hq = Equal.trans(Nat, SW.value(X.shl(m, r)), C.low(64n, C.shift(r, SW.value(m))), q, sv,
    Equal.trans(Nat, C.low(64n, C.shift(r, SW.value(m))), C.low(64n, q), q, Equal.cong(Nat, Nat, z => C.low(64n, C.shift(r, z)), SW.value(m), 1n+np, hM), WW.low_fit(64n, q, fits_up(53n, 11n, q, f53))))
  +he = L.subst(Nat, z => {Nat.is_lt(z, 2048n) == True{} : Bool}, Nat.add(970n, j), Nat.add(j, 970n), N.add_comm(970n, j), N.le_lt_trans(j, 52n, 1078n, hj, {==}))
  +l52 = C.low(52n, q)
  +c1 = enc(one, h1, X.shl(m, r), Nat.add(j, 970n), he, q, hq, f53)
  +c2 = pack_q(one, h1, q, j, hj, f53, n52)
  +c3 = round_q(q, j, bq, hzq)
  +c4 = RT.round_shift(False{}, r, 1n+np, Nat.add(j, 2895n))
  +c5 = Equal.cong(Nat, F.F64, z => SF.round(False{}, 1n+np, z), Nat.add(Nat.add(j, 2895n), r), xv, Equal.trans(Nat, Nat.add(Nat.add(j, 2895n), r), x0(), xv, ex(j, hj), hx))
  +s3 = Equal.trans(F.F64, SF.round(False{}, q, Nat.add(j, 2895n)), SF.pack(False{}, q, Nat.add(j, 2895n)), SF.encode(False{}, Nat.add(j, 970n), l52), c3, c2)
  +s4 = Equal.trans(F.F64, SF.round(False{}, 1n+np, Nat.add(Nat.add(j, 2895n), r)), SF.round(False{}, q, Nat.add(j, 2895n)), SF.encode(False{}, Nat.add(j, 970n), l52), Equal.sym(F.F64, SF.round(False{}, q, Nat.add(j, 2895n)), SF.round(False{}, 1n+np, Nat.add(Nat.add(j, 2895n), r)), c4), s3)
  +sp = Equal.trans(F.F64, SF.round(False{}, 1n+np, xv), SF.round(False{}, 1n+np, Nat.add(Nat.add(j, 2895n), r)), SF.encode(False{}, Nat.add(j, 970n), l52), Equal.sym(F.F64, SF.round(False{}, 1n+np, Nat.add(Nat.add(j, 2895n), r)), SF.round(False{}, 1n+np, xv), c5), s4)
  Equal.trans(F.F64, bits(X.shl(m, r), Nat.add(j, 970n)), SF.encode(False{}, Nat.add(j, 970n), l52), SF.round(False{}, 1n+np, xv), c1, Equal.sym(F.F64, SF.round(False{}, 1n+np, xv), SF.encode(False{}, Nat.add(j, 970n), l52), sp))

def main_j(+one: Nat, +h1: {one == 1n : Nat}, +xv: Nat, +hx: {Nat.sub(SF.zb(), 53n) == xv : Nat}, +m: WU.U64, +np: Nat, +hM: {SW.value(m) == 1n+np : Nat}, +hf: {C.fits(53n, 1n+np) == True{} : Bool}, +j: Nat, +hbl: {M.bit_length(1n+np) == 1n+j : Nat}) -> {R.f53(m, X.clz(m)) == SF.round(False{}, 1n+np, xv) : F.F64}:
  +hj = hj_of(np, j, hf, hbl)
  Equal.trans(F.F64, R.f53(m, X.clz(m)), bits(X.shl(m, Nat.sub(52n, j)), Nat.add(j, 970n)), SF.round(False{}, 1n+np, xv),
    impl_eq(m, np, hM, j, hj, hbl),
    main_g(one, h1, xv, hx, m, np, hM, j, hj, hbl))

def bl_nz(+np: Nat, +h: {M.bit_length(1n+np) == 0n : Nat}) -> Empty:
  N.succ_zero(M.bit_length(C.half(1n+np)), Equal.trans(Nat, 1n+M.bit_length(C.half(1n+np)), M.bit_length(1n+np), 0n, Equal.sym(Nat, M.bit_length(1n+np), 1n+M.bit_length(C.half(1n+np)), WC.bl_succ(np)), h))

def main_b(+one: Nat, +h1: {one == 1n : Nat}, +xv: Nat, +hx: {Nat.sub(SF.zb(), 53n) == xv : Nat}, +m: WU.U64, +np: Nat, +hM: {SW.value(m) == 1n+np : Nat}, +hf: {C.fits(53n, 1n+np) == True{} : Bool}, +b: Nat, +hb: {M.bit_length(1n+np) == b : Nat}) -> {R.f53(m, X.clz(m)) == SF.round(False{}, 1n+np, xv) : F.F64}:
  match b:
    case 0n:
      Empty.absurd({R.f53(m, X.clz(m)) == SF.round(False{}, 1n+np, xv) : F.F64}, bl_nz(np, hb))
    case 1n+j:
      main_j(one, h1, xv, hx, m, np, hM, hf, j, hb)

def main_v(+one: Nat, +h1: {one == 1n : Nat}, +xv: Nat, +hx: {Nat.sub(SF.zb(), 53n) == xv : Nat}, +m: WU.U64, +np: Nat, +hM: {SW.value(m) == 1n+np : Nat}, +hf: {C.fits(53n, 1n+np) == True{} : Bool}) -> {R.f53(m, X.clz(m)) == SF.round(False{}, 1n+np, xv) : F.F64}:
  main_b(one, h1, xv, hx, m, np, hM, hf, M.bit_length(1n+np), {==})

# ---- Float64.value ----

# the low 53 bits of the source output
def mm(+x: WU.U64) -> WU.U64:
  WU.U64{X.lo(x), U32.and(X.hi(x), 2097151)}

def m_val(+x: WU.U64) -> {SW.value(mm(x)) == C.low(53n, SW.value(x)) : Nat}:
  match x:
    case WU.U64{+l, +h}:
      +n = Nat.add(v(l), C.shift(32n, v(h)))
      Equal.trans(Nat, Nat.add(v(l), C.shift(32n, v(U32.and(h, 2097151)))), Nat.add(v(l), C.shift(32n, C.low(21n, v(h)))), C.low(53n, n),
        Equal.cong(Nat, Nat, z => Nat.add(v(l), C.shift(32n, z)), v(U32.and(h, 2097151)), C.low(21n, v(h)), FB.andm(h, 21n, 2097151, {==})),
        Equal.sym(Nat, C.low(53n, n), Nat.add(v(l), C.shift(32n, C.low(21n, v(h)))),
          Equal.trans(Nat, C.low(53n, n), Nat.add(C.low(32n, n), C.shift(32n, C.low(21n, C.high(32n, n)))), Nat.add(v(l), C.shift(32n, C.low(21n, v(h)))),
            FB.low_split(32n, 21n, n),
            Equal.trans(Nat, Nat.add(C.low(32n, n), C.shift(32n, C.low(21n, C.high(32n, n)))), Nat.add(v(l), C.shift(32n, C.low(21n, C.high(32n, n)))), Nat.add(v(l), C.shift(32n, C.low(21n, v(h)))),
              Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(32n, C.low(21n, C.high(32n, n)))), C.low(32n, n), v(l), WW.low_u(32n, v(l), v(h), LW.vb(l))),
              Equal.cong(Nat, Nat, z => Nat.add(v(l), C.shift(32n, C.low(21n, z))), C.high(32n, n), v(h), WW.high_u(32n, v(l), v(h), LW.vb(l)))))))

def iz(+m: WU.U64, +vm: Nat, +hv: {SW.value(m) == vm : Nat}) -> {X.is_zero(m) == Nat.is_eq(vm, 0n) : Bool}:
  Equal.trans(Bool, X.is_zero(m), Nat.is_eq(SW.value(m), 0n), Nat.is_eq(vm, 0n), WA.is_zero_value(m), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), SW.value(m), vm, hv))

def hl_of(+x: WU.U64, +vm: Nat, +hv: {SW.value(mm(x)) == vm : Nat}) -> {C.low(53n, SW.value(x)) == vm : Nat}:
  Equal.trans(Nat, C.low(53n, SW.value(x)), SW.value(mm(x)), vm, Equal.sym(Nat, SW.value(mm(x)), C.low(53n, SW.value(x)), m_val(x)), hv)

def value_z(+x: WU.U64, +xv: Nat, +hv: {SW.value(mm(x)) == 0n : Nat}) -> {R.to_float(x) == SF.round(False{}, C.low(53n, SW.value(x)), xv) : F.F64}:
  +n = C.low(53n, SW.value(x))
  +hz = Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), n, 0n, hl_of(x, 0n, hv))
  %Equal.sym(Bool, X.is_zero(mm(x)), Nat.is_eq(0n, 0n), iz(mm(x), 0n, hv)) : {R.f53_z(mm(x), _) == SF.round(False{}, n, xv) : F.F64}
  Equal.trans(F.F64, R.f53_z(mm(x), Nat.is_eq(0n, 0n)), SF.zero(False{}), SF.round(False{}, n, xv), {==}, Equal.sym(F.F64, SF.round(False{}, n, xv), SF.zero(False{}), Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.zero(False{}), SF.round_u(False{}, n, xv, Nat.max(Nat.sub(Nat.add(xv, M.bit_length(n)), 53n), Nat.sub(SF.zb(), 1074n)))), Nat.is_eq(n, 0n), True{}, hz)))

def value_s(+x: WU.U64, +np: Nat, +xv: Nat, +hx: {Nat.sub(SF.zb(), 53n) == xv : Nat}, +hv: {SW.value(mm(x)) == 1n+np : Nat}) -> {R.to_float(x) == SF.round(False{}, C.low(53n, SW.value(x)), xv) : F.F64}:
  +hl = hl_of(x, 1n+np, hv)
  +hf = Equal.trans(Bool, C.fits(53n, 1n+np), C.fits(53n, C.low(53n, SW.value(x))), True{}, Equal.cong(Nat, Bool, z => C.fits(53n, z), 1n+np, C.low(53n, SW.value(x)), Equal.sym(Nat, C.low(53n, SW.value(x)), 1n+np, hl)), WW.low_fits(53n, SW.value(x)))
  %Equal.sym(Nat, C.low(53n, SW.value(x)), 1n+np, hl) : {R.to_float(x) == SF.round(False{}, _, xv) : F.F64}
  %Equal.sym(Bool, X.is_zero(mm(x)), Nat.is_eq(1n+np, 0n), iz(mm(x), 1n+np, hv)) : {R.f53_z(mm(x), _) == SF.round(False{}, 1n+np, xv) : F.F64}
  Equal.trans(F.F64, R.f53_z(mm(x), Nat.is_eq(1n+np, 0n)), R.f53(mm(x), X.clz(mm(x))), SF.round(False{}, 1n+np, xv), {==}, main_v(1n, {==}, xv, hx, mm(x), np, hv, hf))

def value_c(+vm: Nat, +x: WU.U64, +xv: Nat, +hx: {Nat.sub(SF.zb(), 53n) == xv : Nat}, +hv: {SW.value(mm(x)) == vm : Nat}) -> {R.to_float(x) == SF.round(False{}, C.low(53n, SW.value(x)), xv) : F.F64}:
  match vm:
    case 0n:
      value_z(x, xv, hv)
    case 1n+np:
      value_s(x, np, xv, hx, hv)

# THEOREM (Float64.value)
def value(+x: WU.U64) -> SR.Float64.value(x):
  value_c(SW.value(mm(x)), x, Nat.sub(SF.zb(), 53n), {==}, {==})

# ---- Float64.lt_one ----
# The comparison is F.lt itself (Go's <): the checker evaluates what it can
# on 1.0 = Bits{0, H} (H = 0x3FF00000) at the word level, and every value
# fact about H comes from word equations (hH, hK), so no 30-bit constant is
# ever unfolded into a natural number.

def and_f(+b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the value of the high word of 1.0 without its sign bit: 1023 * 2^20
def hv_one(+H: U32, +K: U32, +hH: {U32.and(H, 2147483647) == U32.mul(K, X.pow2(20n)) : U32}, +hK: {U32.to_nat(K) == 1023n : Nat}) -> {v(U32.and(H, 2147483647)) == C.shift(20n, 1023n) : Nat}:
  Equal.trans(Nat, v(U32.and(H, 2147483647)), v(U32.mul(K, X.pow2(20n))), C.shift(20n, 1023n),
    Equal.cong(U32, Nat, z => v(z), U32.and(H, 2147483647), U32.mul(K, X.pow2(20n)), hH),
    Equal.trans(Nat, v(U32.mul(K, X.pow2(20n))), C.low(32n, C.shift(20n, v(K))), C.shift(20n, 1023n),
      SH.mul_p2(K, 20n, {==}),
      Equal.trans(Nat, C.low(32n, C.shift(20n, v(K))), C.low(32n, C.shift(20n, 1023n)), C.shift(20n, 1023n),
        Equal.cong(Nat, Nat, z => C.low(32n, C.shift(20n, z)), v(K), 1023n, hK),
        WW.low_fit(32n, C.shift(20n, 1023n), fits_shift(20n, 12n, 1023n, {==})))))

# a double Bits{l, hw(E, qh)} with E < 1023 is below 1.0 = Bits{0, H}
def below_one(+l: U32, +qh: U32, +E: Nat, +H: U32, +K: U32, +hE: {Nat.is_lt(E, 1023n) == True{} : Bool}, +hn: {F.is_nan(F.Bits{0, H}) == False{} : Bool}, +hz: {F.is_zero(F.Bits{0, H}) == False{} : Bool}, +hs: {F.signbit(F.Bits{0, H}) == False{} : Bool}, +hH: {U32.and(H, 2147483647) == U32.mul(K, X.pow2(20n)) : U32}, +hK: {U32.to_nat(K) == 1023n : Nat}) -> {F.lt(F.Bits{l, hw(E, qh)}, F.Bits{0, H}) == True{} : Bool}:
  +h = hw(E, qh)
  +x = {F.Bits{l, h} : F.F64}
  +y = {F.Bits{0, H} : F.F64}
  +lq = C.low(20n, v(qh))
  +he = N.lt_trans(E, 1023n, 2048n, hE, {==})
  +vh = hw_value(1n, {==}, E, qh, he)
  +f11 = fits_lt11(E, he)
  +f31 = Equal.trans(Bool, C.fits(31n, v(h)), C.fits(31n, Nat.add(lq, C.shift(20n, E))), True{}, Equal.cong(Nat, Bool, z => C.fits(31n, z), v(h), Nat.add(lq, C.shift(20n, E)), vh), WW.limbs_fit(20n, 11n, lq, E, WW.low_fits(20n, v(qh)), f11))
  +ef = Equal.trans(Nat, v(U32.and(U32.div(h, 1048576), 2047)), C.low(11n, C.high(20n, v(h))), E, FB.ef_g(1n, {==}, h, 1048576, {==}, 2047, {==}),
    Equal.trans(Nat, C.low(11n, C.high(20n, v(h))), C.low(11n, E), E,
      Equal.cong(Nat, Nat, z => C.low(11n, z), C.high(20n, v(h)), E, Equal.trans(Nat, C.high(20n, v(h)), C.high(20n, Nat.add(lq, C.shift(20n, E))), E, Equal.cong(Nat, Nat, z => C.high(20n, z), v(h), Nat.add(lq, C.shift(20n, E)), vh), WW.high_u(20n, lq, E, WW.low_fits(20n, v(qh))))),
      WW.low_fit(11n, E, f11)))
  +hne = N.is_eq_lt(E, 2047n, N.lt_trans(E, 1023n, 2047n, hE, {==}))
  +nanx = Equal.trans(Bool, F.is_nan(x), Bool.and(Nat.is_eq(E, 2047n), F.nz(F.frac(x))), False{},
    Equal.cong(Nat, Bool, z => Bool.and(Nat.is_eq(z, 2047n), F.nz(F.frac(x))), v(U32.and(U32.div(h, 1048576), 2047)), E, ef),
    %hne : {Bool.and(_, F.nz(F.frac(x))) == False{} : Bool}
    {==})
  +uo = Equal.trans(Bool, F.unordered(x, y), Bool.or(False{}, F.is_nan(y)), False{}, Equal.cong(Bool, Bool, z => Bool.or(z, F.is_nan(y)), F.is_nan(x), False{}, nanx), hn)
  +zs = Equal.trans(Bool, F.zeros(x, y), Bool.and(F.is_zero(x), False{}), False{}, Equal.cong(Bool, Bool, z => Bool.and(F.is_zero(x), z), F.is_zero(y), False{}, hz), and_f(F.is_zero(x)))
  +sx = Equal.trans(Bool, F.signbit(x), SF.sign(x), False{}, FB.signbit_g(1n, {==}, l, h, 2147483648, {==}),
    %f31 : {Bool.not(_) == False{} : Bool}
    {==})
  +vmx = Equal.trans(Nat, SW.value(F.mag(x)), Nat.add(v(l), C.shift(32n, C.low(31n, v(h)))), Nat.add(v(l), C.shift(32n, v(h))),
    Equal.cong(Nat, Nat, z => Nat.add(v(l), C.shift(32n, z)), v(U32.and(h, 2147483647)), C.low(31n, v(h)), FB.andm(h, 31n, 2147483647, {==})),
    Equal.cong(Nat, Nat, z => Nat.add(v(l), C.shift(32n, z)), C.low(31n, v(h)), v(h), WW.low_fit(31n, v(h), f31)))
  +vmy = Equal.cong(Nat, Nat, z => C.shift(32n, z), v(U32.and(H, 2147483647)), C.shift(20n, 1023n), hv_one(H, K, hH, hK))
  +hlt = WW.lt_hi(32n, v(l), v(h), 0n, C.shift(20n, 1023n), LW.vb(l),
    %vh : {Nat.is_lt(_, C.shift(20n, 1023n)) == True{} : Bool}
    WW.lt_hi(20n, lq, E, 0n, 1023n, WW.low_fits(20n, v(qh)), hE))
  +cmp = Equal.trans(Bool, X.lt(F.mag(x), F.mag(y)), Nat.is_lt(SW.value(F.mag(x)), SW.value(F.mag(y))), True{}, WA.lt_value(F.mag(x), F.mag(y)),
    %vmx : {Nat.is_lt(_, SW.value(F.mag(y))) == True{} : Bool}
    %vmy : {Nat.is_lt(Nat.add(v(l), C.shift(32n, v(h))), _) == True{} : Bool}
    hlt)
  %Equal.sym(Bool, F.unordered(x, y), False{}, uo) : {F.lt_z(x, y, _, F.zeros(x, y)) == True{} : Bool}
  %Equal.sym(Bool, F.zeros(x, y), False{}, zs) : {F.lt_z(x, y, False{}, _) == True{} : Bool}
  %Equal.sym(Bool, F.signbit(x), False{}, sx) : {F.lt_s(x, y, _, F.signbit(y)) == True{} : Bool}
  %Equal.sym(Bool, F.signbit(y), False{}, hs) : {F.lt_s(x, y, False{}, _) == True{} : Bool}
  cmp

def lt_z_case(+x: WU.U64, +hv: {SW.value(mm(x)) == 0n : Nat}) -> {F.lt(R.to_float(x), F.one()) == True{} : Bool}:
  %Equal.sym(Bool, X.is_zero(mm(x)), Nat.is_eq(0n, 0n), iz(mm(x), 0n, hv)) : {F.lt(R.f53_z(mm(x), _), F.one()) == True{} : Bool}
  {==}

def lt_s_case(+x: WU.U64, +np: Nat, +hv: {SW.value(mm(x)) == 1n+np : Nat}) -> {F.lt(R.to_float(x), F.one()) == True{} : Bool}:
  +hl = hl_of(x, 1n+np, hv)
  +hf = Equal.trans(Bool, C.fits(53n, 1n+np), C.fits(53n, C.low(53n, SW.value(x))), True{}, Equal.cong(Nat, Bool, z => C.fits(53n, z), 1n+np, C.low(53n, SW.value(x)), Equal.sym(Nat, C.low(53n, SW.value(x)), 1n+np, hl)), WW.low_fits(53n, SW.value(x)))
  +j = J(np)
  +Q = X.shl(mm(x), Nat.sub(52n, j))
  +hE = Equal.trans(Bool, Nat.is_lt(Nat.add(j, 970n), 1023n), Nat.is_lt(j, 53n), True{}, WW.lt_cancel_r(j, 53n, 970n), N.le_lt_succ(j, 52n, j52(np, hf)))
  %Equal.sym(Bool, X.is_zero(mm(x)), Nat.is_eq(1n+np, 0n), iz(mm(x), 1n+np, hv)) : {F.lt(R.f53_z(mm(x), _), F.one()) == True{} : Bool}
  %impl_eq(mm(x), np, hv, j, j52(np, hf), WC.bl_succ(np)) : {F.lt(_, F.one()) == True{} : Bool}
  below_one(X.lo(Q), X.hi(Q), Nat.add(j, 970n), 1072693248, 1023, hE, {==}, {==}, {==}, {==}, {==})

def lt_c(+vm: Nat, +x: WU.U64, +hv: {SW.value(mm(x)) == vm : Nat}) -> {F.lt(R.to_float(x), F.one()) == True{} : Bool}:
  match vm:
    case 0n:
      lt_z_case(x, hv)
    case 1n+np:
      lt_s_case(x, np, hv)

# THEOREM (Float64.lt_one)
def lt_one(+x: WU.U64) -> SR.Float64.lt_one(x):
  lt_c(SW.value(mm(x)), x, {==})
