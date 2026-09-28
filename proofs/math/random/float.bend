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
def exp_amt(+j: Nat, +hj: {Nat.is_le(j, 52n) == True{} : Bool}) -> {Nat.sub(1033n, Nat.sub(63n, j)) == Nat.add(970n, j) : Nat}:
  +r = Nat.sub(52n, j)
  +e1 = N.sub_add(52n, j, hj)
  +e3 = Equal.trans(Nat, Nat.add(r, Nat.add(970n, j)), Nat.add(Nat.add(970n, j), r), 1022n, N.add_comm(r, Nat.add(970n, j)), Equal.cong(Nat, Nat, z => Nat.add(970n, z), Nat.add(j, r), 52n, e1))
  %Equal.sym(Nat, Nat.sub(63n, j), Nat.add(11n, r), sub63(j, hj)) : {Nat.sub(1033n, _) == Nat.add(970n, j) : Nat}
  %e3 : {Nat.sub(_, r) == Nat.add(970n, j) : Nat}
  N.add_sub_cancel(r, Nat.add(970n, j))

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

# ---- the rounding of spec/math/f64.bend on m * 2^-53 ----

def x0() -> Nat:
  Nat.sub(SF.zb(), 53n)

# the exponent field of spec round: (2895 + j) + 1075 - 3000 = 970 + j
def ef_spec(+j: Nat) -> {Nat.sub(Nat.add(Nat.add(2895n, j), 1075n), SF.zb()) == Nat.add(970n, j) : Nat}:
  %N.add_comm(1075n, j) : {Nat.sub(Nat.add(2895n, _), 3000n) == Nat.add(970n, j) : Nat}
  {==}

# a significand 2^52 <= q < 2^53 at the ulp 2895 + j is the normal double
# with exponent field 970 + j
def pack_q(+q: Nat, +j: Nat, +hj: {Nat.is_le(j, 52n) == True{} : Bool}, +f53: {C.fits(53n, q) == True{} : Bool}, +n52: {C.fits(52n, q) == False{} : Bool}) -> {SF.pack(False{}, q, Nat.add(2895n, j)) == SF.encode(False{}, Nat.add(970n, j), C.low(52n, q)) : F.F64}:
  +u = Nat.add(2895n, j)
  +l52 = C.low(52n, q)
  +pa = SF.pack_n(False{}, q, u)
  +pb = SF.pack_e(False{}, Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), 0n)
  +pe = SF.pack_e(False{}, Nat.sub(Nat.add(u, 1075n), SF.zb()), l52)
  +pe2 = SF.pack_e(False{}, Nat.add(970n, j), l52)
  +e1 = Equal.cong(Bool, F.F64, c => SF.pick(F.F64, c, pa, pb), C.fits(53n, q), True{}, f53)
  +e2 = Equal.cong(Bool, F.F64, c => SF.pick(F.F64, c, SF.encode(False{}, 0n, q), pe), C.fits(52n, q), False{}, n52)
  +e3 = Equal.cong(Nat, F.F64, z => SF.pack_e(False{}, z, l52), Nat.sub(Nat.add(u, 1075n), SF.zb()), Nat.add(970n, j), ef_spec(j))
  +hle = N.lt_not_le(j, 1077n, N.le_lt_trans(j, 52n, 1077n, hj, {==}))
  ?TODO

def qspec(+m: Nat, +j: Nat) -> Nat:
  SF.pick(Nat, Nat.is_le(x0(), Nat.add(2895n, j)), SF.rne(m, Nat.sub(Nat.add(2895n, j), x0())), C.shift(Nat.sub(x0(), Nat.add(2895n, j)), m))

def qs_b(+m: Nat, +j: Nat, +hj: {Nat.is_le(j, 52n) == True{} : Bool}, +b: Bool, +hb: {Nat.is_le(52n, j) == b : Bool}) -> {qspec(m, j) == C.shift(Nat.sub(52n, j), m) : Nat}:
  match b:
    case False{}:
      Equal.cong(Bool, Nat, c => SF.pick(Nat, c, SF.rne(m, Nat.sub(Nat.add(2895n, j), x0())), C.shift(Nat.sub(x0(), Nat.add(2895n, j)), m)), Nat.is_le(x0(), Nat.add(2895n, j)), False{}, hb)
    case True{}:
      +ej = N.le_antisym(j, 52n, hj, hb)
      %Equal.sym(Nat, j, 52n, ej) : {qspec(m, _) == C.shift(Nat.sub(52n, _), m) : Nat}
      {==}

# the significand spec round forms: m 2^(52 - j)
def qs(+m: Nat, +j: Nat, +hj: {Nat.is_le(j, 52n) == True{} : Bool}) -> {qspec(m, j) == C.shift(Nat.sub(52n, j), m) : Nat}:
  qs_b(m, j, hj, Nat.is_le(52n, j), {==})

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

def dle(+a: Nat, +b: Nat, +h: {Nat.is_le(Nat.double(a), Nat.double(b)) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n _:
      N.zero_le(b)
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, L.false_true(h))
    case 1n+ap 1n+bp:
      dle(ap, bp, h)
