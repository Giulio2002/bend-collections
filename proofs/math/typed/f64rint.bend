import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ./width.bend as WW
import ./w64add.bend as WA
import ./w64sh.bend as SH
import ./u64laws.bend as UL
import ./f64bits.bend as FB
import ./f64round.bend as FR
import ./f64adda.bend as AA
import ./f64tools.bend as T

# Rounding to an integral value (IEEE 754-2019 5.3.1 roundToIntegral, C99
# F.10.6): Trunc.value, Floor.value, Ceil.value and Round.value. A finite x
# below 2^52 in magnitude is m 2^-k (k = Z - xexp(x) >= 1); the
# implementation splits m into q = m >> k, r = m - (q << k) and the half unit
# h = 2^(k-1) (for k >= 64: q = 0, r = m, h = 2^63), moves q up one by the
# direction's rule, and rounds q at the scale Z with round_w (exact: q has at
# most 53 bits). Each piece is the spec's integral(): high(k, m), low(k, m)
# and rne's h, read through the W64 clauses (Shr, Shl, Sub, Lt, Eq, Odd,
# IsZero, Add) and f64tools.rw_value.

# ---- the direction's rule on values ----

def upn(+m: F.RMode, +s: Bool, +q: Nat, +r: Nat, +h: Nat) -> Bool:
  match m:
    case F.Trunc{}:
      False{}
    case F.Floor{}:
      Bool.and(s, Bool.not(Nat.is_eq(r, 0n)))
    case F.Ceil{}:
      Bool.and(Bool.not(s), Bool.not(Nat.is_eq(r, 0n)))
    case F.Even{}:
      Bool.or(Nat.is_lt(h, r), Bool.and(Nat.is_eq(r, h), Nat.is_eq(Nat.mod(q, 2n), 1n)))

def up_v(+m: F.RMode, +s: Bool, +q: WU.U64, +r: WU.U64, +h: WU.U64) -> {F.ri_up(m, s, q, r, h) == upn(m, s, SW.value(q), SW.value(r), SW.value(h)) : Bool}:
  match m:
    case F.Trunc{}:
      {==}
    case F.Floor{}:
      Equal.cong(Bool, Bool, b => Bool.and(s, Bool.not(b)), X.is_zero(r), Nat.is_eq(SW.value(r), 0n), WA.is_zero_value(r))
    case F.Ceil{}:
      Equal.cong(Bool, Bool, b => Bool.and(Bool.not(s), Bool.not(b)), X.is_zero(r), Nat.is_eq(SW.value(r), 0n), WA.is_zero_value(r))
    case F.Even{}:
      +e1 = Equal.cong(Bool, Bool, b => Bool.or(b, Bool.and(X.eq(r, h), X.odd(q))), X.lt(h, r), Nat.is_lt(SW.value(h), SW.value(r)), WA.lt_value(h, r))
      +e2 = Equal.cong(Bool, Bool, b => Bool.or(Nat.is_lt(SW.value(h), SW.value(r)), Bool.and(b, X.odd(q))), X.eq(r, h), Nat.is_eq(SW.value(r), SW.value(h)), WA.eq_value(r, h))
      +e3 = Equal.cong(Bool, Bool, b => Bool.or(Nat.is_lt(SW.value(h), SW.value(r)), Bool.and(Nat.is_eq(SW.value(r), SW.value(h)), b)), X.odd(q), Nat.is_eq(Nat.mod(SW.value(q), 2n), 1n), WA.odd_value(q))
      +b1 = Bool.or(Nat.is_lt(SW.value(h), SW.value(r)), Bool.and(X.eq(r, h), X.odd(q)))
      +b2 = Bool.or(Nat.is_lt(SW.value(h), SW.value(r)), Bool.and(Nat.is_eq(SW.value(r), SW.value(h)), X.odd(q)))
      +b3 = Bool.or(Nat.is_lt(SW.value(h), SW.value(r)), Bool.and(Nat.is_eq(SW.value(r), SW.value(h)), Nat.is_eq(Nat.mod(SW.value(q), 2n), 1n)))
      Equal.trans(Bool, F.ri_up(F.Even{}, s, q, r, h), b1, b3, e1, Equal.trans(Bool, b1, b2, b3, e2, e3))

# ---- q + up, rounded at the scale Z ----

def b64v(+b: Bool) -> {SW.value(F.b64(b)) == SF.b2n(b) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def b2n63(+b: Bool) -> {C.fits(63n, SF.b2n(b)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def addb(+q: WU.U64, +b: Bool, +hq: {C.fits(63n, SW.value(q)) == True{} : Bool}) -> {SW.value(X.add(q, F.b64(b))) == Nat.add(SW.value(q), SF.b2n(b)) : Nat}:
  +Q = SW.value(q)
  e1 = WA.add_value(q, F.b64(b))
  +e2 = Equal.cong(Nat, Nat, n => C.low(64n, Nat.add(Q, n)), SW.value(F.b64(b)), SF.b2n(b), b64v(b))
  +hf = FR.fits_add1(63n, Q, SF.b2n(b), hq, b2n63(b))
  +e3 = WW.low_fit(64n, Nat.add(Q, SF.b2n(b)), hf)
  Equal.trans(Nat, SW.value(X.add(q, F.b64(b))), C.low(64n, Nat.add(Q, SW.value(F.b64(b)))), Nat.add(Q, SF.b2n(b)), e1, Equal.trans(Nat, C.low(64n, Nat.add(Q, SW.value(F.b64(b)))), C.low(64n, Nat.add(Q, SF.b2n(b))), Nat.add(Q, SF.b2n(b)), e2, e3))

def G(+m: F.RMode, +s: Bool, +a: Nat, +b: Nat, +c: Nat) -> F.F64:
  SF.round(s, Nat.add(a, SF.b2n(upn(m, s, a, b, c))), 3000n)

def riq(+m: F.RMode, +s: Bool, +q: WU.U64, +r: WU.U64, +h: WU.U64, +hq: {C.fits(63n, SW.value(q)) == True{} : Bool}) -> {F.ri_q(m, s, q, r, h) == G(m, s, SW.value(q), SW.value(r), SW.value(h)) : F.F64}:
  +u = F.ri_up(m, s, q, r, h)
  +Q = SW.value(q)
  +e1 = T.rw_value(s, 3000n, X.add(q, F.b64(u)), {==})
  +e2 = Equal.cong(Nat, F.F64, n => SF.round(s, n, 3000n), SW.value(X.add(q, F.b64(u))), Nat.add(Q, SF.b2n(u)), addb(q, u, hq))
  +e3 = Equal.cong(Bool, F.F64, b => SF.round(s, Nat.add(Q, SF.b2n(b)), 3000n), u, upn(m, s, Q, SW.value(r), SW.value(h)), up_v(m, s, q, r, h))
  Equal.trans(F.F64, F.ri_q(m, s, q, r, h), SF.round(s, SW.value(X.add(q, F.b64(u))), 3000n), G(m, s, Q, SW.value(r), SW.value(h)), e1, Equal.trans(F.F64, SF.round(s, SW.value(X.add(q, F.b64(u))), 3000n), SF.round(s, Nat.add(Q, SF.b2n(u)), 3000n), G(m, s, Q, SW.value(r), SW.value(h)), e2, e3))

def g3(+m: F.RMode, +s: Bool, +a: Nat, +a2: Nat, +ha: {a == a2 : Nat}, +b: Nat, +b2: Nat, +hb: {b == b2 : Nat}, +c: Nat, +c2: Nat, +hc: {c == c2 : Nat}) -> {G(m, s, a, b, c) == G(m, s, a2, b2, c2) : F.F64}:
  +e1 = Equal.cong(Nat, F.F64, t => G(m, s, t, b, c), a, a2, ha)
  +e2 = Equal.cong(Nat, F.F64, t => G(m, s, a2, t, c), b, b2, hb)
  +e3 = Equal.cong(Nat, F.F64, t => G(m, s, a2, b2, t), c, c2, hc)
  Equal.trans(F.F64, G(m, s, a, b, c), G(m, s, a2, b, c), G(m, s, a2, b2, c2), e1, Equal.trans(F.F64, G(m, s, a2, b, c), G(m, s, a2, b2, c), G(m, s, a2, b2, c2), e2, e3))

# the spec's integral at k = 1 + j, in the same shape
def integ(+m: F.RMode, +s: Bool, +n: Nat, +j: Nat) -> {SF.round(s, SF.integral(m, s, n, 1n+j), 3000n) == G(m, s, C.high(1n+j, n), C.low(1n+j, n), C.shift(j, 1n)) : F.F64}:
  match m:
    case F.Trunc{}:
      Equal.cong(Nat, F.F64, t => SF.round(s, t, 3000n), C.high(1n+j, n), Nat.add(C.high(1n+j, n), 0n), Equal.sym(Nat, Nat.add(C.high(1n+j, n), 0n), C.high(1n+j, n), N.add_zero(C.high(1n+j, n))))
    case F.Floor{}:
      {==}
    case F.Ceil{}:
      {==}
    case F.Even{}:
      {==}

# ---- fewer than 64 fractional bits ----

def le64(+j: Nat) -> {Nat.is_le(64n, Nat.add(1n+j, 63n)) == True{} : Bool}:
  L.subst(Nat, t => {Nat.is_le(63n, t) == True{} : Bool}, Nat.add(63n, j), Nat.add(j, 63n), NA.add_comm(63n, j), N.le_add_right(63n, j))

def hfit(+j: Nat, +V: Nat, +hv: {C.fits(64n, V) == True{} : Bool}) -> {C.fits(63n, C.high(1n+j, V)) == True{} : Bool}:
  +f = SH.fits_mono(64n, Nat.add(1n+j, 63n), V, le64(j), hv)
  Equal.trans(Bool, C.fits(63n, C.high(1n+j, V)), C.fits(Nat.add(1n+j, 63n), V), True{}, Equal.sym(Bool, C.fits(Nat.add(1n+j, 63n), V), C.fits(63n, C.high(1n+j, V)), FR.fits_hc(1n+j, 63n, V)), f)

# 2^(k-1) as a word
def half_v(+j: Nat, +hb: {Nat.is_lt(1n+j, 64n) == True{} : Bool}) -> {SW.value(X.shl(WU.U64{1, 0}, Nat.sub(1n+j, 1n))) == C.shift(j, 1n) : Nat}:
  +hj = N.lt_trans(j, 1n+j, 64n, N.lt_succ(j), hb)
  +hl = N.lt_le(1n+j, 64n, hb)
  +hj1 = L.subst(Nat, t => {Nat.is_le(t, 64n) == True{} : Bool}, 1n+j, Nat.add(j, 1n), Equal.sym(Nat, Nat.add(j, 1n), 1n+j, Equal.trans(Nat, Nat.add(j, 1n), 1n+Nat.add(j, 0n), 1n+j, N.add_succ(j, 0n), Equal.cong(Nat, Nat, t => 1n+t, Nat.add(j, 0n), j, N.add_zero(j)))), hl)
  +e = AA.shl_v(WU.U64{1, 0}, j, 1n, hj, hj1, {==})
  L.subst(Nat, t => {SW.value(X.shl(WU.U64{1, 0}, t)) == C.shift(j, 1n) : Nat}, j, Nat.sub(j, 0n), Equal.sym(Nat, Nat.sub(j, 0n), j, N.sub_zero(j)), e)

def small_case(+m: F.RMode, +s: Bool, +w: WU.U64, +j: Nat, +hb: {Nat.is_lt(1n+j, 64n) == True{} : Bool}) -> {F.ri_k(m, s, w, 1n+j, True{}) == G(m, s, C.high(1n+j, SW.value(w)), C.low(1n+j, SW.value(w)), C.shift(j, 1n)) : F.F64}:
  +V = SW.value(w)
  +q = X.shr(w, 1n+j)
  +sq = X.shl(q, 1n+j)
  +r = X.sub(w, sq)
  +h = X.shl(WU.U64{1, 0}, Nat.sub(1n+j, 1n))
  +Hq = C.high(1n+j, V)
  +Lq = C.low(1n+j, V)
  +S = C.shift(1n+j, Hq)
  eq1 = SH.shr_value(w, 1n+j)
  eq2 = SH.shr_value(w, 1n+j)
  eq3 = SH.shr_value(w, 1n+j)
  +hQ = L.subst(Nat, t => {C.fits(63n, t) == True{} : Bool}, Hq, SW.value(q), Equal.sym(Nat, SW.value(q), Hq, eq1), hfit(j, V, UL.vb(w)))
  esl0 = SH.shl_value(q, 1n+j, hb)
  +esl1 = Equal.cong(Nat, Nat, t => C.low(64n, C.shift(1n+j, t)), SW.value(q), Hq, eq2)
  +eV = WW.low_high(1n+j, V)
  +eV2 = WW.low_high(1n+j, V)
  +hSV0 = L.subst(Nat, t => {Nat.is_le(S, t) == True{} : Bool}, Nat.add(S, Lq), Nat.add(Lq, S), NA.add_comm(S, Lq), N.le_add_right(S, Lq))
  +hSV = L.subst(Nat, t => {Nat.is_le(S, t) == True{} : Bool}, Nat.add(Lq, S), V, Equal.sym(Nat, V, Nat.add(Lq, S), eV), hSV0)
  +hSf = SH.fits_lek(64n, S, V, hSV, UL.vb(w))
  +esl = Equal.trans(Nat, SW.value(sq), C.low(64n, S), S, Equal.trans(Nat, SW.value(sq), C.low(64n, C.shift(1n+j, SW.value(q))), C.low(64n, S), esl0, esl1), WW.low_fit(64n, S, hSf))
  +esl2 = Equal.trans(Nat, SW.value(sq), C.low(64n, S), S, Equal.trans(Nat, SW.value(sq), C.low(64n, C.shift(1n+j, SW.value(q))), C.low(64n, S), SH.shl_value(q, 1n+j, hb), Equal.cong(Nat, Nat, t => C.low(64n, C.shift(1n+j, t)), SW.value(q), Hq, eq3)), WW.low_fit(64n, S, SH.fits_lek(64n, S, V, L.subst(Nat, t => {Nat.is_le(S, t) == True{} : Bool}, Nat.add(Lq, S), V, Equal.sym(Nat, V, Nat.add(Lq, S), eV2), L.subst(Nat, t => {Nat.is_le(S, t) == True{} : Bool}, Nat.add(S, Lq), Nat.add(Lq, S), NA.add_comm(S, Lq), N.le_add_right(S, Lq))), UL.vb(w))))
  +hle = L.subst(Nat, t => {Nat.is_le(t, V) == True{} : Bool}, S, SW.value(sq), Equal.sym(Nat, SW.value(sq), S, esl), hSV)
  er0 = WA.sub_value(w, sq, hle)
  +er1 = Equal.cong(Nat, Nat, t => Nat.sub(V, t), SW.value(sq), S, esl2)
  +eV3 = WW.low_high(1n+j, V)
  +er2 = Equal.cong(Nat, Nat, t => Nat.sub(t, S), V, Nat.add(Lq, S), eV3)
  +er3 = FR.sub_add_l(Lq, S)
  +er = Equal.trans(Nat, SW.value(r), Nat.sub(V, SW.value(sq)), Lq, er0, Equal.trans(Nat, Nat.sub(V, SW.value(sq)), Nat.sub(V, S), Lq, er1, Equal.trans(Nat, Nat.sub(V, S), Nat.sub(Nat.add(Lq, S), S), Lq, er2, er3)))
  +ehv = half_v(j, hb)
  +e0 = riq(m, s, q, r, h, hQ)
  e4 = SH.shr_value(w, 1n+j)
  Equal.trans(F.F64, F.ri_q(m, s, q, r, h), G(m, s, SW.value(q), SW.value(r), SW.value(h)), G(m, s, Hq, Lq, C.shift(j, 1n)), e0, g3(m, s, SW.value(q), Hq, e4, SW.value(r), Lq, er, SW.value(h), C.shift(j, 1n), ehv))

# ---- 64 or more fractional bits: the integer part is 0 ----

def c63(+one: Nat, +h1: {one == 1n : Nat}, +c: U32, +hc: {c == U32{WD.pw(32n, 31n)} : U32}) -> {SW.value(WU.U64{0, c}) == C.shift(63n, one) : Nat}:
  Equal.trans(Nat, C.shift(32n, U32.to_nat(c)), C.shift(32n, C.shift(31n, one)), C.shift(63n, one), Equal.cong(Nat, Nat, z => C.shift(32n, z), U32.to_nat(c), C.shift(31n, one), FB.pwv(31n, {==}, one, h1, c, hc)), Equal.sym(Nat, C.shift(63n, one), C.shift(32n, C.shift(31n, one)), WW.shift_comp(32n, 31n, one)))

# V < 2^k is not above 2^k
def nlt(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +V: Nat, +hf: {C.fits(k, V) == True{} : Bool}) -> {Nat.is_lt(C.shift(k, one), V) == False{} : Bool}:
  +hl = Equal.trans(Bool, Nat.is_lt(V, C.shift(k, one)), C.fits(k, V), True{}, FR.lt_fit(k, one, h1, V), hf)
  N.le_not_lt(C.shift(k, one), V, N.lt_le(V, C.shift(k, one), hl))

def upn_big(+m: F.RMode, +s: Bool, +V: Nat, +a: Nat, +b: Nat, +la: {Nat.is_lt(a, V) == False{} : Bool}, +lb: {Nat.is_lt(b, V) == False{} : Bool}) -> {upn(m, s, 0n, V, a) == upn(m, s, 0n, V, b) : Bool}:
  match m:
    case F.Trunc{}:
      {==}
    case F.Floor{}:
      {==}
    case F.Ceil{}:
      {==}
    case F.Even{}:
      +ea = Equal.trans(Bool, upn(F.Even{}, s, 0n, V, a), Bool.and(Nat.is_eq(V, a), False{}), False{}, Equal.cong(Bool, Bool, t => Bool.or(t, Bool.and(Nat.is_eq(V, a), False{})), Nat.is_lt(a, V), False{}, la), FR.and_f(Nat.is_eq(V, a)))
      +eb = Equal.trans(Bool, upn(F.Even{}, s, 0n, V, b), Bool.and(Nat.is_eq(V, b), False{}), False{}, Equal.cong(Bool, Bool, t => Bool.or(t, Bool.and(Nat.is_eq(V, b), False{})), Nat.is_lt(b, V), False{}, lb), FR.and_f(Nat.is_eq(V, b)))
      Equal.trans(Bool, upn(F.Even{}, s, 0n, V, a), False{}, upn(F.Even{}, s, 0n, V, b), ea, Equal.sym(Bool, upn(F.Even{}, s, 0n, V, b), False{}, eb))

def large_case(+m: F.RMode, +s: Bool, +w: WU.U64, +j: Nat, +hb: {Nat.is_le(64n, 1n+j) == True{} : Bool}, +hw: {C.fits(53n, SW.value(w)) == True{} : Bool}, +one: Nat, +h1: {one == 1n : Nat}, +c: U32, +hc: {c == U32{WD.pw(32n, 31n)} : U32}) -> {F.ri_q(m, s, WU.U64{0, 0}, w, WU.U64{0, c}) == SF.round(s, SF.integral(m, s, SW.value(w), 1n+j), 3000n) : F.F64}:
  +V = SW.value(w)
  +vc = SW.value(WU.U64{0, c})
  +h53 = N.le_trans(53n, 64n, 1n+j, {==}, hb)
  +f = SH.fits_mono(53n, 1n+j, V, h53, hw)
  +eh = N.eq_from_is_eq(C.high(1n+j, V), 0n, f)
  +el = WW.low_fit(1n+j, V, SH.fits_mono(53n, 1n+j, V, N.le_trans(53n, 64n, 1n+j, {==}, hb), hw))
  +fj = SH.fits_mono(53n, j, V, N.le_trans(53n, 63n, j, {==}, hb), hw)
  +la = nlt(j, 1n, {==}, V, fj)
  +lb0 = nlt(63n, one, h1, V, SH.fits_mono(53n, 63n, V, {==}, hw))
  +lb = L.subst(Nat, t => {Nat.is_lt(t, V) == False{} : Bool}, C.shift(63n, one), vc, Equal.sym(Nat, vc, C.shift(63n, one), c63(one, h1, c, hc)), lb0)
  +eu = upn_big(m, s, V, C.shift(j, 1n), vc, la, lb)
  +e0 = riq(m, s, WU.U64{0, 0}, w, WU.U64{0, c}, {==})
  +e1 = Equal.sym(F.F64, SF.round(s, SF.integral(m, s, V, 1n+j), 3000n), G(m, s, C.high(1n+j, V), C.low(1n+j, V), C.shift(j, 1n)), integ(m, s, V, j))
  +e2 = Equal.sym(F.F64, G(m, s, C.high(1n+j, V), C.low(1n+j, V), C.shift(j, 1n)), G(m, s, 0n, V, C.shift(j, 1n)), g3(m, s, C.high(1n+j, V), 0n, eh, C.low(1n+j, V), V, el, C.shift(j, 1n), C.shift(j, 1n), {==}))
  +e3 = Equal.cong(Bool, F.F64, t => SF.round(s, SF.b2n(t), 3000n), upn(m, s, 0n, V, vc), upn(m, s, 0n, V, C.shift(j, 1n)), Equal.sym(Bool, upn(m, s, 0n, V, C.shift(j, 1n)), upn(m, s, 0n, V, vc), eu))
  Equal.trans(F.F64, F.ri_q(m, s, WU.U64{0, 0}, w, WU.U64{0, c}), G(m, s, 0n, V, vc), SF.round(s, SF.integral(m, s, V, 1n+j), 3000n), e0, Equal.trans(F.F64, G(m, s, 0n, V, vc), G(m, s, 0n, V, C.shift(j, 1n)), SF.round(s, SF.integral(m, s, V, 1n+j), 3000n), e3, Equal.trans(F.F64, G(m, s, 0n, V, C.shift(j, 1n)), G(m, s, C.high(1n+j, V), C.low(1n+j, V), C.shift(j, 1n)), SF.round(s, SF.integral(m, s, V, 1n+j), 3000n), e2, e1)))

def rik_c(+m: F.RMode, +s: Bool, +w: WU.U64, +j: Nat, +hw: {C.fits(53n, SW.value(w)) == True{} : Bool}, +b: Bool, +hb: {Nat.is_lt(1n+j, 64n) == b : Bool}) -> {F.ri_k(m, s, w, 1n+j, b) == SF.round(s, SF.integral(m, s, SW.value(w), 1n+j), 3000n) : F.F64}:
  match b:
    case True{}:
      +V = SW.value(w)
      Equal.trans(F.F64, F.ri_k(m, s, w, 1n+j, True{}), G(m, s, C.high(1n+j, V), C.low(1n+j, V), C.shift(j, 1n)), SF.round(s, SF.integral(m, s, V, 1n+j), 3000n), small_case(m, s, w, j, hb), Equal.sym(F.F64, SF.round(s, SF.integral(m, s, V, 1n+j), 3000n), G(m, s, C.high(1n+j, V), C.low(1n+j, V), C.shift(j, 1n)), integ(m, s, V, j)))
    case False{}:
      large_case(m, s, w, j, N.not_lt_le(1n+j, 64n, hb), hw, 1n, {==}, 2147483648, {==})

def rik(+m: F.RMode, +s: Bool, +w: WU.U64, +k: Nat, +hk: {Nat.is_le(1n, k) == True{} : Bool}, +hw: {C.fits(53n, SW.value(w)) == True{} : Bool}) -> {F.ri_k(m, s, w, k, Nat.is_lt(k, 64n)) == SF.round(s, SF.integral(m, s, SW.value(w), k), 3000n) : F.F64}:
  match k:
    case 0n:
      Empty.absurd({F.ri_k(m, s, w, 0n, Nat.is_lt(0n, 64n)) == SF.round(s, SF.integral(m, s, SW.value(w), 0n), 3000n) : F.F64}, UL.true_ne_false(Equal.sym(Bool, False{}, True{}, hk)))
    case 1n+ +j:
      rik_c(m, s, w, j, hw, Nat.is_lt(1n+j, 64n), {==})

# ---- the finite case and the special values ----

def RI(+m: F.RMode, +x: F.F64) -> F.F64:
  SF.round(SF.sign(x), SF.integral(m, SF.sign(x), SF.mant(x), Nat.sub(SF.zb(), SF.xexp(x))), SF.zb())

def ti_fin(+m: F.RMode, +x: F.F64, +c: Bool, +hc: {Nat.is_le(3000n, F.dexp(x)) == c : Bool}) -> {F.ri_fin(m, x, c) == SF.pick(F.F64, c, x, RI(m, x)) : F.F64}:
  match c:
    case True{}:
      {==}
    case False{}:
      +k = Nat.sub(3000n, F.dexp(x))
      +hk = FR.lt_sub_pos(F.dexp(x), 3000n, N.not_le_lt(3000n, F.dexp(x), hc))
      +hw = L.subst(Nat, t => {C.fits(53n, t) == True{} : Bool}, SF.mant(x), SW.value(F.dmant(x)), Equal.sym(Nat, SW.value(F.dmant(x)), SF.mant(x), T.dmant_value(x)), T.mant_fits(x))
      +e0 = rik(m, F.signbit(x), F.dmant(x), k, hk, hw)
      +e1 = Equal.cong(Bool, F.F64, t => SF.round(t, SF.integral(m, t, SW.value(F.dmant(x)), k), 3000n), F.signbit(x), SF.sign(x), FB.signbit_value(x))
      +e2 = Equal.cong(Nat, F.F64, t => SF.round(SF.sign(x), SF.integral(m, SF.sign(x), t, k), 3000n), SW.value(F.dmant(x)), SF.mant(x), T.dmant_value(x))
      +e3 = Equal.cong(Nat, F.F64, t => SF.round(SF.sign(x), SF.integral(m, SF.sign(x), SF.mant(x), Nat.sub(3000n, t)), 3000n), F.dexp(x), SF.xexp(x), T.dexp_value(x))
      +r0 = SF.round(F.signbit(x), SF.integral(m, F.signbit(x), SW.value(F.dmant(x)), k), 3000n)
      +r1 = SF.round(SF.sign(x), SF.integral(m, SF.sign(x), SW.value(F.dmant(x)), k), 3000n)
      +r2 = SF.round(SF.sign(x), SF.integral(m, SF.sign(x), SF.mant(x), k), 3000n)
      Equal.trans(F.F64, F.ri_fin(m, x, False{}), r0, RI(m, x), e0, Equal.trans(F.F64, r0, r1, RI(m, x), e1, Equal.trans(F.F64, r1, r2, RI(m, x), e2, e3)))

def ti_c(+m: F.RMode, +x: F.F64, +t: Bool, +z: Bool, +hz: {X.is_zero(F.frac(x)) == z : Bool}) -> {F.ri_cls(m, x, t) == SF.pick(F.F64, Bool.and(t, Bool.not(z)), SF.qnan(), SF.pick(F.F64, Bool.or(Bool.and(t, z), Nat.is_le(SF.zb(), SF.xexp(x))), x, RI(m, x))) : F.F64}:
  match t z:
    case True{} True{}:
      Equal.cong(Bool, F.F64, b => F.nan_or(x, Bool.not(b)), X.is_zero(F.frac(x)), True{}, hz)
    case True{} False{}:
      Equal.cong(Bool, F.F64, b => F.nan_or(x, Bool.not(b)), X.is_zero(F.frac(x)), False{}, hz)
    case False{} _:
      +e1 = ti_fin(m, x, Nat.is_le(3000n, F.dexp(x)), {==})
      +e2 = Equal.cong(Nat, F.F64, u => SF.pick(F.F64, Nat.is_le(3000n, u), x, RI(m, x)), F.dexp(x), SF.xexp(x), T.dexp_value(x))
      Equal.trans(F.F64, F.ri_fin(m, x, Nat.is_le(3000n, F.dexp(x))), SF.pick(F.F64, Nat.is_le(3000n, F.dexp(x)), x, RI(m, x)), SF.pick(F.F64, Nat.is_le(3000n, SF.xexp(x)), x, RI(m, x)), e1, e2)

def ti_value(+m: F.RMode, +x: F.F64) -> {F.to_integral(m, x) == SF.to_integral(m, x) : F.F64}:
  +e1 = Equal.cong(Nat, F.F64, u => F.ri_cls(m, x, Nat.is_eq(u, 2047n)), F.exp_field(x), SF.efield(x), T.ea(x))
  Equal.trans(F.F64, F.to_integral(m, x), F.ri_cls(m, x, Nat.is_eq(SF.efield(x), 2047n)), SF.to_integral(m, x), e1, ti_c(m, x, Nat.is_eq(SF.efield(x), 2047n), Nat.is_eq(SF.frac(x), 0n), T.fz(x)))

def trunc_value(+x: F.F64) -> SF.Trunc.value(x):
  ti_value(F.Trunc{}, x)

def floor_value(+x: F.F64) -> SF.Floor.value(x):
  ti_value(F.Floor{}, x)

def ceil_value(+x: F.F64) -> SF.Ceil.value(x):
  ti_value(F.Ceil{}, x)

def round_value(+x: F.F64) -> SF.Round.value(x):
  ti_value(F.Even{}, x)
