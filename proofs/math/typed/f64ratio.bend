import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../../src/math/num.bend as NE
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ./width.bend as WW
import ./w64add.bend as WA
import ./w64sh.bend as SH
import ./w64clz.bend as CZ
import ./f64bits.bend as FB
import ./f64rtools.bend as RT
import ./f64adda.bend as AA
import ./f64divf.bend as DF
import ./f64nrp.bend as NR
import ./f64bl.bend as BL
import ./f64tools.bend as T
import ./f64conv.bend as CV

# as_integer_ratio (python_style_math_stdlib_design.pdf 3.3; CPython's
# float.as_integer_ratio, with the denominator as its exponent):
# AsIntegerRatio.value. Below 2^52 the significand loses its trailing zeros
# into the denominator (ctz, one halving at a time, is the spec's tz by
# Odd.value / Half.value); above, it is shifted left and must fit 64 bits
# (Clz.value, f64nrp.tbf / tbn, as in f64conv).

# ---- trailing zeros ----

def cz(+fuel: Nat, +w: WU.U64, +o: Bool, +ho: {X.odd(w) == o : Bool}) -> {F.ctz_go(fuel, w, o) == SF.tz(fuel, SW.value(w)) : Nat}:
  match fuel o:
    case 0n _:
      {==}
    case 1n+ +f True{}:
      +h = Equal.trans(Bool, Nat.is_eq(Nat.mod(SW.value(w), 2n), 1n), X.odd(w), True{}, Equal.sym(Bool, X.odd(w), Nat.is_eq(Nat.mod(SW.value(w), 2n), 1n), WA.odd_value(w)), ho)
      Equal.sym(Nat, SF.tz(1n+f, SW.value(w)), 0n, Equal.cong(Bool, Nat, b => SF.pick(Nat, b, 0n, 1n+SF.tz(f, Nat.div(SW.value(w), 2n))), Nat.is_eq(Nat.mod(SW.value(w), 2n), 1n), True{}, h))
    case 1n+ +f False{}:
      +h = Equal.trans(Bool, Nat.is_eq(Nat.mod(SW.value(w), 2n), 1n), X.odd(w), False{}, Equal.sym(Bool, X.odd(w), Nat.is_eq(Nat.mod(SW.value(w), 2n), 1n), WA.odd_value(w)), ho)
      +e0 = Equal.cong(Bool, Nat, b => SF.pick(Nat, b, 0n, 1n+SF.tz(f, Nat.div(SW.value(w), 2n))), Nat.is_eq(Nat.mod(SW.value(w), 2n), 1n), False{}, h)
      +e1 = cz(f, X.half(w), X.odd(X.half(w)), {==})
      +e2 = Equal.cong(Nat, Nat, t => SF.tz(f, t), SW.value(X.half(w)), Nat.div(SW.value(w), 2n), WA.half_value(w))
      +e3 = Equal.trans(Nat, F.ctz_go(f, X.half(w), X.odd(X.half(w))), SF.tz(f, SW.value(X.half(w))), SF.tz(f, Nat.div(SW.value(w), 2n)), e1, e2)
      Equal.trans(Nat, 1n+F.ctz_go(f, X.half(w), X.odd(X.half(w))), 1n+SF.tz(f, Nat.div(SW.value(w), 2n)), SF.tz(1n+f, SW.value(w)), Equal.cong(Nat, Nat, t => 1n+t, F.ctz_go(f, X.half(w), X.odd(X.half(w))), SF.tz(f, Nat.div(SW.value(w), 2n)), e3), Equal.sym(Nat, SF.tz(1n+f, SW.value(w)), 1n+SF.tz(f, Nat.div(SW.value(w), 2n)), e0))

def ctz_v(+w: WU.U64) -> {F.ctz(w) == SF.tz(64n, SW.value(w)) : Nat}:
  cz(64n, w, X.odd(w), {==})

# ---- below 2^52 ----

def SMALL(+x: F.F64) -> Result<&2, &2, NE.NumError, SF.Rat>:
  Done{SF.Rat{SF.sign(x), C.high(Nat.min(SF.tz(64n, SF.mant(x)), Nat.sub(SF.zb(), SF.xexp(x))), SF.mant(x)), Nat.sub(Nat.sub(SF.zb(), SF.xexp(x)), Nat.min(SF.tz(64n, SF.mant(x)), Nat.sub(SF.zb(), SF.xexp(x))))}}

def G(+s: Bool, +V: Nat, +k: Nat, +j: Nat) -> Result<&2, &2, NE.NumError, SF.Rat>:
  Done{SF.Rat{s, C.high(j, V), Nat.sub(k, j)}}

def small_v(+x: F.F64) -> {SF.rtriple(F.ar_small(F.signbit(x), F.dmant(x), Nat.sub(3000n, F.dexp(x)), Nat.min(F.ctz(F.dmant(x)), Nat.sub(3000n, F.dexp(x))))) == SMALL(x) : Result<&2, &2, NE.NumError, SF.Rat>}:
  +w = F.dmant(x)
  +V = SW.value(w)
  +k = Nat.sub(3000n, F.dexp(x))
  +j = Nat.min(F.ctz(w), k)
  +e1 = Equal.cong(Nat, Result<&2, &2, NE.NumError, SF.Rat>, t => Done{SF.Rat{F.signbit(x), t, Nat.sub(k, j)}}, SW.value(X.shr(w, j)), C.high(j, V), SH.shr_value(w, j))
  +e2 = Equal.cong(Nat, Result<&2, &2, NE.NumError, SF.Rat>, t => G(F.signbit(x), V, k, Nat.min(t, k)), F.ctz(w), SF.tz(64n, V), ctz_v(w))
  +e3 = Equal.cong(Bool, Result<&2, &2, NE.NumError, SF.Rat>, t => G(t, V, k, Nat.min(SF.tz(64n, V), k)), F.signbit(x), SF.sign(x), FB.signbit_value(x))
  +e4 = Equal.cong(Nat, Result<&2, &2, NE.NumError, SF.Rat>, t => G(SF.sign(x), t, k, Nat.min(SF.tz(64n, t), k)), V, SF.mant(x), T.dmant_value(x))
  +e5 = Equal.cong(Nat, Result<&2, &2, NE.NumError, SF.Rat>, t => G(SF.sign(x), SF.mant(x), Nat.sub(3000n, t), Nat.min(SF.tz(64n, SF.mant(x)), Nat.sub(3000n, t))), F.dexp(x), SF.xexp(x), T.dexp_value(x))
  +r1 = G(F.signbit(x), V, k, j)
  +r2 = G(F.signbit(x), V, k, Nat.min(SF.tz(64n, V), k))
  +r3 = G(SF.sign(x), V, k, Nat.min(SF.tz(64n, V), k))
  +r4 = G(SF.sign(x), SF.mant(x), k, Nat.min(SF.tz(64n, SF.mant(x)), k))
  Equal.trans(Result<&2, &2, NE.NumError, SF.Rat>, Done{SF.Rat{F.signbit(x), SW.value(X.shr(w, j)), Nat.sub(k, j)}}, r1, SMALL(x), e1, Equal.trans(Result<&2, &2, NE.NumError, SF.Rat>, r1, r2, SMALL(x), e2, Equal.trans(Result<&2, &2, NE.NumError, SF.Rat>, r2, r3, SMALL(x), e3, Equal.trans(Result<&2, &2, NE.NumError, SF.Rat>, r3, r4, SMALL(x), e4, e5))))

# ---- at least 2^52 ----

def BIGR(+s: Bool, +n: Nat) -> Result<&2, &2, NE.NumError, SF.Rat>:
  SF.pick(Result<&2, &2, NE.NumError, SF.Rat>, C.fits(64n, n), Done{SF.Rat{s, n, 0n}}, Fail{NE.Overflow{}})

def ab_c(+s: Bool, +w: WU.U64, +k: Nat, +hz: {Nat.is_eq(SW.value(w), 0n) == False{} : Bool}, +c: Bool, +hc: {Nat.is_le(Nat.add(k, M.bit_length(SW.value(w))), 64n) == c : Bool}) -> {SF.rtriple(F.ar_big(s, w, k, c)) == BIGR(s, C.shift(k, SW.value(w))) : Result<&2, &2, NE.NumError, SF.Rat>}:
  match c:
    case True{}:
      +V = SW.value(w)
      +B = M.bit_length(V)
      +S = C.shift(k, V)
      +hb1 = BL.bl_pos(V, hz, B, {==})
      +hkl = Equal.trans(Bool, Nat.is_lt(k, Nat.add(k, B)), Nat.is_lt(Nat.add(k, 0n), Nat.add(k, B)), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(t, Nat.add(k, B)), k, Nat.add(k, 0n), Equal.sym(Nat, Nat.add(k, 0n), k, N.add_zero(k))), N.lt_add_left(0n, B, k, N.succ_le_lt(0n, B, hb1)))
      +hk = N.lt_le_trans(k, Nat.add(k, B), 64n, hkl, hc)
      +ev = AA.shl_v(w, k, B, hk, hc, RT.bl_fit(V))
      +hf = SH.fits_mono(Nat.add(k, B), 64n, S, hc, NR.tbf(k, V, Nat.add(k, B), {==}))
      +e1 = Equal.cong(Nat, Result<&2, &2, NE.NumError, SF.Rat>, n => Done{SF.Rat{s, n, 0n}}, SW.value(X.shl(w, k)), S, ev)
      +e2 = Equal.cong(Bool, Result<&2, &2, NE.NumError, SF.Rat>, b => SF.pick(Result<&2, &2, NE.NumError, SF.Rat>, b, Done{SF.Rat{s, S, 0n}}, Fail{NE.Overflow{}}), C.fits(64n, S), True{}, hf)
      Equal.trans(Result<&2, &2, NE.NumError, SF.Rat>, Done{SF.Rat{s, SW.value(X.shl(w, k)), 0n}}, Done{SF.Rat{s, S, 0n}}, BIGR(s, S), e1, Equal.sym(Result<&2, &2, NE.NumError, SF.Rat>, BIGR(s, S), Done{SF.Rat{s, S, 0n}}, e2))
    case False{}:
      +V = SW.value(w)
      +B = M.bit_length(V)
      +S = C.shift(k, V)
      +J = Nat.add(k, B)
      +K = Nat.sub(J, 1n)
      +hJ = N.not_le_lt(J, 64n, hc)
      +hJ1 = N.le_trans(1n, 65n, J, {==}, N.lt_succ_le_succ(64n, J, hJ))
      +ek = Equal.sym(Nat, Nat.add(1n, K), J, N.sub_add(J, 1n, hJ1))
      +hK = N.lt_succ_le(64n, K, L.subst(Nat, t => {Nat.is_lt(64n, t) == True{} : Bool}, J, 1n+K, ek, hJ))
      +nf = DF.nfit_mono(64n, K, S, hK, NR.tbn(k, V, K, hz, ek))
      Equal.sym(Result<&2, &2, NE.NumError, SF.Rat>, BIGR(s, S), Fail{NE.Overflow{}}, Equal.cong(Bool, Result<&2, &2, NE.NumError, SF.Rat>, b => SF.pick(Result<&2, &2, NE.NumError, SF.Rat>, b, Done{SF.Rat{s, S, 0n}}, Fail{NE.Overflow{}}), C.fits(64n, S), False{}, nf))

def big_v(+x: F.F64, +hc: {Nat.is_le(3000n, F.dexp(x)) == True{} : Bool}) -> {SF.rtriple(F.ar_big(F.signbit(x), F.dmant(x), Nat.sub(F.dexp(x), 3000n), Nat.is_le(Nat.add(Nat.sub(F.dexp(x), 3000n), Nat.sub(64n, X.clz(F.dmant(x)))), 64n))) == BIGR(SF.sign(x), C.shift(Nat.sub(SF.xexp(x), SF.zb()), SF.mant(x))) : Result<&2, &2, NE.NumError, SF.Rat>}:
  +w = F.dmant(x)
  +V = SW.value(w)
  +B = M.bit_length(V)
  +k = Nat.sub(F.dexp(x), 3000n)
  +hB = N.le_trans(B, 53n, 64n, BL.bl_le(53n, V, T.mw53(x), Nat.is_le(B, 53n), {==}), {==})
  +eb = Equal.trans(Nat, Nat.sub(64n, X.clz(w)), Nat.sub(64n, Nat.sub(64n, B)), B, Equal.cong(Nat, Nat, t => Nat.sub(64n, t), X.clz(w), Nat.sub(64n, B), CZ.clz_value(w)), T.subsub(64n, B, hB))
  +e0 = Equal.cong(Nat, Result<&2, &2, NE.NumError, SF.Rat>, t => SF.rtriple(F.ar_big(F.signbit(x), w, k, Nat.is_le(Nat.add(k, t), 64n))), Nat.sub(64n, X.clz(w)), B, eb)
  +e1 = ab_c(F.signbit(x), w, k, CV.big_nz(x, hc), Nat.is_le(Nat.add(k, B), 64n), {==})
  +e2 = Equal.cong(Bool, Result<&2, &2, NE.NumError, SF.Rat>, t => BIGR(t, C.shift(k, V)), F.signbit(x), SF.sign(x), FB.signbit_value(x))
  +e3 = Equal.cong(Nat, Result<&2, &2, NE.NumError, SF.Rat>, t => BIGR(SF.sign(x), C.shift(k, t)), V, SF.mant(x), T.dmant_value(x))
  +e4 = Equal.cong(Nat, Result<&2, &2, NE.NumError, SF.Rat>, t => BIGR(SF.sign(x), C.shift(Nat.sub(t, 3000n), SF.mant(x))), F.dexp(x), SF.xexp(x), T.dexp_value(x))
  +r0 = SF.rtriple(F.ar_big(F.signbit(x), w, k, Nat.is_le(Nat.add(k, Nat.sub(64n, X.clz(w))), 64n)))
  +r1 = SF.rtriple(F.ar_big(F.signbit(x), w, k, Nat.is_le(Nat.add(k, B), 64n)))
  +r2 = BIGR(F.signbit(x), C.shift(k, V))
  +r3 = BIGR(SF.sign(x), C.shift(k, V))
  +r4 = BIGR(SF.sign(x), C.shift(k, SF.mant(x)))
  +r5 = BIGR(SF.sign(x), C.shift(Nat.sub(SF.xexp(x), SF.zb()), SF.mant(x)))
  Equal.trans(Result<&2, &2, NE.NumError, SF.Rat>, r0, r1, r5, e0, Equal.trans(Result<&2, &2, NE.NumError, SF.Rat>, r1, r2, r5, e1, Equal.trans(Result<&2, &2, NE.NumError, SF.Rat>, r2, r3, r5, e2, Equal.trans(Result<&2, &2, NE.NumError, SF.Rat>, r3, r4, r5, e3, e4))))

# ---- the cases ----

def FINR(+x: F.F64, +c: Bool) -> Result<&2, &2, NE.NumError, SF.Rat>:
  SF.pick(Result<&2, &2, NE.NumError, SF.Rat>, c, BIGR(SF.sign(x), CV.IPc(x, c)), SMALL(x))

def arf_c(+x: F.F64, +c: Bool, +hc: {Nat.is_le(3000n, F.dexp(x)) == c : Bool}) -> {SF.rtriple(F.ar_fin(x, c)) == FINR(x, c) : Result<&2, &2, NE.NumError, SF.Rat>}:
  match c:
    case True{}:
      big_v(x, hc)
    case False{}:
      small_v(x)

def arz_c(+x: F.F64, +iz: Bool) -> {SF.rtriple(F.ar_z(x, iz)) == SF.pick(Result<&2, &2, NE.NumError, SF.Rat>, iz, Done{SF.Rat{False{}, 0n, 0n}}, FINR(x, Nat.is_le(SF.zb(), SF.xexp(x)))) : Result<&2, &2, NE.NumError, SF.Rat>}:
  match iz:
    case True{}:
      {==}
    case False{}:
      +e1 = arf_c(x, Nat.is_le(3000n, F.dexp(x)), {==})
      +e2 = Equal.cong(Nat, Result<&2, &2, NE.NumError, SF.Rat>, t => FINR(x, Nat.is_le(3000n, t)), F.dexp(x), SF.xexp(x), T.dexp_value(x))
      Equal.trans(Result<&2, &2, NE.NumError, SF.Rat>, SF.rtriple(F.ar_fin(x, Nat.is_le(3000n, F.dexp(x)))), FINR(x, Nat.is_le(3000n, F.dexp(x))), FINR(x, Nat.is_le(3000n, SF.xexp(x))), e1, e2)

def ar_c(+x: F.F64, +t: Bool, +z: Bool, +hz: {X.is_zero(F.frac(x)) == z : Bool}) -> {SF.rtriple(F.ar_cls(x, t)) == SF.pick(Result<&2, &2, NE.NumError, SF.Rat>, Bool.and(t, Bool.not(z)), Fail{NE.BadDomain{}}, SF.pick(Result<&2, &2, NE.NumError, SF.Rat>, Bool.and(t, z), Fail{NE.Overflow{}}, SF.pick(Result<&2, &2, NE.NumError, SF.Rat>, SF.is_zero(x), Done{SF.Rat{False{}, 0n, 0n}}, FINR(x, Nat.is_le(SF.zb(), SF.xexp(x)))))) : Result<&2, &2, NE.NumError, SF.Rat>}:
  match t z:
    case True{} True{}:
      Equal.cong(Bool, Result<&2, &2, NE.NumError, SF.Rat>, b => SF.rtriple(F.ar_top(Bool.not(b))), X.is_zero(F.frac(x)), True{}, hz)
    case True{} False{}:
      Equal.cong(Bool, Result<&2, &2, NE.NumError, SF.Rat>, b => SF.rtriple(F.ar_top(Bool.not(b))), X.is_zero(F.frac(x)), False{}, hz)
    case False{} _:
      +e1 = Equal.cong(Bool, Result<&2, &2, NE.NumError, SF.Rat>, b => SF.rtriple(F.ar_z(x, b)), F.is_zero(x), SF.is_zero(x), FB.is_zero_value(x))
      Equal.trans(Result<&2, &2, NE.NumError, SF.Rat>, SF.rtriple(F.ar_z(x, F.is_zero(x))), SF.rtriple(F.ar_z(x, SF.is_zero(x))), SF.pick(Result<&2, &2, NE.NumError, SF.Rat>, SF.is_zero(x), Done{SF.Rat{False{}, 0n, 0n}}, FINR(x, Nat.is_le(SF.zb(), SF.xexp(x)))), e1, arz_c(x, SF.is_zero(x)))

def as_integer_ratio_value(+x: F.F64) -> SF.AsIntegerRatio.value(x):
  +e1 = Equal.cong(Nat, Result<&2, &2, NE.NumError, SF.Rat>, u => SF.rtriple(F.ar_cls(x, Nat.is_eq(u, 2047n))), F.exp_field(x), SF.efield(x), T.ea(x))
  Equal.trans(Result<&2, &2, NE.NumError, SF.Rat>, SF.rtriple(F.as_integer_ratio(x)), SF.rtriple(F.ar_cls(x, Nat.is_eq(SF.efield(x), 2047n))), SF.as_ratio(x), e1, ar_c(x, Nat.is_eq(SF.efield(x), 2047n), Nat.is_eq(SF.frac(x), 0n), T.fz(x)))
