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
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ./width.bend as WW
import ./w64add.bend as WA
import ./w64sh.bend as SH
import ./w64clz.bend as CZ
import ./u32laws.bend as LW
import ./f64bits.bend as FB
import ./f64light.bend as FL
import ./f64round.bend as FR
import ./f64rtools.bend as RT
import ./f64nrp.bend as NR
import ./f64bl.bend as BL
import ./f64tools.bend as T
import ./f64rint.bend as RI

# The conversions to unsigned integers (python_style_math_stdlib_design.pdf
# 3.1: int(x) truncates toward zero; 2.6: a fixed width raises instead of
# wrapping; IEEE 754-2019 5.8 convertToInteger with the invalid exception
# as an error value): ToU64.value, ToU32.value, FloorU64.value,
# CeilU64.value and RoundU64.value. A finite x is m 2^(xexp - Z): below 2^52
# its integer part is m >> (Z - xexp) (Shr.value), above it m << (xexp - Z),
# which fits 64 bits exactly when (xexp - Z) + bit_length(m) <= 64
# (Clz.value, f64nrp.tbf / tbn).

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# the spec's verdict on a nonnegative-or-zero integer part n with sign s
def TN(+s: Bool, +n: Nat) -> Result<&2, &2, NE.NumError, Nat>:
  SF.pick(Result<&2, &2, NE.NumError, Nat>, Bool.or(Bool.and(s, Bool.not(Nat.is_eq(n, 0n))), Bool.not(C.fits(64n, n))), Fail{NE.Overflow{}}, Done{n})

def TS(+s: Bool, +n: Nat) -> Result<&2, &2, NE.NumError, Nat>:
  SF.pick(Result<&2, &2, NE.NumError, Nat>, Bool.and(s, Bool.not(Nat.is_eq(n, 0n))), Fail{NE.Overflow{}}, Done{n})

def tn(+w: WU.U64, +b: Bool) -> {SF.rv64(F.tu_neg(w, b)) == SF.pick(Result<&2, &2, NE.NumError, Nat>, b, Fail{NE.Overflow{}}, Done{SW.value(w)}) : Result<&2, &2, NE.NumError, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def tuint_v(+s: Bool, +w: WU.U64) -> {SF.rv64(F.tu_int(s, w)) == TS(s, SW.value(w)) : Result<&2, &2, NE.NumError, Nat>}:
  +e1 = Equal.cong(Bool, Result<&2, &2, NE.NumError, Nat>, b => SF.rv64(F.tu_neg(w, Bool.and(s, Bool.not(b)))), X.is_zero(w), Nat.is_eq(SW.value(w), 0n), WA.is_zero_value(w))
  Equal.trans(Result<&2, &2, NE.NumError, Nat>, SF.rv64(F.tu_int(s, w)), SF.rv64(F.tu_neg(w, Bool.and(s, Bool.not(Nat.is_eq(SW.value(w), 0n))))), TS(s, SW.value(w)), e1, tn(w, Bool.and(s, Bool.not(Nat.is_eq(SW.value(w), 0n)))))

# TN is TS when n fits 64 bits
def tn_fit(+s: Bool, +n: Nat, +hf: {C.fits(64n, n) == True{} : Bool}) -> {TS(s, n) == TN(s, n) : Result<&2, &2, NE.NumError, Nat>}:
  +A = Bool.and(s, Bool.not(Nat.is_eq(n, 0n)))
  +e1 = Equal.cong(Bool, Result<&2, &2, NE.NumError, Nat>, b => SF.pick(Result<&2, &2, NE.NumError, Nat>, Bool.or(A, Bool.not(b)), Fail{NE.Overflow{}}, Done{n}), C.fits(64n, n), True{}, hf)
  +e2 = Equal.cong(Bool, Result<&2, &2, NE.NumError, Nat>, b => SF.pick(Result<&2, &2, NE.NumError, Nat>, b, Fail{NE.Overflow{}}, Done{n}), Bool.or(A, False{}), A, FR.or_f(A))
  Equal.sym(Result<&2, &2, NE.NumError, Nat>, TN(s, n), TS(s, n), Equal.trans(Result<&2, &2, NE.NumError, Nat>, TN(s, n), SF.pick(Result<&2, &2, NE.NumError, Nat>, Bool.or(A, False{}), Fail{NE.Overflow{}}, Done{n}), TS(s, n), e1, e2))

# ---- below 2^52: a right shift ----

def le_k64(+k: Nat) -> {Nat.is_le(64n, Nat.add(k, 64n)) == True{} : Bool}:
  L.subst(Nat, t => {Nat.is_le(64n, t) == True{} : Bool}, Nat.add(64n, k), Nat.add(k, 64n), NA.add_comm(64n, k), N.le_add_right(64n, k))

def small_nat(+s: Bool, +w: WU.U64, +k: Nat) -> {SF.rv64(F.tu_int(s, X.shr(w, k))) == TN(s, C.high(k, SW.value(w))) : Result<&2, &2, NE.NumError, Nat>}:
  +V = SW.value(w)
  +H = C.high(k, V)
  +e1 = tuint_v(s, X.shr(w, k))
  +e2 = Equal.cong(Nat, Result<&2, &2, NE.NumError, Nat>, n => TS(s, n), SW.value(X.shr(w, k)), H, SH.shr_value(w, k))
  +hf = Equal.trans(Bool, C.fits(64n, H), C.fits(Nat.add(k, 64n), V), True{}, Equal.sym(Bool, C.fits(Nat.add(k, 64n), V), C.fits(64n, H), FR.fits_hc(k, 64n, V)), SH.fits_mono(64n, Nat.add(k, 64n), V, le_k64(k), FL.vb64(w)))
  Equal.trans(Result<&2, &2, NE.NumError, Nat>, SF.rv64(F.tu_int(s, X.shr(w, k))), TS(s, SW.value(X.shr(w, k))), TN(s, H), e1, Equal.trans(Result<&2, &2, NE.NumError, Nat>, TS(s, SW.value(X.shr(w, k))), TS(s, H), TN(s, H), e2, tn_fit(s, H, hf)))

# ---- at least 2^52: a left shift that must fit ----

def subsub(+a: Nat, +b: Nat, +h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.sub(a, Nat.sub(a, b)) == b : Nat}:
  +d = Nat.sub(a, b)
  L.subst(Nat, t => {Nat.sub(t, d) == b : Nat}, Nat.add(b, d), a, N.sub_add(a, b, h), FR.sub_add_l(b, d))

def big_c(+s: Bool, +w: WU.U64, +k: Nat, +hz: {Nat.is_eq(SW.value(w), 0n) == False{} : Bool}, +c: Bool, +hc: {Nat.is_le(Nat.add(k, M.bit_length(SW.value(w))), 64n) == c : Bool}) -> {SF.rv64(F.tu_big(s, w, k, c)) == TN(s, C.shift(k, SW.value(w))) : Result<&2, &2, NE.NumError, Nat>}:
  match c:
    case True{}:
      +V = SW.value(w)
      +B = M.bit_length(V)
      +S = C.shift(k, V)
      +hb1 = BL.bl_pos(V, hz, B, {==})
      +hkl = Equal.trans(Bool, Nat.is_lt(k, Nat.add(k, B)), Nat.is_lt(Nat.add(k, 0n), Nat.add(k, B)), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(t, Nat.add(k, B)), k, Nat.add(k, 0n), Equal.sym(Nat, Nat.add(k, 0n), k, N.add_zero(k))), N.lt_add_left(0n, B, k, N.succ_le_lt(0n, B, hb1)))
      +hk = N.lt_le_trans(k, Nat.add(k, B), 64n, hkl, hc)
      +ev = FL.shl_v(w, k, B, hk, hc, RT.bl_fit(V))
      +e1 = tuint_v(s, X.shl(w, k))
      +e2 = Equal.cong(Nat, Result<&2, &2, NE.NumError, Nat>, n => TS(s, n), SW.value(X.shl(w, k)), S, ev)
      +hf = SH.fits_mono(Nat.add(k, B), 64n, S, hc, NR.tbf(k, V, Nat.add(k, B), {==}))
      Equal.trans(Result<&2, &2, NE.NumError, Nat>, SF.rv64(F.tu_int(s, X.shl(w, k))), TS(s, SW.value(X.shl(w, k))), TN(s, S), e1, Equal.trans(Result<&2, &2, NE.NumError, Nat>, TS(s, SW.value(X.shl(w, k))), TS(s, S), TN(s, S), e2, tn_fit(s, S, hf)))
    case False{}:
      +V = SW.value(w)
      +B = M.bit_length(V)
      +S = C.shift(k, V)
      +A = Bool.and(s, Bool.not(Nat.is_eq(S, 0n)))
      +J = Nat.add(k, B)
      +K = Nat.sub(J, 1n)
      +hJ = N.not_le_lt(J, 64n, hc)
      +hJ1 = N.le_trans(1n, 65n, J, {==}, N.lt_succ_le_succ(64n, J, hJ))
      +ek = Equal.sym(Nat, Nat.add(1n, K), J, N.sub_add(J, 1n, hJ1))
      +hK = N.lt_succ_le(64n, K, L.subst(Nat, t => {Nat.is_lt(64n, t) == True{} : Bool}, J, 1n+K, ek, hJ))
      +nf = FL.nfit_mono(64n, K, S, hK, NR.tbn(k, V, K, hz, ek))
      +e1 = Equal.cong(Bool, Result<&2, &2, NE.NumError, Nat>, b => SF.pick(Result<&2, &2, NE.NumError, Nat>, Bool.or(A, Bool.not(b)), Fail{NE.Overflow{}}, Done{S}), C.fits(64n, S), False{}, nf)
      +e2 = Equal.cong(Bool, Result<&2, &2, NE.NumError, Nat>, b => SF.pick(Result<&2, &2, NE.NumError, Nat>, b, Fail{NE.Overflow{}}, Done{S}), Bool.or(A, True{}), True{}, FR.or_t(A))
      Equal.sym(Result<&2, &2, NE.NumError, Nat>, TN(s, S), Fail{NE.Overflow{}}, Equal.trans(Result<&2, &2, NE.NumError, Nat>, TN(s, S), SF.pick(Result<&2, &2, NE.NumError, Nat>, Bool.or(A, True{}), Fail{NE.Overflow{}}, Done{S}), Fail{NE.Overflow{}}, e1, e2))

def big_nat(+s: Bool, +w: WU.U64, +k: Nat, +hz: {Nat.is_eq(SW.value(w), 0n) == False{} : Bool}, +hw: {C.fits(53n, SW.value(w)) == True{} : Bool}) -> {SF.rv64(F.tu_big(s, w, k, Nat.is_le(Nat.add(k, Nat.sub(64n, X.clz(w))), 64n))) == TN(s, C.shift(k, SW.value(w))) : Result<&2, &2, NE.NumError, Nat>}:
  +V = SW.value(w)
  +B = M.bit_length(V)
  +hB = N.le_trans(B, 53n, 64n, BL.bl_le(53n, V, hw, Nat.is_le(B, 53n), {==}), {==})
  +eb = Equal.trans(Nat, Nat.sub(64n, X.clz(w)), Nat.sub(64n, Nat.sub(64n, B)), B, Equal.cong(Nat, Nat, t => Nat.sub(64n, t), X.clz(w), Nat.sub(64n, B), CZ.clz_value(w)), subsub(64n, B, hB))
  +e1 = Equal.cong(Nat, Result<&2, &2, NE.NumError, Nat>, t => SF.rv64(F.tu_big(s, w, k, Nat.is_le(Nat.add(k, t), 64n))), Nat.sub(64n, X.clz(w)), B, eb)
  Equal.trans(Result<&2, &2, NE.NumError, Nat>, SF.rv64(F.tu_big(s, w, k, Nat.is_le(Nat.add(k, Nat.sub(64n, X.clz(w))), 64n))), SF.rv64(F.tu_big(s, w, k, Nat.is_le(Nat.add(k, B), 64n))), TN(s, C.shift(k, V)), e1, big_c(s, w, k, hz, Nat.is_le(Nat.add(k, B), 64n), {==}))

# ---- the finite case ----

# a double with scale at least Z is normal, so its significand is not zero
# the significand at an abstract exponent-is-zero bit b: instantiated at
# False, the hidden bit 2^52 is never evaluated
def mz(+x: F.F64, +b: Bool, +hb: {Nat.is_eq(SF.efield(x), 0n) == b : Bool}) -> {Nat.is_eq(SF.mant(x), 0n) == Nat.is_eq(Nat.add(SF.frac(x), C.shift(52n, SF.b2n(Bool.not(b)))), 0n) : Bool}:
  Equal.cong(Bool, Bool, t => Nat.is_eq(Nat.add(SF.frac(x), C.shift(52n, SF.b2n(Bool.not(t)))), 0n), Nat.is_eq(SF.efield(x), 0n), b, hb)

def bnz_c(+x: F.F64, +z: Bool, +hz: {Nat.is_eq(F.exp_field(x), 0n) == z : Bool}, +h: {Nat.is_le(3000n, F.dexp_z(F.exp_field(x), z)) == True{} : Bool}) -> {Nat.is_eq(SF.mant(x), 0n) == False{} : Bool}:
  match z:
    case True{}:
      Empty.absurd({Nat.is_eq(SF.mant(x), 0n) == False{} : Bool}, FL.true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case False{}:
      +hz2 = L.subst(Nat, t => {Nat.is_eq(t, 0n) == False{} : Bool}, F.exp_field(x), SF.efield(x), T.ea(x), hz)
      +Fr = SF.frac(x)
      +e1 = mz(x, False{}, hz2)
      # the hidden bit stays b2n(not False): no closed 2^52
      +H = SF.b2n(Bool.not(False{}))
      +e2 = FB.z2(Fr, 52n, H)
      +e3 = Equal.cong(Bool, Bool, t => Bool.and(Nat.is_eq(Fr, 0n), t), Nat.is_eq(H, 0n), False{}, {==})
      Equal.trans(Bool, Nat.is_eq(SF.mant(x), 0n), Nat.is_eq(Nat.add(Fr, C.shift(52n, H)), 0n), False{}, e1, Equal.trans(Bool, Nat.is_eq(Nat.add(Fr, C.shift(52n, H)), 0n), Bool.and(Nat.is_eq(Fr, 0n), Nat.is_eq(H, 0n)), False{}, e2, Equal.trans(Bool, Bool.and(Nat.is_eq(Fr, 0n), Nat.is_eq(H, 0n)), Bool.and(Nat.is_eq(Fr, 0n), False{}), False{}, e3, FR.and_f(Nat.is_eq(Fr, 0n)))))

def big_nz(+x: F.F64, +h: {Nat.is_le(3000n, F.dexp(x)) == True{} : Bool}) -> {Nat.is_eq(SW.value(F.dmant(x)), 0n) == False{} : Bool}:
  L.subst(Nat, t => {Nat.is_eq(t, 0n) == False{} : Bool}, SF.mant(x), SW.value(F.dmant(x)), Equal.sym(Nat, SW.value(F.dmant(x)), SF.mant(x), T.dmant_value(x)), bnz_c(x, Nat.is_eq(F.exp_field(x), 0n), {==}, h))

def hw53(+x: F.F64) -> {C.fits(53n, SW.value(F.dmant(x))) == True{} : Bool}:
  L.subst(Nat, t => {C.fits(53n, t) == True{} : Bool}, SF.mant(x), SW.value(F.dmant(x)), Equal.sym(Nat, SW.value(F.dmant(x)), SF.mant(x), T.dmant_value(x)), T.mant_fits(x))

def IPc(+x: F.F64, +c: Bool) -> Nat:
  SF.pick(Nat, c, C.shift(Nat.sub(SF.xexp(x), SF.zb()), SF.mant(x)), C.high(Nat.sub(SF.zb(), SF.xexp(x)), SF.mant(x)))

def tu_fin_c(+x: F.F64, +c: Bool, +hc: {Nat.is_le(3000n, F.dexp(x)) == c : Bool}) -> {SF.rv64(F.tu_fin(x, c)) == TN(SF.sign(x), IPc(x, c)) : Result<&2, &2, NE.NumError, Nat>}:
  match c:
    case True{}:
      +k = Nat.sub(F.dexp(x), 3000n)
      +e0 = big_nat(F.signbit(x), F.dmant(x), k, big_nz(x, hc), hw53(x))
      +e1 = Equal.cong(Bool, Result<&2, &2, NE.NumError, Nat>, t => TN(t, C.shift(k, SW.value(F.dmant(x)))), F.signbit(x), SF.sign(x), FB.signbit_value(x))
      +e2 = Equal.cong(Nat, Result<&2, &2, NE.NumError, Nat>, t => TN(SF.sign(x), C.shift(k, t)), SW.value(F.dmant(x)), SF.mant(x), T.dmant_value(x))
      +e3 = Equal.cong(Nat, Result<&2, &2, NE.NumError, Nat>, t => TN(SF.sign(x), C.shift(Nat.sub(t, 3000n), SF.mant(x))), F.dexp(x), SF.xexp(x), T.dexp_value(x))
      +r0 = TN(F.signbit(x), C.shift(k, SW.value(F.dmant(x))))
      +r1 = TN(SF.sign(x), C.shift(k, SW.value(F.dmant(x))))
      +r2 = TN(SF.sign(x), C.shift(k, SF.mant(x)))
      Equal.trans(Result<&2, &2, NE.NumError, Nat>, SF.rv64(F.tu_fin(x, True{})), r0, TN(SF.sign(x), IPc(x, True{})), e0, Equal.trans(Result<&2, &2, NE.NumError, Nat>, r0, r1, TN(SF.sign(x), IPc(x, True{})), e1, Equal.trans(Result<&2, &2, NE.NumError, Nat>, r1, r2, TN(SF.sign(x), IPc(x, True{})), e2, e3)))
    case False{}:
      +k = Nat.sub(3000n, F.dexp(x))
      +e0 = small_nat(F.signbit(x), F.dmant(x), k)
      +e1 = Equal.cong(Bool, Result<&2, &2, NE.NumError, Nat>, t => TN(t, C.high(k, SW.value(F.dmant(x)))), F.signbit(x), SF.sign(x), FB.signbit_value(x))
      +e2 = Equal.cong(Nat, Result<&2, &2, NE.NumError, Nat>, t => TN(SF.sign(x), C.high(k, t)), SW.value(F.dmant(x)), SF.mant(x), T.dmant_value(x))
      +e3 = Equal.cong(Nat, Result<&2, &2, NE.NumError, Nat>, t => TN(SF.sign(x), C.high(Nat.sub(3000n, t), SF.mant(x))), F.dexp(x), SF.xexp(x), T.dexp_value(x))
      +r0 = TN(F.signbit(x), C.high(k, SW.value(F.dmant(x))))
      +r1 = TN(SF.sign(x), C.high(k, SW.value(F.dmant(x))))
      +r2 = TN(SF.sign(x), C.high(k, SF.mant(x)))
      Equal.trans(Result<&2, &2, NE.NumError, Nat>, SF.rv64(F.tu_fin(x, False{})), r0, TN(SF.sign(x), IPc(x, False{})), e0, Equal.trans(Result<&2, &2, NE.NumError, Nat>, r0, r1, TN(SF.sign(x), IPc(x, False{})), e1, Equal.trans(Result<&2, &2, NE.NumError, Nat>, r1, r2, TN(SF.sign(x), IPc(x, False{})), e2, e3)))

def TNR(+a: Bool, +b: Bool, +c: Bool, +n: Nat, +f: Bool) -> Result<&2, &2, NE.NumError, Nat>:
  SF.pick(Result<&2, &2, NE.NumError, Nat>, a, Fail{NE.BadDomain{}}, SF.pick(Result<&2, &2, NE.NumError, Nat>, Bool.or(b, Bool.or(c, Bool.not(f))), Fail{NE.Overflow{}}, Done{n}))

def tu_c(+x: F.F64, +t: Bool, +z: Bool, +hz: {X.is_zero(F.frac(x)) == z : Bool}) -> {SF.rv64(F.tu_cls(x, t)) == TNR(Bool.and(t, Bool.not(z)), Bool.and(t, z), Bool.and(SF.sign(x), Bool.not(Nat.is_eq(SF.int_part(x), 0n))), SF.int_part(x), C.fits(64n, SF.int_part(x))) : Result<&2, &2, NE.NumError, Nat>}:
  match t z:
    case True{} True{}:
      Equal.cong(Bool, Result<&2, &2, NE.NumError, Nat>, b => SF.rv64(F.tu_top(Bool.not(b))), X.is_zero(F.frac(x)), True{}, hz)
    case True{} False{}:
      Equal.cong(Bool, Result<&2, &2, NE.NumError, Nat>, b => SF.rv64(F.tu_top(Bool.not(b))), X.is_zero(F.frac(x)), False{}, hz)
    case False{} _:
      +e1 = tu_fin_c(x, Nat.is_le(3000n, F.dexp(x)), {==})
      +e2 = Equal.cong(Nat, Result<&2, &2, NE.NumError, Nat>, u => TN(SF.sign(x), IPc(x, Nat.is_le(3000n, u))), F.dexp(x), SF.xexp(x), T.dexp_value(x))
      Equal.trans(Result<&2, &2, NE.NumError, Nat>, SF.rv64(F.tu_fin(x, Nat.is_le(3000n, F.dexp(x)))), TN(SF.sign(x), IPc(x, Nat.is_le(3000n, F.dexp(x)))), TN(SF.sign(x), SF.int_part(x)), e1, e2)

def to_u64_value(+x: F.F64) -> SF.ToU64.value(x):
  +e1 = Equal.cong(Nat, Result<&2, &2, NE.NumError, Nat>, u => SF.rv64(F.tu_cls(x, Nat.is_eq(u, 2047n))), F.exp_field(x), SF.efield(x), T.ea(x))
  Equal.trans(Result<&2, &2, NE.NumError, Nat>, SF.rv64(F.to_u64(x)), SF.rv64(F.tu_cls(x, Nat.is_eq(SF.efield(x), 2047n))), SF.to_nat(x, 64n), e1, tu_c(x, Nat.is_eq(SF.efield(x), 2047n), Nat.is_eq(SF.frac(x), 0n), T.fz(x)))

# ---- 32 bits: the 64-bit result, when its high word is zero ----

def f32r(r: Result<&2, &2, NE.NumError, Nat>) -> Result<&2, &2, NE.NumError, Nat>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+n}:
      SF.pick(Result<&2, &2, NE.NumError, Nat>, C.fits(32n, n), Done{n}, Fail{NE.Overflow{}})

def t32_c(+l: U32, +h: U32, +c: Bool, +hc: {U32.is_zero(h) == c : Bool}) -> {SF.rv32(F.tu32_w(WU.U64{l, h}, c)) == SF.pick(Result<&2, &2, NE.NumError, Nat>, c, Done{SW.value(WU.U64{l, h})}, Fail{NE.Overflow{}}) : Result<&2, &2, NE.NumError, Nat>}:
  match c:
    case True{}:
      +h0 = N.eq_from_is_eq(v(h), 0n, Equal.trans(Bool, Nat.is_eq(v(h), 0n), U32.is_zero(h), True{}, Equal.sym(Bool, U32.is_zero(h), Nat.is_eq(v(h), 0n), LW.zero_nat(h)), hc))
      +e1 = Equal.cong(Nat, Nat, t => Nat.add(v(l), C.shift(32n, t)), v(h), 0n, h0)
      +e2 = Equal.trans(Nat, SW.value(WU.U64{l, h}), Nat.add(v(l), 0n), v(l), Equal.trans(Nat, SW.value(WU.U64{l, h}), Nat.add(v(l), C.shift(32n, 0n)), Nat.add(v(l), 0n), e1, {==}), N.add_zero(v(l)))
      Equal.cong(Nat, Result<&2, &2, NE.NumError, Nat>, t => Done{t}, v(l), SW.value(WU.U64{l, h}), Equal.sym(Nat, SW.value(WU.U64{l, h}), v(l), e2))
    case False{}:
      {==}

def t32w(+w: WU.U64) -> {SF.rv32(F.tu32_w(w, U32.is_zero(X.hi(w)))) == SF.pick(Result<&2, &2, NE.NumError, Nat>, C.fits(32n, SW.value(w)), Done{SW.value(w)}, Fail{NE.Overflow{}}) : Result<&2, &2, NE.NumError, Nat>}:
  match w:
    case WU.U64{+l, +h}:
      +ef = Equal.trans(Bool, U32.is_zero(h), Nat.is_eq(v(h), 0n), C.fits(32n, SW.value(WU.U64{l, h})), LW.zero_nat(h), Equal.cong(Nat, Bool, t => Nat.is_eq(t, 0n), v(h), C.high(32n, SW.value(WU.U64{l, h})), Equal.sym(Nat, C.high(32n, SW.value(WU.U64{l, h})), v(h), WW.high_u(32n, v(l), v(h), LW.vb(l)))))
      +e1 = t32_c(l, h, U32.is_zero(h), {==})
      +e2 = Equal.cong(Bool, Result<&2, &2, NE.NumError, Nat>, b => SF.pick(Result<&2, &2, NE.NumError, Nat>, b, Done{SW.value(WU.U64{l, h})}, Fail{NE.Overflow{}}), U32.is_zero(h), C.fits(32n, SW.value(WU.U64{l, h})), ef)
      Equal.trans(Result<&2, &2, NE.NumError, Nat>, SF.rv32(F.tu32_w(WU.U64{l, h}, U32.is_zero(h))), SF.pick(Result<&2, &2, NE.NumError, Nat>, U32.is_zero(h), Done{SW.value(WU.U64{l, h})}, Fail{NE.Overflow{}}), SF.pick(Result<&2, &2, NE.NumError, Nat>, C.fits(32n, SW.value(WU.U64{l, h})), Done{SW.value(WU.U64{l, h})}, Fail{NE.Overflow{}}), e1, e2)

def t32(r: Result<&2, &2, NE.NumError, WU.U64>) -> {SF.rv32(F.tu32(r)) == f32r(SF.rv64(r)) : Result<&2, &2, NE.NumError, Nat>}:
  match r:
    case Fail{e}:
      {==}
    case Done{+w}:
      t32w(w)

def pn(+b: Bool, +n: Nat) -> {SF.pick(Result<&2, &2, NE.NumError, Nat>, b, Done{n}, Fail{NE.Overflow{}}) == SF.pick(Result<&2, &2, NE.NumError, Nat>, Bool.not(b), Fail{NE.Overflow{}}, Done{n}) : Result<&2, &2, NE.NumError, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def s32_c(+a: Bool, +b: Bool, +c: Bool, +n: Nat, +f: Bool, +hf: {C.fits(64n, n) == f : Bool}) -> {f32r(TNR(a, b, c, n, f)) == TNR(a, b, c, n, C.fits(32n, n)) : Result<&2, &2, NE.NumError, Nat>}:
  match a b c f:
    case True{} _ _ _:
      {==}
    case False{} True{} _ _:
      {==}
    case False{} False{} True{} _:
      {==}
    case False{} False{} False{} True{}:
      pn(C.fits(32n, n), n)
    case False{} False{} False{} False{}:
      +g = FL.nfit_mono(32n, 64n, n, {==}, hf)
      Equal.cong(Bool, Result<&2, &2, NE.NumError, Nat>, t => TNR(False{}, False{}, False{}, n, t), False{}, C.fits(32n, n), Equal.sym(Bool, C.fits(32n, n), False{}, g))

def to_u32_value(+x: F.F64) -> SF.ToU32.value(x):
  +R64 = SF.rv64(F.to_u64(x))
  +e1 = t32(F.to_u64(x))
  +e2 = Equal.cong(Result<&2, &2, NE.NumError, Nat>, Result<&2, &2, NE.NumError, Nat>, r => f32r(r), R64, SF.to_nat(x, 64n), to_u64_value(x))
  +IP = SF.int_part(x)
  +e3 = s32_c(SF.is_nan(x), SF.is_inf(x), Bool.and(SF.sign(x), Bool.not(Nat.is_eq(IP, 0n))), IP, C.fits(64n, IP), {==})
  Equal.trans(Result<&2, &2, NE.NumError, Nat>, SF.rv32(F.to_u32(x)), f32r(R64), SF.to_nat(x, 32n), e1, Equal.trans(Result<&2, &2, NE.NumError, Nat>, f32r(R64), f32r(SF.to_nat(x, 64n)), SF.to_nat(x, 32n), e2, e3))

# ---- floor, ceil, round, then the conversion ----

def floor_u64_value(+x: F.F64) -> SF.FloorU64.value(x):
  Equal.trans(Result<&2, &2, NE.NumError, Nat>, SF.rv64(F.to_u64(F.floor(x))), SF.to_nat(F.floor(x), 64n), SF.to_nat(SF.to_integral(F.Floor{}, x), 64n), to_u64_value(F.floor(x)), Equal.cong(F.F64, Result<&2, &2, NE.NumError, Nat>, y => SF.to_nat(y, 64n), F.floor(x), SF.to_integral(F.Floor{}, x), RI.floor_value(x)))

def ceil_u64_value(+x: F.F64) -> SF.CeilU64.value(x):
  Equal.trans(Result<&2, &2, NE.NumError, Nat>, SF.rv64(F.to_u64(F.ceil(x))), SF.to_nat(F.ceil(x), 64n), SF.to_nat(SF.to_integral(F.Ceil{}, x), 64n), to_u64_value(F.ceil(x)), Equal.cong(F.F64, Result<&2, &2, NE.NumError, Nat>, y => SF.to_nat(y, 64n), F.ceil(x), SF.to_integral(F.Ceil{}, x), RI.ceil_value(x)))

def round_u64_value(+x: F.F64) -> SF.RoundU64.value(x):
  Equal.trans(Result<&2, &2, NE.NumError, Nat>, SF.rv64(F.to_u64(F.round(x))), SF.to_nat(F.round(x), 64n), SF.to_nat(SF.to_integral(F.Even{}, x), 64n), to_u64_value(F.round(x)), Equal.cong(F.F64, Result<&2, &2, NE.NumError, Nat>, y => SF.to_nat(y, 64n), F.round(x), SF.to_integral(F.Even{}, x), RI.round_value(x)))
