import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ./width.bend as WW
import ./w64sh.bend as SH
import ./w64clz.bend as CZ
import ./f64bits.bend as FB
import ./f64round.bend as FR
import ./u32laws.bend as LW
import ../../lib/word.bend as WD
import ./f64bl.bend as BL
import ./f64rtools.bend as RT
import ./f64tools.bend as T
import ./f64rint.bend as RI

# frexp and ldexp (python_style_math_stdlib_design.pdf 4.4; C99 7.12.6.4,
# 7.12.6.6 and F.9.3.4, F.9.3.6): Frexp.value, Ldexp.value. frexp rounds
# the significand at the scale Z - bit_length (exact: f64tools.rw_value with
# Clz.value for the bit length); ldexp rounds the significand at the moved
# scale, and a scale below the subnormal range by more than the significand
# is a zero of x's sign (tiny below: Flocq's round_NE of a value under half
# the smallest subnormal).

# ---- underflow to zero ----

def sub_le_self(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+ +bp:
      {==}
    case 1n+ +ap 0n:
      N.le_refl(1n+ap)
    case 1n+ +ap 1n+ +bp:
      N.le_trans(Nat.sub(ap, bp), ap, 1n+ap, sub_le_self(ap, bp), N.le_succ(ap))

# m < 2^53 divided by 2^(1+j) >= 2^54 rounds to 0
def rne_zero(+m: Nat, +j: Nat, +hm: {C.fits(53n, m) == True{} : Bool}, +hj: {Nat.is_le(53n, j) == True{} : Bool}) -> {SF.rne(m, 1n+j) == 0n : Nat}:
  +hj1 = N.le_trans(53n, j, 1n+j, hj, N.le_succ(j))
  +f1 = SH.fits_mono(53n, 1n+j, m, hj1, hm)
  +eh = N.eq_from_is_eq(C.high(1n+j, m), 0n, f1)
  +el = WW.low_fit(1n+j, m, SH.fits_mono(53n, 1n+j, m, N.le_trans(53n, j, 1n+j, hj, N.le_succ(j)), hm))
  +fj = SH.fits_mono(53n, j, m, hj, hm)
  +hl = Equal.trans(Bool, Nat.is_lt(m, C.shift(j, 1n)), C.fits(j, m), True{}, FR.lt_fit(j, 1n, {==}, m), fj)
  +la = RI.nlt(j, 1n, {==}, m, SH.fits_mono(53n, j, m, hj, hm))
  +le = N.is_eq_lt(m, C.shift(j, 1n), hl)
  +H = C.shift(j, 1n)
  +e1 = Equal.cong(Nat, Nat, t => SF.rne_up(t, C.low(1n+j, m), H), C.high(1n+j, m), 0n, eh)
  +e2 = Equal.cong(Nat, Nat, t => SF.rne_up(0n, t, H), C.low(1n+j, m), m, el)
  +e3 = Equal.cong(Bool, Nat, b => Nat.add(0n, SF.b2n(Bool.or(b, Bool.and(Nat.is_eq(m, H), False{})))), Nat.is_lt(H, m), False{}, la)
  +e4 = Equal.cong(Bool, Nat, b => SF.b2n(Bool.and(b, False{})), Nat.is_eq(m, H), False{}, le)
  Equal.trans(Nat, SF.rne(m, 1n+j), SF.rne_up(0n, C.low(1n+j, m), H), 0n, e1, Equal.trans(Nat, SF.rne_up(0n, C.low(1n+j, m), H), SF.rne_up(0n, m, H), 0n, e2, Equal.trans(Nat, SF.rne_up(0n, m, H), SF.b2n(Bool.and(Nat.is_eq(m, H), False{})), 0n, e3, e4)))

def max_le(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.max(a, b) == b : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+ +ap 0n:
      Empty.absurd({Nat.max(1n+ap, 0n) == 0n : Nat}, LW.true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case 1n+ +ap 1n+ +bp:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.max(ap, bp), bp, max_le(ap, bp, h))

# a zero pattern with sign s (as f64addc.bz)
def bz0(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +c: U32, +hc: {c == U32{WD.pw(32n, 31n)} : U32}) -> {F.Bits{0, U32.from_nat(C.shift(31n, SF.pick(Nat, s, one, 0n)))} == SF.pick(F.F64, s, F.Bits{0, c}, F.Bits{0, 0}) : F.F64}:
  match s:
    case True{}:
      Equal.cong(U32, F.F64, z => F.Bits{0, z}, U32.from_nat(C.shift(31n, one)), c, Equal.trans(U32, U32.from_nat(C.shift(31n, one)), U32.from_nat(U32.to_nat(c)), c, Equal.cong(Nat, U32, z => U32.from_nat(z), C.shift(31n, one), U32.to_nat(c), Equal.sym(Nat, U32.to_nat(c), C.shift(31n, one), FB.pwv(31n, {==}, one, h1, c, hc))), LW.rt(c)))
    case False{}:
      {==}

def bz(+s: Bool) -> {FR.bits(s, 0n) == SF.zero(s) : F.F64}:
  Equal.trans(F.F64, F.Bits{0, U32.from_nat(C.shift(31n, SF.b2n(s)))}, F.Bits{0, U32.from_nat(C.shift(31n, SF.pick(Nat, s, 1n, 0n)))}, SF.zero(s), Equal.cong(Nat, F.F64, z => F.Bits{0, U32.from_nat(C.shift(31n, z))}, SF.b2n(s), SF.pick(Nat, s, 1n, 0n), Equal.sym(Nat, SF.pick(Nat, s, 1n, 0n), SF.b2n(s), FR.pb(s, 1n, {==}))), bz0(1n, {==}, s, 2147483648, {==}))

# round_u unfolded at an abstract ulp u: instantiated at a literal u, the
# checker never evaluates pack's closed exponent arithmetic
def ru(+s: Bool, +m: Nat, +x: Nat, +u: Nat) -> {SF.round_u(s, m, x, u) == SF.pack(s, SF.pick(Nat, Nat.is_le(x, u), SF.rne(m, Nat.sub(u, x)), C.shift(Nat.sub(x, u), m)), u) : F.F64}:
  {==}

def tiny_c(+s: Bool, +m: Nat, +x: Nat, +hm: {C.fits(53n, m) == True{} : Bool}, +hx: {Nat.is_lt(x, 63n) == True{} : Bool}, +z: Bool, +hz: {Nat.is_eq(m, 0n) == z : Bool}) -> {SF.round(s, m, x) == SF.zero(s) : F.F64}:
  match z:
    case True{}:
      Equal.cong(Bool, F.F64, b => SF.pick(F.F64, b, SF.zero(s), SF.round_u(s, m, x, Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), 1926n))), Nat.is_eq(m, 0n), True{}, hz)
    case False{}:
      +B = M.bit_length(m)
      +A = Nat.sub(Nat.add(x, B), 53n)
      +hB = BL.bl_le(53n, m, hm, Nat.is_le(B, 53n), {==})
      +hx62 = N.lt_succ_le(x, 62n, hx)
      +h1 = Equal.trans(Bool, Nat.is_le(Nat.add(x, B), Nat.add(62n, B)), Nat.is_le(x, 62n), True{}, FR.le_cancel_r(x, 62n, B), hx62)
      +h2 = N.le_trans(B, 53n, 1864n, hB, {==})
      +hA = N.le_trans(A, Nat.add(x, B), 1926n, sub_le_self(Nat.add(x, B), 53n), N.le_trans(Nat.add(x, B), Nat.add(62n, B), 1926n, h1, h2))
      +emax = max_le(A, 1926n, hA)
      +hxa = N.le_trans(x, 62n, 1926n, N.lt_succ_le(x, 62n, hx), {==})
      +hxb = N.le_trans(x, 62n, 1925n, N.lt_succ_le(x, 62n, hx), {==})
      +j = Nat.sub(1925n, x)
      +hj = RT.le_sub(53n, x, 1925n, N.le_trans(x, 62n, 1872n, N.lt_succ_le(x, 62n, hx), {==}))
      +P = SF.pick(Nat, Nat.is_le(x, 1926n), SF.rne(m, Nat.sub(1926n, x)), C.shift(Nat.sub(x, 1926n), m))
      +e1 = Equal.cong(Bool, F.F64, b => SF.pick(F.F64, b, SF.zero(s), SF.round_u(s, m, x, Nat.max(A, 1926n))), Nat.is_eq(m, 0n), False{}, hz)
      +e2 = Equal.cong(Nat, F.F64, u => SF.round_u(s, m, x, u), Nat.max(A, 1926n), 1926n, emax)
      # the pick reduces under pack's argument, so the checker never unfolds pack
      +e3p = Equal.cong(Bool, Nat, b => SF.pick(Nat, b, SF.rne(m, Nat.sub(1926n, x)), C.shift(Nat.sub(x, 1926n), m)), Nat.is_le(x, 1926n), True{}, hxa)
      +e3 = Equal.cong(Nat, F.F64, t => SF.pack(s, t, 1926n), SF.pick(Nat, Nat.is_le(x, 1926n), SF.rne(m, Nat.sub(1926n, x)), C.shift(Nat.sub(x, 1926n), m)), SF.rne(m, Nat.sub(1926n, x)), e3p)
      +e4 = Equal.cong(Nat, F.F64, t => SF.pack(s, SF.rne(m, t), 1926n), Nat.sub(1926n, x), 1n+j, N.sub_succ_left(1925n, x, hxb))
      +e5 = Equal.cong(Nat, F.F64, t => SF.pack(s, t, 1926n), SF.rne(m, 1n+j), 0n, rne_zero(m, j, hm, hj))
      +e6 = FR.enc_bits(s, 0n, 0n)
      +r1 = SF.round_u(s, m, x, Nat.max(A, 1926n))
      +r2 = SF.round_u(s, m, x, 1926n)
      +r3 = SF.pack(s, SF.rne(m, Nat.sub(1926n, x)), 1926n)
      +r4 = SF.pack(s, SF.rne(m, 1n+j), 1926n)
      +r5 = SF.pack(s, 0n, 1926n)
      +r6 = FR.bits(s, 0n)
      +r2p = SF.pack(s, SF.pick(Nat, Nat.is_le(x, 1926n), SF.rne(m, Nat.sub(1926n, x)), C.shift(Nat.sub(x, 1926n), m)), 1926n)
      Equal.trans(F.F64, SF.round(s, m, x), r1, SF.zero(s), e1, Equal.trans(F.F64, r1, r2, SF.zero(s), e2, Equal.trans(F.F64, r2, r2p, SF.zero(s), ru(s, m, x, 1926n), Equal.trans(F.F64, r2p, r3, SF.zero(s), e3, Equal.trans(F.F64, r3, r4, SF.zero(s), e4, Equal.trans(F.F64, r4, r5, SF.zero(s), e5, Equal.trans(F.F64, r5, r6, SF.zero(s), e6, bz(s))))))))

def tiny(+s: Bool, +m: Nat, +x: Nat, +hm: {C.fits(53n, m) == True{} : Bool}, +hx: {Nat.is_lt(x, 63n) == True{} : Bool}) -> {SF.round(s, m, x) == SF.zero(s) : F.F64}:
  tiny_c(s, m, x, hm, hx, Nat.is_eq(m, 0n), {==})

# ---- frexp ----

def ee_c(+t: Nat, +c: Bool) -> {F.exp_pick(t, c) == SF.pick(F.Exp, c, F.Exp{False{}, Nat.sub(t, 3000n)}, F.Exp{True{}, Nat.sub(3000n, t)}) : F.Exp}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def exp_eq(+t: Nat) -> {F.exp_of(t) == SF.exp_of(t) : F.Exp}:
  ee_c(t, Nat.is_le(3000n, t))

def FIN(+x: F.F64) -> F.F64 & F.Exp:
  (SF.round(SF.sign(x), SF.mant(x), Nat.sub(SF.zb(), M.bit_length(SF.mant(x)))), SF.exp_of(Nat.add(SF.xexp(x), M.bit_length(SF.mant(x)))))

def fx_nz(+x: F.F64) -> {F.fx_fin(x, F.dmant(x), Nat.sub(64n, X.clz(F.dmant(x)))) == FIN(x) : F.F64 & F.Exp}:
  +w = F.dmant(x)
  +V = SW.value(w)
  +B = M.bit_length(V)
  +hB = BL.bl_le(53n, V, T.mw53(x), Nat.is_le(B, 53n), {==})
  +eb = Equal.trans(Nat, Nat.sub(64n, X.clz(w)), Nat.sub(64n, Nat.sub(64n, B)), B, Equal.cong(Nat, Nat, t => Nat.sub(64n, t), X.clz(w), Nat.sub(64n, B), CZ.clz_value(w)), T.subsub(64n, B, N.le_trans(B, 53n, 64n, hB, {==})))
  +e0 = Equal.cong(Nat, F.F64 & F.Exp, b => F.fx_fin(x, w, b), Nat.sub(64n, X.clz(w)), B, eb)
  +hx = RT.le_sub(63n, B, 3000n, N.le_trans(B, 53n, 2937n, BL.bl_le(53n, V, T.mw53(x), Nat.is_le(B, 53n), {==}), {==}))
  +a1 = T.rw_value(F.signbit(x), Nat.sub(3000n, B), w, hx)
  +a2 = Equal.cong(Bool, F.F64, t => SF.round(t, V, Nat.sub(3000n, B)), F.signbit(x), SF.sign(x), FB.signbit_value(x))
  +a3 = Equal.cong(Nat, F.F64, t => SF.round(SF.sign(x), t, Nat.sub(3000n, M.bit_length(t))), V, SF.mant(x), T.dmant_value(x))
  +A0 = F.round_w(F.signbit(x), Nat.sub(3000n, B), w)
  +A1 = SF.round(F.signbit(x), V, Nat.sub(3000n, B))
  +A2 = SF.round(SF.sign(x), V, Nat.sub(3000n, B))
  +A3 = SF.round(SF.sign(x), SF.mant(x), Nat.sub(SF.zb(), M.bit_length(SF.mant(x))))
  +ea = Equal.trans(F.F64, A0, A1, A3, a1, Equal.trans(F.F64, A1, A2, A3, a2, a3))
  +b1 = exp_eq(Nat.add(F.dexp(x), B))
  +b2 = Equal.cong(Nat, F.Exp, t => SF.exp_of(Nat.add(t, B)), F.dexp(x), SF.xexp(x), T.dexp_value(x))
  +b3 = Equal.cong(Nat, F.Exp, t => SF.exp_of(Nat.add(SF.xexp(x), M.bit_length(t))), V, SF.mant(x), T.dmant_value(x))
  +B0 = F.exp_of(Nat.add(F.dexp(x), B))
  +B1 = SF.exp_of(Nat.add(F.dexp(x), B))
  +B2 = SF.exp_of(Nat.add(SF.xexp(x), B))
  +B3 = SF.exp_of(Nat.add(SF.xexp(x), M.bit_length(SF.mant(x))))
  +eb2 = Equal.trans(F.Exp, B0, B1, B3, b1, Equal.trans(F.Exp, B1, B2, B3, b2, b3))
  +p1 = Equal.cong(F.F64, F.F64 & F.Exp, t => (t, B0), A0, A3, ea)
  +p2 = Equal.cong(F.Exp, F.F64 & F.Exp, t => (A3, t), B0, B3, eb2)
  Equal.trans(F.F64 & F.Exp, F.fx_fin(x, w, Nat.sub(64n, X.clz(w))), F.fx_fin(x, w, B), FIN(x), e0, Equal.trans(F.F64 & F.Exp, (A0, B0), (A3, B0), FIN(x), p1, p2))

def fxz_c(+x: F.F64, +iz: Bool) -> {F.fx_z(x, iz) == SF.pickt(F.F64 & F.Exp, iz, (x, F.Exp{False{}, 0n}), FIN(x)) : F.F64 & F.Exp}:
  match iz:
    case True{}:
      {==}
    case False{}:
      fx_nz(x)

def fx_c(+x: F.F64, +t: Bool, +z: Bool, +hz: {X.is_zero(F.frac(x)) == z : Bool}) -> {F.fx_cls(x, t) == SF.pickt(F.F64 & F.Exp, Bool.and(t, Bool.not(z)), (SF.qnan(), F.Exp{False{}, 0n}), SF.pickt(F.F64 & F.Exp, Bool.or(Bool.and(t, z), SF.is_zero(x)), (x, F.Exp{False{}, 0n}), FIN(x))) : F.F64 & F.Exp}:
  match t z:
    case True{} True{}:
      Equal.cong(Bool, F.F64 & F.Exp, b => (F.nan_or(x, Bool.not(b)), F.Exp{False{}, 0n}), X.is_zero(F.frac(x)), True{}, hz)
    case True{} False{}:
      Equal.cong(Bool, F.F64 & F.Exp, b => (F.nan_or(x, Bool.not(b)), F.Exp{False{}, 0n}), X.is_zero(F.frac(x)), False{}, hz)
    case False{} _:
      +e1 = Equal.cong(Bool, F.F64 & F.Exp, b => F.fx_z(x, b), F.is_zero(x), SF.is_zero(x), FB.is_zero_value(x))
      Equal.trans(F.F64 & F.Exp, F.fx_z(x, F.is_zero(x)), F.fx_z(x, SF.is_zero(x)), SF.pickt(F.F64 & F.Exp, SF.is_zero(x), (x, F.Exp{False{}, 0n}), FIN(x)), e1, fxz_c(x, SF.is_zero(x)))

def frexp_value(+x: F.F64) -> SF.Frexp.value(x):
  +e1 = Equal.cong(Nat, F.F64 & F.Exp, u => F.fx_cls(x, Nat.is_eq(u, 2047n)), F.exp_field(x), SF.efield(x), T.ea(x))
  Equal.trans(F.F64 & F.Exp, F.frexp(x), F.fx_cls(x, Nat.is_eq(SF.efield(x), 2047n)), SF.frexp(x), e1, fx_c(x, Nat.is_eq(SF.efield(x), 2047n), Nat.is_eq(SF.frac(x), 0n), T.fz(x)))

# ---- ldexp ----

def LD(+x: F.F64, +neg: Bool, +k: Nat) -> F.F64:
  SF.round(SF.sign(x), SF.mant(x), SF.pick(Nat, neg, Nat.sub(SF.xexp(x), k), Nat.add(SF.xexp(x), k)))

# the round_w of the significand at scale u is the spec's round at u
def rwx(+x: F.F64, +u: Nat, +hu: {Nat.is_le(63n, u) == True{} : Bool}) -> {F.round_w(F.signbit(x), u, F.dmant(x)) == SF.round(SF.sign(x), SF.mant(x), u) : F.F64}:
  +a1 = T.rw_value(F.signbit(x), u, F.dmant(x), hu)
  +a2 = Equal.cong(Bool, F.F64, t => SF.round(t, SW.value(F.dmant(x)), u), F.signbit(x), SF.sign(x), FB.signbit_value(x))
  +a3 = Equal.cong(Nat, F.F64, t => SF.round(SF.sign(x), t, u), SW.value(F.dmant(x)), SF.mant(x), T.dmant_value(x))
  Equal.trans(F.F64, F.round_w(F.signbit(x), u, F.dmant(x)), SF.round(F.signbit(x), SW.value(F.dmant(x)), u), SF.round(SF.sign(x), SF.mant(x), u), a1, Equal.trans(F.F64, SF.round(F.signbit(x), SW.value(F.dmant(x)), u), SF.round(SF.sign(x), SW.value(F.dmant(x)), u), SF.round(SF.sign(x), SF.mant(x), u), a2, a3))

# a - k < 63 when a < k + 63
def slt(+a: Nat, +k: Nat, +h: {Nat.is_lt(a, Nat.add(k, 63n)) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(a, k), 63n) == True{} : Bool}:
  match a k:
    case 0n 0n:
      {==}
    case 0n 1n+ +kp:
      {==}
    case 1n+ +ap 0n:
      h
    case 1n+ +ap 1n+ +kp:
      slt(ap, kp, h)

def ldn_c(+x: F.F64, +k: Nat, +c: Bool, +hc: {Nat.is_lt(F.dexp(x), Nat.add(k, 63n)) == c : Bool}) -> {F.ld_neg(x, k, c) == LD(x, True{}, k) : F.F64}:
  match c:
    case True{}:
      +h1 = L.subst(Nat, t => {Nat.is_lt(t, Nat.add(k, 63n)) == True{} : Bool}, F.dexp(x), SF.xexp(x), T.dexp_value(x), hc)
      +et = tiny(SF.sign(x), SF.mant(x), Nat.sub(SF.xexp(x), k), T.mant_fits(x), slt(SF.xexp(x), k, h1))
      +ez = Equal.trans(F.F64, F.zero(F.signbit(x)), SF.zero(F.signbit(x)), SF.zero(SF.sign(x)), T.zero_v(F.signbit(x)), Equal.cong(Bool, F.F64, t => SF.zero(t), F.signbit(x), SF.sign(x), FB.signbit_value(x)))
      Equal.trans(F.F64, F.zero(F.signbit(x)), SF.zero(SF.sign(x)), LD(x, True{}, k), ez, Equal.sym(F.F64, LD(x, True{}, k), SF.zero(SF.sign(x)), et))
    case False{}:
      +h0 = N.not_lt_le(F.dexp(x), Nat.add(k, 63n), hc)
      +h1 = L.subst(Nat, t => {Nat.is_le(t, F.dexp(x)) == True{} : Bool}, Nat.add(k, 63n), Nat.add(63n, k), NA.add_comm(k, 63n), h0)
      +hu = RT.le_sub(63n, k, F.dexp(x), h1)
      +e1 = rwx(x, Nat.sub(F.dexp(x), k), hu)
      +e2 = Equal.cong(Nat, F.F64, t => SF.round(SF.sign(x), SF.mant(x), Nat.sub(t, k)), F.dexp(x), SF.xexp(x), T.dexp_value(x))
      Equal.trans(F.F64, F.round_w(F.signbit(x), Nat.sub(F.dexp(x), k), F.dmant(x)), SF.round(SF.sign(x), SF.mant(x), Nat.sub(F.dexp(x), k)), LD(x, True{}, k), e1, e2)

def ldf_c(+x: F.F64, +neg: Bool, +k: Nat) -> {F.ld_fin(x, neg, k) == LD(x, neg, k) : F.F64}:
  match neg:
    case True{}:
      ldn_c(x, k, Nat.is_lt(F.dexp(x), Nat.add(k, 63n)), {==})
    case False{}:
      +hu = N.le_trans(63n, F.dexp(x), Nat.add(F.dexp(x), k), T.dexp_ge(x), N.le_add_right(F.dexp(x), k))
      +e1 = rwx(x, Nat.add(F.dexp(x), k), hu)
      +e2 = Equal.cong(Nat, F.F64, t => SF.round(SF.sign(x), SF.mant(x), Nat.add(t, k)), F.dexp(x), SF.xexp(x), T.dexp_value(x))
      Equal.trans(F.F64, F.round_w(F.signbit(x), Nat.add(F.dexp(x), k), F.dmant(x)), SF.round(SF.sign(x), SF.mant(x), Nat.add(F.dexp(x), k)), LD(x, False{}, k), e1, e2)

def ldz_c(+x: F.F64, +neg: Bool, +k: Nat, +iz: Bool) -> {F.ld_z(x, F.Exp{neg, k}, iz) == SF.pick(F.F64, iz, x, LD(x, neg, k)) : F.F64}:
  match iz:
    case True{}:
      {==}
    case False{}:
      ldf_c(x, neg, k)

def ld_c(+x: F.F64, +neg: Bool, +k: Nat, +t: Bool, +z: Bool, +hz: {X.is_zero(F.frac(x)) == z : Bool}) -> {F.ld_cls(x, F.Exp{neg, k}, t) == SF.pick(F.F64, Bool.and(t, Bool.not(z)), SF.qnan(), SF.pick(F.F64, Bool.or(Bool.and(t, z), SF.is_zero(x)), x, LD(x, neg, k))) : F.F64}:
  match t z:
    case True{} True{}:
      Equal.cong(Bool, F.F64, b => F.nan_or(x, Bool.not(b)), X.is_zero(F.frac(x)), True{}, hz)
    case True{} False{}:
      Equal.cong(Bool, F.F64, b => F.nan_or(x, Bool.not(b)), X.is_zero(F.frac(x)), False{}, hz)
    case False{} _:
      +e1 = Equal.cong(Bool, F.F64, b => F.ld_z(x, F.Exp{neg, k}, b), F.is_zero(x), SF.is_zero(x), FB.is_zero_value(x))
      Equal.trans(F.F64, F.ld_z(x, F.Exp{neg, k}, F.is_zero(x)), F.ld_z(x, F.Exp{neg, k}, SF.is_zero(x)), SF.pick(F.F64, SF.is_zero(x), x, LD(x, neg, k)), e1, ldz_c(x, neg, k, SF.is_zero(x)))

def ldexp_value(+x: F.F64, +neg: Bool, +k: Nat) -> SF.Ldexp.value(x, neg, k):
  +e1 = Equal.cong(Nat, F.F64, u => F.ld_cls(x, F.Exp{neg, k}, Nat.is_eq(u, 2047n)), F.exp_field(x), SF.efield(x), T.ea(x))
  Equal.trans(F.F64, F.ldexp(x, F.Exp{neg, k}), F.ld_cls(x, F.Exp{neg, k}, Nat.is_eq(SF.efield(x), 2047n)), SF.ldexp(x, neg, k), e1, ld_c(x, neg, k, Nat.is_eq(SF.efield(x), 2047n), Nat.is_eq(SF.frac(x), 0n), T.fz(x)))
