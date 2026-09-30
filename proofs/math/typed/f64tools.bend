import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ./width.bend as WW
import ./w64add.bend as WA
import ./w64sh.bend as SH
import ./f64bits.bend as FB
import ./f64light.bend as FL
import ./f64round.bend as FR
import ./f64rtools.bend as RT
import ./f64norm.bend as NM
import ./f64nrp.bend as NR
import ./f64cmp.bend as FC
import ./natcmp.bend as NC
import ../../lib/word.bend as WD

# The two tools of the rounding, conversion and remainder functions: dmant
# and dexp decode a double into the spec's significand mant (hidden bit
# included) and scale xexp, and round_w, SoftFloat's normRoundPackToF64 on
# any 64-bit integer (a sticky shift first when its top bit is set), is the
# spec's round (Flocq's round_NE of m 2^(x - Z)) for every scale x >= 63.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# ---- decoding ----

def dz(+E: Nat, +z: Bool) -> {F.dexp_z(E, z) == SF.pick(Nat, z, Nat.sub(SF.zb(), 1074n), Nat.sub(Nat.add(E, SF.zb()), 1075n)) : Nat}:
  match z:
    case True{}:
      {==}
    case False{}:
      Equal.sym(Nat, Nat.sub(Nat.add(E, SF.zb()), 1075n), Nat.add(E, 1925n), Equal.trans(Nat, Nat.sub(Nat.add(E, SF.zb()), 1075n), Nat.add(1925n, E), Nat.add(E, 1925n), FC.esub(E), NA.add_comm(1925n, E)))

def dexp_value(+x: F.F64) -> {F.dexp(x) == SF.xexp(x) : Nat}:
  match x:
    case F.Bits{+xl, +xh}:
      +e1 = Equal.cong(Nat, Nat, t => F.dexp_z(t, Nat.is_eq(t, 0n)), F.exp_field(F.Bits{xl, xh}), SF.efield(F.Bits{xl, xh}), FL.hea(xl, xh))
      Equal.trans(Nat, F.dexp(F.Bits{xl, xh}), F.dexp_z(SF.efield(F.Bits{xl, xh}), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), SF.xexp(F.Bits{xl, xh}), e1, dz(SF.efield(F.Bits{xl, xh}), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)))

def dmf(+f: WU.U64) -> {SW.value(F.dmant_z(f, False{})) == SW.value(X.add(f, WU.U64{0, 1048576})) : Nat}:
  {==}

def dm(+one: Nat, +h1: {one == 1n : Nat}, +f: WU.U64, +Fr: Nat, +hf: {SW.value(f) == Fr : Nat}, +hF: {C.fits(52n, Fr) == True{} : Bool}, +z: Bool) -> {SW.value(F.dmant_z(f, z)) == Nat.add(Fr, C.shift(52n, SF.b2n(Bool.not(z)))) : Nat}:
  match z:
    case True{}:
      +e0 = Equal.trans(Nat, Nat.add(Fr, C.shift(52n, 0n)), Nat.add(Fr, 0n), Fr, Equal.cong(Nat, Nat, t => Nat.add(Fr, t), C.shift(52n, 0n), 0n, WW.shift_zero(52n)), N.add_zero(Fr))
      Equal.trans(Nat, SW.value(f), Fr, Nat.add(Fr, C.shift(52n, 0n)), hf, Equal.sym(Nat, Nat.add(Fr, C.shift(52n, 0n)), Fr, e0))
    case False{}:
      +hFf = L.subst(Nat, t => {C.fits(52n, t) == True{} : Bool}, Fr, SW.value(f), Equal.sym(Nat, SW.value(f), Fr, hf), hF)
      +e1 = NM.hid(one, h1, f, hFf, 1048576, {==})
      +e2 = Equal.cong(Nat, Nat, t => Nat.add(t, C.shift(52n, one)), SW.value(f), Fr, hf)
      # the hidden bit stays `one` / `b2n(not False)`: the checker never
      # meets the closed 2^52
      +eo = Equal.trans(Nat, one, 1n, SF.b2n(Bool.not(False{})), h1, {==})
      +e3 = Equal.cong(Nat, Nat, t => Nat.add(Fr, C.shift(52n, t)), one, SF.b2n(Bool.not(False{})), eo)
      # the implementation's side unfolds on its own (dmant_z), the spec's
      # side is the goal's term as written, so the conversion is syntactic
      +e4 = Equal.trans(Nat, SW.value(X.add(f, WU.U64{0, 1048576})), Nat.add(SW.value(f), C.shift(52n, one)), Nat.add(Fr, C.shift(52n, SF.b2n(Bool.not(False{})))), e1, Equal.trans(Nat, Nat.add(SW.value(f), C.shift(52n, one)), Nat.add(Fr, C.shift(52n, one)), Nat.add(Fr, C.shift(52n, SF.b2n(Bool.not(False{})))), e2, e3))
      +e5 = dmf(f)
      Equal.trans(Nat, SW.value(F.dmant_z(f, False{})), SW.value(X.add(f, WU.U64{0, 1048576})), Nat.add(Fr, C.shift(52n, SF.b2n(Bool.not(False{})))), e5, e4)

def dmant_value(+x: F.F64) -> {SW.value(F.dmant(x)) == SF.mant(x) : Nat}:
  match x:
    case F.Bits{+xl, +xh}:
      +e1 = Equal.cong(Nat, Nat, t => SW.value(F.dmant_z(F.frac(F.Bits{xl, xh}), Nat.is_eq(t, 0n))), F.exp_field(F.Bits{xl, xh}), SF.efield(F.Bits{xl, xh}), FL.hea(xl, xh))
      Equal.trans(Nat, SW.value(F.dmant(F.Bits{xl, xh})), SW.value(F.dmant_z(F.frac(F.Bits{xl, xh}), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n))), SF.mant(F.Bits{xl, xh}), e1, dm(1n, {==}, F.frac(F.Bits{xl, xh}), SF.frac(F.Bits{xl, xh}), FL.hfr(xl, xh), FL.hF(xl, xh), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)))

def b2n_fits(+b: Bool) -> {C.fits(1n, SF.b2n(b)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the significand has at most 53 bits
def mant_fits(+x: F.F64) -> {C.fits(53n, SF.mant(x)) == True{} : Bool}:
  match x:
    case F.Bits{+xl, +xh}:
      WW.limbs_fit(52n, 1n, SF.frac(F.Bits{xl, xh}), SF.b2n(Bool.not(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n))), FL.hF(xl, xh), b2n_fits(Bool.not(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n))))

# ---- round_w ----

def zero_eq(+s: Bool) -> {F.zero(s) == SF.zero(s) : F.F64}:
  match s:
    case True{}:
      {==}
    case False{}:
      {==}

def nz_mono(+h: Nat, +J: Nat, +hle: {Nat.is_le(h, J) == True{} : Bool}, +hz: {Nat.is_eq(h, 0n) == False{} : Bool}) -> {Nat.is_eq(J, 0n) == False{} : Bool}:
  match J:
    case 0n:
      +e = N.le_antisym(h, 0n, hle, N.zero_le(h))
      NC.absurd_tf({Nat.is_eq(0n, 0n) == False{} : Bool}, Equal.sym(Bool, True{}, False{}, Equal.trans(Bool, True{}, Nat.is_eq(h, 0n), False{}, Equal.sym(Bool, Nat.is_eq(h, 0n), True{}, L.subst(Nat, t => {Nat.is_eq(t, 0n) == True{} : Bool}, 0n, h, Equal.sym(Nat, h, 0n, e), {==})), hz)))
    case 1n+j:
      {==}

# h <= jam(h, l)
def le_jam(+h: Nat, +l: Nat) -> {Nat.is_le(h, SW.jam(h, l)) == True{} : Bool}:
  +t = Nat.max(C.bit(h), Nat.min(l, 1n))
  +ejf = FR.jam_form(h, l)
  +hhb = WW.le_add_r(C.bit(h), t, Nat.double(C.half(h)), RT.max_ge_l(C.bit(h), Nat.min(l, 1n)))
  +h1 = L.subst(Nat, z => {Nat.is_le(z, Nat.add(t, Nat.double(C.half(h)))) == True{} : Bool}, Nat.add(C.bit(h), Nat.double(C.half(h))), h, Equal.sym(Nat, h, Nat.add(C.bit(h), Nat.double(C.half(h))), WW.hb(h)), hhb)
  L.subst(Nat, z => {Nat.is_le(h, z) == True{} : Bool}, Nat.add(t, Nat.double(C.half(h))), SW.jam(h, l), Equal.sym(Nat, SW.jam(h, l), Nat.add(t, Nat.double(C.half(h))), ejf), h1)

# top bit set: a sticky shift by one, then normRoundPack at the next scale
def rw_hi(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +x: Nat, +w: WU.U64, +hx: {Nat.is_le(63n, x) == True{} : Bool}, +hnf: {C.fits(63n, SW.value(w)) == False{} : Bool}) -> {F.rw_top(s, x, w, True{}) == SF.round(s, SW.value(w), x) : F.F64}:
  +V = SW.value(w)
  +J = SW.jam(C.high(1n, V), C.low(1n, V))
  ej1 = SH.shr_jam_value(w, 1n)
  ej2 = SH.shr_jam_value(w, 1n)
  ej3 = SH.shr_jam_value(w, 1n)
  +fh = Equal.trans(Bool, C.fits(63n, C.high(1n, V)), C.fits(64n, V), True{}, Equal.sym(Bool, C.fits(64n, V), C.fits(63n, C.high(1n, V)), FR.fits_hc(1n, 63n, V)), FL.vb64(w))
  +fJ = Equal.trans(Bool, C.fits(63n, J), C.fits(63n, C.high(1n, V)), True{}, RT.jam_fits(62n, C.high(1n, V), C.low(1n, V)), fh)
  +nh = FL.nfit_mono(1n, 63n, V, {==}, hnf)
  +nzJ = nz_mono(C.high(1n, V), J, le_jam(C.high(1n, V), C.low(1n, V)), nh)
  +h63 = L.subst(Nat, t => {C.fits(63n, t) == True{} : Bool}, J, SW.value(X.shr_jam(w, 1n)), Equal.sym(Nat, SW.value(X.shr_jam(w, 1n)), J, ej1), fJ)
  +hz = L.subst(Nat, t => {Nat.is_eq(t, 0n) == False{} : Bool}, J, SW.value(X.shr_jam(w, 1n)), Equal.sym(Nat, SW.value(X.shr_jam(w, 1n)), J, ej2), nzJ)
  +hx1 = N.le_trans(63n, x, Nat.add(x, 1n), hx, N.le_add_right(x, 1n))
  +ex = NA.add_assoc(x, 1n, 2180n)
  +r1 = NR.nrp(one, h1, s, Nat.add(x, 2181n), X.shr_jam(w, 1n), Nat.add(x, 1n), ex, hz, h63, hx1)
  +r2 = Equal.cong(Nat, F.F64, t => SF.round(s, t, Nat.add(x, 1n)), SW.value(X.shr_jam(w, 1n)), J, ej3)
  +hb = N.le_trans(56n, 64n, M.bit_length(V), {==}, FL.nfit_bl(63n, V, hnf))
  +r3 = RT.round_jam(s, 1n, V, x, hb)
  Equal.trans(F.F64, F.norm_round_pack(s, Nat.add(x, 2181n), X.shr_jam(w, 1n)), SF.round(s, SW.value(X.shr_jam(w, 1n)), Nat.add(x, 1n)), SF.round(s, V, x), r1, Equal.trans(F.F64, SF.round(s, SW.value(X.shr_jam(w, 1n)), Nat.add(x, 1n)), SF.round(s, J, Nat.add(x, 1n)), SF.round(s, V, x), r2, Equal.sym(F.F64, SF.round(s, V, x), SF.round(s, J, Nat.add(x, 1n)), r3)))

# the top value 2^63 of the test in rw_z (the word c = 2^31 kept abstract, so
# the checker never expands 2^31 in unary)
def top_eq(+one: Nat, +h1: {one == 1n : Nat}, +w: WU.U64, +c: U32, +hc: {c == U32{WD.pw(32n, 31n)} : U32}) -> {X.le(WU.U64{0, c}, w) == Bool.not(C.fits(63n, SW.value(w))) : Bool}:
  e1 = WA.le_value(WU.U64{0, c}, w)
  +ec = FB.pwv(31n, {==}, one, h1, c, hc)
  +e2 = Equal.cong(Nat, Nat, t => Nat.add(0n, C.shift(32n, t)), v(c), C.shift(31n, one), ec)
  +S = C.shift(32n, C.shift(31n, one))
  +e30 = Equal.trans(Nat, Nat.add(0n, S), Nat.add(S, 0n), S, NA.add_comm(0n, S), N.add_zero(S))
  +e3 = Equal.trans(Nat, Nat.add(0n, S), S, C.shift(63n, one), e30, Equal.sym(Nat, C.shift(63n, one), S, WW.shift_comp(32n, 31n, one)))
  +e4 = Equal.cong(Nat, Bool, t => Nat.is_le(t, SW.value(w)), SW.value(WU.U64{0, c}), C.shift(63n, one), Equal.trans(Nat, SW.value(WU.U64{0, c}), Nat.add(0n, C.shift(32n, C.shift(31n, one))), C.shift(63n, one), e2, e3))
  Equal.trans(Bool, X.le(WU.U64{0, c}, w), Nat.is_le(SW.value(WU.U64{0, c}), SW.value(w)), Bool.not(C.fits(63n, SW.value(w))), e1, Equal.trans(Bool, Nat.is_le(SW.value(WU.U64{0, c}), SW.value(w)), Nat.is_le(C.shift(63n, one), SW.value(w)), Bool.not(C.fits(63n, SW.value(w))), e4, FB.le_fit(63n, one, h1, SW.value(w))))

def rw_f(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +x: Nat, +w: WU.U64, +hx: {Nat.is_le(63n, x) == True{} : Bool}, +hz: {Nat.is_eq(SW.value(w), 0n) == False{} : Bool}, +f: Bool, +hf: {C.fits(63n, SW.value(w)) == f : Bool}) -> {F.rw_top(s, x, w, Bool.not(f)) == SF.round(s, SW.value(w), x) : F.F64}:
  match f:
    case True{}:
      NR.nrp(one, h1, s, Nat.add(x, 2180n), w, x, {==}, hz, hf, hx)
    case False{}:
      rw_hi(one, h1, s, x, w, hx, hf)

def rw_c(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +x: Nat, +w: WU.U64, +hx: {Nat.is_le(63n, x) == True{} : Bool}, +z: Bool, +hz: {Nat.is_eq(SW.value(w), 0n) == z : Bool}) -> {F.rw_z(s, x, w, z) == SF.round(s, SW.value(w), x) : F.F64}:
  match z:
    case True{}:
      +e1 = Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.zero(s), SF.round_u(s, SW.value(w), x, Nat.max(Nat.sub(Nat.add(x, M.bit_length(SW.value(w))), 53n), Nat.sub(SF.zb(), 1074n)))), Nat.is_eq(SW.value(w), 0n), True{}, hz)
      Equal.trans(F.F64, F.zero(s), SF.zero(s), SF.round(s, SW.value(w), x), zero_eq(s), Equal.sym(F.F64, SF.round(s, SW.value(w), x), SF.zero(s), e1))
    case False{}:
      +et = Equal.cong(Bool, F.F64, t => F.rw_top(s, x, w, t), X.le(WU.U64{0, 2147483648}, w), Bool.not(C.fits(63n, SW.value(w))), top_eq(one, h1, w, 2147483648, {==}))
      Equal.trans(F.F64, F.rw_top(s, x, w, X.le(WU.U64{0, 2147483648}, w)), F.rw_top(s, x, w, Bool.not(C.fits(63n, SW.value(w)))), SF.round(s, SW.value(w), x), et, rw_f(one, h1, s, x, w, hx, hz, C.fits(63n, SW.value(w)), {==}))

# round_w is the spec's round
def rw_value(+s: Bool, +x: Nat, +w: WU.U64, +hx: {Nat.is_le(63n, x) == True{} : Bool}) -> {F.round_w(s, x, w) == SF.round(s, SW.value(w), x) : F.F64}:
  +ez = Equal.cong(Bool, F.F64, t => F.rw_z(s, x, w, t), X.is_zero(w), Nat.is_eq(SW.value(w), 0n), WA.is_zero_value(w))
  Equal.trans(F.F64, F.round_w(s, x, w), F.rw_z(s, x, w, Nat.is_eq(SW.value(w), 0n)), SF.round(s, SW.value(w), x), ez, rw_c(1n, {==}, s, x, w, hx, Nat.is_eq(SW.value(w), 0n), {==}))

# ---- the fields as the spec reads them ----

def ea(+x: F.F64) -> {F.exp_field(x) == SF.efield(x) : Nat}:
  match x:
    case F.Bits{+xl, +xh}:
      FL.hea(xl, xh)

def fz(+x: F.F64) -> {X.is_zero(F.frac(x)) == Nat.is_eq(SF.frac(x), 0n) : Bool}:
  match x:
    case F.Bits{+xl, +xh}:
      Equal.trans(Bool, X.is_zero(F.frac(F.Bits{xl, xh})), Nat.is_eq(SW.value(F.frac(F.Bits{xl, xh})), 0n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n), WA.is_zero_value(F.frac(F.Bits{xl, xh})), Equal.cong(Nat, Bool, t => Nat.is_eq(t, 0n), SW.value(F.frac(F.Bits{xl, xh})), SF.frac(F.Bits{xl, xh}), FL.hfr(xl, xh)))

# the scale of a finite double is at least 1926 (the subnormal scale)
def dge_z(+e: Nat, +z: Bool) -> {Nat.is_le(63n, F.dexp_z(e, z)) == True{} : Bool}:
  match z:
    case True{}:
      {==}
    case False{}:
      L.subst(Nat, t => {Nat.is_le(63n, t) == True{} : Bool}, Nat.add(1925n, e), Nat.add(e, 1925n), NA.add_comm(1925n, e), {==})

def dexp_ge(+x: F.F64) -> {Nat.is_le(63n, F.dexp(x)) == True{} : Bool}:
  dge_z(F.exp_field(x), Nat.is_eq(F.exp_field(x), 0n))

def xexp_ge(+x: F.F64) -> {Nat.is_le(63n, SF.xexp(x)) == True{} : Bool}:
  L.subst(Nat, t => {Nat.is_le(63n, t) == True{} : Bool}, F.dexp(x), SF.xexp(x), dexp_value(x), dexp_ge(x))

def zero_v(+s: Bool) -> {F.zero(s) == SF.zero(s) : F.F64}:
  zero_eq(s)

def mw53(+x: F.F64) -> {C.fits(53n, SW.value(F.dmant(x))) == True{} : Bool}:
  L.subst(Nat, t => {C.fits(53n, t) == True{} : Bool}, SF.mant(x), SW.value(F.dmant(x)), Equal.sym(Nat, SW.value(F.dmant(x)), SF.mant(x), dmant_value(x)), mant_fits(x))

def subsub(+a: Nat, +b: Nat, +h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.sub(a, Nat.sub(a, b)) == b : Nat}:
  +d = Nat.sub(a, b)
  L.subst(Nat, t => {Nat.sub(t, d) == b : Nat}, Nat.add(b, d), a, N.sub_add(a, b, h), FR.sub_add_l(b, d))

def bzc(+c: Bool) -> {Nat.is_eq(SF.b2n(Bool.not(c)), 0n) == c : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def and_comm(+a: Bool, +b: Bool) -> {Bool.and(a, b) == Bool.and(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# the significand is zero exactly for the zeros
def mant_z(+x: F.F64) -> {Nat.is_eq(SF.mant(x), 0n) == SF.is_zero(x) : Bool}:
  +c = Nat.is_eq(SF.efield(x), 0n)
  +fz0 = Nat.is_eq(SF.frac(x), 0n)
  +e1 = FB.z2(SF.frac(x), 52n, SF.b2n(Bool.not(c)))
  +e2 = Equal.cong(Bool, Bool, b => Bool.and(fz0, b), Nat.is_eq(SF.b2n(Bool.not(c)), 0n), c, bzc(c))
  Equal.trans(Bool, Nat.is_eq(SF.mant(x), 0n), Bool.and(fz0, Nat.is_eq(SF.b2n(Bool.not(c)), 0n)), SF.is_zero(x), e1, Equal.trans(Bool, Bool.and(fz0, Nat.is_eq(SF.b2n(Bool.not(c)), 0n)), Bool.and(fz0, c), SF.is_zero(x), e2, and_comm(fz0, c)))

def dmz(+x: F.F64) -> {Nat.is_eq(SW.value(F.dmant(x)), 0n) == SF.is_zero(x) : Bool}:
  Equal.trans(Bool, Nat.is_eq(SW.value(F.dmant(x)), 0n), Nat.is_eq(SF.mant(x), 0n), SF.is_zero(x), Equal.cong(Nat, Bool, t => Nat.is_eq(t, 0n), SW.value(F.dmant(x)), SF.mant(x), dmant_value(x)), mant_z(x))
