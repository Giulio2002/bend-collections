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
import ../../lib/word.bend as WD
import ./width.bend as WW
import ./u32laws.bend as LW
import ./w64add.bend as WA
import ./w64sh.bend as SH
import ./natcmp.bend as NC
import ./natfuel.bend as NF
import ./f64bits.bend as FB
import ./f64round.bend as FR
import ./f64bl.bend as BL
import ./f64rtools.bend as RT

# The equal-exponent paths of addMagsF64 and subMagsF64: exact sums and
# differences packed directly or rounded once.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def bz0(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +c: U32, +hc: {c == U32{WD.pw(32n, 31n)} : U32}) -> {F.Bits{0, U32.from_nat(C.shift(31n, SF.pick(Nat, s, one, 0n)))} == SF.pick(F.F64, s, F.Bits{0, c}, F.Bits{0, 0}) : F.F64}:
  match s:
    case True{}:
      Equal.cong(U32, F.F64, z => F.Bits{0, z}, U32.from_nat(C.shift(31n, one)), c, Equal.trans(U32, U32.from_nat(C.shift(31n, one)), U32.from_nat(v(c)), c, Equal.cong(Nat, U32, z => U32.from_nat(z), C.shift(31n, one), v(c), Equal.sym(Nat, v(c), C.shift(31n, one), FB.pwv(31n, {==}, one, h1, c, hc))), LW.rt(c)))
    case False{}:
      {==}

# a zero pattern with sign s
def bz(+s: Bool) -> {FR.bits(s, 0n) == SF.zero(s) : F.F64}:
  Equal.trans(F.F64, F.Bits{0, U32.from_nat(C.shift(31n, SF.b2n(s)))}, F.Bits{0, U32.from_nat(C.shift(31n, SF.pick(Nat, s, 1n, 0n)))}, SF.zero(s), Equal.cong(Nat, F.F64, z => F.Bits{0, U32.from_nat(C.shift(31n, z))}, SF.b2n(s), SF.pick(Nat, s, 1n, 0n), Equal.sym(Nat, SF.pick(Nat, s, 1n, 0n), SF.b2n(s), FR.pb(s, 1n, {==}))), bz0(1n, {==}, s, 2147483648, {==}))

def max_le(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.max(a, b) == b : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+ +ap 0n:
      NC.absurd_tf({Nat.max(1n+ap, 0n) == 0n : Nat}, h)
    case 1n+ +ap 1n+ +bp:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.max(ap, bp), bp, max_le(ap, bp, h))

# X.cmp is the order of the values
def cp_c(+x: Nat, +y: Nat, +c: Cmp, +hc: {Nat.cmp(x, y) == c : Cmp}) -> {X.cmp_pick(Nat.is_lt(x, y), Nat.is_eq(x, y)) == c : Cmp}:
  match c:
    case LT{}:
      Equal.trans(Cmp, X.cmp_pick(Nat.is_lt(x, y), Nat.is_eq(x, y)), X.cmp_pick(True{}, Nat.is_eq(x, y)), LT{}, Equal.cong(Bool, Cmp, t => X.cmp_pick(t, Nat.is_eq(x, y)), Nat.is_lt(x, y), True{}, Equal.cong(Cmp, Bool, t => Cmp.is_lt(t), Nat.cmp(x, y), LT{}, hc)), {==})
    case EQ{}:
      Equal.trans(Cmp, X.cmp_pick(Nat.is_lt(x, y), Nat.is_eq(x, y)), X.cmp_pick(False{}, Nat.is_eq(x, y)), EQ{}, Equal.cong(Bool, Cmp, t => X.cmp_pick(t, Nat.is_eq(x, y)), Nat.is_lt(x, y), False{}, Equal.cong(Cmp, Bool, t => Cmp.is_lt(t), Nat.cmp(x, y), EQ{}, hc)), Equal.cong(Bool, Cmp, t => X.cmp_pick(False{}, t), Nat.is_eq(x, y), True{}, Equal.cong(Cmp, Bool, t => Cmp.is_eq(t), Nat.cmp(x, y), EQ{}, hc)))
    case GT{}:
      Equal.trans(Cmp, X.cmp_pick(Nat.is_lt(x, y), Nat.is_eq(x, y)), X.cmp_pick(False{}, Nat.is_eq(x, y)), GT{}, Equal.cong(Bool, Cmp, t => X.cmp_pick(t, Nat.is_eq(x, y)), Nat.is_lt(x, y), False{}, Equal.cong(Cmp, Bool, t => Cmp.is_lt(t), Nat.cmp(x, y), GT{}, hc)), Equal.cong(Bool, Cmp, t => X.cmp_pick(False{}, t), Nat.is_eq(x, y), False{}, Equal.cong(Cmp, Bool, t => Cmp.is_eq(t), Nat.cmp(x, y), GT{}, hc)))

def cmpv(+a: WU.U64, +b: WU.U64) -> {X.cmp(a, b) == Nat.cmp(SW.value(a), SW.value(b)) : Cmp}:
  l1 = WA.lt_value(a, b)
  q1 = WA.eq_value(a, b)
  +e1 = Equal.cong(Bool, Cmp, t => X.cmp_pick(t, X.eq(a, b)), X.lt(a, b), Nat.is_lt(SW.value(a), SW.value(b)), l1)
  +e2 = Equal.cong(Bool, Cmp, t => X.cmp_pick(Nat.is_lt(SW.value(a), SW.value(b)), t), X.eq(a, b), Nat.is_eq(SW.value(a), SW.value(b)), q1)
  Equal.trans(Cmp, X.cmp_pick(X.lt(a, b), X.eq(a, b)), X.cmp_pick(Nat.is_lt(SW.value(a), SW.value(b)), X.eq(a, b)), Nat.cmp(SW.value(a), SW.value(b)), e1, Equal.trans(Cmp, X.cmp_pick(Nat.is_lt(SW.value(a), SW.value(b)), X.eq(a, b)), X.cmp_pick(Nat.is_lt(SW.value(a), SW.value(b)), Nat.is_eq(SW.value(a), SW.value(b))), Nat.cmp(SW.value(a), SW.value(b)), e2, cp_c(SW.value(a), SW.value(b), Nat.cmp(SW.value(a), SW.value(b)), {==})))

def addv2(+fa: WU.U64, +fb: WU.U64, +Fa: Nat, +Fb: Nat, +hfa: {SW.value(fa) == Fa : Nat}, +hfb: {SW.value(fb) == Fb : Nat}, +hFa: {C.fits(52n, Fa) == True{} : Bool}, +hFb: {C.fits(52n, Fb) == True{} : Bool}) -> {SW.value(X.add(fa, fb)) == Nat.add(Fa, Fb) : Nat}:
  a1 = WA.add_value(fa, fb)
  +f53 = FR.fits_add1(52n, Fa, Fb, hFa, hFb)
  Equal.trans(Nat, SW.value(X.add(fa, fb)), C.low(64n, Nat.add(SW.value(fa), SW.value(fb))), Nat.add(Fa, Fb), a1, Equal.trans(Nat, C.low(64n, Nat.add(SW.value(fa), SW.value(fb))), C.low(64n, Nat.add(Fa, Fb)), Nat.add(Fa, Fb), Equal.cong(Nat, Nat, z => C.low(64n, z), Nat.add(SW.value(fa), SW.value(fb)), Nat.add(Fa, Fb), Equal.trans(Nat, Nat.add(SW.value(fa), SW.value(fb)), Nat.add(Fa, SW.value(fb)), Nat.add(Fa, Fb), Equal.cong(Nat, Nat, z => Nat.add(z, SW.value(fb)), SW.value(fa), Fa, hfa), Equal.cong(Nat, Nat, z => Nat.add(Fa, z), SW.value(fb), Fb, hfb))), WW.low_fit(64n, Nat.add(Fa, Fb), SH.fits_mono(53n, 64n, Nat.add(Fa, Fb), {==}, f53))))

def shl_v(+a: WU.U64, +k: Nat, +j: Nat, +hk: {Nat.is_lt(k, 64n) == True{} : Bool}, +hj: {Nat.is_le(Nat.add(k, j), 64n) == True{} : Bool}, +ha: {C.fits(j, SW.value(a)) == True{} : Bool}) -> {SW.value(X.shl(a, k)) == C.shift(k, SW.value(a)) : Nat}:
  sv = SH.shl_value(a, k, hk)
  +f = SH.fits_mono(Nat.add(k, j), 64n, C.shift(k, SW.value(a)), hj, Equal.trans(Bool, C.fits(Nat.add(k, j), C.shift(k, SW.value(a))), C.fits(j, SW.value(a)), True{}, RT.fits_sh(k, j, SW.value(a)), ha))
  Equal.trans(Nat, SW.value(X.shl(a, k)), C.low(64n, C.shift(k, SW.value(a))), C.shift(k, SW.value(a)), sv, WW.low_fit(64n, C.shift(k, SW.value(a)), f))

def f53(+one: Nat, +h1: {one == 1n : Nat}, +Fr: Nat, +hF: {C.fits(52n, Fr) == True{} : Bool}) -> {C.fits(53n, Nat.add(Fr, C.shift(52n, one))) == True{} : Bool}:
  WW.limbs_fit(52n, 1n, Fr, one, hF, L.subst(Nat, z => {C.fits(1n, z) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==}))

# a sum below 2^53 at the subnormal exponent is exact
def r1926(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +m: Nat, +hm: {C.fits(53n, m) == True{} : Bool}, +u: Nat, +hu: {u == 1926n : Nat}, +z: Bool, +hz: {Nat.is_eq(m, 0n) == z : Bool}) -> {SF.round(s, m, 1926n) == FR.bits(s, Nat.add(m, C.shift(52n, 0n))) : F.F64}:
  match z:
    case True{}:
      +e0 = N.eq_from_is_eq(m, 0n, hz)
      Equal.trans(F.F64, SF.round(s, m, 1926n), SF.zero(s), FR.bits(s, Nat.add(m, C.shift(52n, 0n))), Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.zero(s), SF.round_u(s, m, 1926n, Nat.max(Nat.sub(Nat.add(1926n, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)))), Nat.is_eq(m, 0n), True{}, hz), Equal.sym(F.F64, FR.bits(s, Nat.add(m, C.shift(52n, 0n))), SF.zero(s), Equal.trans(F.F64, FR.bits(s, Nat.add(m, C.shift(52n, 0n))), FR.bits(s, 0n), SF.zero(s), Equal.cong(Nat, F.F64, w => FR.bits(s, Nat.add(w, 0n)), m, 0n, e0), bz(s))))
    case False{}:
      +hb = BL.bl_le(53n, m, hm, Nat.is_le(M.bit_length(m), 53n), {==})
      +hle = NF.sub_mono_l(Nat.add(1926n, M.bit_length(m)), 1979n, 53n, N.le_add_left(M.bit_length(m), 53n, 1926n, hb))
      +eu = Equal.trans(Nat, Nat.max(Nat.sub(Nat.add(1926n, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), 1926n, u, max_le(Nat.sub(Nat.add(1926n, M.bit_length(m)), 53n), 1926n, hle), Equal.sym(Nat, u, 1926n, hu))
      +l1 = Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.zero(s), SF.round_u(s, m, 1926n, Nat.max(Nat.sub(Nat.add(1926n, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)))), Nat.is_eq(m, 0n), False{}, hz)
      +l2 = Equal.cong(Nat, F.F64, w => SF.round_u(s, m, 1926n, w), Nat.max(Nat.sub(Nat.add(1926n, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), u, eu)
      +hu1 = L.subst(Nat, w => {Nat.is_le(1926n, w) == True{} : Bool}, 1926n, u, Equal.sym(Nat, u, 1926n, hu), {==})
      +hu2 = L.subst(Nat, w => {Nat.sub(w, 1926n) == 0n : Nat}, 1926n, u, Equal.sym(Nat, u, 1926n, hu), {==})
      +l3a = Equal.cong(Bool, F.F64, t => SF.pack(s, SF.pick(Nat, t, SF.rne(m, Nat.sub(u, 1926n)), C.shift(Nat.sub(1926n, u), m)), u), Nat.is_le(1926n, u), True{}, hu1)
      +l3b = Equal.cong(Nat, F.F64, w => SF.pack(s, SF.rne(m, w), u), Nat.sub(u, 1926n), 0n, hu2)
      +hq = N.lt_le(m, C.shift(53n, one), Equal.trans(Bool, Nat.is_lt(m, C.shift(53n, one)), C.fits(53n, m), True{}, FR.lt_fit(53n, one, h1, m), hm))
      +l4 = FR.pkg(one, h1, s, m, u, 0n, Equal.sym(Nat, u, 1926n, hu), hq, FR.or_t(Bool.not(C.fits(52n, m))), FR.pick_lt(C.fits(53n, m)))
      +r3 = Equal.trans(F.F64, SF.round_u(s, m, 1926n, u), SF.pack(s, SF.rne(m, Nat.sub(u, 1926n)), u), FR.bits(s, Nat.add(m, C.shift(52n, 0n))), l3a, Equal.trans(F.F64, SF.pack(s, SF.rne(m, Nat.sub(u, 1926n)), u), SF.pack(s, m, u), FR.bits(s, Nat.add(m, C.shift(52n, 0n))), l3b, l4))
      Equal.trans(F.F64, SF.round(s, m, 1926n), SF.round_u(s, m, 1926n, Nat.max(Nat.sub(Nat.add(1926n, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), FR.bits(s, Nat.add(m, C.shift(52n, 0n))), l1, Equal.trans(F.F64, SF.round_u(s, m, 1926n, Nat.max(Nat.sub(Nat.add(1926n, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.round_u(s, m, 1926n, u), FR.bits(s, Nat.add(m, C.shift(52n, 0n))), l2, r3))

# addMags, both subnormal: pack(s, 0, fa + fb)
def ame0(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +fa: WU.U64, +fb: WU.U64, +Fa: Nat, +Fb: Nat, +hfa: {SW.value(fa) == Fa : Nat}, +hfb: {SW.value(fb) == Fb : Nat}, +hFa: {C.fits(52n, Fa) == True{} : Bool}, +hFb: {C.fits(52n, Fb) == True{} : Bool}) -> {F.pack(s, 0n, X.add(fa, fb)) == SF.round(s, Nat.add(Fa, Fb), 1926n) : F.F64}:
  +ev = addv2(fa, fb, Fa, Fb, hfa, hfb, hFa, hFb)
  +f53 = FR.fits_add1(52n, Fa, Fb, hFa, hFb)
  +hn = L.subst(Nat, z => {C.fits(63n, Nat.add(z, C.shift(52n, 0n))) == True{} : Bool}, Nat.add(Fa, Fb), SW.value(X.add(fa, fb)), Equal.sym(Nat, SW.value(X.add(fa, fb)), Nat.add(Fa, Fb), ev), L.subst(Nat, z => {C.fits(63n, z) == True{} : Bool}, Nat.add(Fa, Fb), Nat.add(Nat.add(Fa, Fb), 0n), Equal.sym(Nat, Nat.add(Nat.add(Fa, Fb), 0n), Nat.add(Fa, Fb), N.add_zero(Nat.add(Fa, Fb))), SH.fits_mono(53n, 63n, Nat.add(Fa, Fb), {==}, f53)))
  +i1 = FR.pack_v(s, 0n, {==}, X.add(fa, fb), hn)
  +i2 = Equal.cong(Nat, F.F64, z => FR.bits(s, Nat.add(z, C.shift(52n, 0n))), SW.value(X.add(fa, fb)), Nat.add(Fa, Fb), ev)
  Equal.trans(F.F64, F.pack(s, 0n, X.add(fa, fb)), FR.bits(s, Nat.add(Nat.add(Fa, Fb), C.shift(52n, 0n))), SF.round(s, Nat.add(Fa, Fb), 1926n), Equal.trans(F.F64, F.pack(s, 0n, X.add(fa, fb)), FR.bits(s, Nat.add(SW.value(X.add(fa, fb)), C.shift(52n, 0n))), FR.bits(s, Nat.add(Nat.add(Fa, Fb), C.shift(52n, 0n))), i1, i2), Equal.sym(F.F64, SF.round(s, Nat.add(Fa, Fb), 1926n), FR.bits(s, Nat.add(Nat.add(Fa, Fb), C.shift(52n, 0n))), r1926(one, h1, s, Nat.add(Fa, Fb), f53, 1926n, {==}, Nat.is_eq(Nat.add(Fa, Fb), 0n), {==})))

def swap4(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  +i1 = Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), Equal.trans(Nat, Nat.add(b, Nat.add(c, d)), Nat.add(Nat.add(b, c), d), Nat.add(c, Nat.add(b, d)), Equal.sym(Nat, Nat.add(Nat.add(b, c), d), Nat.add(b, Nat.add(c, d)), NA.add_assoc(b, c, d)), Equal.trans(Nat, Nat.add(Nat.add(b, c), d), Nat.add(Nat.add(c, b), d), Nat.add(c, Nat.add(b, d)), Equal.cong(Nat, Nat, z => Nat.add(z, d), Nat.add(b, c), Nat.add(c, b), NA.add_comm(b, c)), NA.add_assoc(c, b, d))))
  Equal.trans(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)), NA.add_assoc(a, b, Nat.add(c, d)), Equal.trans(Nat, Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(a, Nat.add(c, Nat.add(b, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)), i1, Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))), NA.add_assoc(a, c, Nat.add(b, d)))))

def c53(+one: Nat, +h1: {one == 1n : Nat}, +c: U32, +hc: {c == U32{WD.pw(32n, 21n)} : U32}) -> {SW.value(WU.U64{0, c}) == C.shift(53n, one) : Nat}:
  Equal.trans(Nat, C.shift(32n, v(c)), C.shift(32n, C.shift(21n, one)), C.shift(53n, one), Equal.cong(Nat, Nat, z => C.shift(32n, z), v(c), C.shift(21n, one), FB.pwv(21n, {==}, one, h1, c, hc)), Equal.sym(Nat, C.shift(53n, one), C.shift(32n, C.shift(21n, one)), WW.shift_comp(32n, 21n, one)))

# addMags, equal normal exponents e: the 54-bit sum at bit 62
def amen(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +e: Nat, +fa: WU.U64, +fb: WU.U64, +Fa: Nat, +Fb: Nat, +hfa: {SW.value(fa) == Fa : Nat}, +hfb: {SW.value(fb) == Fb : Nat}, +hFa: {C.fits(52n, Fa) == True{} : Bool}, +hFb: {C.fits(52n, Fb) == True{} : Bool}, +c: U32, +hc: {c == U32{WD.pw(32n, 21n)} : U32}) -> {F.round_pack(s, Nat.add(F.off(), e), X.shl(X.add(WU.U64{0, c}, X.add(fa, fb)), 9n)) == SF.round(s, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), Nat.add(1925n, e)) : F.F64}:
  +eW = Equal.trans(Nat, Nat.add(C.shift(53n, one), Nat.add(Fa, Fb)), Nat.add(Nat.add(C.shift(52n, one), C.shift(52n, one)), Nat.add(Fa, Fb)), Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(Fa, Fb)), Nat.double(C.shift(52n, one)), Nat.add(C.shift(52n, one), C.shift(52n, one)), NA.double_self(C.shift(52n, one))), Equal.trans(Nat, Nat.add(Nat.add(C.shift(52n, one), C.shift(52n, one)), Nat.add(Fa, Fb)), Nat.add(Nat.add(C.shift(52n, one), Fa), Nat.add(C.shift(52n, one), Fb)), Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), swap4(C.shift(52n, one), C.shift(52n, one), Fa, Fb), Equal.trans(Nat, Nat.add(Nat.add(C.shift(52n, one), Fa), Nat.add(C.shift(52n, one), Fb)), Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(C.shift(52n, one), Fb)), Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(C.shift(52n, one), Fb)), Nat.add(C.shift(52n, one), Fa), Nat.add(Fa, C.shift(52n, one)), NA.add_comm(C.shift(52n, one), Fa)), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(Fa, C.shift(52n, one)), z), Nat.add(C.shift(52n, one), Fb), Nat.add(Fb, C.shift(52n, one)), NA.add_comm(C.shift(52n, one), Fb)))))
  +fW = FR.fits_add1(53n, Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one)), f53(one, h1, Fa, hFa), f53(one, h1, Fb, hFb))
  +fV = L.subst(Nat, z => {C.fits(54n, z) == True{} : Bool}, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), Nat.add(C.shift(53n, one), Nat.add(Fa, Fb)), Equal.sym(Nat, Nat.add(C.shift(53n, one), Nat.add(Fa, Fb)), Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), eW), fW)
  +eA = Equal.trans(Nat, SW.value(X.add(WU.U64{0, c}, X.add(fa, fb))), C.low(64n, Nat.add(SW.value(WU.U64{0, c}), SW.value(X.add(fa, fb)))), Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), WA.add_value(WU.U64{0, c}, X.add(fa, fb)), Equal.trans(Nat, C.low(64n, Nat.add(SW.value(WU.U64{0, c}), SW.value(X.add(fa, fb)))), C.low(64n, Nat.add(C.shift(53n, one), SW.value(X.add(fa, fb)))), Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), Equal.cong(Nat, Nat, z => C.low(64n, Nat.add(z, SW.value(X.add(fa, fb)))), SW.value(WU.U64{0, c}), C.shift(53n, one), c53(one, h1, c, hc)), Equal.trans(Nat, C.low(64n, Nat.add(C.shift(53n, one), SW.value(X.add(fa, fb)))), C.low(64n, Nat.add(C.shift(53n, one), Nat.add(Fa, Fb))), Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), Equal.cong(Nat, Nat, z => C.low(64n, Nat.add(C.shift(53n, one), z)), SW.value(X.add(fa, fb)), Nat.add(Fa, Fb), addv2(fa, fb, Fa, Fb, hfa, hfb, hFa, hFb)), Equal.trans(Nat, C.low(64n, Nat.add(C.shift(53n, one), Nat.add(Fa, Fb))), Nat.add(C.shift(53n, one), Nat.add(Fa, Fb)), Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), WW.low_fit(64n, Nat.add(C.shift(53n, one), Nat.add(Fa, Fb)), SH.fits_mono(54n, 64n, Nat.add(C.shift(53n, one), Nat.add(Fa, Fb)), {==}, fV)), eW))))
  +fA = L.subst(Nat, z => {C.fits(54n, z) == True{} : Bool}, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), SW.value(X.add(WU.U64{0, c}, X.add(fa, fb))), Equal.sym(Nat, SW.value(X.add(WU.U64{0, c}, X.add(fa, fb))), Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), eA), fW)
  +eS = Equal.trans(Nat, SW.value(X.shl(X.add(WU.U64{0, c}, X.add(fa, fb)), 9n)), C.shift(9n, SW.value(X.add(WU.U64{0, c}, X.add(fa, fb)))), C.shift(9n, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one)))), shl_v(X.add(WU.U64{0, c}, X.add(fa, fb)), 9n, 54n, {==}, {==}, fA), Equal.cong(Nat, Nat, z => C.shift(9n, z), SW.value(X.add(WU.U64{0, c}, X.add(fa, fb))), Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), eA))
  +f63 = Equal.trans(Bool, C.fits(63n, C.shift(9n, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))))), C.fits(54n, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one)))), True{}, RT.fits_sh(9n, 54n, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one)))), fW)
  +h63 = L.subst(Nat, z => {C.fits(63n, z) == True{} : Bool}, C.shift(9n, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one)))), SW.value(X.shl(X.add(WU.U64{0, c}, X.add(fa, fb)), 9n)), Equal.sym(Nat, SW.value(X.shl(X.add(WU.U64{0, c}, X.add(fa, fb)), 9n)), C.shift(9n, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one)))), eS), f63)
  +f0 = Equal.trans(Bool, C.fits(53n, C.shift(53n, one)), Nat.is_lt(C.shift(53n, one), C.shift(53n, one)), False{}, Equal.sym(Bool, Nat.is_lt(C.shift(53n, one), C.shift(53n, one)), C.fits(53n, C.shift(53n, one)), FR.lt_fit(53n, one, h1, C.shift(53n, one))), N.lt_irrefl(C.shift(53n, one)))
  +hle = L.subst(Nat, z => {Nat.is_le(C.shift(53n, one), z) == True{} : Bool}, Nat.add(C.shift(53n, one), Nat.add(Fa, Fb)), Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), eW, N.le_add_right(C.shift(53n, one), Nat.add(Fa, Fb)))
  +f62 = Equal.trans(Bool, C.fits(62n, C.shift(9n, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))))), C.fits(53n, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one)))), False{}, RT.fits_sh(9n, 53n, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one)))), FR.nfit(53n, C.shift(53n, one), Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), hle, f0))
  +h62 = L.subst(Nat, z => {C.fits(62n, z) == False{} : Bool}, C.shift(9n, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one)))), SW.value(X.shl(X.add(WU.U64{0, c}, X.add(fa, fb)), 9n)), Equal.sym(Nat, SW.value(X.shl(X.add(WU.U64{0, c}, X.add(fa, fb)), 9n)), C.shift(9n, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one)))), eS), f62)
  +hx = Equal.trans(Nat, Nat.add(Nat.add(e, 1916n), 2180n), Nat.add(e, 4096n), Nat.add(4096n, e), NA.add_assoc(e, 1916n, 2180n), NA.add_comm(e, 4096n))
  +r1 = FR.round_pack(s, Nat.add(F.off(), e), X.shl(X.add(WU.U64{0, c}, X.add(fa, fb)), 9n), Nat.add(e, 1916n), hx, h62, h63)
  +r2 = Equal.cong(Nat, F.F64, z => SF.round(s, z, Nat.add(e, 1916n)), SW.value(X.shl(X.add(WU.U64{0, c}, X.add(fa, fb)), 9n)), C.shift(9n, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one)))), eS)
  +r3 = RT.round_shift(s, 9n, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), Nat.add(e, 1916n))
  +ex = Equal.trans(Nat, Nat.add(Nat.add(e, 1916n), 9n), Nat.add(e, 1925n), Nat.add(1925n, e), NA.add_assoc(e, 1916n, 9n), NA.add_comm(e, 1925n))
  +r4 = Equal.cong(Nat, F.F64, z => SF.round(s, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), z), Nat.add(Nat.add(e, 1916n), 9n), Nat.add(1925n, e), ex)
  Equal.trans(F.F64, F.round_pack(s, Nat.add(F.off(), e), X.shl(X.add(WU.U64{0, c}, X.add(fa, fb)), 9n)), SF.round(s, SW.value(X.shl(X.add(WU.U64{0, c}, X.add(fa, fb)), 9n)), Nat.add(e, 1916n)), SF.round(s, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), Nat.add(1925n, e)), r1, Equal.trans(F.F64, SF.round(s, SW.value(X.shl(X.add(WU.U64{0, c}, X.add(fa, fb)), 9n)), Nat.add(e, 1916n)), SF.round(s, C.shift(9n, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one)))), Nat.add(e, 1916n)), SF.round(s, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), Nat.add(1925n, e)), r2, Equal.trans(F.F64, SF.round(s, C.shift(9n, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one)))), Nat.add(e, 1916n)), SF.round(s, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), Nat.add(Nat.add(e, 1916n), 9n)), SF.round(s, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), Nat.add(1925n, e)), r3, r4)))
