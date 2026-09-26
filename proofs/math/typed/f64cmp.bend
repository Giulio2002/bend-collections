import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../lib/word.bend as WD
import ../../lib/u32.bend as U
import ./width.bend as WW
import ./u32laws.bend as LW
import ./w64add.bend as WA
import ./f64bits.bend as FB
import ./natcmp.bend as NC

# Lt.value, Le.value and Eq.value of spec/math/f64.bend. The order of the
# finite doubles by value, m * 2^e, is the order of their bit patterns
# read as integers (sign aside): IEEE 754-2019 section 3.4's encoding is
# monotone, the fact Flocq proves as Binary.bounded_lt / B2R_le (Boldo and
# Melquiond, Flocq, ARITH 2011) and that SoftFloat's f64_lt/f64_le compare
# magnitudes by. Here K(x) = frac + 2^52 * efield is that integer.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# ---- the scaled significands G = 2^e' * (F + 2^52 c) of two finite doubles ----

# shift(a, x) <= shift(b, x) for a <= b
def shmk(+a: Nat, +b: Nat, +x: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(C.shift(a, x), C.shift(b, x)) == True{} : Bool}:
  +h0 = WW.shift_mono(a, x, C.shift(Nat.sub(b, a), x), WW.shift_ge(Nat.sub(b, a), x))
  L.subst(Nat, z => {Nat.is_le(C.shift(a, x), z) == True{} : Bool}, C.shift(a, C.shift(Nat.sub(b, a), x)), C.shift(b, x), Equal.sym(Nat, C.shift(b, x), C.shift(a, C.shift(Nat.sub(b, a), x)), NC.sh_split(b, a, x, h)), h0)

# G < 2^(1+E) * 2^52
def gub(+one: Nat, +h1: {one == 1n : Nat}, +E: Nat, +b: Bool, +hb: {Nat.is_eq(E, 0n) == b : Bool}, +c: Nat, +hc: {c == SF.b2n(Bool.not(b)) : Nat}, +F: Nat, +hF: {C.fits(52n, F) == True{} : Bool}) -> {Nat.is_lt(C.shift(SF.pick(Nat, b, 1n, E), Nat.add(F, C.shift(52n, c))), C.shift(1n+E, C.shift(52n, one))) == True{} : Bool}:
  match b:
    case True{}:
      +eE = N.eq_from_is_eq(E, 0n, hb)
      +ef = Equal.trans(Nat, Nat.add(F, C.shift(52n, c)), Nat.add(F, 0n), F, Equal.cong(Nat, Nat, z => Nat.add(F, C.shift(52n, z)), c, 0n, hc), N.add_zero(F))
      +h0 = WW.shift_lt(1n, F, C.shift(52n, one), WW.lt_one(52n, one, h1, F, hF))
      +h2 = L.subst(Nat, z => {Nat.is_lt(C.shift(1n, z), C.shift(1n, C.shift(52n, one))) == True{} : Bool}, F, Nat.add(F, C.shift(52n, c)), Equal.sym(Nat, Nat.add(F, C.shift(52n, c)), F, ef), h0)
      L.subst(Nat, z => {Nat.is_lt(C.shift(1n, Nat.add(F, C.shift(52n, c))), C.shift(1n+z, C.shift(52n, one))) == True{} : Bool}, 0n, E, Equal.sym(Nat, E, 0n, eE), h2)
    case False{}:
      +ec = Equal.trans(Nat, c, 1n, one, hc, Equal.sym(Nat, one, 1n, h1))
      +es = Equal.cong(Nat, Nat, z => Nat.add(F, C.shift(52n, z)), c, one, ec)
      +h0 = N.lt_add_r2(F, C.shift(52n, one), C.shift(52n, one), WW.lt_one(52n, one, h1, F, hF))
      +h1b = L.subst(Nat, z => {Nat.is_lt(Nat.add(F, C.shift(52n, one)), z) == True{} : Bool}, Nat.add(C.shift(52n, one), C.shift(52n, one)), Nat.double(C.shift(52n, one)), Equal.sym(Nat, Nat.double(C.shift(52n, one)), Nat.add(C.shift(52n, one), C.shift(52n, one)), NA.double_self(C.shift(52n, one))), h0)
      +h2 = WW.shift_lt(E, Nat.add(F, C.shift(52n, one)), Nat.double(C.shift(52n, one)), h1b)
      +h3 = L.subst(Nat, z => {Nat.is_lt(C.shift(E, Nat.add(F, C.shift(52n, one))), z) == True{} : Bool}, C.shift(E, Nat.double(C.shift(52n, one))), Nat.double(C.shift(E, C.shift(52n, one))), WW.shift_dbl(E, C.shift(52n, one)), h2)
      L.subst(Nat, z => {Nat.is_lt(C.shift(E, z), Nat.double(C.shift(E, C.shift(52n, one)))) == True{} : Bool}, Nat.add(F, C.shift(52n, one)), Nat.add(F, C.shift(52n, c)), Equal.sym(Nat, Nat.add(F, C.shift(52n, c)), Nat.add(F, C.shift(52n, one)), es), h3)

# a normal G is at least 2^E * 2^52
def glb(+one: Nat, +h1: {one == 1n : Nat}, +E: Nat, +c: Nat, +hc: {c == 1n : Nat}, +F: Nat) -> {Nat.is_le(C.shift(E, C.shift(52n, one)), C.shift(E, Nat.add(F, C.shift(52n, c)))) == True{} : Bool}:
  +ec = Equal.trans(Nat, c, 1n, one, hc, Equal.sym(Nat, one, 1n, h1))
  +e1 = Equal.cong(Nat, Nat, z => C.shift(52n, z), c, one, ec)
  +h0 = L.subst(Nat, z => {Nat.is_le(C.shift(52n, one), z) == True{} : Bool}, Nat.add(C.shift(52n, one), F), Nat.add(F, C.shift(52n, one)), NA.add_comm(C.shift(52n, one), F), N.le_add_right(C.shift(52n, one), F))
  +h2 = L.subst(Nat, z => {Nat.is_le(C.shift(52n, one), Nat.add(F, z)) == True{} : Bool}, C.shift(52n, one), C.shift(52n, c), Equal.sym(Nat, C.shift(52n, c), C.shift(52n, one), e1), h0)
  WW.shift_mono(E, C.shift(52n, one), Nat.add(F, C.shift(52n, c)), h2)

def gcmp_lt(+one: Nat, +h1: {one == 1n : Nat}, +E1: Nat, +b1: Bool, +hb1: {Nat.is_eq(E1, 0n) == b1 : Bool}, +c1: Nat, +hc1: {c1 == SF.b2n(Bool.not(b1)) : Nat}, +F1: Nat, +hF1: {C.fits(52n, F1) == True{} : Bool}, +E2: Nat, +c2: Nat, +hc2: {c2 == 1n : Nat}, +F2: Nat, +hlt: {Nat.is_lt(E1, E2) == True{} : Bool}) -> {Nat.is_lt(C.shift(SF.pick(Nat, b1, 1n, E1), Nat.add(F1, C.shift(52n, c1))), C.shift(SF.pick(Nat, False{}, 1n, E2), Nat.add(F2, C.shift(52n, c2)))) == True{} : Bool}:
  +G1 = C.shift(SF.pick(Nat, b1, 1n, E1), Nat.add(F1, C.shift(52n, c1)))
  +G2 = C.shift(E2, Nat.add(F2, C.shift(52n, c2)))
  +ha = gub(one, h1, E1, b1, hb1, c1, hc1, F1, hF1)
  +hb = shmk(1n+E1, E2, C.shift(52n, one), N.lt_succ_le_succ(E1, E2, hlt))
  +hc = glb(one, h1, E2, c2, hc2, F2)
  N.lt_le_trans(G1, C.shift(1n+E1, C.shift(52n, one)), G2, ha, N.le_trans(C.shift(1n+E1, C.shift(52n, one)), C.shift(E2, C.shift(52n, one)), G2, hb, hc))

# G orders like (E, F) lexicographically
def gcmp_c(+one: Nat, +h1: {one == 1n : Nat}, +E1: Nat, +b1: Bool, +hb1: {Nat.is_eq(E1, 0n) == b1 : Bool}, +c1: Nat, +hc1: {c1 == SF.b2n(Bool.not(b1)) : Nat}, +F1: Nat, +hF1: {C.fits(52n, F1) == True{} : Bool}, +E2: Nat, +b2: Bool, +hb2: {Nat.is_eq(E2, 0n) == b2 : Bool}, +c2: Nat, +hc2: {c2 == SF.b2n(Bool.not(b2)) : Nat}, +F2: Nat, +hF2: {C.fits(52n, F2) == True{} : Bool}, +d: Cmp, +hd: {Nat.cmp(E1, E2) == d : Cmp}) -> {Nat.cmp(C.shift(SF.pick(Nat, b1, 1n, E1), Nat.add(F1, C.shift(52n, c1))), C.shift(SF.pick(Nat, b2, 1n, E2), Nat.add(F2, C.shift(52n, c2)))) == NC.lex(d, Nat.cmp(F1, F2)) : Cmp}:
  match d:
    case LT{}:
      +hlt = NC.lt_of_cmp(E1, E2, hd)
      +eb2 = Equal.trans(Bool, b2, Nat.is_eq(E2, 0n), False{}, Equal.sym(Bool, Nat.is_eq(E2, 0n), b2, hb2), N.is_eq_sym_false(0n, E2, N.is_eq_lt(0n, E2, N.le_lt_trans(0n, E1, E2, N.zero_le(E1), hlt))))
      +hc2b = L.subst(Bool, z => {c2 == SF.b2n(Bool.not(z)) : Nat}, b2, False{}, eb2, hc2)
      +r = NC.cmp_lt(C.shift(SF.pick(Nat, b1, 1n, E1), Nat.add(F1, C.shift(52n, c1))), C.shift(SF.pick(Nat, False{}, 1n, E2), Nat.add(F2, C.shift(52n, c2))), gcmp_lt(one, h1, E1, b1, hb1, c1, hc1, F1, hF1, E2, c2, hc2b, F2, hlt))
      L.subst(Bool, z => {Nat.cmp(C.shift(SF.pick(Nat, b1, 1n, E1), Nat.add(F1, C.shift(52n, c1))), C.shift(SF.pick(Nat, z, 1n, E2), Nat.add(F2, C.shift(52n, c2)))) == LT{} : Cmp}, False{}, b2, Equal.sym(Bool, b2, False{}, eb2), r)
    case GT{}:
      +hgt = NC.lt_of_gt(E1, E2, hd)
      +eb1 = Equal.trans(Bool, b1, Nat.is_eq(E1, 0n), False{}, Equal.sym(Bool, Nat.is_eq(E1, 0n), b1, hb1), N.is_eq_sym_false(0n, E1, N.is_eq_lt(0n, E1, N.le_lt_trans(0n, E2, E1, N.zero_le(E2), hgt))))
      +hc1b = L.subst(Bool, z => {c1 == SF.b2n(Bool.not(z)) : Nat}, b1, False{}, eb1, hc1)
      +r = NC.cmp_gt(C.shift(SF.pick(Nat, False{}, 1n, E1), Nat.add(F1, C.shift(52n, c1))), C.shift(SF.pick(Nat, b2, 1n, E2), Nat.add(F2, C.shift(52n, c2))), gcmp_lt(one, h1, E2, b2, hb2, c2, hc2, F2, hF2, E1, c1, hc1b, F1, hgt))
      L.subst(Bool, z => {Nat.cmp(C.shift(SF.pick(Nat, z, 1n, E1), Nat.add(F1, C.shift(52n, c1))), C.shift(SF.pick(Nat, b2, 1n, E2), Nat.add(F2, C.shift(52n, c2)))) == GT{} : Cmp}, False{}, b1, Equal.sym(Bool, b1, False{}, eb1), r)
    case EQ{}:
      +eE = NC.eq_of_cmp(E1, E2, hd)
      +eb = Equal.trans(Bool, b1, Nat.is_eq(E1, 0n), b2, Equal.sym(Bool, Nat.is_eq(E1, 0n), b1, hb1), Equal.trans(Bool, Nat.is_eq(E1, 0n), Nat.is_eq(E2, 0n), b2, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), E1, E2, eE), hb2))
      +ec = Equal.trans(Nat, c1, SF.b2n(Bool.not(b1)), c2, hc1, Equal.trans(Nat, SF.b2n(Bool.not(b1)), SF.b2n(Bool.not(b2)), c2, Equal.cong(Bool, Nat, z => SF.b2n(Bool.not(z)), b1, b2, eb), Equal.sym(Nat, c2, SF.b2n(Bool.not(b2)), hc2)))
      +S1 = C.shift(52n, c1)
      +p1 = SF.pick(Nat, b1, 1n, E1)
      +base = Equal.trans(Cmp, Nat.cmp(C.shift(p1, Nat.add(F1, S1)), C.shift(p1, Nat.add(F2, S1))), Nat.cmp(Nat.add(F1, S1), Nat.add(F2, S1)), Nat.cmp(F1, F2), NC.cmp_shift(p1, Nat.add(F1, S1), Nat.add(F2, S1)), NC.cmp_addr(F1, F2, S1))
      +s1 = L.subst(Nat, z => {Nat.cmp(C.shift(SF.pick(Nat, b1, 1n, E1), Nat.add(F1, C.shift(52n, c1))), C.shift(SF.pick(Nat, b1, 1n, E1), Nat.add(F2, C.shift(52n, z)))) == Nat.cmp(F1, F2) : Cmp}, c1, c2, ec, base)
      +s2 = L.subst(Bool, z => {Nat.cmp(C.shift(SF.pick(Nat, b1, 1n, E1), Nat.add(F1, C.shift(52n, c1))), C.shift(SF.pick(Nat, z, 1n, E1), Nat.add(F2, C.shift(52n, c2)))) == Nat.cmp(F1, F2) : Cmp}, b1, b2, eb, s1)
      L.subst(Nat, z => {Nat.cmp(C.shift(SF.pick(Nat, b1, 1n, E1), Nat.add(F1, C.shift(52n, c1))), C.shift(SF.pick(Nat, b2, 1n, z), Nat.add(F2, C.shift(52n, c2)))) == Nat.cmp(F1, F2) : Cmp}, E1, E2, eE, s2)

def gcmp(+one: Nat, +h1: {one == 1n : Nat}, +E1: Nat, +b1: Bool, +hb1: {Nat.is_eq(E1, 0n) == b1 : Bool}, +c1: Nat, +hc1: {c1 == SF.b2n(Bool.not(b1)) : Nat}, +F1: Nat, +hF1: {C.fits(52n, F1) == True{} : Bool}, +E2: Nat, +b2: Bool, +hb2: {Nat.is_eq(E2, 0n) == b2 : Bool}, +c2: Nat, +hc2: {c2 == SF.b2n(Bool.not(b2)) : Nat}, +F2: Nat, +hF2: {C.fits(52n, F2) == True{} : Bool}) -> {Nat.cmp(C.shift(SF.pick(Nat, b1, 1n, E1), Nat.add(F1, C.shift(52n, c1))), C.shift(SF.pick(Nat, b2, 1n, E2), Nat.add(F2, C.shift(52n, c2)))) == NC.lex(Nat.cmp(E1, E2), Nat.cmp(F1, F2)) : Cmp}:
  gcmp_c(one, h1, E1, b1, hb1, c1, hc1, F1, hF1, E2, b2, hb2, c2, hc2, F2, hF2, Nat.cmp(E1, E2), {==})

# ---- the value order of two doubles ----

def hF(+xl: U32, +xh: U32) -> {C.fits(52n, SF.frac(F.Bits{xl, xh})) == True{} : Bool}:
  WW.limbs_fit(32n, 20n, v(xl), C.low(20n, v(xh)), LW.vb(xl), WW.low_fits(20n, v(xh)))

def esub(+E: Nat) -> {Nat.sub(Nat.add(E, SF.zb()), 1075n) == Nat.add(1925n, E) : Nat}:
  Equal.trans(Nat, Nat.sub(Nat.add(E, SF.zb()), 1075n), Nat.sub(Nat.add(SF.zb(), E), 1075n), Nat.add(1925n, E), Equal.cong(Nat, Nat, z => Nat.sub(z, 1075n), Nat.add(E, SF.zb()), Nat.add(SF.zb(), E), NA.add_comm(E, SF.zb())), {==})

# 2^xexp = 2^1925 * 2^e' with e' = max(E, 1)
def xsh(+E: Nat, +b: Bool, +m: Nat) -> {C.shift(SF.pick(Nat, b, Nat.sub(SF.zb(), 1074n), Nat.sub(Nat.add(E, SF.zb()), 1075n)), m) == C.shift(1925n, C.shift(SF.pick(Nat, b, 1n, E), m)) : Nat}:
  match b:
    case True{}:
      WW.shift_comp(1925n, 1n, m)
    case False{}:
      Equal.trans(Nat, C.shift(Nat.sub(Nat.add(E, SF.zb()), 1075n), m), C.shift(Nat.add(1925n, E), m), C.shift(1925n, C.shift(E, m)), Equal.cong(Nat, Nat, z => C.shift(z, m), Nat.sub(Nat.add(E, SF.zb()), 1075n), Nat.add(1925n, E), esub(E)), WW.shift_comp(1925n, E, m))

# the finite branch of mag_cmp compares K
def mcf(+one: Nat, +h1: {one == 1n : Nat}, +xl: U32, +xh: U32, +yl: U32, +yh: U32) -> {Nat.cmp(C.shift(Nat.sub(SF.xexp(F.Bits{xl, xh}), Nat.min(SF.xexp(F.Bits{xl, xh}), SF.xexp(F.Bits{yl, yh}))), SF.mant(F.Bits{xl, xh})), C.shift(Nat.sub(SF.xexp(F.Bits{yl, yh}), Nat.min(SF.xexp(F.Bits{xl, xh}), SF.xexp(F.Bits{yl, yh}))), SF.mant(F.Bits{yl, yh}))) == Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))) : Cmp}:
  +hFx = hF(xl, xh)
  +hFy = hF(yl, yh)
  +e1 = NC.cmp_min(SF.xexp(F.Bits{xl, xh}), SF.xexp(F.Bits{yl, yh}), SF.mant(F.Bits{xl, xh}), SF.mant(F.Bits{yl, yh}))
  +ex = xsh(SF.efield(F.Bits{xl, xh}), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), SF.mant(F.Bits{xl, xh}))
  +ey = xsh(SF.efield(F.Bits{yl, yh}), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), SF.mant(F.Bits{yl, yh}))
  +e2 = Equal.trans(Cmp, Nat.cmp(C.shift(SF.xexp(F.Bits{xl, xh}), SF.mant(F.Bits{xl, xh})), C.shift(SF.xexp(F.Bits{yl, yh}), SF.mant(F.Bits{yl, yh}))), Nat.cmp(C.shift(1925n, C.shift(SF.pick(Nat, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), 1n, SF.efield(F.Bits{xl, xh})), SF.mant(F.Bits{xl, xh}))), C.shift(SF.xexp(F.Bits{yl, yh}), SF.mant(F.Bits{yl, yh}))), Nat.cmp(C.shift(1925n, C.shift(SF.pick(Nat, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), 1n, SF.efield(F.Bits{xl, xh})), SF.mant(F.Bits{xl, xh}))), C.shift(1925n, C.shift(SF.pick(Nat, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), 1n, SF.efield(F.Bits{yl, yh})), SF.mant(F.Bits{yl, yh})))), Equal.cong(Nat, Cmp, z => Nat.cmp(z, C.shift(SF.xexp(F.Bits{yl, yh}), SF.mant(F.Bits{yl, yh}))), C.shift(SF.xexp(F.Bits{xl, xh}), SF.mant(F.Bits{xl, xh})), C.shift(1925n, C.shift(SF.pick(Nat, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), 1n, SF.efield(F.Bits{xl, xh})), SF.mant(F.Bits{xl, xh}))), ex), Equal.cong(Nat, Cmp, z => Nat.cmp(C.shift(1925n, C.shift(SF.pick(Nat, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), 1n, SF.efield(F.Bits{xl, xh})), SF.mant(F.Bits{xl, xh}))), z), C.shift(SF.xexp(F.Bits{yl, yh}), SF.mant(F.Bits{yl, yh})), C.shift(1925n, C.shift(SF.pick(Nat, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), 1n, SF.efield(F.Bits{yl, yh})), SF.mant(F.Bits{yl, yh}))), ey))
  +e3 = NC.cmp_shift(1925n, C.shift(SF.pick(Nat, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), 1n, SF.efield(F.Bits{xl, xh})), SF.mant(F.Bits{xl, xh})), C.shift(SF.pick(Nat, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), 1n, SF.efield(F.Bits{yl, yh})), SF.mant(F.Bits{yl, yh})))
  +e4 = gcmp(one, h1, SF.efield(F.Bits{xl, xh}), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), {==}, SF.b2n(Bool.not(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n))), {==}, SF.frac(F.Bits{xl, xh}), hFx, SF.efield(F.Bits{yl, yh}), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), {==}, SF.b2n(Bool.not(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n))), {==}, SF.frac(F.Bits{yl, yh}), hFy)
  +e5 = Equal.sym(Cmp, Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))), NC.lex(Nat.cmp(SF.efield(F.Bits{xl, xh}), SF.efield(F.Bits{yl, yh})), Nat.cmp(SF.frac(F.Bits{xl, xh}), SF.frac(F.Bits{yl, yh}))), NC.cmp_limbs(52n, SF.frac(F.Bits{xl, xh}), SF.efield(F.Bits{xl, xh}), SF.frac(F.Bits{yl, yh}), SF.efield(F.Bits{yl, yh}), hFx, hFy))
  Equal.trans(Cmp, Nat.cmp(C.shift(Nat.sub(SF.xexp(F.Bits{xl, xh}), Nat.min(SF.xexp(F.Bits{xl, xh}), SF.xexp(F.Bits{yl, yh}))), SF.mant(F.Bits{xl, xh})), C.shift(Nat.sub(SF.xexp(F.Bits{yl, yh}), Nat.min(SF.xexp(F.Bits{xl, xh}), SF.xexp(F.Bits{yl, yh}))), SF.mant(F.Bits{yl, yh}))), Nat.cmp(C.shift(SF.xexp(F.Bits{xl, xh}), SF.mant(F.Bits{xl, xh})), C.shift(SF.xexp(F.Bits{yl, yh}), SF.mant(F.Bits{yl, yh}))), Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))), e1, Equal.trans(Cmp, Nat.cmp(C.shift(SF.xexp(F.Bits{xl, xh}), SF.mant(F.Bits{xl, xh})), C.shift(SF.xexp(F.Bits{yl, yh}), SF.mant(F.Bits{yl, yh}))), Nat.cmp(C.shift(1925n, C.shift(SF.pick(Nat, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), 1n, SF.efield(F.Bits{xl, xh})), SF.mant(F.Bits{xl, xh}))), C.shift(1925n, C.shift(SF.pick(Nat, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), 1n, SF.efield(F.Bits{yl, yh})), SF.mant(F.Bits{yl, yh})))), Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))), e2, Equal.trans(Cmp, Nat.cmp(C.shift(1925n, C.shift(SF.pick(Nat, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), 1n, SF.efield(F.Bits{xl, xh})), SF.mant(F.Bits{xl, xh}))), C.shift(1925n, C.shift(SF.pick(Nat, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), 1n, SF.efield(F.Bits{yl, yh})), SF.mant(F.Bits{yl, yh})))), Nat.cmp(C.shift(SF.pick(Nat, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), 1n, SF.efield(F.Bits{xl, xh})), SF.mant(F.Bits{xl, xh})), C.shift(SF.pick(Nat, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), 1n, SF.efield(F.Bits{yl, yh})), SF.mant(F.Bits{yl, yh}))), Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))), e3, Equal.trans(Cmp, Nat.cmp(C.shift(SF.pick(Nat, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), 1n, SF.efield(F.Bits{xl, xh})), SF.mant(F.Bits{xl, xh})), C.shift(SF.pick(Nat, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), 1n, SF.efield(F.Bits{yl, yh})), SF.mant(F.Bits{yl, yh}))), NC.lex(Nat.cmp(SF.efield(F.Bits{xl, xh}), SF.efield(F.Bits{yl, yh})), Nat.cmp(SF.frac(F.Bits{xl, xh}), SF.frac(F.Bits{yl, yh}))), Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))), e4, e5))))

def and_l(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      NC.absurd_tf({False{} == True{} : Bool}, h)

def and_r(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      NC.absurd_tf({b == True{} : Bool}, h)

def or_l(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      NC.absurd_tf({True{} == False{} : Bool}, Equal.sym(Bool, True{}, False{}, h))
    case False{}:
      {==}

def or_r(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      NC.absurd_tf({b == False{} : Bool}, Equal.sym(Bool, True{}, False{}, h))
    case False{}:
      h

# neither infinite nor NaN: the exponent field is not 2047
def nl(+a: Bool, +d: Bool, +hi: {Bool.and(a, d) == False{} : Bool}, +hn: {Bool.and(a, Bool.not(d)) == False{} : Bool}) -> {a == False{} : Bool}:
  match a d:
    case True{} True{}:
      NC.absurd_tf({True{} == False{} : Bool}, Equal.sym(Bool, True{}, False{}, hi))
    case True{} False{}:
      NC.absurd_tf({True{} == False{} : Bool}, Equal.sym(Bool, True{}, False{}, hn))
    case False{} _:
      {==}

def lt2047(+xl: U32, +xh: U32, +hi: {SF.is_inf(F.Bits{xl, xh}) == False{} : Bool}, +hn: {SF.is_nan(F.Bits{xl, xh}) == False{} : Bool}) -> {Nat.is_lt(SF.efield(F.Bits{xl, xh}), 2047n) == True{} : Bool}:
  +a = nl(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n), hi, hn)
  Equal.trans(Bool, Nat.is_lt(SF.efield(F.Bits{xl, xh}), 2047n), Bool.not(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n)), True{}, FB.lt_ne(SF.efield(F.Bits{xl, xh}), 2047n, WW.low_lt(11n, C.high(20n, v(xh)))), Equal.cong(Bool, Bool, t => Bool.not(t), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), False{}, a))

def magc_c(+one: Nat, +h1: {one == 1n : Nat}, +xl: U32, +xh: U32, +yl: U32, +yh: U32, +nx: {SF.is_nan(F.Bits{xl, xh}) == False{} : Bool}, +ny: {SF.is_nan(F.Bits{yl, yh}) == False{} : Bool}, +ix: Bool, +hix: {SF.is_inf(F.Bits{xl, xh}) == ix : Bool}, +iy: Bool, +hiy: {SF.is_inf(F.Bits{yl, yh}) == iy : Bool}) -> {SF.pick(Cmp, ix, SF.pick(Cmp, iy, EQ{}, GT{}), SF.pick(Cmp, iy, LT{}, Nat.cmp(C.shift(Nat.sub(SF.xexp(F.Bits{xl, xh}), Nat.min(SF.xexp(F.Bits{xl, xh}), SF.xexp(F.Bits{yl, yh}))), SF.mant(F.Bits{xl, xh})), C.shift(Nat.sub(SF.xexp(F.Bits{yl, yh}), Nat.min(SF.xexp(F.Bits{xl, xh}), SF.xexp(F.Bits{yl, yh}))), SF.mant(F.Bits{yl, yh}))))) == Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))) : Cmp}:
  match ix iy:
    case True{} True{}:
      +ex = N.eq_from_is_eq(SF.efield(F.Bits{xl, xh}), 2047n, and_l(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n), hix))
      +ey = N.eq_from_is_eq(SF.efield(F.Bits{yl, yh}), 2047n, and_l(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n), hiy))
      +fx = N.eq_from_is_eq(SF.frac(F.Bits{xl, xh}), 0n, and_r(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n), hix))
      +fy = N.eq_from_is_eq(SF.frac(F.Bits{yl, yh}), 0n, and_r(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n), hiy))
      +eE = Equal.trans(Nat, SF.efield(F.Bits{xl, xh}), 2047n, SF.efield(F.Bits{yl, yh}), ex, Equal.sym(Nat, SF.efield(F.Bits{yl, yh}), 2047n, ey))
      +eF = Equal.trans(Nat, SF.frac(F.Bits{xl, xh}), 0n, SF.frac(F.Bits{yl, yh}), fx, Equal.sym(Nat, SF.frac(F.Bits{yl, yh}), 0n, fy))
      +eK = Equal.trans(Nat, Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh}))), Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(52n, SF.efield(F.Bits{xl, xh}))), SF.frac(F.Bits{xl, xh}), SF.frac(F.Bits{yl, yh}), eF), Equal.cong(Nat, Nat, z => Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, z)), SF.efield(F.Bits{xl, xh}), SF.efield(F.Bits{yl, yh}), eE))
      Equal.sym(Cmp, Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))), EQ{}, L.subst(Nat, z => {Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), z) == EQ{} : Cmp}, Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh}))), eK, NC.cmp_refl(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))))))
    case True{} False{}:
      +ex = N.eq_from_is_eq(SF.efield(F.Bits{xl, xh}), 2047n, and_l(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n), hix))
      +hy = lt2047(yl, yh, hiy, ny)
      +h = L.subst(Nat, z => {Nat.is_lt(SF.efield(F.Bits{yl, yh}), z) == True{} : Bool}, 2047n, SF.efield(F.Bits{xl, xh}), Equal.sym(Nat, SF.efield(F.Bits{xl, xh}), 2047n, ex), hy)
      Equal.sym(Cmp, Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))), GT{}, Equal.trans(Cmp, Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))), NC.lex(Nat.cmp(SF.efield(F.Bits{xl, xh}), SF.efield(F.Bits{yl, yh})), Nat.cmp(SF.frac(F.Bits{xl, xh}), SF.frac(F.Bits{yl, yh}))), GT{}, NC.cmp_limbs(52n, SF.frac(F.Bits{xl, xh}), SF.efield(F.Bits{xl, xh}), SF.frac(F.Bits{yl, yh}), SF.efield(F.Bits{yl, yh}), hF(xl, xh), hF(yl, yh)), Equal.cong(Cmp, Cmp, t => NC.lex(t, Nat.cmp(SF.frac(F.Bits{xl, xh}), SF.frac(F.Bits{yl, yh}))), Nat.cmp(SF.efield(F.Bits{xl, xh}), SF.efield(F.Bits{yl, yh})), GT{}, NC.cmp_gt(SF.efield(F.Bits{xl, xh}), SF.efield(F.Bits{yl, yh}), h))))
    case False{} True{}:
      +ey = N.eq_from_is_eq(SF.efield(F.Bits{yl, yh}), 2047n, and_l(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n), hiy))
      +hx = lt2047(xl, xh, hix, nx)
      +h = L.subst(Nat, z => {Nat.is_lt(SF.efield(F.Bits{xl, xh}), z) == True{} : Bool}, 2047n, SF.efield(F.Bits{yl, yh}), Equal.sym(Nat, SF.efield(F.Bits{yl, yh}), 2047n, ey), hx)
      Equal.sym(Cmp, Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))), LT{}, Equal.trans(Cmp, Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))), NC.lex(Nat.cmp(SF.efield(F.Bits{xl, xh}), SF.efield(F.Bits{yl, yh})), Nat.cmp(SF.frac(F.Bits{xl, xh}), SF.frac(F.Bits{yl, yh}))), LT{}, NC.cmp_limbs(52n, SF.frac(F.Bits{xl, xh}), SF.efield(F.Bits{xl, xh}), SF.frac(F.Bits{yl, yh}), SF.efield(F.Bits{yl, yh}), hF(xl, xh), hF(yl, yh)), Equal.cong(Cmp, Cmp, t => NC.lex(t, Nat.cmp(SF.frac(F.Bits{xl, xh}), SF.frac(F.Bits{yl, yh}))), Nat.cmp(SF.efield(F.Bits{xl, xh}), SF.efield(F.Bits{yl, yh})), LT{}, NC.cmp_lt(SF.efield(F.Bits{xl, xh}), SF.efield(F.Bits{yl, yh}), h))))
    case False{} False{}:
      mcf(one, h1, xl, xh, yl, yh)

# mag_cmp is the order of K on doubles that are not NaN
def magc(+one: Nat, +h1: {one == 1n : Nat}, +xl: U32, +xh: U32, +yl: U32, +yh: U32, +nx: {SF.is_nan(F.Bits{xl, xh}) == False{} : Bool}, +ny: {SF.is_nan(F.Bits{yl, yh}) == False{} : Bool}) -> {SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh}) == Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))) : Cmp}:
  magc_c(one, h1, xl, xh, yl, yh, nx, ny, SF.is_inf(F.Bits{xl, xh}), {==}, SF.is_inf(F.Bits{yl, yh}), {==})

# the magnitude word is K
def magQ(+xl: U32, +xh: U32) -> {Nat.add(v(xl), C.shift(32n, C.low(31n, v(xh)))) == Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))) : Nat}:
  +H = v(xh)
  +f = C.low(20n, H)
  +Ee = C.low(11n, C.high(20n, H))
  Equal.trans(Nat, Nat.add(v(xl), C.shift(32n, C.low(31n, H))), Nat.add(v(xl), C.shift(32n, Nat.add(f, C.shift(20n, Ee)))), Nat.add(Nat.add(v(xl), C.shift(32n, f)), C.shift(52n, Ee)), Equal.cong(Nat, Nat, z => Nat.add(v(xl), C.shift(32n, z)), C.low(31n, H), Nat.add(f, C.shift(20n, Ee)), FB.low_split(20n, 11n, H)), Equal.trans(Nat, Nat.add(v(xl), C.shift(32n, Nat.add(f, C.shift(20n, Ee)))), Nat.add(v(xl), Nat.add(C.shift(32n, f), C.shift(32n, C.shift(20n, Ee)))), Nat.add(Nat.add(v(xl), C.shift(32n, f)), C.shift(52n, Ee)), Equal.cong(Nat, Nat, z => Nat.add(v(xl), z), C.shift(32n, Nat.add(f, C.shift(20n, Ee))), Nat.add(C.shift(32n, f), C.shift(32n, C.shift(20n, Ee))), WW.shift_add(32n, f, C.shift(20n, Ee))), Equal.trans(Nat, Nat.add(v(xl), Nat.add(C.shift(32n, f), C.shift(32n, C.shift(20n, Ee)))), Nat.add(v(xl), Nat.add(C.shift(32n, f), C.shift(52n, Ee))), Nat.add(Nat.add(v(xl), C.shift(32n, f)), C.shift(52n, Ee)), Equal.cong(Nat, Nat, z => Nat.add(v(xl), Nat.add(C.shift(32n, f), z)), C.shift(32n, C.shift(20n, Ee)), C.shift(52n, Ee), Equal.sym(Nat, C.shift(52n, Ee), C.shift(32n, C.shift(20n, Ee)), WW.shift_comp(32n, 20n, Ee))), Equal.sym(Nat, Nat.add(Nat.add(v(xl), C.shift(32n, f)), C.shift(52n, Ee)), Nat.add(v(xl), Nat.add(C.shift(32n, f), C.shift(52n, Ee))), NA.add_assoc(v(xl), C.shift(32n, f), C.shift(52n, Ee))))))

def magv(+xl: U32, +xh: U32, +m31: U32, +hm31: {m31 == U32{WD.mask(32n, 31n)} : U32}) -> {SW.value(WU.U64{xl, U32.and(xh, m31)}) == Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))) : Nat}:
  Equal.trans(Nat, Nat.add(v(xl), C.shift(32n, v(U32.and(xh, m31)))), Nat.add(v(xl), C.shift(32n, C.low(31n, v(xh)))), Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Equal.cong(Nat, Nat, z => Nat.add(v(xl), C.shift(32n, z)), v(U32.and(xh, m31)), C.low(31n, v(xh)), FB.andm(xh, 31n, m31, hm31)), magQ(xl, xh))

# ---- the comparison clauses ----

def hm(+one: Nat, +h1: {one == 1n : Nat}, +xl: U32, +xh: U32, +yl: U32, +yh: U32, +nx: {SF.is_nan(F.Bits{xl, xh}) == False{} : Bool}, +ny: {SF.is_nan(F.Bits{yl, yh}) == False{} : Bool}) -> {X.lt(F.mag(F.Bits{xl, xh}), F.mag(F.Bits{yl, yh})) == Cmp.is_lt(SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})) : Bool}:
  e1 = WA.lt_value(F.mag(F.Bits{xl, xh}), F.mag(F.Bits{yl, yh}))
  +e2 = Equal.trans(Bool, Nat.is_lt(SW.value(F.mag(F.Bits{xl, xh})), SW.value(F.mag(F.Bits{yl, yh}))), Nat.is_lt(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), SW.value(F.mag(F.Bits{yl, yh}))), Nat.is_lt(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))), Equal.cong(Nat, Bool, t => Nat.is_lt(t, SW.value(F.mag(F.Bits{yl, yh}))), SW.value(F.mag(F.Bits{xl, xh})), Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), magv(xl, xh, 2147483647, {==})), Equal.cong(Nat, Bool, t => Nat.is_lt(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), t), SW.value(F.mag(F.Bits{yl, yh})), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh}))), magv(yl, yh, 2147483647, {==})))
  +e3 = Equal.cong(Cmp, Bool, t => Cmp.is_lt(t), Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))), SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh}), Equal.sym(Cmp, SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh}), Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))), magc(one, h1, xl, xh, yl, yh, nx, ny)))
  Equal.trans(Bool, X.lt(F.mag(F.Bits{xl, xh}), F.mag(F.Bits{yl, yh})), Nat.is_lt(SW.value(F.mag(F.Bits{xl, xh})), SW.value(F.mag(F.Bits{yl, yh}))), Cmp.is_lt(SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), e1, Equal.trans(Bool, Nat.is_lt(SW.value(F.mag(F.Bits{xl, xh})), SW.value(F.mag(F.Bits{yl, yh}))), Nat.is_lt(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))), Cmp.is_lt(SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), e2, e3))

def hm2(+one: Nat, +h1: {one == 1n : Nat}, +xl: U32, +xh: U32, +yl: U32, +yh: U32, +nx: {SF.is_nan(F.Bits{xl, xh}) == False{} : Bool}, +ny: {SF.is_nan(F.Bits{yl, yh}) == False{} : Bool}) -> {X.lt(F.mag(F.Bits{yl, yh}), F.mag(F.Bits{xl, xh})) == Cmp.is_lt(SF.flip(SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh}))) : Bool}:
  e1 = WA.lt_value(F.mag(F.Bits{yl, yh}), F.mag(F.Bits{xl, xh}))
  +e2 = Equal.trans(Bool, Nat.is_lt(SW.value(F.mag(F.Bits{yl, yh})), SW.value(F.mag(F.Bits{xl, xh}))), Nat.is_lt(Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh}))), SW.value(F.mag(F.Bits{xl, xh}))), Nat.is_lt(Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh}))), Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh})))), Equal.cong(Nat, Bool, t => Nat.is_lt(t, SW.value(F.mag(F.Bits{xl, xh}))), SW.value(F.mag(F.Bits{yl, yh})), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh}))), magv(yl, yh, 2147483647, {==})), Equal.cong(Nat, Bool, t => Nat.is_lt(Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh}))), t), SW.value(F.mag(F.Bits{xl, xh})), Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), magv(xl, xh, 2147483647, {==})))
  +e3 = Equal.cong(Cmp, Bool, t => Cmp.is_lt(t), Nat.cmp(Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh}))), Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh})))), SF.flip(Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh}))))), Equal.sym(Cmp, SF.flip(Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh}))))), Nat.cmp(Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh}))), Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh})))), NC.cmp_flip(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh}))))))
  +e4 = Equal.cong(Cmp, Bool, t => Cmp.is_lt(SF.flip(t)), Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))), SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh}), Equal.sym(Cmp, SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh}), Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))), magc(one, h1, xl, xh, yl, yh, nx, ny)))
  Equal.trans(Bool, X.lt(F.mag(F.Bits{yl, yh}), F.mag(F.Bits{xl, xh})), Nat.is_lt(SW.value(F.mag(F.Bits{yl, yh})), SW.value(F.mag(F.Bits{xl, xh}))), Cmp.is_lt(SF.flip(SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh}))), e1, Equal.trans(Bool, Nat.is_lt(SW.value(F.mag(F.Bits{yl, yh})), SW.value(F.mag(F.Bits{xl, xh}))), Nat.is_lt(Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh}))), Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh})))), Cmp.is_lt(SF.flip(SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh}))), e2, Equal.trans(Bool, Nat.is_lt(Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh}))), Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh})))), Cmp.is_lt(SF.flip(Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))))), Cmp.is_lt(SF.flip(SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh}))), e3, e4)))

def lts(+xl: U32, +xh: U32, +yl: U32, +yh: U32, +sa: Bool, +sb: Bool, +mc: Cmp, +h: {X.lt(F.mag(F.Bits{xl, xh}), F.mag(F.Bits{yl, yh})) == Cmp.is_lt(mc) : Bool}, +h2: {X.lt(F.mag(F.Bits{yl, yh}), F.mag(F.Bits{xl, xh})) == Cmp.is_lt(SF.flip(mc)) : Bool}) -> {F.lt_s(F.Bits{xl, xh}, F.Bits{yl, yh}, sa, sb) == Cmp.is_lt(SF.pick(Cmp, Bool.not(Bool.xor(sa, sb)), SF.pick(Cmp, sa, SF.flip(mc), mc), SF.pick(Cmp, sa, LT{}, GT{}))) : Bool}:
  match sa sb:
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      h
    case True{} True{}:
      h2

def nlf(+c: Cmp) -> {Bool.not(Cmp.is_lt(SF.flip(c))) == Cmp.is_le(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def nlc(+c: Cmp) -> {Bool.not(Cmp.is_lt(c)) == Cmp.is_le(SF.flip(c)) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def eqflip(+c: Cmp) -> {Cmp.is_eq(c) == Cmp.is_eq(SF.flip(c)) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def andff(+a: Bool, +b: Bool) -> {Bool.and(a, Bool.and(b, False{})) == False{} : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} _:
      {==}

def les(+xl: U32, +xh: U32, +yl: U32, +yh: U32, +sa: Bool, +sb: Bool, +mc: Cmp, +h: {X.lt(F.mag(F.Bits{xl, xh}), F.mag(F.Bits{yl, yh})) == Cmp.is_lt(mc) : Bool}, +h2: {X.lt(F.mag(F.Bits{yl, yh}), F.mag(F.Bits{xl, xh})) == Cmp.is_lt(SF.flip(mc)) : Bool}) -> {F.le_s(F.Bits{xl, xh}, F.Bits{yl, yh}, sa, sb) == Cmp.is_le(SF.pick(Cmp, Bool.not(Bool.xor(sa, sb)), SF.pick(Cmp, sa, SF.flip(mc), mc), SF.pick(Cmp, sa, LT{}, GT{}))) : Bool}:
  match sa sb:
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      Equal.trans(Bool, Bool.not(X.lt(F.mag(F.Bits{yl, yh}), F.mag(F.Bits{xl, xh}))), Bool.not(Cmp.is_lt(SF.flip(mc))), Cmp.is_le(mc), Equal.cong(Bool, Bool, t => Bool.not(t), X.lt(F.mag(F.Bits{yl, yh}), F.mag(F.Bits{xl, xh})), Cmp.is_lt(SF.flip(mc)), h2), nlf(mc))
    case True{} True{}:
      Equal.trans(Bool, Bool.not(X.lt(F.mag(F.Bits{xl, xh}), F.mag(F.Bits{yl, yh}))), Bool.not(Cmp.is_lt(mc)), Cmp.is_le(SF.flip(mc)), Equal.cong(Bool, Bool, t => Bool.not(t), X.lt(F.mag(F.Bits{xl, xh}), F.mag(F.Bits{yl, yh})), Cmp.is_lt(mc), h), nlc(mc))

def eqs(+eL: Bool, +eW: Bool, +sa: Bool, +sb: Bool, +mc: Cmp, +h: {Bool.and(eL, eW) == Cmp.is_eq(mc) : Bool}) -> {Bool.and(eL, Bool.and(eW, Nat.is_eq(SF.b2n(sa), SF.b2n(sb)))) == Cmp.is_eq(SF.pick(Cmp, Bool.not(Bool.xor(sa, sb)), SF.pick(Cmp, sa, SF.flip(mc), mc), SF.pick(Cmp, sa, LT{}, GT{}))) : Bool}:
  match sa sb:
    case True{} True{}:
      Equal.trans(Bool, Bool.and(eL, Bool.and(eW, True{})), Bool.and(eL, eW), Cmp.is_eq(SF.flip(mc)), Equal.cong(Bool, Bool, t => Bool.and(eL, t), Bool.and(eW, True{}), eW, U.and_true(eW)), Equal.trans(Bool, Bool.and(eL, eW), Cmp.is_eq(mc), Cmp.is_eq(SF.flip(mc)), h, eqflip(mc)))
    case False{} False{}:
      Equal.trans(Bool, Bool.and(eL, Bool.and(eW, True{})), Bool.and(eL, eW), Cmp.is_eq(mc), Equal.cong(Bool, Bool, t => Bool.and(eL, t), Bool.and(eW, True{}), eW, U.and_true(eW)), h)
    case True{} False{}:
      andff(eL, eW)
    case False{} True{}:
      andff(eL, eW)

def lt_gen(+one: Nat, +h1: {one == 1n : Nat}, +xl: U32, +xh: U32, +yl: U32, +yh: U32, +bad: Bool, +hbad: {Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})) == bad : Bool}, +z: Bool) -> {F.lt_z(F.Bits{xl, xh}, F.Bits{yl, yh}, bad, z) == Bool.and(Bool.not(bad), Cmp.is_lt(SF.pick(Cmp, z, EQ{}, SF.pick(Cmp, Bool.not(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}))), SF.pick(Cmp, SF.sign(F.Bits{xl, xh}), SF.flip(SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), SF.pick(Cmp, SF.sign(F.Bits{xl, xh}), LT{}, GT{}))))) : Bool}:
  match bad z:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      +nx = or_l(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh}), hbad)
      +ny = or_r(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh}), hbad)
      +e1 = Equal.trans(Bool, F.lt_s(F.Bits{xl, xh}, F.Bits{yl, yh}, F.signbit(F.Bits{xl, xh}), F.signbit(F.Bits{yl, yh})), F.lt_s(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), F.signbit(F.Bits{yl, yh})), F.lt_s(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh})), Equal.cong(Bool, Bool, t => F.lt_s(F.Bits{xl, xh}, F.Bits{yl, yh}, t, F.signbit(F.Bits{yl, yh})), F.signbit(F.Bits{xl, xh}), SF.sign(F.Bits{xl, xh}), FB.signbit_value(F.Bits{xl, xh})), Equal.cong(Bool, Bool, t => F.lt_s(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), t), F.signbit(F.Bits{yl, yh}), SF.sign(F.Bits{yl, yh}), FB.signbit_value(F.Bits{yl, yh})))
      Equal.trans(Bool, F.lt_s(F.Bits{xl, xh}, F.Bits{yl, yh}, F.signbit(F.Bits{xl, xh}), F.signbit(F.Bits{yl, yh})), F.lt_s(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh})), Cmp.is_lt(SF.pick(Cmp, Bool.not(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}))), SF.pick(Cmp, SF.sign(F.Bits{xl, xh}), SF.flip(SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), SF.pick(Cmp, SF.sign(F.Bits{xl, xh}), LT{}, GT{}))), e1, lts(xl, xh, yl, yh, SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}), SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh}), hm(one, h1, xl, xh, yl, yh, nx, ny), hm2(one, h1, xl, xh, yl, yh, nx, ny)))

def le_gen(+one: Nat, +h1: {one == 1n : Nat}, +xl: U32, +xh: U32, +yl: U32, +yh: U32, +bad: Bool, +hbad: {Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})) == bad : Bool}, +z: Bool) -> {F.le_z(F.Bits{xl, xh}, F.Bits{yl, yh}, bad, z) == Bool.and(Bool.not(bad), Cmp.is_le(SF.pick(Cmp, z, EQ{}, SF.pick(Cmp, Bool.not(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}))), SF.pick(Cmp, SF.sign(F.Bits{xl, xh}), SF.flip(SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), SF.pick(Cmp, SF.sign(F.Bits{xl, xh}), LT{}, GT{}))))) : Bool}:
  match bad z:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      +nx = or_l(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh}), hbad)
      +ny = or_r(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh}), hbad)
      +e1 = Equal.trans(Bool, F.le_s(F.Bits{xl, xh}, F.Bits{yl, yh}, F.signbit(F.Bits{xl, xh}), F.signbit(F.Bits{yl, yh})), F.le_s(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), F.signbit(F.Bits{yl, yh})), F.le_s(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh})), Equal.cong(Bool, Bool, t => F.le_s(F.Bits{xl, xh}, F.Bits{yl, yh}, t, F.signbit(F.Bits{yl, yh})), F.signbit(F.Bits{xl, xh}), SF.sign(F.Bits{xl, xh}), FB.signbit_value(F.Bits{xl, xh})), Equal.cong(Bool, Bool, t => F.le_s(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), t), F.signbit(F.Bits{yl, yh}), SF.sign(F.Bits{yl, yh}), FB.signbit_value(F.Bits{yl, yh})))
      Equal.trans(Bool, F.le_s(F.Bits{xl, xh}, F.Bits{yl, yh}, F.signbit(F.Bits{xl, xh}), F.signbit(F.Bits{yl, yh})), F.le_s(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh})), Cmp.is_le(SF.pick(Cmp, Bool.not(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}))), SF.pick(Cmp, SF.sign(F.Bits{xl, xh}), SF.flip(SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), SF.pick(Cmp, SF.sign(F.Bits{xl, xh}), LT{}, GT{}))), e1, les(xl, xh, yl, yh, SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}), SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh}), hm(one, h1, xl, xh, yl, yh, nx, ny), hm2(one, h1, xl, xh, yl, yh, nx, ny)))

def hq(+one: Nat, +h1: {one == 1n : Nat}, +xl: U32, +xh: U32, +yl: U32, +yh: U32, +nx: {SF.is_nan(F.Bits{xl, xh}) == False{} : Bool}, +ny: {SF.is_nan(F.Bits{yl, yh}) == False{} : Bool}) -> {Bool.and(Nat.is_eq(v(xl), v(yl)), Nat.is_eq(C.low(31n, v(xh)), C.low(31n, v(yh)))) == Cmp.is_eq(SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})) : Bool}:
  +e1 = WW.eq_limbs(32n, v(xl), C.low(31n, v(xh)), v(yl), C.low(31n, v(yh)), LW.vb(xl), LW.vb(yl))
  +e2 = Equal.trans(Bool, Nat.is_eq(Nat.add(v(xl), C.shift(32n, C.low(31n, v(xh)))), Nat.add(v(yl), C.shift(32n, C.low(31n, v(yh))))), Nat.is_eq(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(v(yl), C.shift(32n, C.low(31n, v(yh))))), Nat.is_eq(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))), Equal.cong(Nat, Bool, t => Nat.is_eq(t, Nat.add(v(yl), C.shift(32n, C.low(31n, v(yh))))), Nat.add(v(xl), C.shift(32n, C.low(31n, v(xh)))), Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), magQ(xl, xh)), Equal.cong(Nat, Bool, t => Nat.is_eq(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), t), Nat.add(v(yl), C.shift(32n, C.low(31n, v(yh)))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh}))), magQ(yl, yh)))
  +e3 = Equal.cong(Cmp, Bool, t => Cmp.is_eq(t), Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))), SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh}), Equal.sym(Cmp, SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh}), Nat.cmp(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))), magc(one, h1, xl, xh, yl, yh, nx, ny)))
  Equal.trans(Bool, Bool.and(Nat.is_eq(v(xl), v(yl)), Nat.is_eq(C.low(31n, v(xh)), C.low(31n, v(yh)))), Nat.is_eq(Nat.add(v(xl), C.shift(32n, C.low(31n, v(xh)))), Nat.add(v(yl), C.shift(32n, C.low(31n, v(yh))))), Cmp.is_eq(SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), e1, Equal.trans(Bool, Nat.is_eq(Nat.add(v(xl), C.shift(32n, C.low(31n, v(xh)))), Nat.add(v(yl), C.shift(32n, C.low(31n, v(yh))))), Nat.is_eq(Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.efield(F.Bits{xl, xh}))), Nat.add(SF.frac(F.Bits{yl, yh}), C.shift(52n, SF.efield(F.Bits{yl, yh})))), Cmp.is_eq(SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), e2, e3))

# the high words are equal when sign and the low 31 bits are
def hw(+xl: U32, +xh: U32, +yl: U32, +yh: U32) -> {U32.is_eq(xh, yh) == Bool.and(Nat.is_eq(C.low(31n, v(xh)), C.low(31n, v(yh))), Nat.is_eq(SF.b2n(SF.sign(F.Bits{xl, xh})), SF.b2n(SF.sign(F.Bits{yl, yh})))) : Bool}:
  +e1 = LW.eq_nat(xh, yh)
  +e2 = Equal.trans(Bool, Nat.is_eq(v(xh), v(yh)), Nat.is_eq(Nat.add(C.low(31n, v(xh)), C.shift(31n, C.high(31n, v(xh)))), v(yh)), Nat.is_eq(Nat.add(C.low(31n, v(xh)), C.shift(31n, C.high(31n, v(xh)))), Nat.add(C.low(31n, v(yh)), C.shift(31n, C.high(31n, v(yh))))), Equal.cong(Nat, Bool, t => Nat.is_eq(t, v(yh)), v(xh), Nat.add(C.low(31n, v(xh)), C.shift(31n, C.high(31n, v(xh)))), WW.low_high(31n, v(xh))), Equal.cong(Nat, Bool, t => Nat.is_eq(Nat.add(C.low(31n, v(xh)), C.shift(31n, C.high(31n, v(xh)))), t), v(yh), Nat.add(C.low(31n, v(yh)), C.shift(31n, C.high(31n, v(yh)))), WW.low_high(31n, v(yh))))
  +e3 = Equal.sym(Bool, Bool.and(Nat.is_eq(C.low(31n, v(xh)), C.low(31n, v(yh))), Nat.is_eq(C.high(31n, v(xh)), C.high(31n, v(yh)))), Nat.is_eq(Nat.add(C.low(31n, v(xh)), C.shift(31n, C.high(31n, v(xh)))), Nat.add(C.low(31n, v(yh)), C.shift(31n, C.high(31n, v(yh))))), WW.eq_limbs(31n, C.low(31n, v(xh)), C.high(31n, v(xh)), C.low(31n, v(yh)), C.high(31n, v(yh)), WW.low_fits(31n, v(xh)), WW.low_fits(31n, v(yh))))
  +e4 = Equal.trans(Bool, Bool.and(Nat.is_eq(C.low(31n, v(xh)), C.low(31n, v(yh))), Nat.is_eq(C.high(31n, v(xh)), C.high(31n, v(yh)))), Bool.and(Nat.is_eq(C.low(31n, v(xh)), C.low(31n, v(yh))), Nat.is_eq(SF.b2n(SF.sign(F.Bits{xl, xh})), C.high(31n, v(yh)))), Bool.and(Nat.is_eq(C.low(31n, v(xh)), C.low(31n, v(yh))), Nat.is_eq(SF.b2n(SF.sign(F.Bits{xl, xh})), SF.b2n(SF.sign(F.Bits{yl, yh})))), Equal.cong(Nat, Bool, t => Bool.and(Nat.is_eq(C.low(31n, v(xh)), C.low(31n, v(yh))), Nat.is_eq(t, C.high(31n, v(yh)))), C.high(31n, v(xh)), SF.b2n(SF.sign(F.Bits{xl, xh})), FB.bit_c(C.high(31n, v(xh)), FB.half0(xh))), Equal.cong(Nat, Bool, t => Bool.and(Nat.is_eq(C.low(31n, v(xh)), C.low(31n, v(yh))), Nat.is_eq(SF.b2n(SF.sign(F.Bits{xl, xh})), t)), C.high(31n, v(yh)), SF.b2n(SF.sign(F.Bits{yl, yh})), FB.bit_c(C.high(31n, v(yh)), FB.half0(yh))))
  Equal.trans(Bool, U32.is_eq(xh, yh), Nat.is_eq(v(xh), v(yh)), Bool.and(Nat.is_eq(C.low(31n, v(xh)), C.low(31n, v(yh))), Nat.is_eq(SF.b2n(SF.sign(F.Bits{xl, xh})), SF.b2n(SF.sign(F.Bits{yl, yh})))), e1, Equal.trans(Bool, Nat.is_eq(v(xh), v(yh)), Nat.is_eq(Nat.add(C.low(31n, v(xh)), C.shift(31n, C.high(31n, v(xh)))), Nat.add(C.low(31n, v(yh)), C.shift(31n, C.high(31n, v(yh))))), Bool.and(Nat.is_eq(C.low(31n, v(xh)), C.low(31n, v(yh))), Nat.is_eq(SF.b2n(SF.sign(F.Bits{xl, xh})), SF.b2n(SF.sign(F.Bits{yl, yh})))), e2, Equal.trans(Bool, Nat.is_eq(Nat.add(C.low(31n, v(xh)), C.shift(31n, C.high(31n, v(xh)))), Nat.add(C.low(31n, v(yh)), C.shift(31n, C.high(31n, v(yh))))), Bool.and(Nat.is_eq(C.low(31n, v(xh)), C.low(31n, v(yh))), Nat.is_eq(C.high(31n, v(xh)), C.high(31n, v(yh)))), Bool.and(Nat.is_eq(C.low(31n, v(xh)), C.low(31n, v(yh))), Nat.is_eq(SF.b2n(SF.sign(F.Bits{xl, xh})), SF.b2n(SF.sign(F.Bits{yl, yh})))), e3, e4)))

def eq_gen(+one: Nat, +h1: {one == 1n : Nat}, +xl: U32, +xh: U32, +yl: U32, +yh: U32, +bad: Bool, +hbad: {Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})) == bad : Bool}, +z: Bool) -> {F.eq_z(F.Bits{xl, xh}, F.Bits{yl, yh}, bad, z) == Bool.and(Bool.not(bad), Cmp.is_eq(SF.pick(Cmp, z, EQ{}, SF.pick(Cmp, Bool.not(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}))), SF.pick(Cmp, SF.sign(F.Bits{xl, xh}), SF.flip(SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), SF.pick(Cmp, SF.sign(F.Bits{xl, xh}), LT{}, GT{}))))) : Bool}:
  match bad z:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      +nx = or_l(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh}), hbad)
      +ny = or_r(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh}), hbad)
      +e1 = Equal.trans(Bool, Bool.and(U32.is_eq(xl, yl), U32.is_eq(xh, yh)), Bool.and(Nat.is_eq(v(xl), v(yl)), U32.is_eq(xh, yh)), Bool.and(Nat.is_eq(v(xl), v(yl)), Bool.and(Nat.is_eq(C.low(31n, v(xh)), C.low(31n, v(yh))), Nat.is_eq(SF.b2n(SF.sign(F.Bits{xl, xh})), SF.b2n(SF.sign(F.Bits{yl, yh}))))), Equal.cong(Bool, Bool, t => Bool.and(t, U32.is_eq(xh, yh)), U32.is_eq(xl, yl), Nat.is_eq(v(xl), v(yl)), LW.eq_nat(xl, yl)), Equal.cong(Bool, Bool, t => Bool.and(Nat.is_eq(v(xl), v(yl)), t), U32.is_eq(xh, yh), Bool.and(Nat.is_eq(C.low(31n, v(xh)), C.low(31n, v(yh))), Nat.is_eq(SF.b2n(SF.sign(F.Bits{xl, xh})), SF.b2n(SF.sign(F.Bits{yl, yh})))), hw(xl, xh, yl, yh)))
      Equal.trans(Bool, Bool.and(U32.is_eq(xl, yl), U32.is_eq(xh, yh)), Bool.and(Nat.is_eq(v(xl), v(yl)), Bool.and(Nat.is_eq(C.low(31n, v(xh)), C.low(31n, v(yh))), Nat.is_eq(SF.b2n(SF.sign(F.Bits{xl, xh})), SF.b2n(SF.sign(F.Bits{yl, yh}))))), Cmp.is_eq(SF.pick(Cmp, Bool.not(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}))), SF.pick(Cmp, SF.sign(F.Bits{xl, xh}), SF.flip(SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), SF.pick(Cmp, SF.sign(F.Bits{xl, xh}), LT{}, GT{}))), e1, eqs(Nat.is_eq(v(xl), v(yl)), Nat.is_eq(C.low(31n, v(xh)), C.low(31n, v(yh))), SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}), SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh}), hq(one, h1, xl, xh, yl, yh, nx, ny)))

def lt_value(+x: F.F64, +y: F.F64) -> SF.Lt.value(x, y):
  match x y:
    case F.Bits{+xl, +xh} F.Bits{+yl, +yh}:
      +ebad = Equal.trans(Bool, Bool.or(F.is_nan(F.Bits{xl, xh}), F.is_nan(F.Bits{yl, yh})), Bool.or(SF.is_nan(F.Bits{xl, xh}), F.is_nan(F.Bits{yl, yh})), Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})), Equal.cong(Bool, Bool, t => Bool.or(t, F.is_nan(F.Bits{yl, yh})), F.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{xl, xh}), FB.is_nan_value(F.Bits{xl, xh})), Equal.cong(Bool, Bool, t => Bool.or(SF.is_nan(F.Bits{xl, xh}), t), F.is_nan(F.Bits{yl, yh}), SF.is_nan(F.Bits{yl, yh}), FB.is_nan_value(F.Bits{yl, yh})))
      +ez = Equal.trans(Bool, Bool.and(F.is_zero(F.Bits{xl, xh}), F.is_zero(F.Bits{yl, yh})), Bool.and(SF.is_zero(F.Bits{xl, xh}), F.is_zero(F.Bits{yl, yh})), Bool.and(SF.is_zero(F.Bits{xl, xh}), SF.is_zero(F.Bits{yl, yh})), Equal.cong(Bool, Bool, t => Bool.and(t, F.is_zero(F.Bits{yl, yh})), F.is_zero(F.Bits{xl, xh}), SF.is_zero(F.Bits{xl, xh}), FB.is_zero_value(F.Bits{xl, xh})), Equal.cong(Bool, Bool, t => Bool.and(SF.is_zero(F.Bits{xl, xh}), t), F.is_zero(F.Bits{yl, yh}), SF.is_zero(F.Bits{yl, yh}), FB.is_zero_value(F.Bits{yl, yh})))
      +e1 = Equal.trans(Bool, F.lt_z(F.Bits{xl, xh}, F.Bits{yl, yh}, Bool.or(F.is_nan(F.Bits{xl, xh}), F.is_nan(F.Bits{yl, yh})), Bool.and(F.is_zero(F.Bits{xl, xh}), F.is_zero(F.Bits{yl, yh}))), F.lt_z(F.Bits{xl, xh}, F.Bits{yl, yh}, Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})), Bool.and(F.is_zero(F.Bits{xl, xh}), F.is_zero(F.Bits{yl, yh}))), F.lt_z(F.Bits{xl, xh}, F.Bits{yl, yh}, Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})), Bool.and(SF.is_zero(F.Bits{xl, xh}), SF.is_zero(F.Bits{yl, yh}))), Equal.cong(Bool, Bool, t => F.lt_z(F.Bits{xl, xh}, F.Bits{yl, yh}, t, Bool.and(F.is_zero(F.Bits{xl, xh}), F.is_zero(F.Bits{yl, yh}))), Bool.or(F.is_nan(F.Bits{xl, xh}), F.is_nan(F.Bits{yl, yh})), Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})), ebad), Equal.cong(Bool, Bool, t => F.lt_z(F.Bits{xl, xh}, F.Bits{yl, yh}, Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})), t), Bool.and(F.is_zero(F.Bits{xl, xh}), F.is_zero(F.Bits{yl, yh})), Bool.and(SF.is_zero(F.Bits{xl, xh}), SF.is_zero(F.Bits{yl, yh})), ez))
      Equal.trans(Bool, F.lt_z(F.Bits{xl, xh}, F.Bits{yl, yh}, Bool.or(F.is_nan(F.Bits{xl, xh}), F.is_nan(F.Bits{yl, yh})), Bool.and(F.is_zero(F.Bits{xl, xh}), F.is_zero(F.Bits{yl, yh}))), F.lt_z(F.Bits{xl, xh}, F.Bits{yl, yh}, Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})), Bool.and(SF.is_zero(F.Bits{xl, xh}), SF.is_zero(F.Bits{yl, yh}))), Bool.and(Bool.not(Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh}))), Cmp.is_lt(SF.pick(Cmp, Bool.and(SF.is_zero(F.Bits{xl, xh}), SF.is_zero(F.Bits{yl, yh})), EQ{}, SF.pick(Cmp, Bool.not(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}))), SF.pick(Cmp, SF.sign(F.Bits{xl, xh}), SF.flip(SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), SF.pick(Cmp, SF.sign(F.Bits{xl, xh}), LT{}, GT{}))))), e1, lt_gen(1n, {==}, xl, xh, yl, yh, Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})), {==}, Bool.and(SF.is_zero(F.Bits{xl, xh}), SF.is_zero(F.Bits{yl, yh}))))

def le_value(+x: F.F64, +y: F.F64) -> SF.Le.value(x, y):
  match x y:
    case F.Bits{+xl, +xh} F.Bits{+yl, +yh}:
      +ebad = Equal.trans(Bool, Bool.or(F.is_nan(F.Bits{xl, xh}), F.is_nan(F.Bits{yl, yh})), Bool.or(SF.is_nan(F.Bits{xl, xh}), F.is_nan(F.Bits{yl, yh})), Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})), Equal.cong(Bool, Bool, t => Bool.or(t, F.is_nan(F.Bits{yl, yh})), F.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{xl, xh}), FB.is_nan_value(F.Bits{xl, xh})), Equal.cong(Bool, Bool, t => Bool.or(SF.is_nan(F.Bits{xl, xh}), t), F.is_nan(F.Bits{yl, yh}), SF.is_nan(F.Bits{yl, yh}), FB.is_nan_value(F.Bits{yl, yh})))
      +ez = Equal.trans(Bool, Bool.and(F.is_zero(F.Bits{xl, xh}), F.is_zero(F.Bits{yl, yh})), Bool.and(SF.is_zero(F.Bits{xl, xh}), F.is_zero(F.Bits{yl, yh})), Bool.and(SF.is_zero(F.Bits{xl, xh}), SF.is_zero(F.Bits{yl, yh})), Equal.cong(Bool, Bool, t => Bool.and(t, F.is_zero(F.Bits{yl, yh})), F.is_zero(F.Bits{xl, xh}), SF.is_zero(F.Bits{xl, xh}), FB.is_zero_value(F.Bits{xl, xh})), Equal.cong(Bool, Bool, t => Bool.and(SF.is_zero(F.Bits{xl, xh}), t), F.is_zero(F.Bits{yl, yh}), SF.is_zero(F.Bits{yl, yh}), FB.is_zero_value(F.Bits{yl, yh})))
      +e1 = Equal.trans(Bool, F.le_z(F.Bits{xl, xh}, F.Bits{yl, yh}, Bool.or(F.is_nan(F.Bits{xl, xh}), F.is_nan(F.Bits{yl, yh})), Bool.and(F.is_zero(F.Bits{xl, xh}), F.is_zero(F.Bits{yl, yh}))), F.le_z(F.Bits{xl, xh}, F.Bits{yl, yh}, Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})), Bool.and(F.is_zero(F.Bits{xl, xh}), F.is_zero(F.Bits{yl, yh}))), F.le_z(F.Bits{xl, xh}, F.Bits{yl, yh}, Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})), Bool.and(SF.is_zero(F.Bits{xl, xh}), SF.is_zero(F.Bits{yl, yh}))), Equal.cong(Bool, Bool, t => F.le_z(F.Bits{xl, xh}, F.Bits{yl, yh}, t, Bool.and(F.is_zero(F.Bits{xl, xh}), F.is_zero(F.Bits{yl, yh}))), Bool.or(F.is_nan(F.Bits{xl, xh}), F.is_nan(F.Bits{yl, yh})), Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})), ebad), Equal.cong(Bool, Bool, t => F.le_z(F.Bits{xl, xh}, F.Bits{yl, yh}, Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})), t), Bool.and(F.is_zero(F.Bits{xl, xh}), F.is_zero(F.Bits{yl, yh})), Bool.and(SF.is_zero(F.Bits{xl, xh}), SF.is_zero(F.Bits{yl, yh})), ez))
      Equal.trans(Bool, F.le_z(F.Bits{xl, xh}, F.Bits{yl, yh}, Bool.or(F.is_nan(F.Bits{xl, xh}), F.is_nan(F.Bits{yl, yh})), Bool.and(F.is_zero(F.Bits{xl, xh}), F.is_zero(F.Bits{yl, yh}))), F.le_z(F.Bits{xl, xh}, F.Bits{yl, yh}, Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})), Bool.and(SF.is_zero(F.Bits{xl, xh}), SF.is_zero(F.Bits{yl, yh}))), Bool.and(Bool.not(Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh}))), Cmp.is_le(SF.pick(Cmp, Bool.and(SF.is_zero(F.Bits{xl, xh}), SF.is_zero(F.Bits{yl, yh})), EQ{}, SF.pick(Cmp, Bool.not(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}))), SF.pick(Cmp, SF.sign(F.Bits{xl, xh}), SF.flip(SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), SF.pick(Cmp, SF.sign(F.Bits{xl, xh}), LT{}, GT{}))))), e1, le_gen(1n, {==}, xl, xh, yl, yh, Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})), {==}, Bool.and(SF.is_zero(F.Bits{xl, xh}), SF.is_zero(F.Bits{yl, yh}))))

def eq_value(+x: F.F64, +y: F.F64) -> SF.Eq.value(x, y):
  match x y:
    case F.Bits{+xl, +xh} F.Bits{+yl, +yh}:
      +ebad = Equal.trans(Bool, Bool.or(F.is_nan(F.Bits{xl, xh}), F.is_nan(F.Bits{yl, yh})), Bool.or(SF.is_nan(F.Bits{xl, xh}), F.is_nan(F.Bits{yl, yh})), Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})), Equal.cong(Bool, Bool, t => Bool.or(t, F.is_nan(F.Bits{yl, yh})), F.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{xl, xh}), FB.is_nan_value(F.Bits{xl, xh})), Equal.cong(Bool, Bool, t => Bool.or(SF.is_nan(F.Bits{xl, xh}), t), F.is_nan(F.Bits{yl, yh}), SF.is_nan(F.Bits{yl, yh}), FB.is_nan_value(F.Bits{yl, yh})))
      +ez = Equal.trans(Bool, Bool.and(F.is_zero(F.Bits{xl, xh}), F.is_zero(F.Bits{yl, yh})), Bool.and(SF.is_zero(F.Bits{xl, xh}), F.is_zero(F.Bits{yl, yh})), Bool.and(SF.is_zero(F.Bits{xl, xh}), SF.is_zero(F.Bits{yl, yh})), Equal.cong(Bool, Bool, t => Bool.and(t, F.is_zero(F.Bits{yl, yh})), F.is_zero(F.Bits{xl, xh}), SF.is_zero(F.Bits{xl, xh}), FB.is_zero_value(F.Bits{xl, xh})), Equal.cong(Bool, Bool, t => Bool.and(SF.is_zero(F.Bits{xl, xh}), t), F.is_zero(F.Bits{yl, yh}), SF.is_zero(F.Bits{yl, yh}), FB.is_zero_value(F.Bits{yl, yh})))
      +e1 = Equal.trans(Bool, F.eq_z(F.Bits{xl, xh}, F.Bits{yl, yh}, Bool.or(F.is_nan(F.Bits{xl, xh}), F.is_nan(F.Bits{yl, yh})), Bool.and(F.is_zero(F.Bits{xl, xh}), F.is_zero(F.Bits{yl, yh}))), F.eq_z(F.Bits{xl, xh}, F.Bits{yl, yh}, Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})), Bool.and(F.is_zero(F.Bits{xl, xh}), F.is_zero(F.Bits{yl, yh}))), F.eq_z(F.Bits{xl, xh}, F.Bits{yl, yh}, Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})), Bool.and(SF.is_zero(F.Bits{xl, xh}), SF.is_zero(F.Bits{yl, yh}))), Equal.cong(Bool, Bool, t => F.eq_z(F.Bits{xl, xh}, F.Bits{yl, yh}, t, Bool.and(F.is_zero(F.Bits{xl, xh}), F.is_zero(F.Bits{yl, yh}))), Bool.or(F.is_nan(F.Bits{xl, xh}), F.is_nan(F.Bits{yl, yh})), Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})), ebad), Equal.cong(Bool, Bool, t => F.eq_z(F.Bits{xl, xh}, F.Bits{yl, yh}, Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})), t), Bool.and(F.is_zero(F.Bits{xl, xh}), F.is_zero(F.Bits{yl, yh})), Bool.and(SF.is_zero(F.Bits{xl, xh}), SF.is_zero(F.Bits{yl, yh})), ez))
      Equal.trans(Bool, F.eq_z(F.Bits{xl, xh}, F.Bits{yl, yh}, Bool.or(F.is_nan(F.Bits{xl, xh}), F.is_nan(F.Bits{yl, yh})), Bool.and(F.is_zero(F.Bits{xl, xh}), F.is_zero(F.Bits{yl, yh}))), F.eq_z(F.Bits{xl, xh}, F.Bits{yl, yh}, Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})), Bool.and(SF.is_zero(F.Bits{xl, xh}), SF.is_zero(F.Bits{yl, yh}))), Bool.and(Bool.not(Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh}))), Cmp.is_eq(SF.pick(Cmp, Bool.and(SF.is_zero(F.Bits{xl, xh}), SF.is_zero(F.Bits{yl, yh})), EQ{}, SF.pick(Cmp, Bool.not(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}))), SF.pick(Cmp, SF.sign(F.Bits{xl, xh}), SF.flip(SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), SF.mag_cmp(F.Bits{xl, xh}, F.Bits{yl, yh})), SF.pick(Cmp, SF.sign(F.Bits{xl, xh}), LT{}, GT{}))))), e1, eq_gen(1n, {==}, xl, xh, yl, yh, Bool.or(SF.is_nan(F.Bits{xl, xh}), SF.is_nan(F.Bits{yl, yh})), {==}, Bool.and(SF.is_zero(F.Bits{xl, xh}), SF.is_zero(F.Bits{yl, yh}))))
