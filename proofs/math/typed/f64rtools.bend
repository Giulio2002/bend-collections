import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../natural/bits.bend as BT
import ./width.bend as WW
import ./natcmp.bend as NC
import ./f64round.bend as FR
import ./f64bl.bend as FO

# Two facts about the spec's round (Flocq's round_NE is invariant under
# exact scaling, and the sticky bit summarizes everything below two guard
# bits: Boldo and Melquiond's inbetween lemmas, the correctness argument of
# SoftFloat's shiftRightJam):
#   round(s, m * 2^k, x) = round(s, m, x + k)
#   round(s, m, x) = round(s, jam(m >> d, m mod 2^d), x + d)   when m has
#     at least d + 55 bits

# ---- rounding an exact multiple ----

def lt0f(+h: Nat) -> {Nat.is_lt(h, 0n) == False{} : Bool}:
  N.not_lt_zero(h)

def rne_exact(+k: Nat, +m: Nat) -> {SF.rne(C.shift(k, m), k) == m : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +i:
      +S = C.shift(1n+i, m)
      +h = C.shift(i, 1n)
      +eq = WW.high_u(1n+i, 0n, m, FR.fz(1n+i))
      +el = WW.low_u(1n+i, 0n, m, FR.fz(1n+i))
      +e1 = Equal.cong(Nat, Nat, z => SF.rne_up(z, C.low(1n+i, S), h), C.high(1n+i, S), m, eq)
      +e2 = Equal.cong(Nat, Nat, z => SF.rne_up(m, z, h), C.low(1n+i, S), 0n, el)
      +hz = N.is_eq_sym_false(h, 0n, Equal.trans(Bool, Nat.is_eq(h, 0n), Nat.is_eq(1n, 0n), False{}, WW.shift_eq0(i, 1n), {==}))
      +e3 = Equal.cong(Bool, Nat, t => Nat.add(m, SF.b2n(Bool.or(t, Bool.and(Nat.is_eq(0n, h), Nat.is_eq(Nat.mod(m, 2n), 1n))))), Nat.is_lt(h, 0n), False{}, lt0f(h))
      +e4 = Equal.cong(Bool, Nat, t => Nat.add(m, SF.b2n(Bool.or(False{}, Bool.and(t, Nat.is_eq(Nat.mod(m, 2n), 1n))))), Nat.is_eq(0n, h), False{}, hz)
      +e5 = N.add_zero(m)
      Equal.trans(Nat, SF.rne_up(C.high(1n+i, S), C.low(1n+i, S), h), SF.rne_up(m, C.low(1n+i, S), h), m, e1, Equal.trans(Nat, SF.rne_up(m, C.low(1n+i, S), h), SF.rne_up(m, 0n, h), m, e2, Equal.trans(Nat, SF.rne_up(m, 0n, h), Nat.add(m, SF.b2n(Bool.or(False{}, Bool.and(Nat.is_eq(0n, h), Nat.is_eq(Nat.mod(m, 2n), 1n))))), m, e3, Equal.trans(Nat, Nat.add(m, SF.b2n(Bool.or(False{}, Bool.and(Nat.is_eq(0n, h), Nat.is_eq(Nat.mod(m, 2n), 1n))))), Nat.add(m, 0n), m, e4, e5))))

# rounding m * 2^k by j + k bits is rounding m by j bits
def rne_shift(+k: Nat, +m: Nat, +j: Nat) -> {SF.rne(C.shift(k, m), Nat.add(j, k)) == SF.rne(m, j) : Nat}:
  match j:
    case 0n:
      rne_exact(k, m)
    case 1n+ +i:
      +a = Nat.add(1n+i, k)
      +ea = NA.add_comm(1n+i, k)
      +hq = Equal.trans(Nat, C.high(a, C.shift(k, m)), C.high(Nat.add(k, 1n+i), C.shift(k, m)), C.high(1n+i, m), Equal.cong(Nat, Nat, z => C.high(z, C.shift(k, m)), a, Nat.add(k, 1n+i), ea), Equal.trans(Nat, C.high(Nat.add(k, 1n+i), C.shift(k, m)), C.high(1n+i, C.high(k, C.shift(k, m))), C.high(1n+i, m), WW.high_comp(1n+i, k, C.shift(k, m)), Equal.cong(Nat, Nat, z => C.high(1n+i, z), C.high(k, C.shift(k, m)), m, WW.high_u(k, 0n, m, FR.fz(k)))))
      +hl = Equal.trans(Nat, C.low(a, C.shift(k, m)), C.low(Nat.add(k, 1n+i), C.shift(k, m)), C.shift(k, C.low(1n+i, m)), Equal.cong(Nat, Nat, z => C.low(z, C.shift(k, m)), a, Nat.add(k, 1n+i), ea), WW.low_shift(k, 1n+i, m))
      +hh = Equal.trans(Nat, C.shift(Nat.add(i, k), 1n), C.shift(Nat.add(k, i), 1n), C.shift(k, C.shift(i, 1n)), Equal.cong(Nat, Nat, z => C.shift(z, 1n), Nat.add(i, k), Nat.add(k, i), NA.add_comm(i, k)), WW.shift_comp(k, i, 1n))
      +hc = Equal.trans(Cmp, Nat.cmp(C.low(a, C.shift(k, m)), C.shift(Nat.add(i, k), 1n)), Nat.cmp(C.shift(k, C.low(1n+i, m)), C.shift(Nat.add(i, k), 1n)), Nat.cmp(C.low(1n+i, m), C.shift(i, 1n)), Equal.cong(Nat, Cmp, z => Nat.cmp(z, C.shift(Nat.add(i, k), 1n)), C.low(a, C.shift(k, m)), C.shift(k, C.low(1n+i, m)), hl), Equal.trans(Cmp, Nat.cmp(C.shift(k, C.low(1n+i, m)), C.shift(Nat.add(i, k), 1n)), Nat.cmp(C.shift(k, C.low(1n+i, m)), C.shift(k, C.shift(i, 1n))), Nat.cmp(C.low(1n+i, m), C.shift(i, 1n)), Equal.cong(Nat, Cmp, z => Nat.cmp(C.shift(k, C.low(1n+i, m)), z), C.shift(Nat.add(i, k), 1n), C.shift(k, C.shift(i, 1n)), hh), NC.cmp_shift(k, C.low(1n+i, m), C.shift(i, 1n))))
      +l1 = FR.rne_cmp(C.high(a, C.shift(k, m)), C.low(a, C.shift(k, m)), C.shift(Nat.add(i, k), 1n))
      +l2 = Equal.cong(Nat, Nat, z => FR.rne_c(z, Nat.cmp(C.low(a, C.shift(k, m)), C.shift(Nat.add(i, k), 1n))), C.high(a, C.shift(k, m)), C.high(1n+i, m), hq)
      +l3 = Equal.cong(Cmp, Nat, t => FR.rne_c(C.high(1n+i, m), t), Nat.cmp(C.low(a, C.shift(k, m)), C.shift(Nat.add(i, k), 1n)), Nat.cmp(C.low(1n+i, m), C.shift(i, 1n)), hc)
      +r1 = FR.rne_cmp(C.high(1n+i, m), C.low(1n+i, m), C.shift(i, 1n))
      Equal.trans(Nat, SF.rne_up(C.high(a, C.shift(k, m)), C.low(a, C.shift(k, m)), C.shift(Nat.add(i, k), 1n)), FR.rne_c(C.high(1n+i, m), Nat.cmp(C.low(1n+i, m), C.shift(i, 1n))), SF.rne_up(C.high(1n+i, m), C.low(1n+i, m), C.shift(i, 1n)), Equal.trans(Nat, SF.rne_up(C.high(a, C.shift(k, m)), C.low(a, C.shift(k, m)), C.shift(Nat.add(i, k), 1n)), FR.rne_c(C.high(a, C.shift(k, m)), Nat.cmp(C.low(a, C.shift(k, m)), C.shift(Nat.add(i, k), 1n))), FR.rne_c(C.high(1n+i, m), Nat.cmp(C.low(1n+i, m), C.shift(i, 1n))), l1, Equal.trans(Nat, FR.rne_c(C.high(a, C.shift(k, m)), Nat.cmp(C.low(a, C.shift(k, m)), C.shift(Nat.add(i, k), 1n))), FR.rne_c(C.high(1n+i, m), Nat.cmp(C.low(a, C.shift(k, m)), C.shift(Nat.add(i, k), 1n))), FR.rne_c(C.high(1n+i, m), Nat.cmp(C.low(1n+i, m), C.shift(i, 1n))), l2, l3)), Equal.sym(Nat, SF.rne_up(C.high(1n+i, m), C.low(1n+i, m), C.shift(i, 1n)), FR.rne_c(C.high(1n+i, m), Nat.cmp(C.low(1n+i, m), C.shift(i, 1n))), r1))

# ---- bit lengths under shifts ----

def bl_fit(+n: Nat) -> {C.fits(M.bit_length(n), n) == True{} : Bool}:
  WW.fits_of_lt(M.bit_length(n), n, BT.bit_length_lt(n))

def bl_nfit(+n: Nat, +hz: {Nat.is_eq(n, 0n) == False{} : Bool}) -> {C.fits(Nat.sub(M.bit_length(n), 1n), n) == False{} : Bool}:
  +K = Nat.sub(M.bit_length(n), 1n)
  +nf = Equal.trans(Bool, C.fits(K, C.pow2(K)), Nat.is_lt(C.pow2(K), C.pow2(K)), False{}, WW.fits_lt(K, C.pow2(K)), N.lt_irrefl(C.pow2(K)))
  FR.nfit(K, C.pow2(K), n, FO.lower(n, hz), nf)

def fits_sh(+k: Nat, +a: Nat, +m: Nat) -> {C.fits(Nat.add(k, a), C.shift(k, m)) == C.fits(a, m) : Bool}:
  Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), C.high(Nat.add(k, a), C.shift(k, m)), C.high(a, m), Equal.trans(Nat, C.high(Nat.add(k, a), C.shift(k, m)), C.high(a, C.high(k, C.shift(k, m))), C.high(a, m), WW.high_comp(a, k, C.shift(k, m)), Equal.cong(Nat, Nat, z => C.high(a, z), C.high(k, C.shift(k, m)), m, WW.high_u(k, 0n, m, FR.fz(k)))))

def bl_shift(+k: Nat, +m: Nat, +hz: {Nat.is_eq(m, 0n) == False{} : Bool}) -> {M.bit_length(C.shift(k, m)) == Nat.add(M.bit_length(m), k) : Nat}:
  +B = M.bit_length(m)
  +j = Nat.sub(B, 1n)
  +ej = N.sub_add(B, 1n, FO.bl_pos(m, hz, B, {==}))
  +nf = Equal.trans(Bool, C.fits(Nat.add(k, j), C.shift(k, m)), C.fits(j, m), False{}, fits_sh(k, j, m), bl_nfit(m, hz))
  +f0 = L.subst(Nat, z => {C.fits(z, m) == True{} : Bool}, B, 1n+j, Equal.sym(Nat, 1n+j, B, ej), bl_fit(m))
  +f1 = Equal.trans(Bool, C.fits(Nat.add(k, 1n+j), C.shift(k, m)), C.fits(1n+j, m), True{}, fits_sh(k, 1n+j, m), f0)
  +f2 = L.subst(Nat, z => {C.fits(z, C.shift(k, m)) == True{} : Bool}, Nat.add(k, 1n+j), 1n+Nat.add(k, j), N.add_succ(k, j), f1)
  +eb = FR.bl_c(Nat.add(k, j), C.shift(k, m), nf, f2, Nat.cmp(M.bit_length(C.shift(k, m)), 1n+Nat.add(k, j)), {==})
  +er = Equal.trans(Nat, Nat.add(B, k), Nat.add(1n+j, k), 1n+Nat.add(k, j), Equal.cong(Nat, Nat, z => Nat.add(z, k), B, 1n+j, Equal.sym(Nat, 1n+j, B, ej)), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(j, k), Nat.add(k, j), NA.add_comm(j, k)))
  Equal.trans(Nat, M.bit_length(C.shift(k, m)), 1n+Nat.add(k, j), Nat.add(B, k), eb, Equal.sym(Nat, Nat.add(B, k), 1n+Nat.add(k, j), er))

# ---- scaling ----

def a1(+x: Nat, +k: Nat, +u: Nat, +h: {Nat.is_le(Nat.add(x, k), u) == True{} : Bool}) -> {Nat.sub(u, x) == Nat.add(Nat.sub(u, Nat.add(x, k)), k) : Nat}:
  +r = Nat.sub(u, Nat.add(x, k))
  +eu = N.sub_add(u, Nat.add(x, k), h)
  Equal.trans(Nat, Nat.sub(u, x), Nat.sub(Nat.add(Nat.add(x, k), r), x), Nat.add(r, k), Equal.cong(Nat, Nat, z => Nat.sub(z, x), u, Nat.add(Nat.add(x, k), r), Equal.sym(Nat, Nat.add(Nat.add(x, k), r), u, eu)), Equal.trans(Nat, Nat.sub(Nat.add(Nat.add(x, k), r), x), Nat.sub(Nat.add(x, Nat.add(k, r)), x), Nat.add(r, k), Equal.cong(Nat, Nat, z => Nat.sub(z, x), Nat.add(Nat.add(x, k), r), Nat.add(x, Nat.add(k, r)), NA.add_assoc(x, k, r)), Equal.trans(Nat, Nat.sub(Nat.add(x, Nat.add(k, r)), x), Nat.add(k, r), Nat.add(r, k), N.add_sub_cancel(x, Nat.add(k, r)), NA.add_comm(k, r))))

def qeq_f(+k: Nat, +m: Nat, +x: Nat, +u: Nat, +c1: Bool, +hc1: {Nat.is_le(x, u) == c1 : Bool}, +hc2: {Nat.is_le(Nat.add(x, k), u) == False{} : Bool}) -> {SF.pick(Nat, c1, SF.rne(C.shift(k, m), Nat.sub(u, x)), C.shift(Nat.sub(x, u), C.shift(k, m))) == C.shift(Nat.sub(Nat.add(x, k), u), m) : Nat}:
  match c1:
    case True{}:
      +t = Nat.sub(u, x)
      +eu = N.sub_add(u, x, hc1)
      +hlt0 = N.not_le_lt(Nat.add(x, k), u, hc2)
      +hlt1 = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(x, k)) == True{} : Bool}, u, Nat.add(x, t), Equal.sym(Nat, Nat.add(x, t), u, eu), hlt0)
      +hlt2 = Equal.trans(Bool, Nat.is_lt(t, k), Nat.is_lt(Nat.add(x, t), Nat.add(x, k)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(x, t), Nat.add(x, k)), Nat.is_lt(t, k), WW.lt_cancel_l(x, t, k)), hlt1)
      +htk = N.lt_le(t, k, hlt2)
      +es = NC.sh_split(k, t, m, htk)
      +e1 = Equal.trans(Nat, SF.rne(C.shift(k, m), t), SF.rne(C.shift(t, C.shift(Nat.sub(k, t), m)), t), C.shift(Nat.sub(k, t), m), Equal.cong(Nat, Nat, z => SF.rne(z, t), C.shift(k, m), C.shift(t, C.shift(Nat.sub(k, t), m)), es), rne_exact(t, C.shift(Nat.sub(k, t), m)))
      +e2 = Equal.trans(Nat, Nat.sub(k, t), Nat.sub(Nat.add(k, x), Nat.add(t, x)), Nat.sub(Nat.add(x, k), u), Equal.sym(Nat, Nat.sub(Nat.add(k, x), Nat.add(t, x)), Nat.sub(k, t), FR.sub_cancel_r(k, t, x)), Equal.trans(Nat, Nat.sub(Nat.add(k, x), Nat.add(t, x)), Nat.sub(Nat.add(x, k), Nat.add(t, x)), Nat.sub(Nat.add(x, k), u), Equal.cong(Nat, Nat, z => Nat.sub(z, Nat.add(t, x)), Nat.add(k, x), Nat.add(x, k), NA.add_comm(k, x)), Equal.cong(Nat, Nat, z => Nat.sub(Nat.add(x, k), z), Nat.add(t, x), u, Equal.trans(Nat, Nat.add(t, x), Nat.add(x, t), u, NA.add_comm(t, x), eu))))
      Equal.trans(Nat, SF.rne(C.shift(k, m), t), C.shift(Nat.sub(k, t), m), C.shift(Nat.sub(Nat.add(x, k), u), m), e1, Equal.cong(Nat, Nat, z => C.shift(z, m), Nat.sub(k, t), Nat.sub(Nat.add(x, k), u), e2))
    case False{}:
      +hux = N.lt_le(u, x, N.not_le_lt(x, u, hc1))
      Equal.trans(Nat, C.shift(Nat.sub(x, u), C.shift(k, m)), C.shift(Nat.add(Nat.sub(x, u), k), m), C.shift(Nat.sub(Nat.add(x, k), u), m), Equal.sym(Nat, C.shift(Nat.add(Nat.sub(x, u), k), m), C.shift(Nat.sub(x, u), C.shift(k, m)), WW.shift_comp(Nat.sub(x, u), k, m)), Equal.cong(Nat, Nat, z => C.shift(z, m), Nat.add(Nat.sub(x, u), k), Nat.sub(Nat.add(x, k), u), Equal.sym(Nat, Nat.sub(Nat.add(x, k), u), Nat.add(Nat.sub(x, u), k), FR.sub_add_r(x, k, u, hux))))

def qeq_c(+k: Nat, +m: Nat, +x: Nat, +u: Nat, +c1: Bool, +hc1: {Nat.is_le(x, u) == c1 : Bool}, +c2: Bool, +hc2: {Nat.is_le(Nat.add(x, k), u) == c2 : Bool}) -> {SF.pick(Nat, c1, SF.rne(C.shift(k, m), Nat.sub(u, x)), C.shift(Nat.sub(x, u), C.shift(k, m))) == SF.pick(Nat, c2, SF.rne(m, Nat.sub(u, Nat.add(x, k))), C.shift(Nat.sub(Nat.add(x, k), u), m)) : Nat}:
  match c2:
    case True{}:
      +h1 = N.le_trans(x, Nat.add(x, k), u, N.le_add_right(x, k), hc2)
      +ec1 = Equal.trans(Bool, c1, Nat.is_le(x, u), True{}, Equal.sym(Bool, Nat.is_le(x, u), c1, hc1), h1)
      +r = Nat.sub(u, Nat.add(x, k))
      +base = Equal.trans(Nat, SF.rne(C.shift(k, m), Nat.sub(u, x)), SF.rne(C.shift(k, m), Nat.add(r, k)), SF.rne(m, r), Equal.cong(Nat, Nat, z => SF.rne(C.shift(k, m), z), Nat.sub(u, x), Nat.add(r, k), a1(x, k, u, hc2)), rne_shift(k, m, r))
      L.subst(Bool, t => {SF.pick(Nat, t, SF.rne(C.shift(k, m), Nat.sub(u, x)), C.shift(Nat.sub(x, u), C.shift(k, m))) == SF.rne(m, r) : Nat}, True{}, c1, Equal.sym(Bool, c1, True{}, ec1), base)
    case False{}:
      qeq_f(k, m, x, u, c1, hc1, hc2)


def rs_c(+s: Bool, +k: Nat, +m: Nat, +x: Nat, +z: Bool, +hz: {Nat.is_eq(m, 0n) == z : Bool}) -> {SF.round(s, C.shift(k, m), x) == SF.round(s, m, Nat.add(x, k)) : F.F64}:
  match z:
    case True{}:
      +e0 = Equal.trans(Bool, Nat.is_eq(C.shift(k, m), 0n), Nat.is_eq(m, 0n), True{}, WW.shift_eq0(k, m), hz)
      Equal.trans(F.F64, SF.round(s, C.shift(k, m), x), SF.zero(s), SF.round(s, m, Nat.add(x, k)), Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.zero(s), SF.round_u(s, C.shift(k, m), x, Nat.max(Nat.sub(Nat.add(x, M.bit_length(C.shift(k, m))), 53n), Nat.sub(SF.zb(), 1074n)))), Nat.is_eq(C.shift(k, m), 0n), True{}, e0), Equal.sym(F.F64, SF.round(s, m, Nat.add(x, k)), SF.zero(s), Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.zero(s), SF.round_u(s, m, Nat.add(x, k), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)))), Nat.is_eq(m, 0n), True{}, hz)))
    case False{}:
      +B = M.bit_length(m)
      +e0 = Equal.trans(Bool, Nat.is_eq(C.shift(k, m), 0n), Nat.is_eq(m, 0n), False{}, WW.shift_eq0(k, m), hz)
      +l1 = Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.zero(s), SF.round_u(s, C.shift(k, m), x, Nat.max(Nat.sub(Nat.add(x, M.bit_length(C.shift(k, m))), 53n), Nat.sub(SF.zb(), 1074n)))), Nat.is_eq(C.shift(k, m), 0n), False{}, e0)
      +ea = Equal.trans(Nat, Nat.add(x, Nat.add(B, k)), Nat.add(x, Nat.add(k, B)), Nat.add(Nat.add(x, k), B), Equal.cong(Nat, Nat, z => Nat.add(x, z), Nat.add(B, k), Nat.add(k, B), NA.add_comm(B, k)), Equal.sym(Nat, Nat.add(Nat.add(x, k), B), Nat.add(x, Nat.add(k, B)), NA.add_assoc(x, k, B)))
      +eu = Equal.trans(Nat, Nat.max(Nat.sub(Nat.add(x, M.bit_length(C.shift(k, m))), 53n), Nat.sub(SF.zb(), 1074n)), Nat.max(Nat.sub(Nat.add(x, Nat.add(B, k)), 53n), Nat.sub(SF.zb(), 1074n)), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), Equal.cong(Nat, Nat, w => Nat.max(Nat.sub(Nat.add(x, w), 53n), Nat.sub(SF.zb(), 1074n)), M.bit_length(C.shift(k, m)), Nat.add(B, k), bl_shift(k, m, hz)), Equal.cong(Nat, Nat, w => Nat.max(Nat.sub(w, 53n), Nat.sub(SF.zb(), 1074n)), Nat.add(x, Nat.add(B, k)), Nat.add(Nat.add(x, k), B), ea))
      +l2 = Equal.cong(Nat, F.F64, w => SF.round_u(s, C.shift(k, m), x, w), Nat.max(Nat.sub(Nat.add(x, M.bit_length(C.shift(k, m))), 53n), Nat.sub(SF.zb(), 1074n)), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), eu)
      +l3 = Equal.cong(Nat, F.F64, w => SF.pack(s, w, Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.pick(Nat, Nat.is_le(x, Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.rne(C.shift(k, m), Nat.sub(Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), x)), C.shift(Nat.sub(x, Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), C.shift(k, m))), SF.pick(Nat, Nat.is_le(Nat.add(x, k), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.rne(m, Nat.sub(Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), Nat.add(x, k))), C.shift(Nat.sub(Nat.add(x, k), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), m)), qeq_c(k, m, x, Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), Nat.is_le(x, Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), {==}, Nat.is_le(Nat.add(x, k), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), {==}))
      +r1 = Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.zero(s), SF.round_u(s, m, Nat.add(x, k), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)))), Nat.is_eq(m, 0n), False{}, hz)
      Equal.trans(F.F64, SF.round(s, C.shift(k, m), x), SF.round_u(s, m, Nat.add(x, k), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.round(s, m, Nat.add(x, k)), Equal.trans(F.F64, SF.round(s, C.shift(k, m), x), SF.round_u(s, C.shift(k, m), x, Nat.max(Nat.sub(Nat.add(x, M.bit_length(C.shift(k, m))), 53n), Nat.sub(SF.zb(), 1074n))), SF.round_u(s, m, Nat.add(x, k), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), l1, Equal.trans(F.F64, SF.round_u(s, C.shift(k, m), x, Nat.max(Nat.sub(Nat.add(x, M.bit_length(C.shift(k, m))), 53n), Nat.sub(SF.zb(), 1074n))), SF.round_u(s, C.shift(k, m), x, Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.round_u(s, m, Nat.add(x, k), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), l2, l3)), Equal.sym(F.F64, SF.round(s, m, Nat.add(x, k)), SF.round_u(s, m, Nat.add(x, k), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), r1))

# round(s, m * 2^k, x) = round(s, m, x + k)
def round_shift(+s: Bool, +k: Nat, +m: Nat, +x: Nat) -> {SF.round(s, C.shift(k, m), x) == SF.round(s, m, Nat.add(x, k)) : F.F64}:
  rs_c(s, k, m, x, Nat.is_eq(m, 0n), {==})

# ---- the sticky bit under the spec's round ----

def max_ge_l(+a: Nat, +b: Nat) -> {Nat.is_le(a, Nat.max(a, b)) == True{} : Bool}:
  match a b:
    case 0n _:
      N.zero_le(b)
    case 1n+ +ap 0n:
      N.le_refl(1n+ap)
    case 1n+ +ap 1n+ +bp:
      max_ge_l(ap, bp)

def le_sub(+a: Nat, +c: Nat, +b: Nat, +h: {Nat.is_le(Nat.add(a, c), b) == True{} : Bool}) -> {Nat.is_le(a, Nat.sub(b, c)) == True{} : Bool}:
  +eb = N.sub_add(b, Nat.add(a, c), h)
  +r = Nat.sub(b, Nat.add(a, c))
  +e1 = Equal.trans(Nat, Nat.sub(b, c), Nat.sub(Nat.add(Nat.add(a, c), r), c), Nat.add(a, r), Equal.cong(Nat, Nat, z => Nat.sub(z, c), b, Nat.add(Nat.add(a, c), r), Equal.sym(Nat, Nat.add(Nat.add(a, c), r), b, eb)), Equal.trans(Nat, Nat.sub(Nat.add(Nat.add(a, c), r), c), Nat.sub(Nat.add(c, Nat.add(a, r)), c), Nat.add(a, r), Equal.cong(Nat, Nat, z => Nat.sub(z, c), Nat.add(Nat.add(a, c), r), Nat.add(c, Nat.add(a, r)), Equal.trans(Nat, Nat.add(Nat.add(a, c), r), Nat.add(Nat.add(c, a), r), Nat.add(c, Nat.add(a, r)), Equal.cong(Nat, Nat, z => Nat.add(z, r), Nat.add(a, c), Nat.add(c, a), NA.add_comm(a, c)), NA.add_assoc(c, a, r))), N.add_sub_cancel(c, Nat.add(a, r))))
  L.subst(Nat, z => {Nat.is_le(a, z) == True{} : Bool}, Nat.add(a, r), Nat.sub(b, c), Equal.sym(Nat, Nat.sub(b, c), Nat.add(a, r), e1), N.le_add_right(a, r))

# a bit t <= 1 below 2 y leaves the width of y
def fit_td(+a: Nat, +t: Nat, +y: Nat, +ht: {Nat.is_le(t, 1n) == True{} : Bool}) -> {C.fits(1n+a, Nat.add(t, Nat.double(y))) == C.fits(a, y) : Bool}:
  Equal.cong(Nat, Bool, z => C.fits(a, z), C.half(Nat.add(t, Nat.double(y))), y, Equal.trans(Nat, C.half(Nat.add(t, Nat.double(y))), Nat.add(C.half(t), y), y, WW.half_dbl(t, y), Equal.cong(Nat, Nat, z => Nat.add(z, y), C.half(t), 0n, FR.half_small(t, ht))))

def jam_fits(+a: Nat, +h: Nat, +l: Nat) -> {C.fits(1n+a, SW.jam(h, l)) == C.fits(1n+a, h) : Bool}:
  +t = Nat.max(C.bit(h), Nat.min(l, 1n))
  +e1 = Equal.cong(Nat, Bool, z => C.fits(1n+a, z), SW.jam(h, l), Nat.add(t, Nat.double(C.half(h))), FR.jam_form(h, l))
  +e2 = fit_td(a, t, C.half(h), FR.max_le1(C.bit(h), l, WW.bit_le1(h)))
  +e3 = Equal.sym(Bool, C.fits(1n+a, Nat.add(C.bit(h), Nat.double(C.half(h)))), C.fits(a, C.half(h)), fit_td(a, C.bit(h), C.half(h), WW.bit_le1(h)))
  +e4 = Equal.cong(Nat, Bool, z => C.fits(1n+a, z), Nat.add(C.bit(h), Nat.double(C.half(h))), h, Equal.sym(Nat, h, Nat.add(C.bit(h), Nat.double(C.half(h))), WW.hb(h)))
  Equal.trans(Bool, C.fits(1n+a, SW.jam(h, l)), C.fits(1n+a, Nat.add(t, Nat.double(C.half(h)))), C.fits(1n+a, h), e1, Equal.trans(Bool, C.fits(1n+a, Nat.add(t, Nat.double(C.half(h)))), C.fits(a, C.half(h)), C.fits(1n+a, h), e2, Equal.trans(Bool, C.fits(a, C.half(h)), C.fits(1n+a, Nat.add(C.bit(h), Nat.double(C.half(h)))), C.fits(1n+a, h), e3, e4)))

def nz_bl(+m: Nat, +K: Nat, +hb: {Nat.is_le(1n+K, M.bit_length(m)) == True{} : Bool}, +z: Bool, +hz: {Nat.is_eq(m, 0n) == z : Bool}) -> {z == False{} : Bool}:
  match z:
    case True{}:
      +e0 = N.eq_from_is_eq(m, 0n, hz)
      +h0 = L.subst(Nat, w => {Nat.is_le(1n+K, M.bit_length(w)) == True{} : Bool}, m, 0n, e0, hb)
      +h1 = L.subst(Nat, w => {Nat.is_le(1n+K, w) == True{} : Bool}, M.bit_length(0n), 0n, BT.bit_length_zero(), h0)
      NC.absurd_tf({True{} == False{} : Bool}, h1)
    case False{}:
      {==}

def rj2(+s: Bool, +d: Nat, +m: Nat, +x: Nat, +hb: {Nat.is_le(Nat.add(d, 55n), M.bit_length(m)) == True{} : Bool}, +hz: {Nat.is_eq(m, 0n) == False{} : Bool}, +e: Nat, +fh0: {C.fits(e, C.high(d, m)) == False{} : Bool}, +fh1: {C.fits(1n+e, C.high(d, m)) == True{} : Bool}, +eB: {Nat.add(d, 1n+e) == M.bit_length(m) : Nat}) -> {SF.round(s, m, x) == SF.round(s, SW.jam(C.high(d, m), C.low(d, m)), Nat.add(x, d)) : F.F64}:
  +ejf = FR.jam_form(C.high(d, m), C.low(d, m))
  +hhb = WW.le_add_r(C.bit(C.high(d, m)), Nat.max(C.bit(C.high(d, m)), Nat.min(C.low(d, m), 1n)), Nat.double(C.half(C.high(d, m))), max_ge_l(C.bit(C.high(d, m)), Nat.min(C.low(d, m), 1n)))
  +hhJ = L.subst(Nat, z => {Nat.is_le(z, SW.jam(C.high(d, m), C.low(d, m))) == True{} : Bool}, Nat.add(C.bit(C.high(d, m)), Nat.double(C.half(C.high(d, m)))), C.high(d, m), Equal.sym(Nat, C.high(d, m), Nat.add(C.bit(C.high(d, m)), Nat.double(C.half(C.high(d, m)))), WW.hb(C.high(d, m))), L.subst(Nat, z => {Nat.is_le(Nat.add(C.bit(C.high(d, m)), Nat.double(C.half(C.high(d, m)))), z) == True{} : Bool}, Nat.add(Nat.max(C.bit(C.high(d, m)), Nat.min(C.low(d, m), 1n)), Nat.double(C.half(C.high(d, m)))), SW.jam(C.high(d, m), C.low(d, m)), Equal.sym(Nat, SW.jam(C.high(d, m), C.low(d, m)), Nat.add(Nat.max(C.bit(C.high(d, m)), Nat.min(C.low(d, m), 1n)), Nat.double(C.half(C.high(d, m)))), ejf), hhb))
  +nfJ = FR.nfit(e, C.high(d, m), SW.jam(C.high(d, m), C.low(d, m)), hhJ, fh0)
  +fJ1 = Equal.trans(Bool, C.fits(1n+e, SW.jam(C.high(d, m), C.low(d, m))), C.fits(1n+e, C.high(d, m)), True{}, jam_fits(e, C.high(d, m), C.low(d, m)), fh1)
  +eblJ = FR.bl_c(e, SW.jam(C.high(d, m), C.low(d, m)), nfJ, fJ1, Nat.cmp(M.bit_length(SW.jam(C.high(d, m), C.low(d, m))), 1n+e), {==})
  +hzJ = FR.nz_of(e, SW.jam(C.high(d, m), C.low(d, m)), nfJ)
  +ea = Equal.trans(Nat, Nat.add(Nat.add(x, d), M.bit_length(SW.jam(C.high(d, m), C.low(d, m)))), Nat.add(Nat.add(x, d), 1n+e), Nat.add(x, M.bit_length(m)), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(x, d), z), M.bit_length(SW.jam(C.high(d, m), C.low(d, m))), 1n+e, eblJ), Equal.trans(Nat, Nat.add(Nat.add(x, d), 1n+e), Nat.add(x, Nat.add(d, 1n+e)), Nat.add(x, M.bit_length(m)), NA.add_assoc(x, d, 1n+e), Equal.cong(Nat, Nat, z => Nat.add(x, z), Nat.add(d, 1n+e), M.bit_length(m), eB)))
  +eU = Equal.cong(Nat, Nat, z => Nat.max(Nat.sub(z, 53n), Nat.sub(SF.zb(), 1074n)), Nat.add(Nat.add(x, d), M.bit_length(SW.jam(C.high(d, m), C.low(d, m)))), Nat.add(x, M.bit_length(m)), ea)
  +ed55 = Equal.trans(Nat, Nat.add(Nat.add(x, Nat.add(d, 2n)), 53n), Nat.add(x, Nat.add(Nat.add(d, 2n), 53n)), Nat.add(x, Nat.add(d, 55n)), NA.add_assoc(x, Nat.add(d, 2n), 53n), Equal.cong(Nat, Nat, z => Nat.add(x, z), Nat.add(Nat.add(d, 2n), 53n), Nat.add(d, 55n), NA.add_assoc(d, 2n, 53n)))
  +a0 = L.subst(Nat, z => {Nat.is_le(z, Nat.add(x, M.bit_length(m))) == True{} : Bool}, Nat.add(x, Nat.add(d, 55n)), Nat.add(Nat.add(x, Nat.add(d, 2n)), 53n), Equal.sym(Nat, Nat.add(Nat.add(x, Nat.add(d, 2n)), 53n), Nat.add(x, Nat.add(d, 55n)), ed55), N.le_add_left(Nat.add(d, 55n), M.bit_length(m), x, hb))
  +hu = N.le_trans(Nat.add(x, Nat.add(d, 2n)), Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), le_sub(Nat.add(x, Nat.add(d, 2n)), 53n, Nat.add(x, M.bit_length(m)), a0), max_ge_l(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)))
  +i = Nat.sub(Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), Nat.add(x, Nat.add(d, 2n)))
  +eu = N.sub_add(Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), Nat.add(x, Nat.add(d, 2n)), hu)
  +k1 = Equal.trans(Nat, Nat.sub(Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), x), Nat.sub(Nat.add(Nat.add(x, Nat.add(d, 2n)), i), x), Nat.add(2n+i, d), Equal.cong(Nat, Nat, z => Nat.sub(z, x), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), Nat.add(Nat.add(x, Nat.add(d, 2n)), i), Equal.sym(Nat, Nat.add(Nat.add(x, Nat.add(d, 2n)), i), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), eu)), Equal.trans(Nat, Nat.sub(Nat.add(Nat.add(x, Nat.add(d, 2n)), i), x), Nat.sub(Nat.add(x, Nat.add(Nat.add(d, 2n), i)), x), Nat.add(2n+i, d), Equal.cong(Nat, Nat, z => Nat.sub(z, x), Nat.add(Nat.add(x, Nat.add(d, 2n)), i), Nat.add(x, Nat.add(Nat.add(d, 2n), i)), NA.add_assoc(x, Nat.add(d, 2n), i)), Equal.trans(Nat, Nat.sub(Nat.add(x, Nat.add(Nat.add(d, 2n), i)), x), Nat.add(Nat.add(d, 2n), i), Nat.add(2n+i, d), N.add_sub_cancel(x, Nat.add(Nat.add(d, 2n), i)), Equal.trans(Nat, Nat.add(Nat.add(d, 2n), i), Nat.add(d, 2n+i), Nat.add(2n+i, d), NA.add_assoc(d, 2n, i), NA.add_comm(d, 2n+i)))))
  +k2 = Equal.trans(Nat, Nat.sub(Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), Nat.add(x, d)), Nat.sub(Nat.add(Nat.add(x, Nat.add(d, 2n)), i), Nat.add(x, d)), 2n+i, Equal.cong(Nat, Nat, z => Nat.sub(z, Nat.add(x, d)), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), Nat.add(Nat.add(x, Nat.add(d, 2n)), i), Equal.sym(Nat, Nat.add(Nat.add(x, Nat.add(d, 2n)), i), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), eu)), Equal.trans(Nat, Nat.sub(Nat.add(Nat.add(x, Nat.add(d, 2n)), i), Nat.add(x, d)), Nat.sub(Nat.add(Nat.add(Nat.add(x, d), 2n), i), Nat.add(x, d)), 2n+i, Equal.cong(Nat, Nat, z => Nat.sub(Nat.add(z, i), Nat.add(x, d)), Nat.add(x, Nat.add(d, 2n)), Nat.add(Nat.add(x, d), 2n), Equal.sym(Nat, Nat.add(Nat.add(x, d), 2n), Nat.add(x, Nat.add(d, 2n)), NA.add_assoc(x, d, 2n))), Equal.trans(Nat, Nat.sub(Nat.add(Nat.add(Nat.add(x, d), 2n), i), Nat.add(x, d)), Nat.sub(Nat.add(Nat.add(x, d), 2n+i), Nat.add(x, d)), 2n+i, Equal.cong(Nat, Nat, z => Nat.sub(z, Nat.add(x, d)), Nat.add(Nat.add(Nat.add(x, d), 2n), i), Nat.add(Nat.add(x, d), 2n+i), NA.add_assoc(Nat.add(x, d), 2n, i)), N.add_sub_cancel(Nat.add(x, d), 2n+i))))
  +hle1 = N.le_trans(x, Nat.add(x, Nat.add(d, 2n)), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), N.le_add_right(x, Nat.add(d, 2n)), hu)
  +hle2 = N.le_trans(Nat.add(x, d), Nat.add(x, Nat.add(d, 2n)), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), N.le_add_left(d, Nat.add(d, 2n), x, N.le_add_right(d, 2n)), hu)
  +l1 = Equal.cong(Bool, F.F64, z => SF.pick(F.F64, z, SF.zero(s), SF.round_u(s, m, x, Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)))), Nat.is_eq(m, 0n), False{}, hz)
  +l2 = Equal.cong(Bool, F.F64, z => SF.pack(s, SF.pick(Nat, z, SF.rne(m, Nat.sub(Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), x)), C.shift(Nat.sub(x, Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), m)), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), Nat.is_le(x, Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), True{}, hle1)
  +l3 = Equal.cong(Nat, F.F64, z => SF.pack(s, SF.rne(m, z), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), Nat.sub(Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), x), Nat.add(2n+i, d), k1)
  +l4 = Equal.cong(Nat, F.F64, z => SF.pack(s, z, Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.rne(m, Nat.add(2n+i, d)), SF.rne(SW.jam(C.high(d, m), C.low(d, m)), 2n+i), FR.sticky(i, d, m))
  +r1 = Equal.cong(Bool, F.F64, z => SF.pick(F.F64, z, SF.zero(s), SF.round_u(s, SW.jam(C.high(d, m), C.low(d, m)), Nat.add(x, d), Nat.max(Nat.sub(Nat.add(Nat.add(x, d), M.bit_length(SW.jam(C.high(d, m), C.low(d, m)))), 53n), Nat.sub(SF.zb(), 1074n)))), Nat.is_eq(SW.jam(C.high(d, m), C.low(d, m)), 0n), False{}, hzJ)
  +r2 = Equal.cong(Nat, F.F64, z => SF.round_u(s, SW.jam(C.high(d, m), C.low(d, m)), Nat.add(x, d), z), Nat.max(Nat.sub(Nat.add(Nat.add(x, d), M.bit_length(SW.jam(C.high(d, m), C.low(d, m)))), 53n), Nat.sub(SF.zb(), 1074n)), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), eU)
  +r3 = Equal.cong(Bool, F.F64, z => SF.pack(s, SF.pick(Nat, z, SF.rne(SW.jam(C.high(d, m), C.low(d, m)), Nat.sub(Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), Nat.add(x, d))), C.shift(Nat.sub(Nat.add(x, d), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SW.jam(C.high(d, m), C.low(d, m)))), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), Nat.is_le(Nat.add(x, d), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), True{}, hle2)
  +r4 = Equal.cong(Nat, F.F64, z => SF.pack(s, SF.rne(SW.jam(C.high(d, m), C.low(d, m)), z), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), Nat.sub(Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), Nat.add(x, d)), 2n+i, k2)
  +lhs = Equal.trans(F.F64, SF.round(s, m, x), SF.round_u(s, m, x, Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.pack(s, SF.rne(SW.jam(C.high(d, m), C.low(d, m)), 2n+i), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), l1, Equal.trans(F.F64, SF.round_u(s, m, x, Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.pack(s, SF.rne(m, Nat.sub(Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), x)), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.pack(s, SF.rne(SW.jam(C.high(d, m), C.low(d, m)), 2n+i), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), l2, Equal.trans(F.F64, SF.pack(s, SF.rne(m, Nat.sub(Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), x)), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.pack(s, SF.rne(m, Nat.add(2n+i, d)), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.pack(s, SF.rne(SW.jam(C.high(d, m), C.low(d, m)), 2n+i), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), l3, l4)))
  +rhs = Equal.trans(F.F64, SF.round(s, SW.jam(C.high(d, m), C.low(d, m)), Nat.add(x, d)), SF.round_u(s, SW.jam(C.high(d, m), C.low(d, m)), Nat.add(x, d), Nat.max(Nat.sub(Nat.add(Nat.add(x, d), M.bit_length(SW.jam(C.high(d, m), C.low(d, m)))), 53n), Nat.sub(SF.zb(), 1074n))), SF.pack(s, SF.rne(SW.jam(C.high(d, m), C.low(d, m)), 2n+i), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), r1, Equal.trans(F.F64, SF.round_u(s, SW.jam(C.high(d, m), C.low(d, m)), Nat.add(x, d), Nat.max(Nat.sub(Nat.add(Nat.add(x, d), M.bit_length(SW.jam(C.high(d, m), C.low(d, m)))), 53n), Nat.sub(SF.zb(), 1074n))), SF.round_u(s, SW.jam(C.high(d, m), C.low(d, m)), Nat.add(x, d), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.pack(s, SF.rne(SW.jam(C.high(d, m), C.low(d, m)), 2n+i), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), r2, Equal.trans(F.F64, SF.round_u(s, SW.jam(C.high(d, m), C.low(d, m)), Nat.add(x, d), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.pack(s, SF.rne(SW.jam(C.high(d, m), C.low(d, m)), Nat.sub(Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), Nat.add(x, d))), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.pack(s, SF.rne(SW.jam(C.high(d, m), C.low(d, m)), 2n+i), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), r3, r4)))
  Equal.trans(F.F64, SF.round(s, m, x), SF.pack(s, SF.rne(SW.jam(C.high(d, m), C.low(d, m)), 2n+i), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.round(s, SW.jam(C.high(d, m), C.low(d, m)), Nat.add(x, d)), lhs, Equal.sym(F.F64, SF.round(s, SW.jam(C.high(d, m), C.low(d, m)), Nat.add(x, d)), SF.pack(s, SF.rne(SW.jam(C.high(d, m), C.low(d, m)), 2n+i), Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), rhs))

# round(s, m, x) = round(s, jam(m >> d, m mod 2^d), x + d) when m has d + 55 bits
def round_jam(+s: Bool, +d: Nat, +m: Nat, +x: Nat, +hb: {Nat.is_le(Nat.add(d, 55n), M.bit_length(m)) == True{} : Bool}) -> {SF.round(s, m, x) == SF.round(s, SW.jam(C.high(d, m), C.low(d, m)), Nat.add(x, d)) : F.F64}:
  +hb1 = L.subst(Nat, z => {Nat.is_le(z, M.bit_length(m)) == True{} : Bool}, Nat.add(d, 55n), 1n+Nat.add(d, 54n), Equal.trans(Nat, Nat.add(d, 55n), 1n+Nat.add(d, 54n), 1n+Nat.add(d, 54n), N.add_succ(d, 54n), {==}), hb)
  +hz = nz_bl(m, Nat.add(d, 54n), hb1, Nat.is_eq(m, 0n), {==})
  +j = Nat.sub(M.bit_length(m), 1n)
  +ej = N.sub_add(M.bit_length(m), 1n, FO.bl_pos(m, hz, M.bit_length(m), {==}))
  +hdj = N.le_trans(d, Nat.add(d, 54n), j, N.le_add_right(d, 54n), N.lt_succ_le(Nat.add(d, 54n), j, N.succ_le_lt(Nat.add(d, 54n), 1n+j, L.subst(Nat, z => {Nat.is_le(1n+Nat.add(d, 54n), z) == True{} : Bool}, M.bit_length(m), 1n+j, Equal.sym(Nat, 1n+j, M.bit_length(m), ej), hb1))))
  +e = Nat.sub(j, d)
  +eje = Equal.trans(Nat, Nat.add(e, d), Nat.add(d, e), j, NA.add_comm(e, d), N.sub_add(j, d, hdj))
  +h = C.high(d, m)
  +eB = Equal.trans(Nat, Nat.add(d, 1n+e), 1n+Nat.add(d, e), M.bit_length(m), N.add_succ(d, e), Equal.trans(Nat, 1n+Nat.add(d, e), 1n+j, M.bit_length(m), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(d, e), j, N.sub_add(j, d, hdj)), ej))
  +fB = L.subst(Nat, z => {C.fits(z, m) == True{} : Bool}, M.bit_length(m), Nat.add(d, 1n+e), Equal.sym(Nat, Nat.add(d, 1n+e), M.bit_length(m), eB), bl_fit(m))
  +fh1 = Equal.trans(Bool, C.fits(1n+e, h), C.fits(Nat.add(d, 1n+e), m), True{}, Equal.sym(Bool, C.fits(Nat.add(d, 1n+e), m), C.fits(1n+e, h), FR.fits_hc(d, 1n+e, m)), fB)
  +nj = L.subst(Nat, z => {C.fits(z, m) == False{} : Bool}, j, Nat.add(d, e), Equal.sym(Nat, Nat.add(d, e), j, N.sub_add(j, d, hdj)), bl_nfit(m, hz))
  +fh0 = Equal.trans(Bool, C.fits(e, h), C.fits(Nat.add(d, e), m), False{}, Equal.sym(Bool, C.fits(Nat.add(d, e), m), C.fits(e, h), FR.fits_hc(d, e, m)), nj)
  rj2(s, d, m, x, hb, hz, e, fh0, fh1, eB)
