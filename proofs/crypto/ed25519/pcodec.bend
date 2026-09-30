import Base
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../spec/crypto/curve25519/x25519.bend as SX
import ../../../spec/crypto/ed25519.bend as SE
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../../src/crypto/ed25519/point.bend as PT
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/u32.bend as U
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../curve25519/limbs.bend as LM
import ../curve25519/cong.bend as G
import ../curve25519/xbits.bend as XB
import ../curve25519/xlem.bend as LD
import ../curve25519/num.bend as M2
import ../fe/pw.bend as PW
import ../fe/pow.bend as PO
import ../fe/rel.bend as RE
import ../fe/conv.bend as CV
import ../fe/cst.bend as CS
import ./prel.bend as PR

# Constants, encoding (5.1.2), equality and the field comparisons of
# src/crypto/ed25519/point.bend (on the fast field) against
# spec/crypto/ed25519.bend.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# decoding results: both None, or both Some of related points
def MR(+one: Nat, +pp: Nat, +m: Maybe<&2, PT.Pt>, +sm: Maybe<&2, SE.EPt>) -> Data:
  match m sm:
    case None{} None{}:
      {True{} == True{} : Bool}
    case Some{p} Some{sp}:
      PR.Rp(one, pp, p, sp)
    case None{} Some{sp}:
      {True{} == False{} : Bool}
    case Some{p} None{}:
      {True{} == False{} : Bool}

# ---- small constants ----

def r_val(+one: Nat, +pp: Nat, +x: FE.Fe, +a: Nat, +b: Nat, +e: {a == b : Nat}, +r: RE.Rel(one, pp, x, a)) -> RE.Rel(one, pp, x, b):
  L.subst(Nat, t => RE.Rel(one, pp, x, t), a, b, e, r)

def lt19(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk: {Nat.is_lt(k, WD.sc(17n, one)) == True{} : Bool}) -> {Nat.is_lt(k, WD.sc(19n, one)) == True{} : Bool}:
  N.lt_trans(k, WD.sc(17n, one), WD.sc(19n, one), hk, PW.lt_sc(1n, 17n, one, h1))

# k < 8
def small_lt(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk: {Nat.is_lt(k, 8n) == True{} : Bool}) -> {Nat.is_lt(k, WD.sc(19n, one)) == True{} : Bool}:
  +a = L.subst(Nat, o => {Nat.is_lt(k, WD.sc(3n, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), hk)
  N.lt_trans(k, WD.sc(3n, one), WD.sc(19n, one), a, PW.lt_sc(15n, 3n, one, h1))

def r_small(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +k: Nat, +hk: {Nat.is_lt(k, WD.sc(19n, one)) == True{} : Bool}) -> RE.Rel(one, pp, FE.small(k), k):
  RE.mk(one, pp, FE.small(k), k, LD.small_ok(one, h1, k, hk), G.c_eq(pp, FV.value(FE.small(k)), k, CS.small_val(k)))

def r_zero(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat) -> RE.Rel(one, pp, FE.zero(), 0n):
  r_small(one, h1, pp, 0n, PW.sc_pos(19n, one, h1))

def r_one(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat) -> RE.Rel(one, pp, FE.one(), 1n):
  r_small(one, h1, pp, 1n, LD.one_lt19(one, h1))

def r_c65(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat) -> RE.Rel(one, pp, FE.small(X.a24(one)), FS.digits(one, [65n, 219n, 1n])):
  r_val(one, pp, FE.small(X.a24(one)), X.a24(one), FS.digits(one, [65n, 219n, 1n]), CS.digits_eq(one, [65n, 219n, 1n]), r_small(one, h1, pp, X.a24(one), lt19(one, h1, X.a24(one), LD.a24_lt(one, h1))))

def r_c66(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat) -> RE.Rel(one, pp, FE.small(PT.c121666(one)), FS.digits(one, [66n, 219n, 1n])):
  r_val(one, pp, FE.small(PT.c121666(one)), PT.c121666(one), FS.digits(one, [66n, 219n, 1n]), CS.digits_eq(one, [66n, 219n, 1n]), r_small(one, h1, pp, PT.c121666(one), lt19(one, h1, PT.c121666(one), CS.dig3_lt(one, h1, 66n, 219n, {==}, {==}))))

# ---- d, 2 d, sqrt(-1) from the symbolic one ----

# d for any related 121665 and 121666 (kept variables: the checker never
# runs the constant computation)
def rd_gen(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x65: FE.Fe, +x66: FE.Fe, +r65: RE.Rel(one, pp, x65, FS.digits(one, [65n, 219n, 1n])), +r66: RE.Rel(one, pp, x66, FS.digits(one, [66n, 219n, 1n]))) -> RE.Rel(one, pp, FE.mul(R, FE.neg(R, x65), FE.inv(R, x66)), SE.dconst(one, 1n+pp)):
  +P = {1n+pp : Nat}
  +D65 = FS.digits(one, [65n, 219n, 1n])
  +D66 = FS.digits(one, [66n, 219n, 1n])
  RE.r_mul(one, h1, pp, hP, R, hR, FE.neg(R, x65), FE.inv(R, x66), FS.fsub(P, 0n, D65), FS.finv(P, D66), RE.r_sub(one, h1, pp, hP, R, hR, FE.zero(), x65, 0n, D65, r_zero(one, h1, pp), r65), RE.r_inv(one, h1, pp, hP, R, hR, x66, D66, r66))

def p14_bits() -> List<&2, Bool>:
  [False{}, True{}, True{}]

def eb_p14(+one: Nat, +h1: {one == 1n : Nat}) -> {PO.eb(one, p14_bits()) == 3n : Nat}:
  L.subst(Nat, o => {PO.eb(o, p14_bits()) == 3n : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})

# 8 Fo(250) + 3 == (p - 1) / 4
def p14_exp(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}) -> {Nat.add(Nat.mul(PO.Fo(one, 250n), WD.sc(PO.blen(p14_bits()), one)), PO.eb(one, p14_bits())) == Nat.div(Nat.sub(1n+pp, 1n), 4n) : Nat}:
  +F2 = PO.Fo(one, 250n)
  +P = {1n+pp : Nat}
  %Equal.sym(Nat, WD.sc(3n, one), 8n, PO.small_one(one, h1, 3n, 8n, {==})) : {Nat.add(Nat.mul(F2, _), PO.eb(one, p14_bits())) == Nat.div(Nat.sub(P, 1n), 4n) : Nat}
  %Equal.sym(Nat, PO.eb(one, p14_bits()), 3n, eb_p14(one, h1)) : {Nat.add(Nat.mul(F2, 8n), _) == Nat.div(Nat.sub(P, 1n), 4n) : Nat}
  +e = Nat.add(Nat.mul(F2, 8n), 3n)
  +m4 = Equal.trans(Nat, Nat.mul(e, 4n), Nat.add(Nat.mul(Nat.mul(F2, 8n), 4n), Nat.mul(3n, 4n)), Nat.add(Nat.mul(F2, 32n), 12n), NA.mul_add_right(Nat.mul(F2, 8n), 3n, 4n), M2.cong_l(Nat.mul(Nat.mul(F2, 8n), 4n), Nat.mul(F2, 32n), Nat.mul(3n, 4n), NA.mul_assoc(F2, 8n, 4n)))
  +e1 = Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(e, 4n), 1n), 19n), Nat.add(Nat.add(Nat.add(Nat.mul(F2, 32n), 12n), 1n), 19n), Nat.add(P, 19n), M2.cong_l(Nat.add(Nat.mul(e, 4n), 1n), Nat.add(Nat.add(Nat.mul(F2, 32n), 12n), 1n), 19n, M2.cong_l(Nat.mul(e, 4n), Nat.add(Nat.mul(F2, 32n), 12n), 1n, m4)),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.mul(F2, 32n), 12n), 1n), 19n), Nat.add(Nat.mul(F2, 32n), 32n), Nat.add(P, 19n), Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.mul(F2, 32n), 12n), 1n), 19n), Nat.add(Nat.add(Nat.mul(F2, 32n), 12n), Nat.add(1n, 19n)), Nat.add(Nat.mul(F2, 32n), 32n), NA.add_assoc(Nat.add(Nat.mul(F2, 32n), 12n), 1n, 19n), NA.add_assoc(Nat.mul(F2, 32n), 12n, 20n)), PO.f32(one, h1, pp, hP)))
  +e2 = G.cancel_r(Nat.add(Nat.mul(e, 4n), 1n), P, 19n, e1)
  +e3 = Equal.trans(Nat, P, Nat.add(Nat.mul(e, 4n), 1n), Nat.add(1n, Nat.mul(e, 4n)), Equal.sym(Nat, Nat.add(Nat.mul(e, 4n), 1n), P, e2), NA.add_comm(Nat.mul(e, 4n), 1n))
  %Equal.sym(Nat, P, Nat.add(1n, Nat.mul(e, 4n)), e3) : {e == Nat.div(Nat.sub(_, 1n), 4n) : Nat}
  %Equal.sym(Nat, Nat.sub(Nat.add(1n, Nat.mul(e, 4n)), 1n), Nat.mul(e, 4n), N.add_sub_cancel(1n, Nat.mul(e, 4n))) : {e == Nat.div(_, 4n) : Nat}
  %N.add_zero(Nat.mul(e, 4n)) : {e == Nat.div(_, 4n) : Nat}
  Equal.sym(Nat, Nat.div(Nat.add(Nat.mul(e, 4n), 0n), 4n), e, NR.div_of(e, 3n, 0n, {==}))

def rs_gen(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +two: FE.Fe, +r2: RE.Rel(one, pp, two, 2n)) -> RE.Rel(one, pp, PT.pow_p14(R, two), SE.sqm1(1n+pp)):
  +P = {1n+pp : Nat}
  +ex = Nat.add(Nat.mul(PO.Fo(one, 250n), WD.sc(PO.blen(p14_bits()), one)), PO.eb(one, p14_bits()))
  +k = Nat.div(Nat.sub(P, 1n), 4n)
  +o2 = RE.o(one, pp, two, 2n, r2)
  +c1 = PO.chain_val(one, h1, pp, hP, R, hR, 249n, p14_bits(), two, o2)
  +c1b = G.c_trans(pp, FV.value(PT.pow_p14(R, two)), Nat.pow(FV.value(two), ex), Nat.pow(2n, ex), c1, G.c_pow(pp, FV.value(two), 2n, ex, RE.c(one, pp, two, 2n, r2)))
  +c2 = G.c_eq(pp, Nat.pow(2n, ex), Nat.pow(2n, k), Equal.cong(Nat, Nat, t => Nat.pow(2n, t), ex, k, p14_exp(one, h1, pp, hP)))
  +c3 = G.c_sym(pp, FS.fpow(P, 2n, k), Nat.pow(2n, k), G.c_mod(pp, Nat.pow(2n, k)))
  RE.mk(one, pp, PT.pow_p14(R, two), SE.sqm1(P), PO.pbs_okb(one, h1, R, hR, p14_bits(), two, FE.pow_ones(R, two, 249n, two), o2, PO.po_okb(one, h1, R, hR, 249n, two, two, o2, o2)), G.c_trans(pp, FV.value(PT.pow_p14(R, two)), Nat.pow(2n, ex), FS.fpow(P, 2n, k), c1b, G.c_trans(pp, Nat.pow(2n, ex), Nat.pow(2n, k), FS.fpow(P, 2n, k), c2, c3)))

# ---- the constants of an input list ----

def one_eq(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>) -> {one == X.one_of(xs) : Nat}:
  Equal.sym(Nat, X.one_of(xs), one, CS.one_of_eq(one, h1, xs))

def cr(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>) -> {PT.cs_r(PT.consts(xs)) == WD.sc(17n, one) : Nat}:
  CS.radix_of_eq(one, h1, xs)

def lit_rel(+one: Nat, +pp: Nat, +xs: List<&2, U32>, +x: FE.Fe, +a: Nat, +r: RE.Rel(one, pp, x, a)) -> RE.Rel(one, pp, PT.lit(xs, x), a):
  match xs:
    case Nil{}:
      r
    case Con{h, t}:
      r

def l65(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +xs: List<&2, U32>) -> RE.Rel(one, pp, PT.lit(xs, FE.small(X.a24(X.one_of(xs)))), FS.digits(one, [65n, 219n, 1n])):
  lit_rel(one, pp, xs, FE.small(X.a24(X.one_of(xs))), FS.digits(one, [65n, 219n, 1n]), L.subst(Nat, o => RE.Rel(one, pp, FE.small(X.a24(o)), FS.digits(one, [65n, 219n, 1n])), one, X.one_of(xs), one_eq(one, h1, xs), r_c65(one, h1, pp)))

def l66(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +xs: List<&2, U32>) -> RE.Rel(one, pp, PT.lit(xs, FE.small(PT.c121666(X.one_of(xs)))), FS.digits(one, [66n, 219n, 1n])):
  lit_rel(one, pp, xs, FE.small(PT.c121666(X.one_of(xs))), FS.digits(one, [66n, 219n, 1n]), L.subst(Nat, o => RE.Rel(one, pp, FE.small(PT.c121666(o)), FS.digits(one, [66n, 219n, 1n])), one, X.one_of(xs), one_eq(one, h1, xs), r_c66(one, h1, pp)))

def rd(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +xs: List<&2, U32>) -> RE.Rel(one, pp, PT.cs_d(PT.consts(xs)), SE.dconst(one, 1n+pp)):
  rd_gen(one, h1, pp, hP, X.radix_of(xs), cr(one, h1, xs), PT.lit(xs, FE.small(X.a24(X.one_of(xs)))), PT.lit(xs, FE.small(PT.c121666(X.one_of(xs)))), l65(one, h1, pp, xs), l66(one, h1, pp, xs))

def rd2(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +xs: List<&2, U32>) -> RE.Rel(one, pp, PT.cs_d2(PT.consts(xs)), FS.fadd(1n+pp, SE.dconst(one, 1n+pp), SE.dconst(one, 1n+pp))):
  +D = SE.dconst(one, 1n+pp)
  RE.r_add(one, h1, pp, hP, X.radix_of(xs), cr(one, h1, xs), PT.cs_d(PT.consts(xs)), PT.cs_d(PT.consts(xs)), D, D, rd(one, h1, pp, hP, xs), rd(one, h1, pp, hP, xs))

def rs(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +xs: List<&2, U32>) -> RE.Rel(one, pp, PT.cs_s(PT.consts(xs)), SE.sqm1(1n+pp)):
  rs_gen(one, h1, pp, hP, X.radix_of(xs), cr(one, h1, xs), PT.lit(xs, FE.small(2n)), lit_rel(one, pp, xs, FE.small(2n), 2n, r_small(one, h1, pp, 2n, small_lt(one, h1, 2n, {==}))))

# ---- equality of reduced values ----

def red(+pp: Nat, +a: Nat) -> {Nat.mod(Nat.mod(a, 1n+pp), 1n+pp) == Nat.mod(a, 1n+pp) : Nat}:
  NR.mod_mod(pp, a)

def cv(+one: Nat, +pp: Nat, +x: FE.Fe, +a: Nat, +rx: RE.Rel(one, pp, x, a), +ha: {Nat.mod(a, 1n+pp) == a : Nat}) -> {Nat.mod(FV.value(x), 1n+pp) == a : Nat}:
  Equal.trans(Nat, Nat.mod(FV.value(x), 1n+pp), Nat.mod(a, 1n+pp), a, RE.c(one, pp, x, a, rx), ha)

def eq_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +y: FE.Fe, +a: Nat, +b: Nat, +rx: RE.Rel(one, pp, x, a), +ry: RE.Rel(one, pp, y, b), +ha: {Nat.mod(a, 1n+pp) == a : Nat}, +hb: {Nat.mod(b, 1n+pp) == b : Nat}) -> {FE.eq(R, x, y) == Nat.is_eq(a, b) : Bool}:
  +e1 = CV.eq_val(one, h1, pp, hP, R, hR, x, y, RE.o(one, pp, x, a, rx), RE.o(one, pp, y, b, ry))
  +ea = cv(one, pp, x, a, rx, ha)
  +eb = cv(one, pp, y, b, ry, hb)
  Equal.trans(Bool, FE.eq(R, x, y), Nat.is_eq(Nat.mod(FV.value(x), 1n+pp), Nat.mod(FV.value(y), 1n+pp)), Nat.is_eq(a, b), e1, Equal.trans(Bool, Nat.is_eq(Nat.mod(FV.value(x), 1n+pp), Nat.mod(FV.value(y), 1n+pp)), Nat.is_eq(a, Nat.mod(FV.value(y), 1n+pp)), Nat.is_eq(a, b), Equal.cong(Nat, Bool, z => Nat.is_eq(z, Nat.mod(FV.value(y), 1n+pp)), Nat.mod(FV.value(x), 1n+pp), a, ea), Equal.cong(Nat, Bool, z => Nat.is_eq(a, z), Nat.mod(FV.value(y), 1n+pp), b, eb)))

def iz_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +a: Nat, +rx: RE.Rel(one, pp, x, a), +ha: {Nat.mod(a, 1n+pp) == a : Nat}) -> {FE.is_zero(R, x) == Nat.is_eq(a, 0n) : Bool}:
  +e1 = CV.is_zero_val(one, h1, pp, hP, R, hR, x, RE.o(one, pp, x, a, rx))
  Equal.trans(Bool, FE.is_zero(R, x), Nat.is_eq(Nat.mod(FV.value(x), 1n+pp), 0n), Nat.is_eq(a, 0n), e1, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), Nat.mod(FV.value(x), 1n+pp), a, cv(one, pp, x, a, rx, ha)))

def par_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +a: Nat, +rx: RE.Rel(one, pp, x, a), +ha: {Nat.mod(a, 1n+pp) == a : Nat}) -> {v(FE.parity(R, x)) == Nat.mod(a, 2n) : Nat}:
  Equal.trans(Nat, v(FE.parity(R, x)), Nat.mod(Nat.mod(FV.value(x), 1n+pp), 2n), Nat.mod(a, 2n), CV.parity_val(one, h1, pp, hP, R, hR, x, RE.o(one, pp, x, a, rx)), Equal.cong(Nat, Nat, z => Nat.mod(z, 2n), Nat.mod(FV.value(x), 1n+pp), a, cv(one, pp, x, a, rx, ha)))

def u32_eq_nat(+a: U32, +b: U32) -> {U32.is_eq(a, b) == Nat.is_eq(v(a), v(b)) : Bool}:
  Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), U32.cmp(a, b), Nat.cmp(v(a), v(b)), U.u32_cmp(a, b))

def mod2_le(+a: Nat) -> {Nat.is_le(Nat.mod(a, 2n), 1n) == True{} : Bool}:
  N.lt_succ_le(Nat.mod(a, 2n), 1n, NR.dm_lt(1n, a))

# ---- the point equality ----

def equal_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +p: PT.Pt, +q: PT.Pt, +sp: SE.EPt, +sq: SE.EPt, +hp: PR.Rp(one, pp, p, sp), +hq: PR.Rp(one, pp, q, sq)) -> {PT.equal(R, p, q) == SE.equal(1n+pp, sp, sq) : Bool}:
  match p q sp sq:
    case PT.Pt{+x1, +y1, +z1, +t1} PT.Pt{+x2, +y2, +z2, +t2} SE.EPt{+a1, +b1, +c1, +d1} SE.EPt{+a2, +b2, +c2, +d2}:
      +P = {1n+pp : Nat}
      +rx1 = PR.rX(one, pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +ry1 = PR.rY(one, pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +rz1 = PR.rZ(one, pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +rx2 = PR.rX(one, pp, x2, y2, z2, t2, a2, b2, c2, d2, hq)
      +ry2 = PR.rY(one, pp, x2, y2, z2, t2, a2, b2, c2, d2, hq)
      +rz2 = PR.rZ(one, pp, x2, y2, z2, t2, a2, b2, c2, d2, hq)
      +e1 = eq_rel(one, h1, pp, hP, R, hR, FE.mul(R, x1, z2), FE.mul(R, x2, z1), FS.fmul(P, a1, c2), FS.fmul(P, a2, c1), PR.rmul(one, h1, pp, hP, R, hR, x1, z2, a1, c2, rx1, rz2), PR.rmul(one, h1, pp, hP, R, hR, x2, z1, a2, c1, rx2, rz1), red(pp, Nat.mul(a1, c2)), red(pp, Nat.mul(a2, c1)))
      +e2 = eq_rel(one, h1, pp, hP, R, hR, FE.mul(R, y1, z2), FE.mul(R, y2, z1), FS.fmul(P, b1, c2), FS.fmul(P, b2, c1), PR.rmul(one, h1, pp, hP, R, hR, y1, z2, b1, c2, ry1, rz2), PR.rmul(one, h1, pp, hP, R, hR, y2, z1, b2, c1, ry2, rz1), red(pp, Nat.mul(b1, c2)), red(pp, Nat.mul(b2, c1)))
      Equal.trans(Bool, Bool.and(FE.eq(R, FE.mul(R, x1, z2), FE.mul(R, x2, z1)), FE.eq(R, FE.mul(R, y1, z2), FE.mul(R, y2, z1))), Bool.and(Nat.is_eq(FS.fmul(P, a1, c2), FS.fmul(P, a2, c1)), FE.eq(R, FE.mul(R, y1, z2), FE.mul(R, y2, z1))), Bool.and(Nat.is_eq(FS.fmul(P, a1, c2), FS.fmul(P, a2, c1)), Nat.is_eq(FS.fmul(P, b1, c2), FS.fmul(P, b2, c1))), Equal.cong(Bool, Bool, z => Bool.and(z, FE.eq(R, FE.mul(R, y1, z2), FE.mul(R, y2, z1))), FE.eq(R, FE.mul(R, x1, z2), FE.mul(R, x2, z1)), Nat.is_eq(FS.fmul(P, a1, c2), FS.fmul(P, a2, c1)), e1), Equal.cong(Bool, Bool, z => Bool.and(Nat.is_eq(FS.fmul(P, a1, c2), FS.fmul(P, a2, c1)), z), FE.eq(R, FE.mul(R, y1, z2), FE.mul(R, y2, z1)), Nat.is_eq(FS.fmul(P, b1, c2), FS.fmul(P, b2, c1)), e2))

# ---- encoding ----

def set_eq(+xs: List<&2, U32>, +b: U32) -> {PT.set_top(xs, b) == SE.set_msb(xs, b) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      match xt:
        case Nil{}:
          {==}
        case Con{+y, +yt}:
          Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{x, z}, PT.set_top(Con{y, yt}, b), SE.set_msb(Con{y, yt}, b), set_eq(Con{y, yt}, b))

# the canonical bytes of an element related to a reduced a
def bytes_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +a: Nat, +rx: RE.Rel(one, pp, x, a), +ha: {Nat.mod(a, 1n+pp) == a : Nat}) -> {FE.to_bytes(R, x) == SX.le_bytes(32n, a) : List<&2, U32>}:
  +y = FE.to_bytes(R, x)
  +oy = LM.bytes_okb(32n, y, CV.to_bytes_tight(one, h1, R, x))
  +ey = Equal.trans(Nat, FS.value(y), Nat.mod(FV.value(x), 1n+pp), a, CV.to_bytes_value(one, h1, pp, hP, R, hR, x, RE.o(one, pp, x, a, rx)), cv(one, pp, x, a, rx, ha))
  Equal.trans(List<&2, U32>, y, SX.le_bytes(32n, FS.value(y)), SX.le_bytes(32n, a), Equal.sym(List<&2, U32>, SX.le_bytes(32n, FS.value(y)), y, XB.bytes_le(32n, y, oy)), Equal.cong(Nat, List<&2, U32>, z => SX.le_bytes(32n, z), FS.value(y), a, ey))

def par_u32(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +a: Nat, +rx: RE.Rel(one, pp, x, a), +ha: {Nat.mod(a, 1n+pp) == a : Nat}) -> {FE.parity(R, x) == U32.from_nat(Nat.mod(a, 2n)) : U32}:
  +e = par_rel(one, h1, pp, hP, R, hR, x, a, rx, ha)
  +lt = NR.dm_lt(1n, a)
  U.injective(FE.parity(R, x), U32.from_nat(Nat.mod(a, 2n)), Equal.trans(Nat, v(FE.parity(R, x)), Nat.mod(a, 2n), v(U32.from_nat(Nat.mod(a, 2n))), e, Equal.sym(Nat, v(U32.from_nat(Nat.mod(a, 2n))), Nat.mod(a, 2n), U.to_nat_from_nat(Nat.mod(a, 2n), 1n, {==}, lt))))

def encode_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +p: PT.Pt, +sp: SE.EPt, +hp: PR.Rp(one, pp, p, sp)) -> {PT.encode(R, p) == SE.encode_n(32n, 1n+pp, sp) : List<&2, U32>}:
  match p sp:
    case PT.Pt{+x, +y, +z, +t} SE.EPt{+a, +b, +c, +d}:
      +P = {1n+pp : Nat}
      +rx = PR.rX(one, pp, x, y, z, t, a, b, c, d, hp)
      +ry = PR.rY(one, pp, x, y, z, t, a, b, c, d, hp)
      +rz = PR.rZ(one, pp, x, y, z, t, a, b, c, d, hp)
      +zi = FE.inv(R, z)
      +ZI = FS.finv(P, c)
      +rzi = RE.r_inv(one, h1, pp, hP, R, hR, z, c, rz)
      +my = PR.rmul(one, h1, pp, hP, R, hR, y, zi, b, ZI, ry, rzi)
      +mx = PR.rmul(one, h1, pp, hP, R, hR, x, zi, a, ZI, rx, rzi)
      +eb = bytes_rel(one, h1, pp, hP, R, hR, FE.mul(R, y, zi), FS.fmul(P, b, ZI), my, red(pp, Nat.mul(b, ZI)))
      +ep = par_u32(one, h1, pp, hP, R, hR, FE.mul(R, x, zi), FS.fmul(P, a, ZI), mx, red(pp, Nat.mul(a, ZI)))
      +BY = SX.le_bytes(32n, FS.fmul(P, b, ZI))
      +PB = U32.from_nat(Nat.mod(FS.fmul(P, a, ZI), 2n))
      +e1 = Equal.cong(List<&2, U32>, List<&2, U32>, w => PT.set_top(w, FE.parity(R, FE.mul(R, x, zi))), FE.to_bytes(R, FE.mul(R, y, zi)), BY, eb)
      +e2 = Equal.cong(U32, List<&2, U32>, w => PT.set_top(BY, w), FE.parity(R, FE.mul(R, x, zi)), PB, ep)
      Equal.trans(List<&2, U32>, PT.set_top(FE.to_bytes(R, FE.mul(R, y, zi)), FE.parity(R, FE.mul(R, x, zi))), PT.set_top(BY, PB), SE.set_msb(BY, PB), Equal.trans(List<&2, U32>, PT.set_top(FE.to_bytes(R, FE.mul(R, y, zi)), FE.parity(R, FE.mul(R, x, zi))), PT.set_top(BY, FE.parity(R, FE.mul(R, x, zi))), PT.set_top(BY, PB), e1, e2), set_eq(BY, PB))
