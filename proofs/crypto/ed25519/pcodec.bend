import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/x25519.bend as SX
import ../../../spec/crypto/ed25519.bend as SE
import ../../../src/crypto/curve25519/field.bend as F
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../../src/crypto/ed25519/point.bend as PT
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/u32.bend as U
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../curve25519/limbs.bend as LM
import ../curve25519/consts.bend as K
import ../curve25519/fieldops.bend as FO
import ../curve25519/mulw.bend as MW
import ../curve25519/pow.bend as PW
import ../curve25519/canon.bend as CN
import ../curve25519/eqf.bend as EQ
import ../curve25519/freeze.bend as FZ
import ../curve25519/cong.bend as G
import ../curve25519/rel.bend as RL
import ../curve25519/xbits.bend as XB
import ../curve25519/ladder.bend as LD
import ./scalar.bend as SC
import ./prel.bend as PR
import ../curve25519/num.bend as M2

# Constants, encoding (5.1.2), decoding (5.1.3), equality and the base
# point of src/crypto/ed25519/point.bend against spec/crypto/ed25519.bend.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# decoding results: both None, or both Some of related points
def MR(+pp: Nat, +m: Maybe<&2, PT.Pt>, +sm: Maybe<&2, SE.EPt>) -> Data:
  match m sm:
    case None{} None{}:
      {True{} == True{} : Bool}
    case Some{p} Some{sp}:
      PR.Rp(pp, p, sp)
    case None{} Some{sp}:
      {True{} == False{} : Bool}
    case Some{p} None{}:
      {True{} == False{} : Bool}

# ---- small constants ----

def r_zero(+pp: Nat) -> RL.R(pp, F.zero(), 0n):
  ({==}, G.c_refl(pp, 0n))

def r_one(+pp: Nat) -> RL.R(pp, F.one(), 1n):
  ({==}, G.c_refl(pp, 1n))

def r_small(+pp: Nat, +k: U32, +hk: {Nat.is_le(v(k), 255n) == True{} : Bool}) -> RL.R(pp, F.small(k), v(k)):
  (L.and_intro(Nat.is_le(v(k), 255n), LM.okb(31n, K.rep(31n, 0, Nil{}), 255n), hk, {==}), G.c_eq(pp, FS.value(F.small(k)), v(k), Equal.trans(Nat, FS.value(F.small(k)), Nat.add(v(k), 0n), v(k), {==}, N.add_zero(v(k)))))

def c65_shape() -> {PT.c121665() == Con{65, Con{219, Con{1, K.rep(29n, 0, Nil{})}}} : List<&2, U32>}:
  {==}

def c66_shape() -> {PT.c121666() == Con{66, Con{219, Con{1, K.rep(29n, 0, Nil{})}}} : List<&2, U32>}:
  {==}

def c65_valo(+one: Nat) -> {K.valo(one, PT.c121665()) == FS.digits(one, [65n, 219n, 1n]) : Nat}:
  %Equal.sym(List<&2, U32>, PT.c121665(), Con{65, Con{219, Con{1, K.rep(29n, 0, Nil{})}}}, c65_shape()) : {K.valo(one, _) == FS.digits(one, [65n, 219n, 1n]) : Nat}
  %Equal.sym(Nat, K.valo(one, K.rep(29n, 0, Nil{})), 0n, K.run0(one, 29n, Nil{})) : {Nat.add(Nat.mul(one, v(65)), C.shift(8n, Nat.add(Nat.mul(one, v(219)), C.shift(8n, Nat.add(Nat.mul(one, v(1)), C.shift(8n, _)))))) == FS.digits(one, [65n, 219n, 1n]) : Nat}
  {==}

def c66_valo(+one: Nat) -> {K.valo(one, PT.c121666()) == FS.digits(one, [66n, 219n, 1n]) : Nat}:
  %Equal.sym(List<&2, U32>, PT.c121666(), Con{66, Con{219, Con{1, K.rep(29n, 0, Nil{})}}}, c66_shape()) : {K.valo(one, _) == FS.digits(one, [66n, 219n, 1n]) : Nat}
  %Equal.sym(Nat, K.valo(one, K.rep(29n, 0, Nil{})), 0n, K.run0(one, 29n, Nil{})) : {Nat.add(Nat.mul(one, v(66)), C.shift(8n, Nat.add(Nat.mul(one, v(219)), C.shift(8n, Nat.add(Nat.mul(one, v(1)), C.shift(8n, _)))))) == FS.digits(one, [66n, 219n, 1n]) : Nat}
  {==}

# a constant given through its valo, the list kept a variable
def r_valo(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +ks: List<&2, U32>, +D: Nat, +hv: {K.valo(one, ks) == D : Nat}, +ho: {LM.okb(32n, ks, 255n) == True{} : Bool}) -> RL.R(pp, ks, D):
  (ho, G.c_eq(pp, FS.value(ks), D, Equal.trans(Nat, FS.value(ks), K.valo(one, ks), D, Equal.sym(Nat, K.valo(one, ks), FS.value(ks), K.valo_value(one, h1, ks)), hv)))

def lit_valo(+one: Nat, +xs: List<&2, U32>, +k: List<&2, U32>, +D: Nat, +hv: {K.valo(one, k) == D : Nat}) -> {K.valo(one, PT.lit(xs, k)) == D : Nat}:
  match xs:
    case Nil{}:
      hv
    case Con{h, t}:
      hv

def lit_okb(+xs: List<&2, U32>, +k: List<&2, U32>, +ho: {LM.okb(32n, k, 255n) == True{} : Bool}) -> {LM.okb(32n, PT.lit(xs, k), 255n) == True{} : Bool}:
  match xs:
    case Nil{}:
      ho
    case Con{h, t}:
      ho

def r_lit_small(+pp: Nat, +xs: List<&2, U32>, +k: U32, +hk: {Nat.is_le(v(k), 255n) == True{} : Bool}) -> RL.R(pp, PT.lit(xs, F.small(k)), v(k)):
  match xs:
    case Nil{}:
      r_small(pp, k, hk)
    case Con{h, t}:
      r_small(pp, k, hk)

def r_c65(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +xs: List<&2, U32>) -> RL.R(pp, PT.lit(xs, PT.c121665()), FS.digits(one, [65n, 219n, 1n])):
  r_valo(one, h1, pp, PT.lit(xs, PT.c121665()), FS.digits(one, [65n, 219n, 1n]), lit_valo(one, xs, PT.c121665(), FS.digits(one, [65n, 219n, 1n]), c65_valo(one)), lit_okb(xs, PT.c121665(), {==}))

def r_c66(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +xs: List<&2, U32>) -> RL.R(pp, PT.lit(xs, PT.c121666()), FS.digits(one, [66n, 219n, 1n])):
  r_valo(one, h1, pp, PT.lit(xs, PT.c121666()), FS.digits(one, [66n, 219n, 1n]), lit_valo(one, xs, PT.c121666(), FS.digits(one, [66n, 219n, 1n]), c66_valo(one)), lit_okb(xs, PT.c121666(), {==}))

# ---- d, 2 d, sqrt(-1) ----

def dval(+xs: List<&2, U32>) -> List<&2, U32>:
  F.mul(F.neg(PT.lit(xs, PT.c121665())), F.inv(PT.lit(xs, PT.c121666())))

def r_d(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +xs: List<&2, U32>) -> RL.R(pp, PT.cs_d(PT.consts(xs)), SE.dconst(one, 1n+pp)):
  +P = {1n+pp : Nat}
  +D65 = FS.digits(one, [65n, 219n, 1n])
  +D66 = FS.digits(one, [66n, 219n, 1n])
  +r66 = r_c66(one, h1, pp, xs)
  PR.rmul(one, h1, pp, hP, F.neg(PT.lit(xs, PT.c121665())), F.inv(PT.lit(xs, PT.c121666())), FS.fsub(P, 0n, D65), FS.finv(P, D66), PR.rsub(one, h1, pp, hP, F.zero(), PT.lit(xs, PT.c121665()), 0n, D65, r_zero(pp), r_c65(one, h1, pp, xs)), RL.r_inv(one, h1, pp, hP, PT.lit(xs, PT.c121666()), D66, RL.r_o(pp, PT.lit(xs, PT.c121666()), D66, r66), RL.r_c(pp, PT.lit(xs, PT.c121666()), D66, r66)))

def r_d2(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +xs: List<&2, U32>) -> RL.R(pp, PT.cs_d2(PT.consts(xs)), FS.fadd(1n+pp, SE.dconst(one, 1n+pp), SE.dconst(one, 1n+pp))):
  PR.radd(one, h1, pp, hP, dval(xs), dval(xs), SE.dconst(one, 1n+pp), SE.dconst(one, 1n+pp), r_d(one, h1, pp, hP, xs), r_d(one, h1, pp, hP, xs))

def p14_bits() -> List<&2, Bool>:
  [False{}, True{}, True{}]

def eb_p14(+one: Nat, +h1: {one == 1n : Nat}) -> {PW.eb(one, p14_bits()) == 3n : Nat}:
  L.subst(Nat, o => {PW.eb(o, p14_bits()) == 3n : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})

# 8 Fo(250) + 3 == (p - 1) / 4
def p14_exp(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}) -> {Nat.add(Nat.mul(PW.Fo(one, 250n), WD.sc(PW.blen(p14_bits()), one)), PW.eb(one, p14_bits())) == Nat.div(Nat.sub(1n+pp, 1n), 4n) : Nat}:
  +F2 = PW.Fo(one, 250n)
  +P = {1n+pp : Nat}
  %Equal.sym(Nat, WD.sc(3n, one), 8n, PW.small_one(one, h1, 3n, 8n, {==})) : {Nat.add(Nat.mul(F2, _), PW.eb(one, p14_bits())) == Nat.div(Nat.sub(P, 1n), 4n) : Nat}
  %Equal.sym(Nat, PW.eb(one, p14_bits()), 3n, eb_p14(one, h1)) : {Nat.add(Nat.mul(F2, 8n), _) == Nat.div(Nat.sub(P, 1n), 4n) : Nat}
  +e = Nat.add(Nat.mul(F2, 8n), 3n)
  +m4 = Equal.trans(Nat, Nat.mul(e, 4n), Nat.add(Nat.mul(Nat.mul(F2, 8n), 4n), Nat.mul(3n, 4n)), Nat.add(Nat.mul(F2, 32n), 12n), NA.mul_add_right(Nat.mul(F2, 8n), 3n, 4n), M2.cong_l(Nat.mul(Nat.mul(F2, 8n), 4n), Nat.mul(F2, 32n), Nat.mul(3n, 4n), NA.mul_assoc(F2, 8n, 4n)))
  +e1 = Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(e, 4n), 1n), 19n), Nat.add(Nat.add(Nat.add(Nat.mul(F2, 32n), 12n), 1n), 19n), Nat.add(P, 19n), M2.cong_l(Nat.add(Nat.mul(e, 4n), 1n), Nat.add(Nat.add(Nat.mul(F2, 32n), 12n), 1n), 19n, M2.cong_l(Nat.mul(e, 4n), Nat.add(Nat.mul(F2, 32n), 12n), 1n, m4)),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.mul(F2, 32n), 12n), 1n), 19n), Nat.add(Nat.mul(F2, 32n), 32n), Nat.add(P, 19n), Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.mul(F2, 32n), 12n), 1n), 19n), Nat.add(Nat.add(Nat.mul(F2, 32n), 12n), Nat.add(1n, 19n)), Nat.add(Nat.mul(F2, 32n), 32n), NA.add_assoc(Nat.add(Nat.mul(F2, 32n), 12n), 1n, 19n), NA.add_assoc(Nat.mul(F2, 32n), 12n, 20n)), PW.f32(one, h1, pp, hP)))
  +e2 = G.cancel_r(Nat.add(Nat.mul(e, 4n), 1n), P, 19n, e1)
  +e3 = Equal.trans(Nat, P, Nat.add(Nat.mul(e, 4n), 1n), Nat.add(1n, Nat.mul(e, 4n)), Equal.sym(Nat, Nat.add(Nat.mul(e, 4n), 1n), P, e2), NA.add_comm(Nat.mul(e, 4n), 1n))
  %Equal.sym(Nat, P, Nat.add(1n, Nat.mul(e, 4n)), e3) : {e == Nat.div(Nat.sub(_, 1n), 4n) : Nat}
  %Equal.sym(Nat, Nat.sub(Nat.add(1n, Nat.mul(e, 4n)), 1n), Nat.mul(e, 4n), N.add_sub_cancel(1n, Nat.mul(e, 4n))) : {e == Nat.div(_, 4n) : Nat}
  %N.add_zero(Nat.mul(e, 4n)) : {e == Nat.div(_, 4n) : Nat}
  Equal.sym(Nat, Nat.div(Nat.add(Nat.mul(e, 4n), 0n), 4n), e, NR.div_of(e, 3n, 0n, {==}))

def r_sqm1(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +xs: List<&2, U32>) -> RL.R(pp, PT.cs_s(PT.consts(xs)), SE.sqm1(1n+pp)):
  +P = {1n+pp : Nat}
  +two = PT.lit(xs, F.small(2))
  +ex = Nat.add(Nat.mul(PW.Fo(one, 250n), WD.sc(PW.blen(p14_bits()), one)), PW.eb(one, p14_bits()))
  +k = Nat.div(Nat.sub(P, 1n), 4n)
  +o2 = RL.r_o(pp, two, 2n, r_lit_small(pp, xs, 2, {==}))
  +r2 = r_lit_small(pp, xs, 2, {==})
  +c1 = PW.chain_val(one, h1, pp, hP, 249n, p14_bits(), two, o2)
  +c1b = G.c_trans(pp, FS.value(PT.pow_p14(two)), Nat.pow(FS.value(two), ex), Nat.pow(2n, ex), c1, G.c_pow(pp, FS.value(two), 2n, ex, RL.r_c(pp, two, 2n, r2)))
  +c2 = G.c_eq(pp, Nat.pow(2n, ex), Nat.pow(2n, k), Equal.cong(Nat, Nat, t => Nat.pow(2n, t), ex, k, p14_exp(one, h1, pp, hP)))
  +c3 = G.c_sym(pp, FS.fpow(P, 2n, k), Nat.pow(2n, k), G.c_mod(pp, Nat.pow(2n, k)))
  (PW.pbs_okb(one, h1, p14_bits(), two, F.pow_ones(two, 249n, two), o2, PW.po_okb(one, h1, 249n, two, two, o2, o2)), G.c_trans(pp, FS.value(PT.pow_p14(two)), Nat.pow(2n, ex), FS.fpow(P, 2n, k), c1b, G.c_trans(pp, Nat.pow(2n, ex), Nat.pow(2n, k), FS.fpow(P, 2n, k), c2, c3)))

# ---- equality of reduced values ----

def red(+pp: Nat, +a: Nat) -> {Nat.mod(Nat.mod(a, 1n+pp), 1n+pp) == Nat.mod(a, 1n+pp) : Nat}:
  NR.mod_mod(pp, a)

def eq_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +y: List<&2, U32>, +a: Nat, +b: Nat, +rx: RL.R(pp, x, a), +ry: RL.R(pp, y, b), +ha: {Nat.mod(a, 1n+pp) == a : Nat}, +hb: {Nat.mod(b, 1n+pp) == b : Nat}) -> {F.eq(x, y) == Nat.is_eq(a, b) : Bool}:
  +e1 = EQ.eq_val(one, h1, pp, hP, x, y, RL.r_o(pp, x, a, rx), RL.r_o(pp, y, b, ry))
  +ea = Equal.trans(Nat, Nat.mod(FS.value(x), 1n+pp), Nat.mod(a, 1n+pp), a, RL.r_c(pp, x, a, rx), ha)
  +eb = Equal.trans(Nat, Nat.mod(FS.value(y), 1n+pp), Nat.mod(b, 1n+pp), b, RL.r_c(pp, y, b, ry), hb)
  Equal.trans(Bool, F.eq(x, y), Nat.is_eq(Nat.mod(FS.value(x), 1n+pp), Nat.mod(FS.value(y), 1n+pp)), Nat.is_eq(a, b), e1, Equal.trans(Bool, Nat.is_eq(Nat.mod(FS.value(x), 1n+pp), Nat.mod(FS.value(y), 1n+pp)), Nat.is_eq(a, Nat.mod(FS.value(y), 1n+pp)), Nat.is_eq(a, b), Equal.cong(Nat, Bool, z => Nat.is_eq(z, Nat.mod(FS.value(y), 1n+pp)), Nat.mod(FS.value(x), 1n+pp), a, ea), Equal.cong(Nat, Bool, z => Nat.is_eq(a, z), Nat.mod(FS.value(y), 1n+pp), b, eb)))

def iz_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +a: Nat, +rx: RL.R(pp, x, a), +ha: {Nat.mod(a, 1n+pp) == a : Nat}) -> {F.is_zero(x) == Nat.is_eq(a, 0n) : Bool}:
  +e1 = CN.is_zero_val(one, h1, pp, hP, x, RL.r_o(pp, x, a, rx))
  Equal.trans(Bool, F.is_zero(x), Nat.is_eq(Nat.mod(FS.value(x), 1n+pp), 0n), Nat.is_eq(a, 0n), e1, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), Nat.mod(FS.value(x), 1n+pp), a, Equal.trans(Nat, Nat.mod(FS.value(x), 1n+pp), Nat.mod(a, 1n+pp), a, RL.r_c(pp, x, a, rx), ha)))

def par_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +a: Nat, +rx: RL.R(pp, x, a), +ha: {Nat.mod(a, 1n+pp) == a : Nat}) -> {v(F.parity(x)) == Nat.mod(a, 2n) : Nat}:
  Equal.trans(Nat, v(F.parity(x)), Nat.mod(Nat.mod(FS.value(x), 1n+pp), 2n), Nat.mod(a, 2n), CN.parity_val(one, h1, pp, hP, x, RL.r_o(pp, x, a, rx)), Equal.cong(Nat, Nat, z => Nat.mod(z, 2n), Nat.mod(FS.value(x), 1n+pp), a, Equal.trans(Nat, Nat.mod(FS.value(x), 1n+pp), Nat.mod(a, 1n+pp), a, RL.r_c(pp, x, a, rx), ha)))

def u32_eq_nat(+a: U32, +b: U32) -> {U32.is_eq(a, b) == Nat.is_eq(v(a), v(b)) : Bool}:
  Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), U32.cmp(a, b), Nat.cmp(v(a), v(b)), U.u32_cmp(a, b))

def mod2_le(+a: Nat) -> {Nat.is_le(Nat.mod(a, 2n), 1n) == True{} : Bool}:
  N.lt_succ_le(Nat.mod(a, 2n), 1n, NR.dm_lt(1n, a))

# ---- the point equality ----

def equal_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +p: PT.Pt, +q: PT.Pt, +sp: SE.EPt, +sq: SE.EPt, +hp: PR.Rp(pp, p, sp), +hq: PR.Rp(pp, q, sq)) -> {PT.equal(p, q) == SE.equal(1n+pp, sp, sq) : Bool}:
  match p q sp sq:
    case PT.Pt{+x1, +y1, +z1, +t1} PT.Pt{+x2, +y2, +z2, +t2} SE.EPt{+a1, +b1, +c1, +d1} SE.EPt{+a2, +b2, +c2, +d2}:
      +P = {1n+pp : Nat}
      +rx1 = PR.rX(pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +ry1 = PR.rY(pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +rz1 = PR.rZ(pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +rx2 = PR.rX(pp, x2, y2, z2, t2, a2, b2, c2, d2, hq)
      +ry2 = PR.rY(pp, x2, y2, z2, t2, a2, b2, c2, d2, hq)
      +rz2 = PR.rZ(pp, x2, y2, z2, t2, a2, b2, c2, d2, hq)
      +e1 = eq_rel(one, h1, pp, hP, F.mul(x1, z2), F.mul(x2, z1), FS.fmul(P, a1, c2), FS.fmul(P, a2, c1), PR.rmul(one, h1, pp, hP, x1, z2, a1, c2, rx1, rz2), PR.rmul(one, h1, pp, hP, x2, z1, a2, c1, rx2, rz1), red(pp, Nat.mul(a1, c2)), red(pp, Nat.mul(a2, c1)))
      +e2 = eq_rel(one, h1, pp, hP, F.mul(y1, z2), F.mul(y2, z1), FS.fmul(P, b1, c2), FS.fmul(P, b2, c1), PR.rmul(one, h1, pp, hP, y1, z2, b1, c2, ry1, rz2), PR.rmul(one, h1, pp, hP, y2, z1, b2, c1, ry2, rz1), red(pp, Nat.mul(b1, c2)), red(pp, Nat.mul(b2, c1)))
      Equal.trans(Bool, Bool.and(F.eq(F.mul(x1, z2), F.mul(x2, z1)), F.eq(F.mul(y1, z2), F.mul(y2, z1))), Bool.and(Nat.is_eq(FS.fmul(P, a1, c2), FS.fmul(P, a2, c1)), F.eq(F.mul(y1, z2), F.mul(y2, z1))), Bool.and(Nat.is_eq(FS.fmul(P, a1, c2), FS.fmul(P, a2, c1)), Nat.is_eq(FS.fmul(P, b1, c2), FS.fmul(P, b2, c1))), Equal.cong(Bool, Bool, z => Bool.and(z, F.eq(F.mul(y1, z2), F.mul(y2, z1))), F.eq(F.mul(x1, z2), F.mul(x2, z1)), Nat.is_eq(FS.fmul(P, a1, c2), FS.fmul(P, a2, c1)), e1), Equal.cong(Bool, Bool, z => Bool.and(Nat.is_eq(FS.fmul(P, a1, c2), FS.fmul(P, a2, c1)), z), F.eq(F.mul(y1, z2), F.mul(y2, z1)), Nat.is_eq(FS.fmul(P, b1, c2), FS.fmul(P, b2, c1)), e2))

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
def bytes_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +a: Nat, +rx: RL.R(pp, x, a), +ha: {Nat.mod(a, 1n+pp) == a : Nat}) -> {F.to_bytes(x) == SX.le_bytes(32n, a) : List<&2, U32>}:
  +y = F.freeze(x)
  +oy = CN.freeze_okb(one, h1, pp, hP, x, RL.r_o(pp, x, a, rx))
  +ey = Equal.trans(Nat, FS.value(y), Nat.mod(FS.value(x), 1n+pp), a, CN.freeze_val(one, h1, pp, hP, x, RL.r_o(pp, x, a, rx)), Equal.trans(Nat, Nat.mod(FS.value(x), 1n+pp), Nat.mod(a, 1n+pp), a, RL.r_c(pp, x, a, rx), ha))
  Equal.trans(List<&2, U32>, y, SX.le_bytes(32n, FS.value(y)), SX.le_bytes(32n, a), Equal.sym(List<&2, U32>, SX.le_bytes(32n, FS.value(y)), y, XB.bytes_le(32n, y, oy)), Equal.cong(Nat, List<&2, U32>, z => SX.le_bytes(32n, z), FS.value(y), a, ey))

def par_u32(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +a: Nat, +rx: RL.R(pp, x, a), +ha: {Nat.mod(a, 1n+pp) == a : Nat}) -> {F.parity(x) == U32.from_nat(Nat.mod(a, 2n)) : U32}:
  +e = par_rel(one, h1, pp, hP, x, a, rx, ha)
  +lt = NR.dm_lt(1n, a)
  U.injective(F.parity(x), U32.from_nat(Nat.mod(a, 2n)), Equal.trans(Nat, v(F.parity(x)), Nat.mod(a, 2n), v(U32.from_nat(Nat.mod(a, 2n))), e, Equal.sym(Nat, v(U32.from_nat(Nat.mod(a, 2n))), Nat.mod(a, 2n), U.to_nat_from_nat(Nat.mod(a, 2n), 1n, {==}, lt))))

def encode_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +p: PT.Pt, +sp: SE.EPt, +hp: PR.Rp(pp, p, sp)) -> {PT.encode(p) == SE.encode_n(32n, 1n+pp, sp) : List<&2, U32>}:
  match p sp:
    case PT.Pt{+x, +y, +z, +t} SE.EPt{+a, +b, +c, +d}:
      +P = {1n+pp : Nat}
      +rx = PR.rX(pp, x, y, z, t, a, b, c, d, hp)
      +ry = PR.rY(pp, x, y, z, t, a, b, c, d, hp)
      +rz = PR.rZ(pp, x, y, z, t, a, b, c, d, hp)
      +zi = F.inv(z)
      +ZI = FS.finv(P, c)
      +rzi = RL.r_inv(one, h1, pp, hP, z, c, RL.r_o(pp, z, c, rz), RL.r_c(pp, z, c, rz))
      +my = PR.rmul(one, h1, pp, hP, y, zi, b, ZI, ry, rzi)
      +mx = PR.rmul(one, h1, pp, hP, x, zi, a, ZI, rx, rzi)
      +eb = bytes_rel(one, h1, pp, hP, F.mul(y, zi), FS.fmul(P, b, ZI), my, red(pp, Nat.mul(b, ZI)))
      +ep = par_u32(one, h1, pp, hP, F.mul(x, zi), FS.fmul(P, a, ZI), mx, red(pp, Nat.mul(a, ZI)))
      +e1 = Equal.cong(List<&2, U32>, List<&2, U32>, w => PT.set_top(w, F.parity(F.mul(x, zi))), F.to_bytes(F.mul(y, zi)), SX.le_bytes(32n, FS.fmul(P, b, ZI)), eb)
      +e2 = Equal.cong(U32, List<&2, U32>, w => PT.set_top(SX.le_bytes(32n, FS.fmul(P, b, ZI)), w), F.parity(F.mul(x, zi)), U32.from_nat(Nat.mod(FS.fmul(P, a, ZI), 2n)), ep)
      Equal.trans(List<&2, U32>, PT.set_top(F.to_bytes(F.mul(y, zi)), F.parity(F.mul(x, zi))), PT.set_top(SX.le_bytes(32n, FS.fmul(P, b, ZI)), U32.from_nat(Nat.mod(FS.fmul(P, a, ZI), 2n))), SE.set_msb(SX.le_bytes(32n, FS.fmul(P, b, ZI)), U32.from_nat(Nat.mod(FS.fmul(P, a, ZI), 2n))), Equal.trans(List<&2, U32>, PT.set_top(F.to_bytes(F.mul(y, zi)), F.parity(F.mul(x, zi))), PT.set_top(SX.le_bytes(32n, FS.fmul(P, b, ZI)), F.parity(F.mul(x, zi))), PT.set_top(SX.le_bytes(32n, FS.fmul(P, b, ZI)), U32.from_nat(Nat.mod(FS.fmul(P, a, ZI), 2n))), e1, e2), set_eq(SX.le_bytes(32n, FS.fmul(P, b, ZI)), U32.from_nat(Nat.mod(FS.fmul(P, a, ZI), 2n))))
