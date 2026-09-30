import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/x25519.bend as SX
import ../../../spec/crypto/curve25519/edwards.bend as G
import ../../../spec/crypto/ed25519.bend as SE
import ../../../spec/crypto/ed25519_group.bend as EG
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../../math/number/nt_prime.bend as PM
import ../secp256k1/group/fld.bend as F
import ./group/fq.bend as FQ
import ./fbgrp.bend as FG
import ./fbspec.bend as FB

# The group-law statements of fbspec.bend (LawE, LawQ): the table form of
# [k] B and the specification's double-and-add [k] B are valid points with
# the same affine point (fbgrp.bend), the encoding of a point is a function
# of its affine point, and so is its comparison with any other point.

# ---- the encoding ----

def enc_aff(+one: Nat, +p: Nat, +a: SE.EPt, +b: SE.EPt, +e: {EG.affine(p, a) == EG.affine(p, b) : G.APt}) -> {SE.encode(one, p, a) == SE.encode(one, p, b) : List<&2, U32>}:
  match a b:
    case SE.EPt{+x1, +y1, +z1, +t1} SE.EPt{+x2, +y2, +z2, +t2}:
      +N = C.shift(5n, one)
      +X1 = FS.fmul(p, x1, FS.finv(p, z1))
      +Y1 = FS.fmul(p, y1, FS.finv(p, z1))
      +X2 = FS.fmul(p, x2, FS.finv(p, z2))
      +Y2 = FS.fmul(p, y2, FS.finv(p, z2))
      +ex = Equal.cong(G.APt, Nat, w => G.ax(w), G.APt{X1, Y1}, G.APt{X2, Y2}, e)
      +ey = Equal.cong(G.APt, Nat, w => G.ay(w), G.APt{X1, Y1}, G.APt{X2, Y2}, e)
      Equal.trans(List<&2, U32>, SE.set_msb(SX.le_bytes(N, Y1), U32.from_nat(Nat.mod(X1, 2n))), SE.set_msb(SX.le_bytes(N, Y1), U32.from_nat(Nat.mod(X2, 2n))), SE.set_msb(SX.le_bytes(N, Y2), U32.from_nat(Nat.mod(X2, 2n))), Equal.cong(Nat, List<&2, U32>, w => SE.set_msb(SX.le_bytes(N, Y1), U32.from_nat(Nat.mod(w, 2n))), X1, X2, ex), Equal.cong(Nat, List<&2, U32>, w => SE.set_msb(SX.le_bytes(N, w), U32.from_nat(Nat.mod(X2, 2n))), Y1, Y2, ey))

# ---- the comparison ----

# (a b) c == (a c) b in the field
def rot3(+mp: Nat, +a: Nat, +b: Nat, +c: Nat) -> {FS.fmul(1n+mp, FS.fmul(1n+mp, a, b), c) == FS.fmul(1n+mp, FS.fmul(1n+mp, a, c), b) : Nat}:
  +P = {1n+mp : Nat}
  +e1 = NR.mod_mul_l(mp, Nat.mul(a, b), c)
  +e2 = NR.mod_mul_l(mp, Nat.mul(a, c), b)
  +e3 = Equal.trans(Nat, Nat.mul(Nat.mul(a, b), c), Nat.mul(a, Nat.mul(b, c)), Nat.mul(Nat.mul(a, c), b), NA.mul_assoc(a, b, c), Equal.trans(Nat, Nat.mul(a, Nat.mul(b, c)), Nat.mul(a, Nat.mul(c, b)), Nat.mul(Nat.mul(a, c), b), Equal.cong(Nat, Nat, z => Nat.mul(a, z), Nat.mul(b, c), Nat.mul(c, b), NA.mul_comm(b, c)), Equal.sym(Nat, Nat.mul(Nat.mul(a, c), b), Nat.mul(a, Nat.mul(c, b)), NA.mul_assoc(a, c, b))))
  Equal.trans(Nat, FS.fmul(P, FS.fmul(P, a, b), c), Nat.mod(Nat.mul(Nat.mul(a, b), c), P), FS.fmul(P, FS.fmul(P, a, c), b), e1, Equal.trans(Nat, Nat.mod(Nat.mul(Nat.mul(a, b), c), P), Nat.mod(Nat.mul(Nat.mul(a, c), b), P), FS.fmul(P, FS.fmul(P, a, c), b), Equal.cong(Nat, Nat, z => Nat.mod(z, P), Nat.mul(Nat.mul(a, b), c), Nat.mul(Nat.mul(a, c), b), e3), Equal.sym(Nat, FS.fmul(P, FS.fmul(P, a, c), b), Nat.mod(Nat.mul(Nat.mul(a, c), b), P), e2)))

# (n / z) z == n mod p
def div_mul(+mp: Nat, +hp: PM.Prime(1n+mp), +n: Nat, +z: Nat, +hz: F.NZ(mp, z)) -> {FS.fmul(1n+mp, FS.fmul(1n+mp, n, FS.finv(1n+mp, z)), z) == Nat.mod(n, 1n+mp) : Nat}:
  +W = FS.fmul(1n+mp, FS.fmul(1n+mp, n, FS.finv(1n+mp, z)), z)
  Equal.trans(Nat, W, Nat.mod(W, 1n+mp), Nat.mod(n, 1n+mp), Equal.sym(Nat, Nat.mod(W, 1n+mp), W, FQ.fmul_red(mp, FS.fmul(1n+mp, n, FS.finv(1n+mp, z)), z)), FQ.frac_mul(mp, hp, n, z, hz))

# (n z) / z == n mod p
def mul_div(+mp: Nat, +hp: PM.Prime(1n+mp), +n: Nat, +z: Nat, +hz: F.NZ(mp, z)) -> {FS.fmul(1n+mp, FS.fmul(1n+mp, n, z), FS.finv(1n+mp, z)) == Nat.mod(n, 1n+mp) : Nat}:
  Equal.trans(Nat, FS.fmul(1n+mp, FS.fmul(1n+mp, n, z), FS.finv(1n+mp, z)), FS.fmul(1n+mp, FS.fmul(1n+mp, n, FS.finv(1n+mp, z)), z), Nat.mod(n, 1n+mp), rot3(mp, n, z, FS.finv(1n+mp, z)), div_mul(mp, hp, n, z, hz))

# two Booleans that imply each other
def beq_of(+a: Bool, +b: Bool, f: @+h: {a == True{} : Bool} -> {b == True{} : Bool}, g: @+h: {b == True{} : Bool} -> {a == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, L.false_true(f({==})))
    case False{} True{}:
      g({==})
    case False{} False{}:
      {==}

def is_eq_of(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_eq(a, z) == True{} : Bool}, a, b, e, N.is_eq_refl(a))

# X1 Z2 == X2 Z1 exactly when (X1 / Z1) Z2 == X2 mod p
def cmp_fwd(+mp: Nat, +hp: PM.Prime(1n+mp), +x1: Nat, +z1: Nat, +x2: Nat, +z2: Nat, +hz: F.NZ(mp, z1), +h: {FS.fmul(1n+mp, x1, z2) == FS.fmul(1n+mp, x2, z1) : Nat}) -> {FS.fmul(1n+mp, FS.fmul(1n+mp, x1, FS.finv(1n+mp, z1)), z2) == Nat.mod(x2, 1n+mp) : Nat}:
  +P = {1n+mp : Nat}
  +zi = FS.finv(P, z1)
  +u = FS.fmul(P, x1, z2)
  +v = FS.fmul(P, x2, z1)
  Equal.trans(Nat, FS.fmul(P, FS.fmul(P, x1, zi), z2), FS.fmul(P, u, zi), Nat.mod(x2, P), Equal.sym(Nat, FS.fmul(P, u, zi), FS.fmul(P, FS.fmul(P, x1, zi), z2), rot3(mp, x1, z2, zi)), Equal.trans(Nat, FS.fmul(P, u, zi), FS.fmul(P, v, zi), Nat.mod(x2, P), Equal.cong(Nat, Nat, w => FS.fmul(P, w, zi), u, v, h), mul_div(mp, hp, x2, z1, hz)))

def cmp_bwd(+mp: Nat, +hp: PM.Prime(1n+mp), +x1: Nat, +z1: Nat, +x2: Nat, +z2: Nat, +hz: F.NZ(mp, z1), +h: {FS.fmul(1n+mp, FS.fmul(1n+mp, x1, FS.finv(1n+mp, z1)), z2) == Nat.mod(x2, 1n+mp) : Nat}) -> {FS.fmul(1n+mp, x1, z2) == FS.fmul(1n+mp, x2, z1) : Nat}:
  +P = {1n+mp : Nat}
  +zi = FS.finv(P, z1)
  +X1 = FS.fmul(P, x1, zi)
  +U2 = FS.fmul(P, X1, z2)
  +e1 = Equal.cong(Nat, Nat, w => FS.fmul(P, w, z1), U2, Nat.mod(x2, P), h)
  +e2 = NR.mod_mul_l(mp, x2, z1)
  +e3 = Equal.trans(Nat, FS.fmul(P, U2, z1), FS.fmul(P, FS.fmul(P, X1, z1), z2), FS.fmul(P, x1, z2), rot3(mp, X1, z2, z1), Equal.trans(Nat, FS.fmul(P, FS.fmul(P, X1, z1), z2), FS.fmul(P, Nat.mod(x1, P), z2), FS.fmul(P, x1, z2), Equal.cong(Nat, Nat, w => FS.fmul(P, w, z2), FS.fmul(P, X1, z1), Nat.mod(x1, P), div_mul(mp, hp, x1, z1, hz)), NR.mod_mul_l(mp, x1, z2)))
  Equal.trans(Nat, FS.fmul(P, x1, z2), FS.fmul(P, U2, z1), FS.fmul(P, x2, z1), Equal.sym(Nat, FS.fmul(P, U2, z1), FS.fmul(P, x1, z2), e3), Equal.trans(Nat, FS.fmul(P, U2, z1), FS.fmul(P, Nat.mod(x2, P), z1), FS.fmul(P, x2, z1), e1, e2))

def cmp_aff(+mp: Nat, +hp: PM.Prime(1n+mp), +x1: Nat, +z1: Nat, +x2: Nat, +z2: Nat, +hz: F.NZ(mp, z1)) -> {Nat.is_eq(FS.fmul(1n+mp, x1, z2), FS.fmul(1n+mp, x2, z1)) == Nat.is_eq(FS.fmul(1n+mp, FS.fmul(1n+mp, x1, FS.finv(1n+mp, z1)), z2), Nat.mod(x2, 1n+mp)) : Bool}:
  +P = {1n+mp : Nat}
  +u = FS.fmul(P, x1, z2)
  +v = FS.fmul(P, x2, z1)
  +U2 = FS.fmul(P, FS.fmul(P, x1, FS.finv(P, z1)), z2)
  +V2 = Nat.mod(x2, P)
  beq_of(Nat.is_eq(u, v), Nat.is_eq(U2, V2), h => is_eq_of(U2, V2, cmp_fwd(mp, hp, x1, z1, x2, z2, hz, N.eq_from_is_eq(u, v, h))), h => is_eq_of(u, v, cmp_bwd(mp, hp, x1, z1, x2, z2, hz, N.eq_from_is_eq(U2, V2, h))))

# the comparison of an affine point with an extended one
def eqa(+p: Nat, q: G.APt, b: SE.EPt) -> Bool:
  match q b:
    case G.APt{u, v} SE.EPt{x2, y2, +z2, t2}:
      Bool.and(Nat.is_eq(FS.fmul(p, u, z2), Nat.mod(x2, p)), Nat.is_eq(FS.fmul(p, v, z2), Nat.mod(y2, p)))

def band2(+a: Bool, +a2: Bool, +b: Bool, +b2: Bool, +ea: {a == a2 : Bool}, +eb: {b == b2 : Bool}) -> {Bool.and(a, b) == Bool.and(a2, b2) : Bool}:
  Equal.trans(Bool, Bool.and(a, b), Bool.and(a2, b), Bool.and(a2, b2), Equal.cong(Bool, Bool, z => Bool.and(z, b), a, a2, ea), Equal.cong(Bool, Bool, z => Bool.and(a2, z), b, b2, eb))

# Z != 0 from validity
def valid_nz(+mp: Nat, +d: Nat, +x: Nat, +y: Nat, +z: Nat, +t: Nat, +h: EG.Valid(1n+mp, d, SE.EPt{x, y, z, t})) -> F.NZ(mp, z):
  +P = {1n+mp : Nat}
  +X = FS.fmul(P, x, FS.finv(P, z))
  +Y = FS.fmul(P, y, FS.finv(P, z))
  L.not_true(Nat.is_eq(Nat.mod(z, P), 0n), L.and_left(Bool.not(Nat.is_eq(Nat.mod(z, P), 0n)), Bool.and(Nat.is_eq(G.lhs(P, X, Y), G.rhs(P, d, X, Y)), Nat.is_eq(FS.fmul(P, t, z), FS.fmul(P, x, y))), h))

# the specification's comparison of a valid point with any point, through
# the affine point
def equal_a(+mp: Nat, +d: Nat, +hp: PM.Prime(1n+mp), +a: SE.EPt, +b: SE.EPt, +ha: EG.Valid(1n+mp, d, a)) -> {SE.equal(1n+mp, a, b) == eqa(1n+mp, EG.affine(1n+mp, a), b) : Bool}:
  match a b:
    case SE.EPt{+x1, +y1, +z1, +t1} SE.EPt{+x2, +y2, +z2, +t2}:
      +P = {1n+mp : Nat}
      +hz = valid_nz(mp, d, x1, y1, z1, t1, ha)
      band2(Nat.is_eq(FS.fmul(P, x1, z2), FS.fmul(P, x2, z1)), Nat.is_eq(FS.fmul(P, FS.fmul(P, x1, FS.finv(P, z1)), z2), Nat.mod(x2, P)), Nat.is_eq(FS.fmul(P, y1, z2), FS.fmul(P, y2, z1)), Nat.is_eq(FS.fmul(P, FS.fmul(P, y1, FS.finv(P, z1)), z2), Nat.mod(y2, P)), cmp_aff(mp, hp, x1, z1, x2, z2, hz), cmp_aff(mp, hp, y1, z1, y2, z2, hz))

# valid points with the same affine point compare alike with any point
def equal_aff(+mp: Nat, +d: Nat, +hp: PM.Prime(1n+mp), +a: SE.EPt, +a2: SE.EPt, +b: SE.EPt, +ha: EG.Valid(1n+mp, d, a), +ha2: EG.Valid(1n+mp, d, a2), +e: {EG.affine(1n+mp, a) == EG.affine(1n+mp, a2) : G.APt}) -> {SE.equal(1n+mp, a, b) == SE.equal(1n+mp, a2, b) : Bool}:
  +P = {1n+mp : Nat}
  Equal.trans(Bool, SE.equal(P, a, b), eqa(P, EG.affine(P, a), b), SE.equal(P, a2, b), equal_a(mp, d, hp, a, b, ha), Equal.trans(Bool, eqa(P, EG.affine(P, a), b), eqa(P, EG.affine(P, a2), b), SE.equal(P, a2, b), Equal.cong(G.APt, Bool, w => eqa(P, w, b), EG.affine(P, a), EG.affine(P, a2), e), Equal.sym(Bool, SE.equal(P, a2, b), eqa(P, EG.affine(P, a2), b), equal_a(mp, d, hp, a2, b, ha2))))

# ---- the two statements, for a curve and a valid base point ----

# the table form and the double-and-add have the same affine point
def same_aff(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +q: G.APt, +hb: FG.VA(mp, d, SE.base(1n+mp, d), q), +bs: List<&2, U32>, +hs: {FS.bytes_ok(32n, bs) == True{} : Bool}) -> {EG.affine(1n+mp, FB.smulb(one, 1n+mp, d, bs)) == EG.affine(1n+mp, FB.smul(one, 1n+mp, d, bs)) : G.APt}:
  +P = {1n+mp : Nat}
  +B = SE.base(P, d)
  +X = G.nmul(P, d, FS.value(bs), q)
  +g1 = FG.va_smulb(one, h1, mp, d, hc, B, q, hb, bs, hs)
  +g2 = FG.va_mul(one, h1, mp, d, hc, B, q, hb, bs, hs)
  Equal.trans(G.APt, EG.affine(P, FB.smulb(one, P, d, bs)), X, EG.affine(P, FB.smul(one, P, d, bs)), FG.vE(mp, d, FB.smulb(one, P, d, bs), X, g1), Equal.sym(G.APt, EG.affine(P, FB.smul(one, P, d, bs)), X, FG.vE(mp, d, FB.smul(one, P, d, bs), X, g2)))

def law_e(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +q: G.APt, +hb: FG.VA(mp, d, SE.base(1n+mp, d), q), +bs: List<&2, U32>, +hs: {FS.bytes_ok(32n, bs) == True{} : Bool}) -> {SE.encode(one, 1n+mp, FB.smulb(one, 1n+mp, d, bs)) == SE.encode(one, 1n+mp, FB.smul(one, 1n+mp, d, bs)) : List<&2, U32>}:
  enc_aff(one, 1n+mp, FB.smulb(one, 1n+mp, d, bs), FB.smul(one, 1n+mp, d, bs), same_aff(one, h1, mp, d, hc, q, hb, bs, hs))

def law_q(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +q: G.APt, +hb: FG.VA(mp, d, SE.base(1n+mp, d), q), +bs: List<&2, U32>, +hs: {FS.bytes_ok(32n, bs) == True{} : Bool}, +r: SE.EPt) -> {SE.equal(1n+mp, FB.smulb(one, 1n+mp, d, bs), r) == SE.equal(1n+mp, FB.smul(one, 1n+mp, d, bs), r) : Bool}:
  +P = {1n+mp : Nat}
  +B = SE.base(P, d)
  +X = G.nmul(P, d, FS.value(bs), q)
  equal_aff(mp, d, FQ.cv_prime(mp, d, hc), FB.smulb(one, P, d, bs), FB.smul(one, P, d, bs), r, FG.vV(mp, d, FB.smulb(one, P, d, bs), X, FG.va_smulb(one, h1, mp, d, hc, B, q, hb, bs, hs)), FG.vV(mp, d, FB.smul(one, P, d, bs), X, FG.va_mul(one, h1, mp, d, hc, B, q, hb, bs, hs)), same_aff(one, h1, mp, d, hc, q, hb, bs, hs))
