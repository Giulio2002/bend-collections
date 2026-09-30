import Base
import ./curve25519/field.bend as FS
import ./curve25519/edwards.bend as G
import ./ed25519.bend as ED
import ../lib/common.bend as C

# Ed25519's points in extended coordinates (spec/crypto/ed25519.bend,
# RFC 8032 section 5.1.4) and the affine group of the curve
# (spec/crypto/curve25519/edwards.bend): what the specification's point
# addition, doubling and double-and-add compute, as statements about the
# group. These are the clauses that let a faster scalar multiplication
# (base-point tables, windows, Strauss/Shamir) be proved equal to the
# specification: compute the affine point of both sides in the group.
#
# The clauses are stated for p = FS.prime(one) = 1 + mp and
# d = ED.dconst(one, p) under the hypothesis G.Curve(mp, d) (p is an odd
# prime, d is not a square, sqm1 is a square root of -1), which is proved
# from the certificates of proofs/crypto/ed25519/group (cpar.bend,
# certa.bend, certda.bend, certia.bend: independent roots).
#
#   clause                   statement (a, b valid)
#   Ed25519.add_affine       affine(add(a, b)) == affine(a) + affine(b)
#   Ed25519.add_valid        add(a, b) is valid
#   Ed25519.double_affine    affine(double(a)) == affine(a) + affine(a)
#   Ed25519.double_valid     double(a) is valid
#   Ed25519.identity         affine(identity()) == (0, 1), and it is valid
#   Ed25519.mul_affine       affine(mul(k, a)) == [k mod 2^256] affine(a)
#   Ed25519.mul_valid        mul(k, a) is valid
#   Ed25519.affine_on        the affine point of a valid point is on the curve

# ---- extended coordinates ----

# (X : Y : Z : T) stands for (X / Z, Y / Z)
def affine(+p: Nat, a: ED.EPt) -> G.APt:
  match a:
    case ED.EPt{x, y, +z, t}:
      G.APt{FS.fmul(p, x, FS.finv(p, z)), FS.fmul(p, y, FS.finv(p, z))}

# Z != 0, (X / Z, Y / Z) on the curve and T Z == X Y
def valid(+p: Nat, +d: Nat, a: ED.EPt) -> Bool:
  match a:
    case ED.EPt{+x, +y, +z, +t}:
      Bool.and(Bool.not(Nat.is_eq(Nat.mod(z, p), 0n)),
        Bool.and(Nat.is_eq(G.lhs(p, FS.fmul(p, x, FS.finv(p, z)), FS.fmul(p, y, FS.finv(p, z))), G.rhs(p, d, FS.fmul(p, x, FS.finv(p, z)), FS.fmul(p, y, FS.finv(p, z)))),
          Nat.is_eq(FS.fmul(p, t, z), FS.fmul(p, x, y))))

def Valid(+p: Nat, +d: Nat, +a: ED.EPt) -> Data:
  {valid(p, d, a) == True{} : Bool}

# ---- clauses ----

def AddAffine(+p: Nat, +d: Nat, +a: ED.EPt, +b: ED.EPt) -> Type:
  {affine(p, ED.add(p, d, a, b)) == G.aadd(p, d, affine(p, a), affine(p, b)) : G.APt}

def DoubleAffine(+p: Nat, +d: Nat, +a: ED.EPt) -> Type:
  {affine(p, ED.double(p, a)) == G.aadd(p, d, affine(p, a), affine(p, a)) : G.APt}

def IdentityAffine(+p: Nat) -> Type:
  {affine(p, ED.identity()) == G.azero() : G.APt}

# 2^8 one bits of the scalar are read (one == 1)
def MulAffine(+one: Nat, +p: Nat, +d: Nat, +k: Nat, +a: ED.EPt) -> Type:
  {affine(p, ED.mul(one, p, d, k, a)) == G.nmul(p, d, C.low(C.shift(8n, one), k), affine(p, a)) : G.APt}

def Ed25519.add_affine(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}, +hc: G.Curve(mp, ED.dconst(one, FS.prime(one))), +a: ED.EPt, +b: ED.EPt, +ha: Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), a), +hb: Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), b)) -> Type:
  AddAffine(FS.prime(one), ED.dconst(one, FS.prime(one)), a, b)

def Ed25519.add_valid(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}, +hc: G.Curve(mp, ED.dconst(one, FS.prime(one))), +a: ED.EPt, +b: ED.EPt, +ha: Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), a), +hb: Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), b)) -> Type:
  Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), ED.add(FS.prime(one), ED.dconst(one, FS.prime(one)), a, b))

def Ed25519.double_affine(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}, +hc: G.Curve(mp, ED.dconst(one, FS.prime(one))), +a: ED.EPt, +ha: Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), a)) -> Type:
  DoubleAffine(FS.prime(one), ED.dconst(one, FS.prime(one)), a)

def Ed25519.double_valid(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}, +hc: G.Curve(mp, ED.dconst(one, FS.prime(one))), +a: ED.EPt, +ha: Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), a)) -> Type:
  Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), ED.double(FS.prime(one), a))

def Ed25519.identity(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}, +hc: G.Curve(mp, ED.dconst(one, FS.prime(one)))) -> Type:
  IdentityAffine(FS.prime(one))

def Ed25519.identity_valid(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}, +hc: G.Curve(mp, ED.dconst(one, FS.prime(one)))) -> Type:
  Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), ED.identity())

def Ed25519.mul_affine(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}, +hc: G.Curve(mp, ED.dconst(one, FS.prime(one))), +k: Nat, +a: ED.EPt, +ha: Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), a)) -> Type:
  MulAffine(one, FS.prime(one), ED.dconst(one, FS.prime(one)), k, a)

def Ed25519.mul_valid(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}, +hc: G.Curve(mp, ED.dconst(one, FS.prime(one))), +k: Nat, +a: ED.EPt, +ha: Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), a)) -> Type:
  Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), ED.mul(one, FS.prime(one), ED.dconst(one, FS.prime(one)), k, a))

def Ed25519.affine_on(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}, +hc: G.Curve(mp, ED.dconst(one, FS.prime(one))), +a: ED.EPt, +ha: Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), a)) -> Type:
  G.OnCurve(FS.prime(one), ED.dconst(one, FS.prime(one)), affine(FS.prime(one), a))
