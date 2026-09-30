import Base
import ./field.bend as FS
import ./curve.bend as CS

# The affine group of secp256k1 (SEC 1 section 2.2.1): the points (x, y) of
# y^2 = x^3 + 7 over GF(p) and the point at infinity, with the chord and
# tangent addition. Nothing here is used by the implementation; the
# statements of proofs/crypto/secp256k1/laws_affine.bend relate it to the
# projective formulas of curve.bend.

type APoint is Data:
  AInf{}
  APt{x: Nat, y: Nat}

# y^2 == x^3 + 7 in GF(p); the point at infinity is on the curve
def on_curve(+p: Nat, a: APoint) -> Bool:
  match a:
    case AInf{}:
      True{}
    case APt{+x, +y}:
      CS.on_curve(p, x, y)

# on the curve, with coordinates below p
def valid(+p: Nat, a: APoint) -> Bool:
  match a:
    case AInf{}:
      True{}
    case APt{+x, +y}:
      Bool.and(CS.on_curve(p, x, y), Bool.and(Nat.is_lt(x, p), Nat.is_lt(y, p)))

# -(x, y) = (x, -y)
def neg(+p: Nat, a: APoint) -> APoint:
  match a:
    case AInf{}:
      AInf{}
    case APt{x, y}:
      APt{x, FS.mneg(p, y)}

# the slope of the chord through (x1, y1) and (x2, y2), x1 != x2
def chord(+p: Nat, x1: Nat, y1: Nat, x2: Nat, y2: Nat) -> Nat:
  FS.mmul(p, FS.msub(p, y2, y1), FS.minv(p, FS.msub(p, x2, x1)))

# the slope of the tangent at (x1, y1), y1 != 0
def tangent(+p: Nat, +x1: Nat, y1: Nat) -> Nat:
  FS.mmul(p, FS.mmul(p, 3n, FS.mmul(p, x1, x1)), FS.minv(p, FS.mmul(p, 2n, y1)))

def add_fin(+p: Nat, +x1: Nat, y1: Nat, lam: Nat, +x3: Nat) -> APoint:
  APt{x3, FS.msub(p, FS.mmul(p, lam, FS.msub(p, x1, x3)), y1)}

# x3 = lam^2 - x1 - x2, y3 = lam (x1 - x3) - y1
def add_lam(+p: Nat, +x1: Nat, y1: Nat, x2: Nat, +lam: Nat) -> APoint:
  add_fin(p, x1, y1, lam, FS.msub(p, FS.msub(p, FS.mmul(p, lam, lam), x1), x2))

# xeq: x1 == x2; dbl: y1 == y2 and y1 != 0 (in GF(p))
def add_pt(xeq: Bool, dbl: Bool, +p: Nat, +x1: Nat, +y1: Nat, +x2: Nat, y2: Nat) -> APoint:
  match xeq dbl:
    case False{} _:
      add_lam(p, x1, y1, x2, chord(p, x1, y1, x2, y2))
    case True{} True{}:
      add_lam(p, x1, y1, x2, tangent(p, x1, y1))
    case True{} False{}:
      AInf{}

def add(+p: Nat, a: APoint, b: APoint) -> APoint:
  match a b:
    case AInf{} b2:
      b2
    case APt{x1, y1} AInf{}:
      APt{x1, y1}
    case APt{+x1, +y1} APt{+x2, +y2}:
      add_pt(Nat.is_eq(Nat.mod(x1, p), Nat.mod(x2, p)), Bool.and(Nat.is_eq(Nat.mod(y1, p), Nat.mod(y2, p)), Bool.not(Nat.is_eq(Nat.mod(y1, p), 0n))), p, x1, y1, x2, y2)

def of_sel(i: Bool, +p: Nat, x: Nat, y: Nat, +zi: Nat) -> APoint:
  match i:
    case True{}:
      AInf{}
    case False{}:
      APt{FS.mmul(p, x, zi), FS.mmul(p, y, zi)}

# the affine point of a projective point (X : Y : Z): infinity when Z == 0
# in GF(p), otherwise (X / Z, Y / Z)
def of_proj(+p: Nat, a: CS.SPoint) -> APoint:
  match a:
    case CS.SPoint{x, y, +z}:
      of_sel(Nat.is_eq(Nat.mod(z, p), 0n), p, x, y, FS.minv(p, z))

# a projective point of an affine point: (x : y : 1), (0 : 1 : 0)
def to_proj(a: APoint) -> CS.SPoint:
  match a:
    case AInf{}:
      CS.SPoint{0n, 1n, 0n}
    case APt{x, y}:
      CS.SPoint{x, y, 1n}
