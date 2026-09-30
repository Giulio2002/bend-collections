import Base
import ./field.bend as FS
import ./curve.bend as CS

# The group of secp256k1 on the projective points of curve.bend, as the
# statements of the group law (proofs/crypto/secp256k1/laws_group.bend) need
# it. Nothing here is used by the implementation or by the other
# specifications.
#
# A point (X : Y : Z) is on the curve when Y^2 Z = X^3 + 7 Z^3 in GF(p)
# (the homogeneous form of y^2 = x^3 + 7, SEC 2 section 2.4.1). It is a
# point of the group when moreover Y != 0: on this curve a triple with
# Y = 0 is (0, 0, 0), which is no projective point (X^3 = -7 Z^3 has only
# the solution X = Z = 0, since -7 is not a cube modulo p); the point at
# infinity is (0 : 1 : 0).
#
# Two points are the same projective point when their coordinates are
# proportional; for points with Y != 0 that is X1 Y2 = X2 Y1 and
# Z1 Y2 = Z2 Y1 (the cross products with Y).

def on_curve(+p: Nat, a: CS.SPoint) -> Bool:
  match a:
    case CS.SPoint{+x, +y, +z}:
      Nat.is_eq(FS.mmul(p, FS.mmul(p, y, y), z), FS.madd(p, FS.mmul(p, FS.mmul(p, x, x), x), FS.mmul(p, 7n, FS.mmul(p, FS.mmul(p, z, z), z))))

def y_nonzero(+p: Nat, a: CS.SPoint) -> Bool:
  match a:
    case CS.SPoint{x, y, z}:
      Bool.not(Nat.is_eq(Nat.mod(y, p), 0n))

# a point of the group
def valid(+p: Nat, +a: CS.SPoint) -> Bool:
  Bool.and(on_curve(p, a), y_nonzero(p, a))

# the same projective point
def equiv(+p: Nat, a: CS.SPoint, b: CS.SPoint) -> Bool:
  match a b:
    case CS.SPoint{x1, +y1, z1} CS.SPoint{x2, +y2, z2}:
      Bool.and(Nat.is_eq(FS.mmul(p, x1, y2), FS.mmul(p, x2, y1)), Nat.is_eq(FS.mmul(p, z1, y2), FS.mmul(p, z2, y1)))

# -(X : Y : Z) = (X : -Y : Z)
def neg(+p: Nat, a: CS.SPoint) -> CS.SPoint:
  match a:
    case CS.SPoint{x, y, z}:
      CS.SPoint{x, FS.mneg(p, y), z}

# [k] A as k additions of A: [0] A = O, [k + 1] A = [k] A + A
def smul(+p: Nat, k: Nat, +a: CS.SPoint) -> CS.SPoint:
  match k:
    case 0n:
      CS.infinity()
    case 1n+j:
      CS.padd(p, smul(p, j, a), a)
