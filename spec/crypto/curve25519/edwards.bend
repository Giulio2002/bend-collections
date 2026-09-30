import Base
import ../../math/number.bend as SN
import ./field.bend as FS

# The group of the twisted Edwards curve
#
#     -x^2 + y^2 = 1 + d x^2 y^2        (a = -1)
#
# over Z/pZ, in affine coordinates: the group behind Ed25519
# (spec/crypto/ed25519.bend computes in extended coordinates
# (X : Y : Z : T), x = X / Z, y = Y / Z; spec/crypto/ed25519_group.bend
# relates the two). The addition is the twisted Edwards addition law
#
#     (x1, y1) + (x2, y2) = ((x1 y2 + y1 x2) / (1 + d x1 x2 y1 y2),
#                            (y1 y2 + x1 x2) / (1 - d x1 x2 y1 y2))
#
# (Bernstein, Birkner, Joye, Lange, Peters, "Twisted Edwards curves", 2008;
# Hisil, Wong, Carter, Dawson, "Twisted Edwards curves revisited", 2008),
# with division as multiplication by the Fermat inverse FS.finv, as the
# specification divides. For a prime p, a non-square d and a square -1 the
# law is complete (the denominators never vanish on the curve) and the
# points of the curve form an abelian group with identity (0, 1) and
# inverse (-x, y): the clauses below, proved in proofs/crypto/ed25519/group
# (Hales, "The group law for Edwards curves", 2016, is the model: polynomial
# identities plus the completeness argument).
#
#   clause (hc : Curve(mp, d), p = 1 + mp; a, b, c on the curve)
#   Group.closure     a + b is on the curve
#   Group.zero_on     (0, 1) is on the curve
#   Group.neg_on      -a is on the curve
#   Group.comm        a + b == b + a                       (every a, b)
#   Group.zero        a + (0, 1) == a
#   Group.neg         a + (-a) == (0, 1)
#   Group.assoc       (a + b) + c == a + (b + c)
#   Group.nmul_on     [k] a is on the curve
#   Group.nmul_add    [j + k] a == [j] a + [k] a
#   Group.nmul_mul    [j k] a == [j] ([k] a)
#   Group.nmul_dist   [k] (a + b) == [k] a + [k] b
#
# Every coordinate is a residue below p, so two points are equal exactly
# when they are equal as values (no projective equivalence is needed at
# this level): the laws are equations between points.

type APt is Data:
  APt{x: Nat, y: Nat}

def ax(a: APt) -> Nat:
  match a:
    case APt{x, y}:
      x

def ay(a: APt) -> Nat:
  match a:
    case APt{x, y}:
      y

# ---- the curve equation: lhs == rhs ----

def lhs(+p: Nat, +x: Nat, +y: Nat) -> Nat:
  FS.fsub(p, FS.fmul(p, y, y), FS.fmul(p, x, x))

def rhs(+p: Nat, +d: Nat, +x: Nat, +y: Nat) -> Nat:
  FS.fadd(p, 1n, FS.fmul(p, d, FS.fmul(p, FS.fmul(p, x, x), FS.fmul(p, y, y))))

# a point of the curve, with reduced coordinates
def on_curve(+p: Nat, +d: Nat, a: APt) -> Bool:
  match a:
    case APt{+x, +y}:
      Bool.and(Nat.is_lt(x, p), Bool.and(Nat.is_lt(y, p), Nat.is_eq(lhs(p, x, y), rhs(p, d, x, y))))

# ---- the addition law ----

# d x1 x2 y1 y2
def ct(+p: Nat, +d: Nat, +x1: Nat, +y1: Nat, +x2: Nat, +y2: Nat) -> Nat:
  FS.fmul(p, d, FS.fmul(p, FS.fmul(p, x1, x2), FS.fmul(p, y1, y2)))

def nx(+p: Nat, +x1: Nat, +y1: Nat, +x2: Nat, +y2: Nat) -> Nat:
  FS.fadd(p, FS.fmul(p, x1, y2), FS.fmul(p, y1, x2))

def ny(+p: Nat, +x1: Nat, +y1: Nat, +x2: Nat, +y2: Nat) -> Nat:
  FS.fadd(p, FS.fmul(p, y1, y2), FS.fmul(p, x1, x2))

def dx(+p: Nat, +d: Nat, +x1: Nat, +y1: Nat, +x2: Nat, +y2: Nat) -> Nat:
  FS.fadd(p, 1n, ct(p, d, x1, y1, x2, y2))

def dy(+p: Nat, +d: Nat, +x1: Nat, +y1: Nat, +x2: Nat, +y2: Nat) -> Nat:
  FS.fsub(p, 1n, ct(p, d, x1, y1, x2, y2))

def add_x(+p: Nat, +d: Nat, +x1: Nat, +y1: Nat, +x2: Nat, +y2: Nat) -> Nat:
  FS.fmul(p, nx(p, x1, y1, x2, y2), FS.finv(p, dx(p, d, x1, y1, x2, y2)))

def add_y(+p: Nat, +d: Nat, +x1: Nat, +y1: Nat, +x2: Nat, +y2: Nat) -> Nat:
  FS.fmul(p, ny(p, x1, y1, x2, y2), FS.finv(p, dy(p, d, x1, y1, x2, y2)))

def aadd(+p: Nat, +d: Nat, a: APt, b: APt) -> APt:
  match a b:
    case APt{+x1, +y1} APt{+x2, +y2}:
      APt{add_x(p, d, x1, y1, x2, y2), add_y(p, d, x1, y1, x2, y2)}

def azero() -> APt:
  APt{0n, 1n}

def aneg(+p: Nat, a: APt) -> APt:
  match a:
    case APt{x, y}:
      APt{FS.fsub(p, 0n, x), y}

# [k] a: a added k times
def nmul(+p: Nat, +d: Nat, k: Nat, +a: APt) -> APt:
  match k:
    case 0n:
      azero()
    case 1n+j:
      aadd(p, d, a, nmul(p, d, j, a))

# ---- the parameters ----

# 2^((p - 1) / 4), a square root of -1 (the same expression as the sqm1 of
# spec/crypto/ed25519.bend)
def sqm1(+p: Nat) -> Nat:
  FS.fpow(p, 2n, Nat.div(Nat.sub(p, 1n), 4n))

# p = 1 + mp is an odd prime, d is not zero and not a square (Euler's
# criterion: d^((p - 1) / 2) != 1) and sqm1(p) is a square root of -1
def curve_ok(+mp: Nat, +d: Nat) -> Bool:
  Bool.and(SN.prime(1n+mp),
    Bool.and(Bool.not(Nat.is_eq(Nat.mod(2n, 1n+mp), 0n)),
      Bool.and(Nat.is_eq(Nat.mod(mp, 2n), 0n),
        Bool.and(Bool.not(Nat.is_eq(Nat.mod(d, 1n+mp), 0n)),
          Bool.and(Bool.not(Nat.is_eq(Nat.mod(Nat.pow(d, Nat.div(mp, 2n)), 1n+mp), 1n)),
            Nat.is_eq(FS.fadd(1n+mp, FS.fmul(1n+mp, sqm1(1n+mp), sqm1(1n+mp)), 1n), 0n))))))

def Curve(+mp: Nat, +d: Nat) -> Data:
  {curve_ok(mp, d) == True{} : Bool}

def OnCurve(+p: Nat, +d: Nat, +a: APt) -> Data:
  {on_curve(p, d, a) == True{} : Bool}

# ---- clauses ----

def Group.closure(+mp: Nat, +d: Nat, +hc: Curve(mp, d), +a: APt, +b: APt, +ha: OnCurve(1n+mp, d, a), +hb: OnCurve(1n+mp, d, b)) -> Type:
  OnCurve(1n+mp, d, aadd(1n+mp, d, a, b))

def Group.zero_on(+mp: Nat, +d: Nat, +hc: Curve(mp, d)) -> Type:
  OnCurve(1n+mp, d, azero())

def Group.neg_on(+mp: Nat, +d: Nat, +hc: Curve(mp, d), +a: APt, +ha: OnCurve(1n+mp, d, a)) -> Type:
  OnCurve(1n+mp, d, aneg(1n+mp, a))

def Group.comm(+mp: Nat, +d: Nat, +a: APt, +b: APt) -> Type:
  {aadd(1n+mp, d, a, b) == aadd(1n+mp, d, b, a) : APt}

def Group.zero(+mp: Nat, +d: Nat, +hc: Curve(mp, d), +a: APt, +ha: OnCurve(1n+mp, d, a)) -> Type:
  {aadd(1n+mp, d, a, azero()) == a : APt}

def Group.neg(+mp: Nat, +d: Nat, +hc: Curve(mp, d), +a: APt, +ha: OnCurve(1n+mp, d, a)) -> Type:
  {aadd(1n+mp, d, a, aneg(1n+mp, a)) == azero() : APt}

def Group.assoc(+mp: Nat, +d: Nat, +hc: Curve(mp, d), +a: APt, +b: APt, +c: APt, +ha: OnCurve(1n+mp, d, a), +hb: OnCurve(1n+mp, d, b), +hcc: OnCurve(1n+mp, d, c)) -> Type:
  {aadd(1n+mp, d, aadd(1n+mp, d, a, b), c) == aadd(1n+mp, d, a, aadd(1n+mp, d, b, c)) : APt}

def Group.nmul_on(+mp: Nat, +d: Nat, +hc: Curve(mp, d), +k: Nat, +a: APt, +ha: OnCurve(1n+mp, d, a)) -> Type:
  OnCurve(1n+mp, d, nmul(1n+mp, d, k, a))

def Group.nmul_add(+mp: Nat, +d: Nat, +hc: Curve(mp, d), +j: Nat, +k: Nat, +a: APt, +ha: OnCurve(1n+mp, d, a)) -> Type:
  {nmul(1n+mp, d, Nat.add(j, k), a) == aadd(1n+mp, d, nmul(1n+mp, d, j, a), nmul(1n+mp, d, k, a)) : APt}

def Group.nmul_mul(+mp: Nat, +d: Nat, +hc: Curve(mp, d), +j: Nat, +k: Nat, +a: APt, +ha: OnCurve(1n+mp, d, a)) -> Type:
  {nmul(1n+mp, d, Nat.mul(j, k), a) == nmul(1n+mp, d, j, nmul(1n+mp, d, k, a)) : APt}

def Group.nmul_dist(+mp: Nat, +d: Nat, +hc: Curve(mp, d), +k: Nat, +a: APt, +b: APt, +ha: OnCurve(1n+mp, d, a), +hb: OnCurve(1n+mp, d, b)) -> Type:
  {nmul(1n+mp, d, k, aadd(1n+mp, d, a, b)) == aadd(1n+mp, d, nmul(1n+mp, d, k, a), nmul(1n+mp, d, k, b)) : APt}
