import Base
import ./limbs.bend as L
import ./field.bend as F
import ./bytes.bend as B
import ./fe.bend as R
import ./pt.bend as PX

# The secp256k1 group y^2 = x^3 + 7 over GF(p) (SEC 2 section 2.4.1), in
# homogeneous projective coordinates (X : Y : Z), x = X / Z, y = Y / Z, the
# point at infinity (0 : 1 : 0). Addition and doubling are the complete
# formulas of Renes, Costello and Batina, "Complete addition formulas for
# prime order elliptic curves" (EUROCRYPT 2016), Algorithms 7 and 9 for
# a = 0 with b3 = 3 b = 21: one formula for every pair of inputs (equal
# points, opposite points and infinity included), so there is no
# exceptional case and no branch (the same choice as HACL*'s
# Hacl.Impl.K256.PointAdd / Spec.K256.PointOps).
#
# The formulas are the register programs of spec/crypto/secp256k1/curve.bend
# (transcribed from the paper) written out as straight-line code over field
# records (pt.bend, fe.bend).
#
# Scalar multiplication is double-and-add over the 256 bits of the scalar,
# most significant first (the specification's): for a secret scalar adding
# in every step and selecting the result with an arithmetic mask (no branch
# and no table index on the scalar), for a public one adding only when the
# bit is set.

type Point is Data:
  Point{x: List<&2, Nat>, y: List<&2, Nat>, z: List<&2, Nat>}

# The arithmetic runs on records (pt.bend over fe.bend): a point's
# coordinates are converted once, the formulas and the whole scalar
# multiplication run on registers, and the result is converted back.

def to_pt(p: Point) -> PX.PT:
  match p:
    case Point{x, y, z}: PX.PT{R.of_list(x), R.of_list(y), R.of_list(z)}

def of_pt(q: PX.PT) -> Point:
  match q:
    case PX.PT{x, y, z}: Point{R.to_list(x), R.to_list(y), R.to_list(z)}

# RCB 2016 Algorithm 7 (a = 0), complete: pt.bend add
def add(p: Point, q: Point) -> Point:
  of_pt(PX.add(to_pt(p), to_pt(q)))

# RCB 2016 Algorithm 9 (a = 0): pt.bend dbl
def dbl(p: Point) -> Point:
  of_pt(PX.dbl(to_pt(p)))

def infinity() -> Point:
  Point{F.zero(), F.one(), F.zero()}

def neg(p: Point) -> Point:
  match p:
    case Point{x, y, z}: Point{x, F.neg(y), z}

# b ? p : q, coordinate-wise and branch-free, for b in {0, 1}
def select(+b: Nat, p: Point, q: Point) -> Point:
  match p q:
    case Point{x1, y1, z1} Point{x2, y2, z2}:
      Point{F.select(b, x1, x2), F.select(b, y1, y2), F.select(b, z1, z2)}

# [k] p for a scalar k given by its 16 limbs (any value below 2^256), for a
# secret k: double-and-add over the 256 bits, adding in every step and
# selecting with an arithmetic mask (no branch and no table index on k)
def mul(k: List<&2, Nat>, +p: Point) -> Point:
  of_pt(PX.mul_go(L.bits(k), to_pt(p), PX.infinity()))

# the same for a public k (verification, recovery): the addition only when
# the bit is set
def mul_pub(k: List<&2, Nat>, +p: Point) -> Point:
  of_pt(PX.vmul_go(L.bits(k), to_pt(p), PX.infinity()))

def gx() -> List<&2, Nat>:
  [6040n, 5880n, 33115n, 23026n, 10457n, 11726n, 64731n, 667n,
   2823n, 52871n, 25237n, 21920n, 48044n, 63964n, 26238n, 31166n]

def gy() -> List<&2, Nat>:
  [54456n, 64272n, 53391n, 40007n, 21529n, 42629n, 46152n, 64791n,
   2216n, 3601n, 64508n, 23972n, 50277n, 9891n, 55927n, 18490n]

# the generator G of SEC 2
def g() -> Point:
  Point{gx(), gy(), F.one()}

def is_inf(p: Point) -> Bool:
  match p:
    case Point{x, y, z}: F.is_zero(z)

# ---- affine coordinates and SEC 1 encodings ----

type Affine is Data:
  Affine{x: List<&2, Nat>, y: List<&2, Nat>}

def to_affine_z(+x: List<&2, Nat>, +y: List<&2, Nat>, +zi: List<&2, Nat>) -> Affine:
  Affine{F.mul(x, zi), F.mul(y, zi)}

# (X / Z, Y / Z); (0, 0) for the point at infinity
def to_affine(p: Point) -> Affine:
  match p:
    case Point{x, y, z}: to_affine_z(x, y, F.inv(z))

def aff_x(a: Affine) -> List<&2, Nat>:
  match a:
    case Affine{x, y}: x

def aff_y(a: Affine) -> List<&2, Nat>:
  match a:
    case Affine{x, y}: y

# x^3 + 7
def rhs(+x: List<&2, Nat>) -> List<&2, Nat>:
  F.add(F.mul(F.sq(x), x), F.small(7n))

def on_curve(+x: List<&2, Nat>, +y: List<&2, Nat>) -> Bool:
  F.eq(F.sq(y), rhs(x))

# the square root of x^3 + 7 with the given parity, if x^3 + 7 is a square
def lift_y(+y: List<&2, Nat>, +par: Nat) -> List<&2, Nat>:
  F.select(Nat.sub(Nat.add(F.parity(y), par), Nat.mul(Nat.mul(F.parity(y), par), 2n)), F.neg(y), y)

def decompress_if(+x: List<&2, Nat>, +y: List<&2, Nat>, ok: Bool) -> Maybe<&2, Point>:
  match ok:
    case True{}: Some{Point{x, y, F.one()}}
    case False{}: None{}

def decompress(+x: List<&2, Nat>, +par: Nat) -> Maybe<&2, Point>:
  +y = F.sqrt(rhs(x))
  decompress_if(x, lift_y(y, par), F.eq(F.sq(y), rhs(x)))

def decode_c(+x: List<&2, Nat>, +par: Nat, ok: Bool) -> Maybe<&2, Point>:
  match ok:
    case True{}: decompress(x, par)
    case False{}: None{}

def decode_u(+x: List<&2, Nat>, +y: List<&2, Nat>, ok: Bool) -> Maybe<&2, Point>:
  match ok:
    case True{}: Some{Point{x, y, F.one()}}
    case False{}: None{}

def decode_33(+pre: U32, +rest: List<&2, U32>) -> Maybe<&2, Point>:
  +x = B.of_be(rest)
  decode_c(x, U32.to_nat(U32.and(pre, 1)), Bool.and(Bool.or(U32.is_eq(pre, 2), U32.is_eq(pre, 3)), F.lt_p(x)))

def decode_65(+pre: U32, +rest: List<&2, U32>) -> Maybe<&2, Point>:
  +x = B.of_be(B.prefix(32n, rest))
  +y = B.of_be(B.suffix(32n, rest))
  decode_u(x, y, Bool.and(Bool.and(U32.is_eq(pre, 4), Bool.and(F.lt_p(x), F.lt_p(y))), on_curve(x, y)))

def decode_len(+bs: List<&2, U32>, c33: Bool, c65: Bool) -> Maybe<&2, Point>:
  match c33 c65:
    case True{} _: decode_33(B.head(bs), B.tail(bs))
    case False{} True{}: decode_65(B.head(bs), B.tail(bs))
    case False{} False{}: None{}

# SEC 1 section 2.3.4: a compressed (33 bytes, prefix 02/03) or uncompressed
# (65 bytes, prefix 04) public key, None when malformed, not below p, or
# not on the curve (the point at infinity, encoded 00, is refused)
def decode(+bs: List<&2, U32>) -> Maybe<&2, Point>:
  decode_len(bs, B.has_len(33n, bs), B.has_len(65n, bs))

# SEC 1 section 2.3.3
def enc_c(a: Affine) -> List<&2, U32>:
  match a:
    case Affine{x, +y}: U32.from_nat(Nat.add(F.parity(y), 2n)) <> B.to_be(x)

def encode_compressed(p: Point) -> List<&2, U32>:
  enc_c(to_affine(p))

def enc_u(a: Affine) -> List<&2, U32>:
  match a:
    case Affine{x, y}: 4 <> List.append(&2, U32, B.to_be(x), B.to_be(y))

def encode_uncompressed(p: Point) -> List<&2, U32>:
  enc_u(to_affine(p))
