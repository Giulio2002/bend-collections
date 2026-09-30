import Base
import ../../lib/common.bend as C
import ./field.bend as FS

# The secp256k1 group (SEC 2 section 2.4.1): y^2 = x^3 + 7 over GF(p), the
# generator G and the order n, over the natural numbers (field.bend).
# Nothing of the implementation is used.
#
# Points are homogeneous projective triples (X : Y : Z) with x = X / Z,
# y = Y / Z and the point at infinity (0 : 1 : 0). Addition and doubling
# are Algorithms 7 and 9 of Renes, Costello and Batina, "Complete addition
# formulas for prime order elliptic curves" (EUROCRYPT 2016), for a = 0
# and b3 = 3 b = 21, written as the paper writes them: straight-line
# register programs (t0 <- X1 X2, ...), here with every assignment given a
# fresh register. This is HACL*'s Spec.K256.PointOps.point_add /
# point_double. Scalar multiplication is the textbook left-to-right
# double-and-add over the 256 bits of the scalar.
#
# The textbook affine group law (SEC 1 section 2.2.1; Mathlib's
# WeierstrassCurve.Affine: slope, addX, addY) is in affine.bend, with the
# statement that these projective formulas compute it; see
# docs/CRYPTO_CONTRACTS.md for what of that is proved.

type SPoint is Data:
  SPoint{x: Nat, y: Nat, z: Nat}

type SOp is Data:
  SAdd{i: Nat, j: Nat}
  SSub{i: Nat, j: Nat}
  SMul{i: Nat, j: Nat}

def nth(i: Nat, regs: List<&2, Nat>) -> Nat:
  match i regs:
    case _ Nil{}: 0n
    case 0n r <> t: r
    case 1n+k r <> t: nth(k, t)

def exec(+p: Nat, op: SOp, +regs: List<&2, Nat>) -> Nat:
  match op:
    case SAdd{i, j}: FS.madd(p, nth(i, regs), nth(j, regs))
    case SSub{i, j}: FS.msub(p, nth(i, regs), nth(j, regs))
    case SMul{i, j}: FS.mmul(p, nth(i, regs), nth(j, regs))

# run a program: each instruction appends its result as a new register
def run_go(+p: Nat, prog: List<&2, SOp>, +regs: List<&2, Nat>) -> List<&2, Nat>:
  match prog:
    case Nil{}: regs
    case op <> t: run_go(p, t, List.append(&2, Nat, regs, [exec(p, op, regs)]))

# (the first register is looked at first; the result is run_go's)
def run(+p: Nat, prog: List<&2, SOp>, regs: List<&2, Nat>) -> List<&2, Nat>:
  match regs:
    case Nil{}: run_go(p, prog, Nil{})
    case 0n <> t: run_go(p, prog, 0n <> t)
    case (1n+k) <> t: run_go(p, prog, (1n+k) <> t)

# RCB Algorithm 7 (a = 0). Registers: 0 X1, 1 Y1, 2 Z1, 3 X2, 4 Y2, 5 Z2,
# 6 b3; the paper's lines, in order, write registers 7..39:
#   t0 = X1 X2 (7)      t1 = Y1 Y2 (8)      t2 = Z1 Z2 (9)
#   t3 = X1 + Y1 (10)   t4 = X2 + Y2 (11)   t3 = t3 t4 (12)
#   t4 = t0 + t1 (13)   t3 = t3 - t4 (14)   t4 = Y1 + Z1 (15)
#   X3 = Y2 + Z2 (16)   t4 = t4 X3 (17)     X3 = t1 + t2 (18)
#   t4 = t4 - X3 (19)   X3 = X1 + Z1 (20)   Y3 = X2 + Z2 (21)
#   X3 = X3 Y3 (22)     Y3 = t0 + t2 (23)   Y3 = X3 - Y3 (24)
#   X3 = t0 + t0 (25)   t0 = X3 + t0 (26)   t2 = b3 t2 (27)
#   Z3 = t1 + t2 (28)   t1 = t1 - t2 (29)   Y3 = b3 Y3 (30)
#   X3 = t4 Y3 (31)     t2 = t3 t1 (32)     X3 = t2 - X3 (33)
#   Y3 = Y3 t0 (34)     t1 = t1 Z3 (35)     Y3 = t1 + Y3 (36)
#   t0 = t0 t3 (37)     Z3 = Z3 t4 (38)     Z3 = Z3 + t0 (39)
# and the result is (X3 : Y3 : Z3) = registers (33 : 36 : 39).
def add_prog() -> List<&2, SOp>:
  [SMul{0n, 3n}, SMul{1n, 4n}, SMul{2n, 5n}, SAdd{0n, 1n}, SAdd{3n, 4n},
   SMul{10n, 11n}, SAdd{7n, 8n}, SSub{12n, 13n}, SAdd{1n, 2n}, SAdd{4n, 5n},
   SMul{15n, 16n}, SAdd{8n, 9n}, SSub{17n, 18n}, SAdd{0n, 2n}, SAdd{3n, 5n},
   SMul{20n, 21n}, SAdd{7n, 9n}, SSub{22n, 23n}, SAdd{7n, 7n}, SAdd{25n, 7n},
   SMul{6n, 9n}, SAdd{8n, 27n}, SSub{8n, 27n}, SMul{6n, 24n}, SMul{19n, 30n},
   SMul{14n, 29n}, SSub{32n, 31n}, SMul{30n, 26n}, SMul{29n, 28n}, SAdd{35n, 34n},
   SMul{26n, 14n}, SMul{28n, 19n}, SAdd{38n, 37n}]

# RCB Algorithm 9 (a = 0). Registers: 0 X, 1 Y, 2 Z, 3 b3; lines write
# registers 4..21:
#   t0 = Y Y (4)        Z3 = t0 + t0 (5)    Z3 = Z3 + Z3 (6)
#   Z3 = Z3 + Z3 (7)    t1 = Y Z (8)        t2 = Z Z (9)
#   t2 = b3 t2 (10)     X3 = t2 Z3 (11)     Y3 = t0 + t2 (12)
#   Z3 = t1 Z3 (13)     t1 = t2 + t2 (14)   t2 = t1 + t2 (15)
#   t0 = t0 - t2 (16)   Y3 = t0 Y3 (17)     Y3 = X3 + Y3 (18)
#   t1 = X Y (19)       X3 = t0 t1 (20)     X3 = X3 + X3 (21)
# and the result is (X3 : Y3 : Z3) = registers (21 : 18 : 13).
def dbl_prog() -> List<&2, SOp>:
  [SMul{1n, 1n}, SAdd{4n, 4n}, SAdd{5n, 5n}, SAdd{6n, 6n}, SMul{1n, 2n},
   SMul{2n, 2n}, SMul{3n, 9n}, SMul{10n, 7n}, SAdd{4n, 10n}, SMul{8n, 7n},
   SAdd{10n, 10n}, SAdd{14n, 10n}, SSub{4n, 15n}, SMul{16n, 12n}, SAdd{11n, 17n},
   SMul{0n, 1n}, SMul{16n, 19n}, SAdd{20n, 20n}]

def b3() -> Nat:
  21n

def add_out(+r: List<&2, Nat>) -> SPoint:
  SPoint{nth(33n, r), nth(36n, r), nth(39n, r)}

def padd(+p: Nat, a: SPoint, b: SPoint) -> SPoint:
  match a b:
    case SPoint{x1, y1, z1} SPoint{x2, y2, z2}:
      add_out(run(p, add_prog(), [x1, y1, z1, x2, y2, z2, b3()]))

def dbl_out(+r: List<&2, Nat>) -> SPoint:
  SPoint{nth(21n, r), nth(18n, r), nth(13n, r)}

def pdbl(+p: Nat, a: SPoint) -> SPoint:
  match a:
    case SPoint{x, y, z}:
      dbl_out(run(p, dbl_prog(), [x, y, z, b3()]))

def infinity() -> SPoint:
  SPoint{0n, 1n, 0n}

def is_inf(a: SPoint) -> Bool:
  match a:
    case SPoint{x, y, z}: Nat.is_eq(z, 0n)

# bit i of k
def bit(+i: Nat, +k: Nat) -> Nat:
  C.bit(C.high(i, k))

def step(b: Nat, +p: Nat, +a: SPoint, +d: SPoint) -> SPoint:
  match b:
    case 0n: d
    case 1n+c: padd(p, d, a)

# bits i - 1, ..., 0 of k, most significant first (k is looked at first,
# so that on an unknown k nothing is unfolded)
def bits_go(i: Nat, +k: Nat) -> List<&2, Nat>:
  match i:
    case 0n: Nil{}
    case 1n+ +j: bit(j, k) <> bits_go(j, k)

def bits(+i: Nat, k: Nat) -> List<&2, Nat>:
  match k:
    case 0n: bits_go(i, 0n)
    case 1n+j: bits_go(i, 1n+j)

# left-to-right double-and-add: for each bit b, R = 2 R, then R = R + A
# when b is set
def lmul(+p: Nat, bs: List<&2, Nat>, +a: SPoint, r: SPoint) -> SPoint:
  match bs:
    case Nil{}: r
    case b <> t: lmul(p, t, a, step(b, p, a, pdbl(p, r)))

# [k] A for 0 <= k < 2^256
def pmul(+p: Nat, +k: Nat, +a: SPoint) -> SPoint:
  lmul(p, bits(256n, k), a, infinity())

# G (SEC 2), with z = 1
def g(+one: Nat) -> SPoint:
  SPoint{FS.digits(one, [6040n, 5880n, 33115n, 23026n, 10457n, 11726n, 64731n, 667n,
                         2823n, 52871n, 25237n, 21920n, 48044n, 63964n, 26238n, 31166n]),
         FS.digits(one, [54456n, 64272n, 53391n, 40007n, 21529n, 42629n, 46152n, 64791n,
                         2216n, 3601n, 64508n, 23972n, 50277n, 9891n, 55927n, 18490n]),
         one}

# ---- affine coordinates ----

type SAffine is Data:
  SAffine{x: Nat, y: Nat}

def aff_z(+p: Nat, +x: Nat, +y: Nat, +zi: Nat) -> SAffine:
  SAffine{FS.mmul(p, x, zi), FS.mmul(p, y, zi)}

# (X / Z, Y / Z), (0, 0) for the point at infinity
def to_affine(+p: Nat, a: SPoint) -> SAffine:
  match a:
    case SPoint{x, y, z}: aff_z(p, x, y, FS.minv(p, z))

def aff_x(a: SAffine) -> Nat:
  match a:
    case SAffine{x, y}: x

def aff_y(a: SAffine) -> Nat:
  match a:
    case SAffine{x, y}: y

# x^3 + 7
def rhs(+p: Nat, +x: Nat) -> Nat:
  FS.madd(p, FS.mmul(p, FS.mmul(p, x, x), x), 7n)

def on_curve(+p: Nat, +x: Nat, +y: Nat) -> Bool:
  Nat.is_eq(FS.mmul(p, y, y), rhs(p, x))

# ---- SEC 1 section 2.3: octet strings ----

def byte(+b: U32) -> Nat:
  U32.to_nat(U32.and(b, 255))

# OS2IP (big-endian)
def os2ip_go(bs: List<&2, U32>, acc: Nat) -> Nat:
  match bs:
    case Nil{}: acc
    case b <> t: os2ip_go(t, Nat.add(C.shift(8n, acc), byte(b)))

def os2ip(bs: List<&2, U32>) -> Nat:
  os2ip_go(bs, 0n)

# I2OSP: the n low bytes of x, big-endian
def i2osp_le(n: Nat, +x: Nat) -> List<&2, U32>:
  match n:
    case 0n: Nil{}
    case 1n+k: U32.from_nat(C.low(8n, x)) <> i2osp_le(k, C.high(8n, x))

def i2osp_go(n: Nat, +x: Nat) -> List<&2, U32>:
  List.reverse(&2, U32, i2osp_le(n, x))

# (x is looked at first, so that on an unknown x nothing is unfolded)
def i2osp(+n: Nat, x: Nat) -> List<&2, U32>:
  match x:
    case 0n: i2osp_go(n, 0n)
    case 1n+k: i2osp_go(n, 1n+k)

def length_is(n: Nat, bs: List<&2, U32>) -> Bool:
  Nat.is_eq(List.length(&2, U32, bs), n)

def first(n: Nat, bs: List<&2, U32>) -> List<&2, U32>:
  match n bs:
    case 0n _: Nil{}
    case 1n+k Nil{}: Nil{}
    case 1n+k b <> t: b <> first(k, t)

def after(n: Nat, bs: List<&2, U32>) -> List<&2, U32>:
  match n bs:
    case 0n _: bs
    case 1n+k Nil{}: Nil{}
    case 1n+k b <> t: after(k, t)

def head(bs: List<&2, U32>) -> U32:
  match bs:
    case Nil{}: 0
    case b <> t: b

# ---- SEC 1 section 2.3.3 / 2.3.4: point encodings ----

def enc_c(a: SAffine) -> List<&2, U32>:
  match a:
    case SAffine{x, +y}: U32.from_nat(Nat.add(Nat.mod(y, 2n), 2n)) <> i2osp(32n, x)

# compressed: 02 or 03 (the parity of y), then x
def encode_compressed(+p: Nat, a: SPoint) -> List<&2, U32>:
  enc_c(to_affine(p, a))

def enc_u(a: SAffine) -> List<&2, U32>:
  match a:
    case SAffine{x, y}: 4 <> List.append(&2, U32, i2osp(32n, x), i2osp(32n, y))

# uncompressed: 04, x, y
def encode_uncompressed(+p: Nat, a: SPoint) -> List<&2, U32>:
  enc_u(to_affine(p, a))

# y = (x^3 + 7)^((p + 1) / 4), then y or p - y to get the wanted parity;
# no point when that y does not square to x^3 + 7
def pick_if(+p: Nat, +y: Nat, same: Bool) -> Nat:
  match same:
    case True{}: y
    case False{}: FS.mneg(p, y)

def pick_parity(+p: Nat, +y: Nat, +par: Nat) -> Nat:
  pick_if(p, y, Nat.is_eq(Nat.mod(y, 2n), par))

def decompress_if(+x: Nat, +y: Nat, ok: Bool) -> Maybe<&2, SPoint>:
  match ok:
    case True{}: Some{SPoint{x, y, 1n}}
    case False{}: None{}

def decompress_y(+p: Nat, +x: Nat, +par: Nat, +y: Nat) -> Maybe<&2, SPoint>:
  decompress_if(x, pick_parity(p, y, par), Nat.is_eq(FS.mmul(p, y, y), rhs(p, x)))

def decompress(+p: Nat, +x: Nat, +par: Nat) -> Maybe<&2, SPoint>:
  decompress_y(p, x, par, FS.fsqrt(p, rhs(p, x)))

def decode_c_if(+p: Nat, +pre: U32, +x: Nat, ok: Bool) -> Maybe<&2, SPoint>:
  match ok:
    case True{}: decompress(p, x, U32.to_nat(U32.and(pre, 1)))
    case False{}: None{}

def decode_c(+p: Nat, +pre: U32, +x: Nat) -> Maybe<&2, SPoint>:
  decode_c_if(p, pre, x, Bool.and(Bool.or(U32.is_eq(pre, 2), U32.is_eq(pre, 3)), Nat.is_lt(x, p)))

def decode_u(+p: Nat, +pre: U32, +x: Nat, +y: Nat) -> Maybe<&2, SPoint>:
  decompress_if(x, y, Bool.and(Bool.and(U32.is_eq(pre, 4), Bool.and(Nat.is_lt(x, p), Nat.is_lt(y, p))), on_curve(p, x, y)))

# a compressed (33 bytes) or uncompressed (65 bytes) public key; None when
# malformed, a coordinate is not below p, or the point is not on the curve
def decode_len(+p: Nat, +bs: List<&2, U32>, c33: Bool, c65: Bool) -> Maybe<&2, SPoint>:
  match c33 c65:
    case True{} _: decode_c(p, head(bs), os2ip(after(1n, bs)))
    case False{} True{}: decode_u(p, head(bs), os2ip(first(32n, after(1n, bs))), os2ip(after(33n, bs)))
    case False{} False{}: None{}

def decode(+p: Nat, +bs: List<&2, U32>) -> Maybe<&2, SPoint>:
  decode_len(p, bs, length_is(33n, bs), length_is(65n, bs))
