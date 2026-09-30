import Base
import ../curve25519/field.bend as F
import ../curve25519/fe.bend as FE
import ../curve25519/x25519.bend as X

# edwards25519 points (RFC 8032 section 5.1): -x^2 + y^2 = 1 + d x^2 y^2
# over GF(2^255 - 19) (the fast field of ../curve25519/fe.bend), in
# extended homogeneous coordinates (X : Y : Z : T), x = X / Z, y = Y / Z,
# x y = T / Z. Addition and doubling are the RFC's formulas (section
# 5.1.4), encoding and decoding sections 5.1.2 and 5.1.3. The curve
# constants are computed once per call from small integers by the proved
# field operations and passed along (Cs, with the field's radix).

type Pt is Data:
  Pt{x: FE.Fe, y: FE.Fe, z: FE.Fe, t: FE.Fe}

# the radix R = 2^17, d = -121665 / 121666, 2 d, sqrt(-1) = 2^((p - 1) / 4)
type Cs is Data:
  Cs{r: Nat, d: FE.Fe, d2: FE.Fe, sqm1: FE.Fe}

# 121666 = 66 + 2^8 (219 + 2^8 1)
def c121666(+one: Nat) -> Nat:
  X.digits(one, [66n, 219n, 1n])

# 2^((p - 1) / 4), (p - 1) / 4 = 2^253 - 5: 250 one bits, then 0 1 1
def pow_p14(+R: Nat, +x: FE.Fe) -> FE.Fe:
  FE.pow_bits(R, x, [False{}, True{}, True{}], FE.pow_ones(R, x, 249n, x))

def cs_r(c: Cs) -> Nat:
  match c:
    case Cs{r, d, d2, s}:
      r

def cs_d(c: Cs) -> FE.Fe:
  match c:
    case Cs{r, d, d2, s}:
      d

def cs_d2(c: Cs) -> FE.Fe:
  match c:
    case Cs{r, d, d2, s}:
      d2

def cs_s(c: Cs) -> FE.Fe:
  match c:
    case Cs{r, d, d2, s}:
      s

def cs_of(+R: Nat, +d: FE.Fe, s: FE.Fe) -> Cs:
  Cs{R, d, FE.add(R, d, d), s}

# x, kept behind the input list xs: the proof checker never runs the
# constant computations while xs is unknown
def lit(+xs: List<&2, U32>, x: FE.Fe) -> FE.Fe:
  match xs:
    case Nil{}:
      x
    case Con{h, t}:
      x

# the constants (X.one_of(xs) is 1)
def consts(+xs: List<&2, U32>) -> Cs:
  +one = X.one_of(xs)
  +R = FE.radix(one)
  cs_of(R, FE.mul(R, FE.neg(R, lit(xs, FE.small(X.a24(one)))), FE.inv(R, lit(xs, FE.small(c121666(one))))), pow_p14(R, lit(xs, FE.small(2n))))

# the small constant k, kept behind the radix of c the same way
def small_r(r: Nat, +k: Nat) -> FE.Fe:
  match r:
    case 0n:
      FE.small(k)
    case 1n+q:
      FE.small(k)

def cs_small(c: Cs, +k: Nat) -> FE.Fe:
  match c:
    case Cs{r, d, d2, s}:
      small_r(r, k)

def identity() -> Pt:
  Pt{FE.zero(), FE.one(), FE.one(), FE.zero()}

# RFC 8032 5.1.4, addition
def add(+c: Cs, p: Pt, q: Pt) -> Pt:
  match p q:
    case Pt{+x1, +y1, +z1, +t1} Pt{+x2, +y2, +z2, +t2}:
      +R = cs_r(c)
      +a = FE.mul(R, FE.sub(R, y1, x1), FE.sub(R, y2, x2))
      +b = FE.mul(R, FE.add(R, y1, x1), FE.add(R, y2, x2))
      +cc = FE.mul(R, FE.mul(R, t1, cs_d2(c)), t2)
      +dd = FE.mul(R, FE.add(R, z1, z1), z2)
      +e = FE.sub(R, b, a)
      +f = FE.sub(R, dd, cc)
      +g = FE.add(R, dd, cc)
      +h = FE.add(R, b, a)
      Pt{FE.mul(R, e, f), FE.mul(R, g, h), FE.mul(R, f, g), FE.mul(R, e, h)}

# RFC 8032 5.1.4, doubling
def double(+R: Nat, p: Pt) -> Pt:
  match p:
    case Pt{+x1, +y1, +z1, t1}:
      +a = FE.sq(R, x1)
      +b = FE.sq(R, y1)
      +zz = FE.sq(R, z1)
      +cc = FE.add(R, zz, zz)
      +h = FE.add(R, a, b)
      +e = FE.sub(R, h, FE.sq(R, FE.add(R, x1, y1)))
      +g = FE.sub(R, a, b)
      +f = FE.add(R, cc, g)
      Pt{FE.mul(R, e, f), FE.mul(R, g, h), FE.mul(R, f, g), FE.mul(R, e, h)}

# s == 0: p; s == 1: q
def select(+s: U32, p: Pt, q: Pt) -> Pt:
  match p q:
    case Pt{x1, y1, z1, t1} Pt{x2, y2, z2, t2}:
      Pt{FE.select(s, x1, x2), FE.select(s, y1, y2), FE.select(s, z1, z2), FE.select(s, t1, t2)}

# [bits t = n - 1 .. 0 of bs] p added to 2^n q: double, add, select (the
# same work for every bit: for secret scalars)
def smul(n: Nat, +c: Cs, +bs: List<&2, U32>, +p: Pt, q: Pt) -> Pt:
  match n:
    case 0n:
      q
    case 1n+ +t:
      +q2 = double(cs_r(c), q)
      smul(t, c, bs, p, select(X.kbit(bs, t), q2, add(c, q2, p)))

# the same result, adding only on a one bit (for public scalars)
def smul_bit(z: Bool, +c: Cs, +p: Pt, q2: Pt) -> Pt:
  match z:
    case True{}:
      q2
    case False{}:
      add(c, q2, p)

def smul_vt(n: Nat, +c: Cs, +bs: List<&2, U32>, +p: Pt, q: Pt) -> Pt:
  match n:
    case 0n:
      q
    case 1n+ +t:
      smul_vt(t, c, bs, p, smul_bit(U32.is_eq(X.kbit(bs, t), 0), c, p, double(cs_r(c), q)))

# [k] p for a byte-string scalar k (secret)
def mul(+c: Cs, +k: List<&2, U32>, +p: Pt) -> Pt:
  smul(X.bitlen(k), c, k, p, identity())

# [k] p for a public scalar k
def mul_vt(+c: Cs, +k: List<&2, U32>, +p: Pt) -> Pt:
  smul_vt(X.bitlen(k), c, k, p, identity())

# the last byte with bit 7 set to b (the canonical y has it clear)
def set_top(xs: List<&2, U32>, +b: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, xt}:
      match xt:
        case Nil{}:
          Con{U32.or(x, U32.shln(b, 7n)), Nil{}}
        case Con{y, yt}:
          Con{x, set_top(Con{y, yt}, b)}

# RFC 8032 5.1.2
def encode(+R: Nat, p: Pt) -> List<&2, U32>:
  match p:
    case Pt{+x, +y, +z, t}:
      +zi = FE.inv(R, z)
      set_top(FE.to_bytes(R, FE.mul(R, y, zi)), FE.parity(R, FE.mul(R, x, zi)))

# y >= p for the 32-byte y (bit 255 cleared): the carry of y + 2^256 - p
# is not 0
def ge_p(+y: List<&2, U32>) -> Bool:
  Bool.not(U32.is_eq(F.cr_out(F.carry(F.addl(y, F.comp_p()), 0)), 0))

def dec_fin(+R: Nat, +x: FE.Fe, +y: FE.Fe, +x0: U32, fail: Bool) -> Maybe<&2, Pt>:
  match fail:
    case True{}:
      None{}
    case False{}:
      +x2 = FE.select(U32.xor(FE.parity(R, x), x0), x, FE.neg(R, x))
      Some{Pt{x2, y, FE.one(), FE.mul(R, x2, y)}}

def dec_root(+c: Cs, +x: FE.Fe, +y: FE.Fe, +x0: U32, is_u: Bool, is_nu: Bool) -> Maybe<&2, Pt>:
  match is_u:
    case True{}:
      dec_fin(cs_r(c), x, y, x0, Bool.and(FE.is_zero(cs_r(c), x), U32.is_eq(x0, 1)))
    case False{}:
      match is_nu:
        case True{}:
          +x1 = FE.mul(cs_r(c), x, cs_s(c))
          dec_fin(cs_r(c), x1, y, x0, Bool.and(FE.is_zero(cs_r(c), x1), U32.is_eq(x0, 1)))
        case False{}:
          None{}

def dec_y(+c: Cs, +y: FE.Fe, +x0: U32, bad: Bool) -> Maybe<&2, Pt>:
  match bad:
    case True{}:
      None{}
    case False{}:
      +R = cs_r(c)
      +yy = FE.sq(R, y)
      +u = FE.sub(R, yy, FE.one())
      +v = FE.add(R, FE.mul(R, cs_d(c), yy), FE.one())
      +v3 = FE.mul(R, FE.sq(R, v), v)
      +v7 = FE.mul(R, FE.sq(R, v3), v)
      +x = FE.mul(R, FE.mul(R, u, v3), FE.pow_p58(R, FE.mul(R, u, v7)))
      +vxx = FE.mul(R, v, FE.sq(R, x))
      dec_root(c, x, y, x0, FE.eq(R, vxx, u), FE.eq(R, vxx, FE.neg(R, u)))

# RFC 8032 5.1.3 on 32 bytes below 256
def decode(+c: Cs, +bs: List<&2, U32>) -> Maybe<&2, Pt>:
  dec_y(c, FE.of_bytes(bs), X.kbit(bs, 255n), ge_p(F.of_bytes(bs)))

# the same point: X1 Z2 == X2 Z1 and Y1 Z2 == Y2 Z1
def equal(+R: Nat, p: Pt, q: Pt) -> Bool:
  match p q:
    case Pt{+x1, +y1, +z1, t1} Pt{+x2, +y2, +z2, t2}:
      Bool.and(FE.eq(R, FE.mul(R, x1, z2), FE.mul(R, x2, z1)), FE.eq(R, FE.mul(R, y1, z2), FE.mul(R, y2, z1)))

# the base point: y = 4 / 5, x even
def base_of(m: Maybe<&2, Pt>) -> Pt:
  match m:
    case None{}:
      identity()
    case Some{p}:
      p

def base(+c: Cs) -> Pt:
  +R = cs_r(c)
  base_of(decode(c, FE.to_bytes(R, FE.mul(R, cs_small(c, 4n), FE.inv(R, cs_small(c, 5n))))))
