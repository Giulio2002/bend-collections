import Base
import ../curve25519/field.bend as F
import ../curve25519/x25519.bend as X

# edwards25519 points (RFC 8032 section 5.1): -x^2 + y^2 = 1 + d x^2 y^2
# over GF(2^255 - 19), in extended homogeneous coordinates (X : Y : Z : T),
# x = X / Z, y = Y / Z, x y = T / Z. Addition and doubling are the RFC's
# formulas (section 5.1.4), encoding and decoding sections 5.1.2 and 5.1.3.
# The curve constants are computed once from small integers by the proved
# field operations and passed along (Cs).

type Pt is Data:
  Pt{x: List<&2, U32>, y: List<&2, U32>, z: List<&2, U32>, t: List<&2, U32>}

# d = -121665 / 121666, 2 d, sqrt(-1) = 2^((p - 1) / 4)
type Cs is Data:
  Cs{d: List<&2, U32>, d2: List<&2, U32>, sqm1: List<&2, U32>}

def c121665() -> List<&2, U32>:
  [65, 219, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def c121666() -> List<&2, U32>:
  [66, 219, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

# 2^((p - 1) / 4), (p - 1) / 4 = 2^253 - 5: 250 one bits, then 0 1 1
def pow_p14(+x: List<&2, U32>) -> List<&2, U32>:
  F.pow_bits(x, [False{}, True{}, True{}], F.pow_ones(x, 249n, x))

def cs_d(c: Cs) -> List<&2, U32>:
  match c:
    case Cs{d, d2, s}:
      d

def cs_d2(c: Cs) -> List<&2, U32>:
  match c:
    case Cs{d, d2, s}:
      d2

def cs_s(c: Cs) -> List<&2, U32>:
  match c:
    case Cs{d, d2, s}:
      s

def cs_of(+d: List<&2, U32>) -> Cs:
  Cs{d, F.add(d, d), pow_p14(F.small(2))}

def consts() -> Cs:
  cs_of(F.mul(F.neg(c121665()), F.inv(c121666())))

def identity() -> Pt:
  Pt{F.zero(), F.one(), F.one(), F.zero()}

# RFC 8032 5.1.4, addition
def add(+c: Cs, p: Pt, q: Pt) -> Pt:
  match p q:
    case Pt{+x1, +y1, +z1, +t1} Pt{+x2, +y2, +z2, +t2}:
      +a = F.mul(F.sub(y1, x1), F.sub(y2, x2))
      +b = F.mul(F.add(y1, x1), F.add(y2, x2))
      +cc = F.mul(F.mul(t1, cs_d2(c)), t2)
      +dd = F.mul(F.add(z1, z1), z2)
      +e = F.sub(b, a)
      +f = F.sub(dd, cc)
      +g = F.add(dd, cc)
      +h = F.add(b, a)
      Pt{F.mul(e, f), F.mul(g, h), F.mul(f, g), F.mul(e, h)}

# RFC 8032 5.1.4, doubling
def double(p: Pt) -> Pt:
  match p:
    case Pt{+x1, +y1, +z1, t1}:
      +a = F.sq(x1)
      +b = F.sq(y1)
      +zz = F.sq(z1)
      +cc = F.add(zz, zz)
      +h = F.add(a, b)
      +e = F.sub(h, F.sq(F.add(x1, y1)))
      +g = F.sub(a, b)
      +f = F.add(cc, g)
      Pt{F.mul(e, f), F.mul(g, h), F.mul(f, g), F.mul(e, h)}

# s == 0: p; s == 1: q
def select(+s: U32, p: Pt, q: Pt) -> Pt:
  match p q:
    case Pt{x1, y1, z1, t1} Pt{x2, y2, z2, t2}:
      Pt{F.select(s, x1, x2), F.select(s, y1, y2), F.select(s, z1, z2), F.select(s, t1, t2)}

# [bits t = n - 1 .. 0 of bs] p added to 2^n q: double, add, select
def smul(n: Nat, +c: Cs, +bs: List<&2, U32>, +p: Pt, q: Pt) -> Pt:
  match n:
    case 0n:
      q
    case 1n+ +t:
      +q2 = double(q)
      smul(t, c, bs, p, select(X.kbit(bs, t), q2, add(c, q2, p)))

# [k] p for a byte-string scalar k
def mul(+c: Cs, +k: List<&2, U32>, +p: Pt) -> Pt:
  smul(Nat.mul(8n, X.len(k)), c, k, p, identity())

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
def encode(p: Pt) -> List<&2, U32>:
  match p:
    case Pt{+x, +y, +z, t}:
      +zi = F.inv(z)
      set_top(F.to_bytes(F.mul(y, zi)), F.parity(F.mul(x, zi)))

# y >= p: the carry of y + 2^256 - p is 1
def ge_p(+y: List<&2, U32>) -> Bool:
  U32.is_eq(F.cr_out(F.carry(F.addl(y, F.comp_p()), 0)), 1)

def dec_fin(+x: List<&2, U32>, +y: List<&2, U32>, +x0: U32, fail: Bool) -> Maybe<&2, Pt>:
  match fail:
    case True{}:
      None{}
    case False{}:
      +x2 = F.select(U32.xor(F.parity(x), x0), x, F.neg(x))
      Some{Pt{x2, y, F.one(), F.mul(x2, y)}}

def dec_root(+c: Cs, +x: List<&2, U32>, +y: List<&2, U32>, +x0: U32, +u: List<&2, U32>, +vxx: List<&2, U32>, is_u: Bool, is_nu: Bool) -> Maybe<&2, Pt>:
  match is_u:
    case True{}:
      dec_fin(x, y, x0, Bool.and(F.is_zero(x), U32.is_eq(x0, 1)))
    case False{}:
      match is_nu:
        case True{}:
          +x1 = F.mul(x, cs_s(c))
          dec_fin(x1, y, x0, Bool.and(F.is_zero(x1), U32.is_eq(x0, 1)))
        case False{}:
          None{}

def dec_y(+c: Cs, +y: List<&2, U32>, +x0: U32, bad: Bool) -> Maybe<&2, Pt>:
  match bad:
    case True{}:
      None{}
    case False{}:
      +yy = F.sq(y)
      +u = F.sub(yy, F.one())
      +v = F.add(F.mul(cs_d(c), yy), F.one())
      +v3 = F.mul(F.sq(v), v)
      +v7 = F.mul(F.sq(v3), v)
      +x = F.mul(F.mul(u, v3), F.pow_p58(F.mul(u, v7)))
      +vxx = F.mul(v, F.sq(x))
      dec_root(c, x, y, x0, u, vxx, F.eq(vxx, u), F.eq(vxx, F.neg(u)))

# RFC 8032 5.1.3 on 32 bytes below 256
def decode(+c: Cs, +bs: List<&2, U32>) -> Maybe<&2, Pt>:
  +y = F.of_bytes(bs)
  dec_y(c, y, X.kbit(bs, 255n), ge_p(y))

# the same point: X1 Z2 == X2 Z1 and Y1 Z2 == Y2 Z1
def equal(p: Pt, q: Pt) -> Bool:
  match p q:
    case Pt{+x1, +y1, +z1, t1} Pt{+x2, +y2, +z2, t2}:
      Bool.and(F.eq(F.mul(x1, z2), F.mul(x2, z1)), F.eq(F.mul(y1, z2), F.mul(y2, z1)))

# the base point: y = 4 / 5, x even
def base_of(m: Maybe<&2, Pt>) -> Pt:
  match m:
    case None{}:
      identity()
    case Some{p}:
      p

def base(+c: Cs) -> Pt:
  base_of(decode(c, F.to_bytes(F.mul(F.small(4), F.inv(F.small(5))))))
