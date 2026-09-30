import Base
import ../curve25519/field.bend as F
import ../curve25519/fe.bend as FE
import ../curve25519/x25519.bend as X
import ../curve25519/limbs.bend as LS
import ./pick.bend as PK

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
  FE.pow_bits(R, x, [False{}, True{}, True{}], FE.p250(R, x))

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

# the same without T (for a point that is doubled next: doubling does
# not read T)
def double_nt(+R: Nat, p: Pt) -> Pt:
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
      Pt{FE.mul(R, e, f), FE.mul(R, g, h), FE.mul(R, f, g), FE.zero()}

# s == 0: p; s == 1: q
def select(+s: U32, p: Pt, q: Pt) -> Pt:
  match p q:
    case Pt{x1, y1, z1, t1} Pt{x2, y2, z2, t2}:
      Pt{FE.select(s, x1, x2), FE.select(s, y1, y2), FE.select(s, z1, z2), FE.select(s, t1, t2)}

# [bits t = n - 1 .. 0 of bs] p added to 2^n q: double, add, select (the
# same work for every bit: for secret scalars)
# (p is inspected first: on an unknown point the proof checker keeps the
# call instead of unrolling the loop)
def smul(+p: Pt, n: Nat, +c: Cs, +bs: List<&2, U32>, q: Pt) -> Pt:
  match p:
    case Pt{x0, y0, z0, t0}:
      match n:
        case 0n:
          q
        case 1n+ +t:
          +q2 = double(cs_r(c), q)
          smul(p, t, c, bs, select(X.kbit(bs, t), q2, add(c, q2, p)))

# the same result, adding only on a one bit (for public scalars)
def smul_bit(z: Bool, +c: Cs, +p: Pt, q2: Pt) -> Pt:
  match z:
    case True{}:
      q2
    case False{}:
      add(c, q2, p)

def smul_vt(+p: Pt, n: Nat, +c: Cs, +bs: List<&2, U32>, q: Pt) -> Pt:
  match p:
    case Pt{x0, y0, z0, t0}:
      match n:
        case 0n:
          q
        case 1n+ +t:
          smul_vt(p, t, c, bs, smul_bit(U32.is_eq(X.kbit(bs, t), 0), c, p, double(cs_r(c), q)))

# [k] p for a byte-string scalar k (secret)
def mul(+c: Cs, +k: List<&2, U32>, +p: Pt) -> Pt:
  smul(p, X.bitlen(k), c, k, identity())

# [k] p for a public scalar k
def mul_vt(+c: Cs, +k: List<&2, U32>, +p: Pt) -> Pt:
  smul_vt(p, X.bitlen(k), c, k, identity())

# ---- multiplication of the base point by a table ----
#
# With the 64 rows [0 P, 1 P, ..., 15 P] for P = 16^j B (table, made once in
# the context), [k] B is the sum over the 64 hexadecimal digits k_j of k of
# row j's entry k_j: 64 additions and no doubling. Entries are kept ready
# for additions (Cp), and a secret digit selects its entry by masks over
# the whole row (look), not by an index.

# a point prepared as the second operand of additions: Y + X, Y - X,
# 2 d T, 2 Z
type Cp is Data:
  Cp{ypx: FE.Fe, ymx: FE.Fe, t2d: FE.Fe, z2: FE.Fe}

def cached(+c: Cs, p: Pt) -> Cp:
  match p:
    case Pt{+x, +y, +z, t}:
      +R = cs_r(c)
      Cp{FE.add(R, y, x), FE.sub(R, y, x), FE.mul(R, t, cs_d2(c)), FE.add(R, z, z)}

# p + q for a prepared q: the addition of RFC 8032 5.1.4 with the factors
# of q already formed
def add_c(+R: Nat, p: Pt, q: Cp) -> Pt:
  match p q:
    case Pt{+x1, +y1, +z1, +t1} Cp{ypx, ymx, t2d, z2}:
      +a = FE.mul(R, FE.sub(R, y1, x1), ymx)
      +b = FE.mul(R, FE.add(R, y1, x1), ypx)
      +cc = FE.mul(R, t1, t2d)
      +dd = FE.mul(R, z1, z2)
      +e = FE.sub(R, b, a)
      +f = FE.sub(R, dd, cc)
      +g = FE.add(R, dd, cc)
      +h = FE.add(R, b, a)
      Pt{FE.mul(R, e, f), FE.mul(R, g, h), FE.mul(R, f, g), FE.mul(R, e, h)}

# the same without T
def add_c_nt(+R: Nat, p: Pt, q: Cp) -> Pt:
  match p q:
    case Pt{+x1, +y1, +z1, +t1} Cp{ypx, ymx, t2d, z2}:
      +a = FE.mul(R, FE.sub(R, y1, x1), ymx)
      +b = FE.mul(R, FE.add(R, y1, x1), ypx)
      +cc = FE.mul(R, t1, t2d)
      +dd = FE.mul(R, z1, z2)
      +e = FE.sub(R, b, a)
      +f = FE.sub(R, dd, cc)
      +g = FE.add(R, dd, cc)
      +h = FE.add(R, b, a)
      Pt{FE.mul(R, e, f), FE.mul(R, g, h), FE.mul(R, f, g), FE.zero()}

def cp_zero() -> Cp:
  Cp{FE.zero(), FE.zero(), FE.zero(), FE.zero()}

# the entry of a 16-entry row whose mask is 1 (the other masks 0)
def look16(ms: List<&2, Nat>, r: List<&2, Cp>) -> Cp:
  match ms r:
    case Con{+m0, Con{+m1, Con{+m2, Con{+m3, Con{+m4, Con{+m5, Con{+m6, Con{+m7, Con{+m8, Con{+m9, Con{+m10, Con{+m11, Con{+m12, Con{+m13, Con{+m14, Con{+m15, mt}}}}}}}}}}}}}}}} Con{Cp{a0, b0, c0, d0}, Con{Cp{a1, b1, c1, d1}, Con{Cp{a2, b2, c2, d2}, Con{Cp{a3, b3, c3, d3}, Con{Cp{a4, b4, c4, d4}, Con{Cp{a5, b5, c5, d5}, Con{Cp{a6, b6, c6, d6}, Con{Cp{a7, b7, c7, d7}, Con{Cp{a8, b8, c8, d8}, Con{Cp{a9, b9, c9, d9}, Con{Cp{a10, b10, c10, d10}, Con{Cp{a11, b11, c11, d11}, Con{Cp{a12, b12, c12, d12}, Con{Cp{a13, b13, c13, d13}, Con{Cp{a14, b14, c14, d14}, Con{Cp{a15, b15, c15, d15}, rt}}}}}}}}}}}}}}}}:
      Cp{PK.sel16(PK.M16{m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15}, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15), PK.sel16(PK.M16{m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15}, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15), PK.sel16(PK.M16{m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15}, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15), PK.sel16(PK.M16{m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15}, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15)}
    case _ _:
      cp_zero()

# entry d of a row (d < 16), every entry read
def look(d: Nat, r: List<&2, Cp>) -> Cp:
  look16(LS.ohl(16n, d), r)

# [cached(m), cached(m + p), ...]: n entries
def row_go(n: Nat, +c: Cs, +p: Pt, +m: Pt) -> List<&2, Cp>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{cached(c, m), row_go(k, c, p, add(c, m, p))}

# [0 p, 1 p, ..., 15 p], prepared
def row(+c: Cs, +p: Pt) -> List<&2, Cp>:
  Con{cached(c, identity()), row_go(15n, c, p, p)}

# 16 p
def dbl4(+R: Nat, p: Pt) -> Pt:
  double(R, double(R, double(R, double(R, p))))

# the rows of p, 16 p, 16^2 p, ...: n of them
def table(n: Nat, +c: Cs, +p: Pt) -> List<&2, List<&2, Cp>>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{row(c, p), table(k, c, dbl4(cs_r(c), p))}

# the 64 rows of the base point. The count is the radix 2^17 over 2^11:
# the proof checker sees the radix as a variable and never builds the
# table when it compares terms containing it
def base_table(+c: Cs, +b: Pt) -> List<&2, List<&2, Cp>>:
  table(Nat.div(cs_r(c), 2048n), c, b)

# the hexadecimal digits of a byte string, least significant first
def nibs(bs: List<&2, U32>) -> List<&2, Nat>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, bt}:
      +n = U32.to_nat(b)
      Con{Nat.mod(n, 16n), Con{Nat.div(n, 16n), nibs(bt)}}

# acc plus, for every row and its digit, the row's entry at the digit
def fb(+R: Nat, tab: List<&2, List<&2, Cp>>, ds: List<&2, Nat>, acc: Pt) -> Pt:
  match tab:
    case Nil{}:
      acc
    case Con{r, tt}:
      match ds:
        case Nil{}:
          acc
        case Con{d, dt}:
          fb(R, tt, dt, add_c(R, acc, look(d, r)))

# entry d of a row by its index (for public digits; the zero point when
# there is none)
def nthc(d: Nat, r: List<&2, Cp>) -> Cp:
  match d r:
    case _ Nil{}:
      cp_zero()
    case 0n Con{q, rt}:
      q
    case 1n+e Con{q, rt}:
      nthc(e, rt)

# the same sum with indexed entries (public digits)
def fbv(+R: Nat, tab: List<&2, List<&2, Cp>>, ds: List<&2, Nat>, acc: Pt) -> Pt:
  match tab:
    case Nil{}:
      acc
    case Con{r, tt}:
      match ds:
        case Nil{}:
          acc
        case Con{d, dt}:
          fbv(R, tt, dt, add_c(R, acc, nthc(d, r)))

# [k] B for a 32-byte scalar k and the table of B (secret k: every lookup
# reads its whole row)
def mul_base(+R: Nat, tab: List<&2, List<&2, Cp>>, +k: List<&2, U32>) -> Pt:
  fb(R, tab, nibs(k), identity())

# [k] B for a public scalar k: the entries are indexed
def mul_base_vt(+R: Nat, tab: List<&2, List<&2, Cp>>, +k: List<&2, U32>) -> Pt:
  fbv(R, tab, nibs(k), identity())

# ---- multiplication of a public point by 4-bit windows ----

# the digits ds (least significant first) against the row rw = [0 a, ...,
# 15 a]: 16 ([rest] a) + [d] a, most significant digit first (256
# doublings and 64 additions for a 32-byte scalar)
def win(+R: Nat, +rw: List<&2, Cp>, ds: List<&2, Nat>) -> Pt:
  match ds:
    case Nil{}:
      identity()
    case Con{d, dt}:
      add_c(R, dbl4(R, win(R, rw, dt)), nthc(d, rw))

# 16 p, T computed only by the last doubling
def dbl4n(+R: Nat, p: Pt) -> Pt:
  double(R, double_nt(R, double_nt(R, double_nt(R, p))))

# win without T in the intermediate points (each is doubled next)
def winn(+R: Nat, +rw: List<&2, Cp>, ds: List<&2, Nat>) -> Pt:
  match ds:
    case Nil{}:
      identity()
    case Con{d, dt}:
      add_c_nt(R, dbl4n(R, winn(R, rw, dt)), nthc(d, rw))

# win with those savings (the same point: proofs/crypto/ed25519/pwinf.bend)
def winf(+R: Nat, +rw: List<&2, Cp>, ds: List<&2, Nat>) -> Pt:
  match ds:
    case Nil{}:
      identity()
    case Con{d, dt}:
      add_c(R, dbl4n(R, winn(R, rw, dt)), nthc(d, rw))

# [k] a for a public scalar k
def mul_win(+c: Cs, +k: List<&2, U32>, +a: Pt) -> Pt:
  winf(cs_r(c), row(c, a), nibs(k))

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

def base_go(+c: Cs) -> Pt:
  +R = cs_r(c)
  base_of(decode(c, FE.to_bytes(R, FE.mul(R, cs_small(c, 4n), FE.inv(R, cs_small(c, 5n))))))

# inspecting the radix first keeps the proof checker from running the
# decoding whenever it compares terms containing the base point
def base_r(r: Nat, +c: Cs) -> Pt:
  match r:
    case 0n:
      base_go(c)
    case 1n+q:
      base_go(c)

def base(+c: Cs) -> Pt:
  base_r(cs_r(c), c)
