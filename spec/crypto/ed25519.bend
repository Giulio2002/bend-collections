import Base
import ../lib/common.bend as C
import ./curve25519/field.bend as FS
import ./curve25519/x25519.bend as SX
import ./sha512.bend as SHA
import ../../src/crypto/ed25519/ed25519.bend as E
import ../../src/crypto/ed25519/scalar.bend as ESC

# Ed25519, RFC 8032 section 5.1, over the natural numbers: a transcription
# of the RFC's encoding (5.1.2), decoding (5.1.3), point addition and
# doubling in extended coordinates (5.1.4), key generation (5.1.5),
# signing (5.1.6) and verification (5.1.7, the cofactorless equation
# [S]B == R + [k]A', with S < L required), every field operation mod p
# (FS.fadd, ...), every scalar mod L, the hash FIPS 180-4 SHA-512
# (spec/crypto/sha512.bend). Scalar multiplication is double-and-add over
# the scalar's bits, most significant first (HACL*'s Spec.Ed25519 fixes an
# algorithm in the same way). `one` is the symbolic 1 of
# spec/crypto/curve25519/field.bend: every constant above 2^13 is written
# with it (L, 121665, 121666).
#
#   clause             statement
#   Scalar.reduce      ESC.reduce(bs) has the value value(bs) mod L
#   Scalar.mul_add     ESC.mul_add(k, s, r) has the value (r + k s) mod L
#   Ed25519.public     the implementation's public key is public_key(seed)
#   Ed25519.sign       the implementation's signature is sign(seed, msg)
#   Ed25519.verify     the implementation's verdict is verify(pk, msg, sig)

# ---- scalars ----

# L = 2^252 + 27742317777372353535851937790883648493, little-endian bytes
def ell_bytes() -> List<&2, U32>:
  [237, 211, 245, 92, 26, 99, 18, 88, 214, 156, 247, 162, 222, 249, 222, 20,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16]

def ell(+one: Nat) -> Nat:
  FS.uvalue(one, ell_bytes())

# ---- the curve ----

type EPt is Data:
  EPt{x: Nat, y: Nat, z: Nat, t: Nat}

# d = -121665 / 121666
def dconst(+one: Nat, +p: Nat) -> Nat:
  FS.fmul(p, FS.fsub(p, 0n, FS.digits(one, [65n, 219n, 1n])), FS.finv(p, FS.digits(one, [66n, 219n, 1n])))

# 2^((p - 1) / 4), a square root of -1
def sqm1(+p: Nat) -> Nat:
  FS.fpow(p, 2n, Nat.div(Nat.sub(p, 1n), 4n))

def identity() -> EPt:
  EPt{0n, 1n, 1n, 0n}

# 5.1.4: A = (Y1-X1)(Y2-X2), B = (Y1+X1)(Y2+X2), C = T1 2d T2, D = Z1 2 Z2,
# E = B-A, F = D-C, G = D+C, H = B+A, X3 = EF, Y3 = GH, T3 = EH, Z3 = FG
def add(+p: Nat, +d: Nat, a: EPt, b: EPt) -> EPt:
  match a b:
    case EPt{+x1, +y1, +z1, +t1} EPt{+x2, +y2, +z2, +t2}:
      +ea = FS.fmul(p, FS.fsub(p, y1, x1), FS.fsub(p, y2, x2))
      +eb = FS.fmul(p, FS.fadd(p, y1, x1), FS.fadd(p, y2, x2))
      +ec = FS.fmul(p, FS.fmul(p, t1, FS.fadd(p, d, d)), t2)
      +ed = FS.fmul(p, FS.fadd(p, z1, z1), z2)
      +ee = FS.fsub(p, eb, ea)
      +ef = FS.fsub(p, ed, ec)
      +eg = FS.fadd(p, ed, ec)
      +eh = FS.fadd(p, eb, ea)
      EPt{FS.fmul(p, ee, ef), FS.fmul(p, eg, eh), FS.fmul(p, ef, eg), FS.fmul(p, ee, eh)}

# 5.1.4: A = X1^2, B = Y1^2, C = 2 Z1^2, H = A+B, E = H-(X1+Y1)^2, G = A-B,
# F = C+G, X3 = EF, Y3 = GH, T3 = EH, Z3 = FG
def double(+p: Nat, a: EPt) -> EPt:
  match a:
    case EPt{+x1, +y1, +z1, t1}:
      +ea = FS.fmul(p, x1, x1)
      +eb = FS.fmul(p, y1, y1)
      +zz = FS.fmul(p, z1, z1)
      +ec = FS.fadd(p, zz, zz)
      +eh = FS.fadd(p, ea, eb)
      +xy = FS.fadd(p, x1, y1)
      +ee = FS.fsub(p, eh, FS.fmul(p, xy, xy))
      +eg = FS.fsub(p, ea, eb)
      +ef = FS.fadd(p, ec, eg)
      EPt{FS.fmul(p, ee, ef), FS.fmul(p, eg, eh), FS.fmul(p, ef, eg), FS.fmul(p, ee, eh)}

def pick(b: Nat, q: EPt, r: EPt) -> EPt:
  match b:
    case 0n:
      q
    case 1n+c:
      r

# bits t = n - 1 .. 0 of k: q = 2 q, plus a on a one bit
def smul(+p: Nat, +d: Nat, n: Nat, +k: Nat, +a: EPt, q: EPt) -> EPt:
  match n:
    case 0n:
      q
    case 1n+ +t:
      +q2 = double(p, q)
      smul(p, d, t, k, a, pick(SX.kbit(k, t), q2, add(p, d, q2, a)))

# [k] a for a scalar below 2^256: 256 bits, written 2^8 one (one == 1), so
# the proof checker never unrolls the loop
def mul(+one: Nat, +p: Nat, +d: Nat, +k: Nat, +a: EPt) -> EPt:
  smul(p, d, C.shift(8n, one), k, a, identity())

# ---- encoding, 5.1.2 ----

# the most significant bit of the final octet set to b
def set_msb(xs: List<&2, U32>, +b: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, xt}:
      match xt:
        case Nil{}:
          Con{U32.or(x, U32.shln(b, 7n)), Nil{}}
        case Con{y, yt}:
          Con{x, set_msb(Con{y, yt}, b)}

# n = 32 bytes
def encode_n(n: Nat, +p: Nat, a: EPt) -> List<&2, U32>:
  match a:
    case EPt{+x, +y, +z, t}:
      +zi = FS.finv(p, z)
      set_msb(SX.le_bytes(n, FS.fmul(p, y, zi)), U32.from_nat(Nat.mod(FS.fmul(p, x, zi), 2n)))

# 32 bytes, written 2^5 one (one == 1): the byte count stays symbolic, so the
# checker never expands an encoding (and the SHA-512 over it) into bytes
def encode(+one: Nat, +p: Nat, a: EPt) -> List<&2, U32>:
  encode_n(C.shift(5n, one), p, a)

# ---- decoding, 5.1.3 ----

def dec_fin(+p: Nat, +x: Nat, +y: Nat, +x0: Nat, fail: Bool) -> Maybe<&2, EPt>:
  match fail:
    case True{}:
      None{}
    case False{}:
      +x2 = SX.cs_fst(SX.bxor(Nat.mod(x, 2n), x0), x, FS.fsub(p, 0n, x))
      Some{EPt{x2, y, 1n, FS.fmul(p, x2, y)}}

def dec_root(+p: Nat, +x: Nat, +y: Nat, +x0: Nat, is_u: Bool, is_nu: Bool) -> Maybe<&2, EPt>:
  match is_u:
    case True{}:
      dec_fin(p, x, y, x0, Bool.and(Nat.is_eq(x, 0n), Nat.is_eq(x0, 1n)))
    case False{}:
      match is_nu:
        case True{}:
          +x1 = FS.fmul(p, x, sqm1(p))
          dec_fin(p, x1, y, x0, Bool.and(Nat.is_eq(x1, 0n), Nat.is_eq(x0, 1n)))
        case False{}:
          None{}

# u = y^2 - 1, v = d y^2 + 1, x = u v^3 (u v^7)^((p-5)/8); x or x sqrt(-1)
# when v x^2 is u or -u; fail when x = 0 and x_0 = 1; x = p - x (here as
# -x mod p) when x mod 2 != x_0
def dec_y(+p: Nat, +d: Nat, +y: Nat, +x0: Nat, bad: Bool) -> Maybe<&2, EPt>:
  match bad:
    case True{}:
      None{}
    case False{}:
      +yy = FS.fmul(p, y, y)
      +u = FS.fsub(p, yy, 1n)
      +v = FS.fadd(p, FS.fmul(p, d, yy), 1n)
      +v3 = FS.fmul(p, FS.fmul(p, v, v), v)
      +v7 = FS.fmul(p, FS.fmul(p, v3, v3), v)
      +x = FS.fmul(p, FS.fmul(p, u, v3), FS.fpow(p, FS.fmul(p, u, v7), Nat.div(Nat.sub(p, 5n), 8n)))
      +vxx = FS.fmul(p, v, FS.fmul(p, x, x))
      dec_root(p, x, y, x0, Nat.is_eq(vxx, u), Nat.is_eq(vxx, FS.fsub(p, 0n, u)))

# bit 255 is x_0; the rest is y, rejected when y >= p
def decode(+p: Nat, +d: Nat, +bs: List<&2, U32>) -> Maybe<&2, EPt>:
  +y = FS.value(SX.mask_last(bs))
  dec_y(p, d, y, SX.kbit(FS.value(bs), 255n), Bool.not(Nat.is_lt(y, p)))

# ---- the base point: y = 4/5, x even ----

def base_of(m: Maybe<&2, EPt>) -> EPt:
  match m:
    case None{}:
      identity()
    case Some{a}:
      a

def base(+p: Nat, +d: Nat) -> EPt:
  base_of(decode(p, d, SX.le_bytes(32n, FS.fmul(p, 4n, FS.finv(p, 5n)))))

# the same point: X1 Z2 == X2 Z1 and Y1 Z2 == Y2 Z1
def equal(+p: Nat, a: EPt, b: EPt) -> Bool:
  match a b:
    case EPt{+x1, +y1, +z1, t1} EPt{+x2, +y2, +z2, t2}:
      Bool.and(Nat.is_eq(FS.fmul(p, x1, z2), FS.fmul(p, x2, z1)), Nat.is_eq(FS.fmul(p, y1, z2), FS.fmul(p, y2, z1)))

# ---- bytes ----

def first(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      match xs:
        case Nil{}:
          Nil{}
        case Con{x, xt}:
          Con{x, first(m, xt)}

def rest(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      xs
    case 1n+m:
      match xs:
        case Nil{}:
          Nil{}
        case Con{x, xt}:
          rest(m, xt)

def cat(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      ys
    case Con{x, xt}:
      Con{x, cat(xt, ys)}

# k = SHA-512(R || A || M) mod L; a function of R first, so a comparison of
# two such terms compares R, A and M once instead of walking the digest
def hram(+one: Nat, rb: List<&2, U32>, +a: List<&2, U32>, +msg: List<&2, U32>) -> Nat:
  match rb:
    case Nil{}:
      Nat.mod(FS.value(SHA.sha512_bytes(cat(Nil{}, cat(a, msg)))), ell(one))
    case Con{x, xt}:
      Nat.mod(FS.value(SHA.sha512_bytes(cat(Con{x, xt}, cat(a, msg)))), ell(one))

# ---- 5.1.5 key generation ----

def secret(+h: List<&2, U32>) -> Nat:
  FS.value(SX.clamp(first(32n, h)))

def public_of(+one: Nat, +p: Nat, +d: Nat, +h: List<&2, U32>) -> List<&2, U32>:
  encode(one, p, mul(one, p, d, secret(h), base(p, d)))

def public_key(+one: Nat, +seed: List<&2, U32>) -> List<&2, U32>:
  +p = FS.prime(one)
  public_of(one, p, dconst(one, p), SHA.sha512_bytes(seed))

# ---- 5.1.6 signing ----

def sign_with(+one: Nat, +p: Nat, +d: Nat, +h: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  +el = ell(one)
  +a = public_of(one, p, d, h)
  +r = Nat.mod(FS.value(SHA.sha512_bytes(cat(rest(32n, h), msg))), el)
  +rb = encode(one, p, mul(one, p, d, r, base(p, d)))
  +k = hram(one, rb, a, msg)
  cat(rb, SX.le_bytes(C.shift(5n, one), Nat.mod(Nat.add(r, Nat.mul(k, secret(h))), el)))

def sign(+one: Nat, +seed: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  +p = FS.prime(one)
  sign_with(one, p, dconst(one, p), SHA.sha512_bytes(seed), msg)

# ---- 5.1.7 verification (cofactorless) ----

def check(+one: Nat, +p: Nat, +d: Nat, +s: Nat, +rb: List<&2, U32>, +pk: List<&2, U32>, +msg: List<&2, U32>, ra: Maybe<&2, EPt>, aa: Maybe<&2, EPt>) -> Bool:
  match ra aa:
    case Some{r} Some{+a}:
      +k = hram(one, rb, pk, msg)
      equal(p, mul(one, p, d, s, base(p, d)), add(p, d, r, mul(one, p, d, k, a)))
    case _ _:
      False{}

def verify_with(+one: Nat, +p: Nat, +d: Nat, +pk: List<&2, U32>, +msg: List<&2, U32>, +rb: List<&2, U32>, +s: Nat, s_ok: Bool) -> Bool:
  match s_ok:
    case True{}:
      check(one, p, d, s, rb, pk, msg, decode(p, d, rb), decode(p, d, pk))
    case False{}:
      False{}

def verify(+one: Nat, +pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>) -> Bool:
  +p = FS.prime(one)
  +s = FS.value(rest(32n, sig))
  verify_with(one, p, dconst(one, p), pk, msg, first(32n, sig), s, Nat.is_lt(s, ell(one)))

# ---- clauses ----

def Scalar.reduce(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +hb: {FS.bytes_ok(64n, bs) == True{} : Bool}) -> Type:
  {FS.value(ESC.reduce(bs)) == Nat.mod(FS.value(bs), ell(one)) : Nat}

def Scalar.mul_add(+one: Nat, +h1: {one == 1n : Nat}, +k: List<&2, U32>, +s: List<&2, U32>, +r: List<&2, U32>, +hk: {FS.tight(k) == True{} : Bool}, +hs: {FS.tight(s) == True{} : Bool}, +hr: {FS.tight(r) == True{} : Bool}, +hsl: {Nat.is_lt(FS.value(s), ell(one)) == True{} : Bool}, +hrl: {Nat.is_lt(FS.value(r), ell(one)) == True{} : Bool}) -> Type:
  {FS.value(ESC.mul_add(k, s, r)) == Nat.mod(Nat.add(FS.value(r), Nat.mul(FS.value(k), FS.value(s))), ell(one)) : Nat}

def Ed25519.public(+one: Nat, +h1: {one == 1n : Nat}, +seed: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}) -> Type:
  {E.public_key(seed) == public_key(one, seed) : List<&2, U32>}

def Ed25519.sign(+one: Nat, +h1: {one == 1n : Nat}, +seed: List<&2, U32>, +msg: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}) -> Type:
  {E.sign_raw(seed, msg) == sign(one, seed, msg) : List<&2, U32>}

def Ed25519.verify(+one: Nat, +h1: {one == 1n : Nat}, +pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>, +hp: {FS.tight(pk) == True{} : Bool}, +hg: {FS.bytes_ok(64n, sig) == True{} : Bool}) -> Type:
  {E.verify_raw(pk, msg, sig) == verify(one, pk, msg, sig) : Bool}
