import Base
import ../../../src/crypto/aes/types.bend as T
import ./poly.bend as P
import ./aes.bend as AES
import ../subtle.bend as Eq

# Executable specification of GCM (NIST SP 800-38D) over AES (FIPS 197),
# for 96-bit IVs and 128-bit tags. Bit strings are byte strings (U32 values
# below 256); a block is 16 bytes.

# ---- bits (section 6.1) ----

# The bits of a byte, the most significant (leftmost) first.
def byte_bits(x: U32) -> List<&2, Bool>:
  match x:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, rest}}}}}}}}}:
      [b7, b6, b5, b4, b3, b2, b1, b0]

def string_bits(xs: List<&2, U32>) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      List.append(&2, Bool, byte_bits(x), string_bits(rest))

# The byte whose bits, leftmost first, are the next eight of a bit string.
def bits_bytes(bs: List<&2, Bool>) -> List<&2, U32>:
  match bs:
    case b7 <> b6 <> b5 <> b4 <> b3 <> b2 <> b1 <> b0 <> rest:
      U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}} <> bits_bytes(rest)
    case _:
      Nil{}

# The first n bits of a bit string, zero-filled.
def word_of(n: Nat, bs: List<&2, Bool>) -> Word(n):
  match n bs:
    case 0n _:
      WNil{}
    case 1n+p Nil{}:
      WCon{False{}, word_of(p, Nil{})}
    case 1n+p b <> rest:
      WCon{b, word_of(p, rest)}

# ---- GF(2^128) (section 6.3) ----

# Bit i of a block (bit 0 the leftmost) is the coefficient of x^i, and
# f(x) = 1 + x + x^2 + x^7 + x^128: x^128 = 1 + x + x^2 + x^7 (R = 11100001 || 0^120).
def block(xs: List<&2, U32>) -> Word(128n):
  word_of(128n, string_bits(xs))

def block_bytes(w: Word(128n)) -> List<&2, U32>:
  bits_bytes(P.coefficients(128n, w))

def low() -> Word(128n):
  WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, Word.zero(120n)}}}}}}}}

# X * Y: the polynomial product reduced modulo f.
def mul(x: Word(128n), y: Word(128n)) -> Word(128n):
  P.reduce(128n, low(), P.mul(P.coefficients(128n, x), P.coefficients(128n, y)))

# ---- GHASH (section 6.4, Algorithm 2): Y_i = (Y_(i-1) xor X_i) * H ----

def ghash(+h: Word(128n), x: List<&2, U32>, y: Word(128n)) -> Word(128n):
  match x:
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> rest:
      ghash(h, rest, mul(Word.xor(128n, y, block([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15])), h))
    case _:
      y

# ---- GCTR (section 6.5) ----

# inc_32: the rightmost 32 bits, as an integer, plus one modulo 2^32.
def int32(+a: U32, +b: U32, +c: U32, +d: U32) -> U32:
  U32{word_of(32n, List.reverse(&2, Bool, string_bits([a, b, c, d])))}

def str32(w: U32) -> List<&2, U32>:
  match w:
    case U32{bits}:
      bits_bytes(List.reverse(&2, Bool, P.coefficients(32n, bits)))

def inc32(x: List<&2, U32>) -> List<&2, U32>:
  match x:
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> c0 <> c1 <> c2 <> c3 <> rest:
      List.append(&2, U32, [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11], str32(U32.inc(int32(c0, c1, c2, c3))))
    case _:
      Nil{}

# CIPH_K on a 16-byte block.
def ciph(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +x: List<&2, U32>) -> List<&2, U32>:
  AES.bytes_of(AES.encrypt(nk, nr, key, AES.state_of(x)))

# X xor K over the length of X (MSB_len(X) of K when X is the shorter).
def xor_bytes(x: List<&2, U32>, k: List<&2, U32>) -> List<&2, U32>:
  match x k:
    case a <> xs b <> ks:
      U32.xor(a, b) <> xor_bytes(xs, ks)
    case _ _:
      Nil{}

def gctr(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +x: List<&2, U32>, +cb: List<&2, U32>) -> List<&2, U32>:
  match x:
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> rest:
      List.append(&2, U32, xor_bytes([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15], ciph(nk, nr, key, cb)),
        gctr(nk, nr, key, rest, inc32(cb)))
    case _:
      xor_bytes(x, ciph(nk, nr, key, cb))

# ---- GCM (section 7) ----

def zeros(n: Nat) -> List<&2, U32>:
  List.replicate(U32, n, 0)

# X || 0^v, v = 128*ceil(len(X)/128) - len(X): zero bytes complete the last
# 16-byte block.
def pad(+x: List<&2, U32>) -> List<&2, U32>:
  match x:
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> rest:
      b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> pad(rest)
    case Nil{}:
      Nil{}
    case _:
      List.append(&2, U32, x, zeros(Nat.sub(16n, List.length(&2, U32, x))))

# [n]_(8*width), most significant byte first.
def octets(width: Nat, +n: Nat) -> List<&2, U32>:
  match width:
    case 0n:
      Nil{}
    case 1n+p:
      List.append(&2, U32, octets(p, Nat.div(n, 256n)), [U32.from_nat(Nat.mod(n, 256n))])

# [len(X)]_64: the bit length of X.
def len64(+xs: List<&2, U32>) -> List<&2, U32>:
  octets(8n, Nat.mul(8n, List.length(&2, U32, xs)))

# Algorithm 4, J0 = IV || 0^31 || 1 for a 96-bit IV.
def hash_key(+nk: Nat, +nr: Nat, +key: List<&2, U32>) -> Word(128n):
  block(ciph(nk, nr, key, zeros(16n)))

def j0(+iv: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, iv, [0, 0, 0, 1])

def tag(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +iv: List<&2, U32>, +aad: List<&2, U32>, +c: List<&2, U32>) -> List<&2, U32>:
  gctr(nk, nr, key, block_bytes(ghash(hash_key(nk, nr, key),
    List.append(&2, U32, pad(aad), List.append(&2, U32, pad(c), List.append(&2, U32, len64(aad), len64(c)))), Word.zero(128n))), j0(iv))

# GCM-AE_K(IV, P, A) = (C, T), returned as C || T.
def seal(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +iv: List<&2, U32>, +aad: List<&2, U32>, pt: List<&2, U32>) -> List<&2, U32>:
  +c = gctr(nk, nr, key, pt, inc32(j0(iv)))
  List.append(&2, U32, c, tag(nk, nr, key, iv, aad, c))

def accept(ok: Bool, p: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{p}
    case False{}:
      None{}

def open_checked(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +iv: List<&2, U32>, +aad: List<&2, U32>, +c: List<&2, U32>, t: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  accept(Eq.equal(t, tag(nk, nr, key, iv, aad, c)), gctr(nk, nr, key, c, inc32(j0(iv))))

# GCM-AD_K(IV, C, A, T), the input being C || T: FAIL (None) unless T is
# the tag of C.
def open_split(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +iv: List<&2, U32>, +aad: List<&2, U32>, +input: List<&2, U32>, +n: Nat, short: Bool) -> Maybe<&2, List<&2, U32>>:
  match short:
    case True{}:
      None{}
    case False{}:
      open_checked(nk, nr, key, iv, aad, List.take(&2, U32, input, Nat.sub(n, 16n)), List.drop(&2, U32, input, Nat.sub(n, 16n)))

def open(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +iv: List<&2, U32>, +aad: List<&2, U32>, +input: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  +n = List.length(&2, U32, input)
  open_split(nk, nr, key, iv, aad, input, n, Nat.is_lt(n, 16n))
