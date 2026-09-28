import Base
import ../../../src/crypto/aes/types.bend as T
import ./poly.bend as P

# Executable specification of AES (FIPS 197), transcribed from the standard.
# Only the neutral Quad/State representation is shared with the
# implementation. A byte is a U32; the finite-field operations read its low
# eight bits b7..b0 (section 3.2), the bytes of the API are all below 256.

# Section 3.2/4: the byte b7 b6 ... b0 is the polynomial b7 x^7 + ... + b0.
def bits(x: U32) -> List<&2, Bool>:
  match x:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, rest}}}}}}}}}:
      [b0, b1, b2, b3, b4, b5, b6, b7]

def byte(w: Word(8n)) -> U32:
  match w:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}:
      U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}}

# Section 4.2: m(x) = x^8 + x^4 + x^3 + x + 1, so x^8 = x^4 + x^3 + x + 1.
def low() -> Word(8n):
  WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}

# Section 4.2: the product of two bytes is their polynomial product modulo m(x).
def mul(+a: U32, +b: U32) -> U32:
  byte(P.reduce(8n, low(), P.mul(bits(a), bits(b))))

# Section 4.4 / 5.1.1: the multiplicative inverse b of a nonzero a is the byte
# with a * b = {01}; {00} is mapped to itself. Searched among {01}..{ff}.
def search(n: Nat, +a: U32, +b: U32) -> U32:
  match n:
    case 0n:
      0
    case 1n+p:
      Bool.pick(U32, U32.is_eq(mul(a, b), 1), b, search(p, a, U32.inc(b)))

def inverse(+a: U32) -> U32:
  search(255n, a, 1)

def nth_bit(xs: List<&2, Bool>, n: Nat) -> Bool:
  match xs n:
    case Nil{} _:
      False{}
    case x <> rest 0n:
      x
    case x <> rest 1n+p:
      nth_bit(rest, p)

# Section 5.1.1, equation (5.1): b'_i = b_i + b_(i+4 mod 8) + b_(i+5 mod 8)
#   + b_(i+6 mod 8) + b_(i+7 mod 8) + c_i, with c = {63}.
def affine_bit(+b: List<&2, Bool>, +c: List<&2, Bool>, +i: Nat) -> Bool:
  Bool.xor(Bool.xor(Bool.xor(Bool.xor(Bool.xor(nth_bit(b, i),
    nth_bit(b, Nat.mod(Nat.add(i, 4n), 8n))), nth_bit(b, Nat.mod(Nat.add(i, 5n), 8n))),
    nth_bit(b, Nat.mod(Nat.add(i, 6n), 8n))), nth_bit(b, Nat.mod(Nat.add(i, 7n), 8n))),
    nth_bit(c, i))

def affine(+x: U32) -> U32:
  +b = bits(x)
  +c = bits(99)
  byte(WCon{affine_bit(b, c, 0n), WCon{affine_bit(b, c, 1n), WCon{affine_bit(b, c, 2n),
    WCon{affine_bit(b, c, 3n), WCon{affine_bit(b, c, 4n), WCon{affine_bit(b, c, 5n),
    WCon{affine_bit(b, c, 6n), WCon{affine_bit(b, c, 7n), WNil{}}}}}}}}})

# Section 5.1.1: the S-box is the inverse followed by the affine transformation.
def sbox(+x: U32) -> U32:
  affine(inverse(x))

# s[r,c]: byte r of column c.
def byte_at(w: T.Quad, r: Nat) -> U32:
  match w r:
    case T.W{a, b, c, d} 0n:
      a
    case T.W{a, b, c, d} 1n:
      b
    case T.W{a, b, c, d} 2n:
      c
    case T.W{a, b, c, d} 3n+p:
      d

def column(s: T.State, c: Nat) -> T.Quad:
  match s c:
    case T.S{c0, c1, c2, c3} 0n:
      c0
    case T.S{c0, c1, c2, c3} 1n:
      c1
    case T.S{c0, c1, c2, c3} 2n:
      c2
    case T.S{c0, c1, c2, c3} 3n+p:
      c3

def at(+s: T.State, +r: Nat, +c: Nat) -> U32:
  byte_at(column(s, c), r)

# Section 5.1.1: SubBytes applies the S-box to every byte of the state.
def sub_word(w: T.Quad) -> T.Quad:
  match w:
    case T.W{a, b, c, d}:
      T.W{sbox(a), sbox(b), sbox(c), sbox(d)}

def sub_bytes(s: T.State) -> T.State:
  match s:
    case T.S{c0, c1, c2, c3}:
      T.S{sub_word(c0), sub_word(c1), sub_word(c2), sub_word(c3)}

# Section 5.1.2: s'[r,c] = s[r, (c + shift(r, 4)) mod 4], shift(r, 4) = r.
def shifted(+s: T.State, +c: Nat) -> T.Quad:
  T.W{at(s, 0n, c), at(s, 1n, Nat.mod(Nat.add(c, 1n), 4n)),
    at(s, 2n, Nat.mod(Nat.add(c, 2n), 4n)), at(s, 3n, Nat.mod(Nat.add(c, 3n), 4n))}

def shift_rows(+s: T.State) -> T.State:
  T.S{shifted(s, 0n), shifted(s, 1n), shifted(s, 2n), shifted(s, 3n)}

# Section 5.1.3, equation (5.6).
def mix_column(w: T.Quad) -> T.Quad:
  match w:
    case T.W{+a, +b, +c, +d}:
      T.W{U32.xor(U32.xor(U32.xor(mul(2, a), mul(3, b)), c), d),
        U32.xor(U32.xor(U32.xor(a, mul(2, b)), mul(3, c)), d),
        U32.xor(U32.xor(U32.xor(a, b), mul(2, c)), mul(3, d)),
        U32.xor(U32.xor(U32.xor(mul(3, a), b), c), mul(2, d))}

def mix_columns(s: T.State) -> T.State:
  match s:
    case T.S{c0, c1, c2, c3}:
      T.S{mix_column(c0), mix_column(c1), mix_column(c2), mix_column(c3)}

def xor_word(a: T.Quad, b: T.Quad) -> T.Quad:
  match a b:
    case T.W{a0, a1, a2, a3} T.W{b0, b1, b2, b3}:
      T.W{U32.xor(a0, b0), U32.xor(a1, b1), U32.xor(a2, b2), U32.xor(a3, b3)}

# Section 5.1.4: column c is added to the key word w[round*4 + c].
def add_round_key(s: T.State, w0: T.Quad, w1: T.Quad, w2: T.Quad, w3: T.Quad) -> T.State:
  match s:
    case T.S{c0, c1, c2, c3}:
      T.S{xor_word(c0, w0), xor_word(c1, w1), xor_word(c2, w2), xor_word(c3, w3)}

# Section 5.1, Figure 5. After the initial AddRoundKey, n more full rounds
# (SubBytes, ShiftRows, MixColumns, AddRoundKey) and the final round (no
# MixColumns), each taking the next four words of the key schedule.
def rounds(n: Nat, s: T.State, w: List<&2, T.Quad>) -> T.State:
  match n w:
    case 0n w0 <> w1 <> w2 <> w3 <> rest:
      add_round_key(shift_rows(sub_bytes(s)), w0, w1, w2, w3)
    case 1n+p w0 <> w1 <> w2 <> w3 <> rest:
      rounds(p, add_round_key(mix_columns(shift_rows(sub_bytes(s))), w0, w1, w2, w3), rest)
    case _ _:
      s

def cipher(+nr: Nat, s: T.State, w: List<&2, T.Quad>) -> T.State:
  match w:
    case w0 <> w1 <> w2 <> w3 <> rest:
      rounds(Nat.sub(nr, 1n), add_round_key(s, w0, w1, w2, w3), rest)
    case _:
      s

# Section 5.2: RotWord, SubWord (sub_word above), and Rcon[j] = [x^(j-1), 0, 0, 0].
def rot_word(w: T.Quad) -> T.Quad:
  match w:
    case T.W{a, b, c, d}:
      T.W{b, c, d, a}

def xpow(n: Nat) -> U32:
  match n:
    case 0n:
      1
    case 1n+p:
      mul(2, xpow(p))

def rcon(j: Nat) -> T.Quad:
  T.W{xpow(Nat.sub(j, 1n)), 0, 0, 0}

# w[i] = [key[4i], key[4i+1], key[4i+2], key[4i+3]] for i < Nk.
def key_words(key: List<&2, U32>) -> List<&2, T.Quad>:
  match key:
    case a <> b <> c <> d <> rest:
      T.W{a, b, c, d} <> key_words(rest)
    case _:
      Nil{}

def nth_word(ws: List<&2, T.Quad>, n: Nat) -> T.Quad:
  match ws n:
    case Nil{} _:
      T.W{0, 0, 0, 0}
    case w <> rest 0n:
      w
    case w <> rest 1n+p:
      nth_word(rest, p)

# The transformation of temp = w[i-1] in Figure 11, by k = i mod Nk,
# big = (Nk > 6) and q = i / Nk.
def transform(k: Nat, big: Bool, +q: Nat, temp: T.Quad) -> T.Quad:
  match k:
    case 0n:
      xor_word(sub_word(rot_word(temp)), rcon(q))
    case 1n:
      temp
    case 2n:
      temp
    case 3n:
      temp
    case 4n:
      match big:
        case True{}:
          sub_word(temp)
        case False{}:
          temp
    case 5n+p:
      temp

# w[i] = w[i-Nk] xor transform(w[i-1]); history holds w[i-1], w[i-2], ...
def next_word(+nk: Nat, +i: Nat, +history: List<&2, T.Quad>) -> T.Quad:
  xor_word(nth_word(history, Nat.sub(nk, 1n)),
    transform(Nat.mod(i, nk), Nat.is_lt(6n, nk), Nat.div(i, nk), nth_word(history, 0n)))

def expand(n: Nat, +nk: Nat, +i: Nat, +history: List<&2, T.Quad>) -> List<&2, T.Quad>:
  match n:
    case 0n:
      history
    case 1n+p:
      expand(p, nk, 1n+i, next_word(nk, i, history) <> history)

# Figure 11: Nb*(Nr+1) = 4*(Nr+1) words, the first Nk from the key.
def key_expansion(+nk: Nat, +nr: Nat, key: List<&2, U32>) -> List<&2, T.Quad>:
  List.reverse(&2, T.Quad, expand(Nat.sub(Nat.mul(4n, 1n+nr), nk), nk, nk,
    List.reverse(&2, T.Quad, key_words(key))))

def encrypt(+nk: Nat, +nr: Nat, key: List<&2, U32>, block: T.State) -> T.State:
  cipher(nr, block, key_expansion(nk, nr, key))

# AES-128: Nk = 4, Nr = 10; AES-256: Nk = 8, Nr = 14 (Figure 4).
def aes128(key: List<&2, U32>, block: T.State) -> T.State:
  encrypt(4n, 10n, key, block)

def aes256(key: List<&2, U32>, block: T.State) -> T.State:
  encrypt(8n, 14n, key, block)

# Section 3.4: s[r,c] = in[r + 4c], out[r + 4c] = s[r,c]. Missing input
# bytes read as {00}.
def nth_byte(xs: List<&2, U32>, n: Nat) -> U32:
  match xs n:
    case Nil{} _:
      0
    case x <> rest 0n:
      x
    case x <> rest 1n+p:
      nth_byte(rest, p)

def state_of(+input: List<&2, U32>) -> T.State:
  T.S{T.W{nth_byte(input, 0n), nth_byte(input, 1n), nth_byte(input, 2n), nth_byte(input, 3n)},
    T.W{nth_byte(input, 4n), nth_byte(input, 5n), nth_byte(input, 6n), nth_byte(input, 7n)},
    T.W{nth_byte(input, 8n), nth_byte(input, 9n), nth_byte(input, 10n), nth_byte(input, 11n)},
    T.W{nth_byte(input, 12n), nth_byte(input, 13n), nth_byte(input, 14n), nth_byte(input, 15n)}}

def bytes_of(s: T.State) -> List<&2, U32>:
  match s:
    case T.S{T.W{a0, a1, a2, a3}, T.W{b0, b1, b2, b3}, T.W{c0, c1, c2, c3}, T.W{d0, d1, d2, d3}}:
      [a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3, d0, d1, d2, d3]
