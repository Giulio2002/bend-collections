import Base
import ../../../src/crypto/aes/types.bend as T
import ../../../src/crypto/aes/sbox.bend as B
import ../../../src/crypto/aes/aes.bend as I
import ../../../spec/crypto/aes/aes.bend as S
import ./sbox.bend as L

# The AES implementation equals the FIPS 197 specification, layer by layer:
# the byte functions (./sbox.bend), then SubBytes, ShiftRows, MixColumns,
# AddRoundKey, the rounds, the key expansion and the cipher, for every key
# (of any length and any Nk, Nr) and every state.

# Congruence of the record constructors (one rewrite per field, on variables).
law quad_cong:
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +a2: U32
  for +b2: U32
  for +c2: U32
  for +d2: U32
  for +ea: {a == a2 : U32}
  for +eb: {b == b2 : U32}
  for +ec: {c == c2 : U32}
  for +ed: {d == d2 : U32}
  {T.W{a, b, c, d} == T.W{a2, b2, c2, d2} : T.Quad}

def quad_cong(a, b, c, d, a2, b2, c2, d2, ea, eb, ec, ed):
  %ea : {T.W{a, b, c, d} == T.W{_, b2, c2, d2} : T.Quad}
  %eb : {T.W{a, b, c, d} == T.W{a, _, c2, d2} : T.Quad}
  %ec : {T.W{a, b, c, d} == T.W{a, b, _, d2} : T.Quad}
  %ed : {T.W{a, b, c, d} == T.W{a, b, c, _} : T.Quad}
  {==}

law state_cong:
  for +a: T.Quad
  for +b: T.Quad
  for +c: T.Quad
  for +d: T.Quad
  for +a2: T.Quad
  for +b2: T.Quad
  for +c2: T.Quad
  for +d2: T.Quad
  for +ea: {a == a2 : T.Quad}
  for +eb: {b == b2 : T.Quad}
  for +ec: {c == c2 : T.Quad}
  for +ed: {d == d2 : T.Quad}
  {T.S{a, b, c, d} == T.S{a2, b2, c2, d2} : T.State}

def state_cong(a, b, c, d, a2, b2, c2, d2, ea, eb, ec, ed):
  %ea : {T.S{a, b, c, d} == T.S{_, b2, c2, d2} : T.State}
  %eb : {T.S{a, b, c, d} == T.S{a, _, c2, d2} : T.State}
  %ec : {T.S{a, b, c, d} == T.S{a, b, _, d2} : T.State}
  %ed : {T.S{a, b, c, d} == T.S{a, b, c, _} : T.State}
  {==}

law sub_word_ok:
  for +w: T.Quad
  {I.sub_word(w) == S.sub_word(w) : T.Quad}

def sub_word_ok(w):
  match w:
    case T.W{a, b, c, d}:
      quad_cong(B.sbox(a), B.sbox(b), B.sbox(c), B.sbox(d), S.sbox(a), S.sbox(b), S.sbox(c), S.sbox(d), L.sbox_ok(a), L.sbox_ok(b), L.sbox_ok(c), L.sbox_ok(d))

law sub_bytes_ok:
  for +s: T.State
  {I.sub_bytes(s) == S.sub_bytes(s) : T.State}

def sub_bytes_ok(s):
  match s:
    case T.S{c0, c1, c2, c3}:
      state_cong(I.sub_word(c0), I.sub_word(c1), I.sub_word(c2), I.sub_word(c3), S.sub_word(c0), S.sub_word(c1), S.sub_word(c2), S.sub_word(c3), sub_word_ok(c0), sub_word_ok(c1), sub_word_ok(c2), sub_word_ok(c3))

law shift_rows_ok:
  for +s: T.State
  {I.shift_rows(s) == S.shift_rows(s) : T.State}

def shift_rows_ok(s):
  match s:
    case T.S{T.W{a0, a1, a2, a3}, T.W{b0, b1, b2, b3}, T.W{c0, c1, c2, c3}, T.W{d0, d1, d2, d3}}:
      {==}

law xor4_cong:
  for +p: U32
  for +q: U32
  for +r: U32
  for +s: U32
  for +p2: U32
  for +q2: U32
  for +r2: U32
  for +s2: U32
  for +ep: {p == p2 : U32}
  for +eq: {q == q2 : U32}
  for +er: {r == r2 : U32}
  for +es: {s == s2 : U32}
  {U32.xor(U32.xor(U32.xor(p, q), r), s) == U32.xor(U32.xor(U32.xor(p2, q2), r2), s2) : U32}

def xor4_cong(p, q, r, s, p2, q2, r2, s2, ep, eq, er, es):
  %ep : {U32.xor(U32.xor(U32.xor(p, q), r), s) == U32.xor(U32.xor(U32.xor(_, q2), r2), s2) : U32}
  %eq : {U32.xor(U32.xor(U32.xor(p, q), r), s) == U32.xor(U32.xor(U32.xor(p, _), r2), s2) : U32}
  %er : {U32.xor(U32.xor(U32.xor(p, q), r), s) == U32.xor(U32.xor(U32.xor(p, q), _), s2) : U32}
  %es : {U32.xor(U32.xor(U32.xor(p, q), r), s) == U32.xor(U32.xor(U32.xor(p, q), r), _) : U32}
  {==}

law mix_column_ok:
  for +w: T.Quad
  {I.mix_column(w) == S.mix_column(w) : T.Quad}

def mix_column_ok(w):
  match w:
    case T.W{a, b, c, d}:
      quad_cong(U32.xor(U32.xor(U32.xor(B.xtime(a), B.mul3(b)), c), d), U32.xor(U32.xor(U32.xor(a, B.xtime(b)), B.mul3(c)), d), U32.xor(U32.xor(U32.xor(a, b), B.xtime(c)), B.mul3(d)), U32.xor(U32.xor(U32.xor(B.mul3(a), b), c), B.xtime(d)), U32.xor(U32.xor(U32.xor(S.mul(2, a), S.mul(3, b)), c), d), U32.xor(U32.xor(U32.xor(a, S.mul(2, b)), S.mul(3, c)), d), U32.xor(U32.xor(U32.xor(a, b), S.mul(2, c)), S.mul(3, d)), U32.xor(U32.xor(U32.xor(S.mul(3, a), b), c), S.mul(2, d)),
        xor4_cong(B.xtime(a), B.mul3(b), c, d, S.mul(2, a), S.mul(3, b), c, d, L.xtime_ok(a), L.mul3_ok(b), {==}, {==}), xor4_cong(a, B.xtime(b), B.mul3(c), d, a, S.mul(2, b), S.mul(3, c), d, {==}, L.xtime_ok(b), L.mul3_ok(c), {==}), xor4_cong(a, b, B.xtime(c), B.mul3(d), a, b, S.mul(2, c), S.mul(3, d), {==}, {==}, L.xtime_ok(c), L.mul3_ok(d)), xor4_cong(B.mul3(a), b, c, B.xtime(d), S.mul(3, a), b, c, S.mul(2, d), L.mul3_ok(a), {==}, {==}, L.xtime_ok(d)))

law mix_columns_ok:
  for +s: T.State
  {I.mix_columns(s) == S.mix_columns(s) : T.State}

def mix_columns_ok(s):
  match s:
    case T.S{c0, c1, c2, c3}:
      state_cong(I.mix_column(c0), I.mix_column(c1), I.mix_column(c2), I.mix_column(c3), S.mix_column(c0), S.mix_column(c1), S.mix_column(c2), S.mix_column(c3), mix_column_ok(c0), mix_column_ok(c1), mix_column_ok(c2), mix_column_ok(c3))

law xor_word_ok:
  for +a: T.Quad
  for +b: T.Quad
  {I.xor_word(a, b) == S.xor_word(a, b) : T.Quad}

def xor_word_ok(a, b):
  match a b:
    case T.W{a0, a1, a2, a3} T.W{b0, b1, b2, b3}:
      {==}

law ark_ok:
  for +s: T.State
  for +w0: T.Quad
  for +w1: T.Quad
  for +w2: T.Quad
  for +w3: T.Quad
  {I.add_round_key(s, T.S{w0, w1, w2, w3}) == S.add_round_key(s, w0, w1, w2, w3) : T.State}

def ark_ok(s, w0, w1, w2, w3):
  match s:
    case T.S{c0, c1, c2, c3}:
      %xor_word_ok(c0, w0) : {T.S{I.xor_word(c0, w0), I.xor_word(c1, w1), I.xor_word(c2, w2), I.xor_word(c3, w3)} == T.S{_, S.xor_word(c1, w1), S.xor_word(c2, w2), S.xor_word(c3, w3)} : T.State}
      %xor_word_ok(c1, w1) : {T.S{I.xor_word(c0, w0), I.xor_word(c1, w1), I.xor_word(c2, w2), I.xor_word(c3, w3)} == T.S{I.xor_word(c0, w0), _, S.xor_word(c2, w2), S.xor_word(c3, w3)} : T.State}
      %xor_word_ok(c2, w2) : {T.S{I.xor_word(c0, w0), I.xor_word(c1, w1), I.xor_word(c2, w2), I.xor_word(c3, w3)} == T.S{I.xor_word(c0, w0), I.xor_word(c1, w1), _, S.xor_word(c3, w3)} : T.State}
      %xor_word_ok(c3, w3) : {T.S{I.xor_word(c0, w0), I.xor_word(c1, w1), I.xor_word(c2, w2), I.xor_word(c3, w3)} == T.S{I.xor_word(c0, w0), I.xor_word(c1, w1), I.xor_word(c2, w2), _} : T.State}
      {==}

law round_ok:
  for +s: T.State
  for +w0: T.Quad
  for +w1: T.Quad
  for +w2: T.Quad
  for +w3: T.Quad
  {I.round(s, T.S{w0, w1, w2, w3}) == S.add_round_key(S.mix_columns(S.shift_rows(S.sub_bytes(s))), w0, w1, w2, w3) : T.State}

def round_ok(s, w0, w1, w2, w3):
  %sub_bytes_ok(s) : {I.round(s, T.S{w0, w1, w2, w3}) == S.add_round_key(S.mix_columns(S.shift_rows(_)), w0, w1, w2, w3) : T.State}
  %shift_rows_ok(I.sub_bytes(s)) : {I.round(s, T.S{w0, w1, w2, w3}) == S.add_round_key(S.mix_columns(_), w0, w1, w2, w3) : T.State}
  %mix_columns_ok(I.shift_rows(I.sub_bytes(s))) : {I.round(s, T.S{w0, w1, w2, w3}) == S.add_round_key(_, w0, w1, w2, w3) : T.State}
  ark_ok(I.mix_columns(I.shift_rows(I.sub_bytes(s))), w0, w1, w2, w3)

law last_round_ok:
  for +s: T.State
  for +w0: T.Quad
  for +w1: T.Quad
  for +w2: T.Quad
  for +w3: T.Quad
  {I.last_round(s, T.S{w0, w1, w2, w3}) == S.add_round_key(S.shift_rows(S.sub_bytes(s)), w0, w1, w2, w3) : T.State}

def last_round_ok(s, w0, w1, w2, w3):
  %sub_bytes_ok(s) : {I.last_round(s, T.S{w0, w1, w2, w3}) == S.add_round_key(S.shift_rows(_), w0, w1, w2, w3) : T.State}
  %shift_rows_ok(I.sub_bytes(s)) : {I.last_round(s, T.S{w0, w1, w2, w3}) == S.add_round_key(_, w0, w1, w2, w3) : T.State}
  ark_ok(I.shift_rows(I.sub_bytes(s)), w0, w1, w2, w3)

law rounds_ok:
  for +n: Nat
  for +s: T.State
  for +w: List<&2, T.Quad>
  {I.rounds(n, s, I.round_keys(w)) == S.rounds(n, s, w) : T.State}

def rounds_ok(n, s, w):
  match n w:
    case 0n w0 <> w1 <> w2 <> w3 <> rest:
      last_round_ok(s, w0, w1, w2, w3)
    case 1n+p w0 <> w1 <> w2 <> w3 <> rest:
      %round_ok(s, w0, w1, w2, w3) : {I.rounds(p, I.round(s, T.S{w0, w1, w2, w3}), I.round_keys(rest)) == S.rounds(p, _, rest) : T.State}
      rounds_ok(p, I.round(s, T.S{w0, w1, w2, w3}), rest)
    case 0n Nil{}:
      {==}
    case 0n w0 <> Nil{}:
      {==}
    case 0n w0 <> w1 <> Nil{}:
      {==}
    case 0n w0 <> w1 <> w2 <> Nil{}:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p w0 <> Nil{}:
      {==}
    case 1n+p w0 <> w1 <> Nil{}:
      {==}
    case 1n+p w0 <> w1 <> w2 <> Nil{}:
      {==}

law cipher_ok:
  for +nr: Nat
  for +s: T.State
  for +w: List<&2, T.Quad>
  {I.cipher(nr, s, I.round_keys(w)) == S.cipher(nr, s, w) : T.State}

def cipher_ok(nr, s, w):
  match w:
    case w0 <> w1 <> w2 <> w3 <> rest:
      %ark_ok(s, w0, w1, w2, w3) : {I.rounds(Nat.sub(nr, 1n), I.add_round_key(s, T.S{w0, w1, w2, w3}), I.round_keys(rest)) == S.rounds(Nat.sub(nr, 1n), _, rest) : T.State}
      rounds_ok(Nat.sub(nr, 1n), I.add_round_key(s, T.S{w0, w1, w2, w3}), rest)
    case Nil{}:
      {==}
    case w0 <> Nil{}:
      {==}
    case w0 <> w1 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> Nil{}:
      {==}

# ---- key expansion ----

law rot_word_ok:
  for +w: T.Quad
  {I.rot_word(w) == S.rot_word(w) : T.Quad}

def rot_word_ok(w):
  match w:
    case T.W{a, b, c, d}:
      {==}

law xpow_ok:
  for +n: Nat
  {I.xpow(n) == S.xpow(n) : U32}

def xpow_ok(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %xpow_ok(p) : {B.xtime(I.xpow(p)) == S.mul(2, _) : U32}
      L.xtime_ok(I.xpow(p))

law rcon_ok:
  for +j: Nat
  {I.rcon(j) == S.rcon(j) : T.Quad}

def rcon_ok(j):
  %xpow_ok(Nat.sub(j, 1n)) : {T.W{I.xpow(Nat.sub(j, 1n)), 0, 0, 0} == T.W{_, 0, 0, 0} : T.Quad}
  {==}

law key_words_ok:
  for +key: List<&2, U32>
  {I.key_words(key) == S.key_words(key) : List<&2, T.Quad>}

def key_words_ok(key):
  match key:
    case a <> b <> c <> d <> rest:
      %key_words_ok(rest) : {T.W{a, b, c, d} <> I.key_words(rest) == T.W{a, b, c, d} <> _ : List<&2, T.Quad>}
      {==}
    case Nil{}:
      {==}
    case a <> Nil{}:
      {==}
    case a <> b <> Nil{}:
      {==}
    case a <> b <> c <> Nil{}:
      {==}

law get_word_ok:
  for +ws: List<&2, T.Quad>
  for +n: Nat
  {I.get_word(ws, n) == S.nth_word(ws, n) : T.Quad}

def get_word_ok(ws, n):
  match ws n:
    case Nil{} _:
      {==}
    case w <> rest 0n:
      {==}
    case w <> rest 1n+p:
      get_word_ok(rest, p)

law core_ok:
  for +k: Nat
  for +big: Bool
  for +q: Nat
  for +temp: T.Quad
  {I.schedule_core(k, big, q, temp) == S.transform(k, big, q, temp) : T.Quad}

def core_ok(k, big, q, temp):
  match k:
    case 0n:
      %rcon_ok(q) : {I.xor_word(I.sub_word(I.rot_word(temp)), I.rcon(q)) == S.xor_word(S.sub_word(S.rot_word(temp)), _) : T.Quad}
      %rot_word_ok(temp) : {I.xor_word(I.sub_word(I.rot_word(temp)), I.rcon(q)) == S.xor_word(S.sub_word(_), I.rcon(q)) : T.Quad}
      %sub_word_ok(I.rot_word(temp)) : {I.xor_word(I.sub_word(I.rot_word(temp)), I.rcon(q)) == S.xor_word(_, I.rcon(q)) : T.Quad}
      xor_word_ok(I.sub_word(I.rot_word(temp)), I.rcon(q))
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      match big:
        case True{}:
          sub_word_ok(temp)
        case False{}:
          {==}
    case 5n+p:
      {==}

law next_ok:
  for +nk: Nat
  for +i: Nat
  for +h: List<&2, T.Quad>
  {I.next_word(nk, i, h) == S.next_word(nk, i, h) : T.Quad}

def next_ok(nk, i, h):
  %get_word_ok(h, 0n) : {I.next_word(nk, i, h) == S.xor_word(S.nth_word(h, Nat.sub(nk, 1n)), S.transform(Nat.mod(i, nk), Nat.is_lt(6n, nk), Nat.div(i, nk), _)) : T.Quad}
  %core_ok(Nat.mod(i, nk), Nat.is_lt(6n, nk), Nat.div(i, nk), I.get_word(h, 0n)) : {I.next_word(nk, i, h) == S.xor_word(S.nth_word(h, Nat.sub(nk, 1n)), _) : T.Quad}
  %get_word_ok(h, Nat.sub(nk, 1n)) : {I.next_word(nk, i, h) == S.xor_word(_, I.schedule_core(Nat.mod(i, nk), Nat.is_lt(6n, nk), Nat.div(i, nk), I.get_word(h, 0n))) : T.Quad}
  xor_word_ok(I.get_word(h, Nat.sub(nk, 1n)), I.schedule_core(Nat.mod(i, nk), Nat.is_lt(6n, nk), Nat.div(i, nk), I.get_word(h, 0n)))

law grow_ok:
  for +n: Nat
  for +nk: Nat
  for +i: Nat
  for +h: List<&2, T.Quad>
  {I.grow(n, nk, i, h) == S.expand(n, nk, i, h) : List<&2, T.Quad>}

def grow_ok(n, nk, i, h):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %next_ok(nk, i, h) : {I.grow(p, nk, 1n+i, I.next_word(nk, i, h) <> h) == S.expand(p, nk, 1n+i, _ <> h) : List<&2, T.Quad>}
      grow_ok(p, nk, 1n+i, I.next_word(nk, i, h) <> h)

law expand_ok:
  for +nk: Nat
  for +nr: Nat
  for +key: List<&2, U32>
  {I.expand(nk, nr, key) == I.round_keys(S.key_expansion(nk, nr, key)) : List<&2, T.State>}

def expand_ok(nk, nr, key):
  %key_words_ok(key) : {I.expand(nk, nr, key) == I.round_keys(List.reverse(&2, T.Quad, S.expand(Nat.sub(Nat.mul(4n, 1n+nr), nk), nk, nk, List.reverse(&2, T.Quad, _)))) : List<&2, T.State>}
  %grow_ok(Nat.sub(Nat.mul(4n, 1n+nr), nk), nk, nk, List.reverse(&2, T.Quad, I.key_words(key))) : {I.expand(nk, nr, key) == I.round_keys(List.reverse(&2, T.Quad, _)) : List<&2, T.State>}
  {==}

# The implementation's cipher with its expanded key is FIPS 197's Cipher
# with KeyExpansion, for every Nk, Nr, key and block.
law encrypt_ok:
  for +nk: Nat
  for +nr: Nat
  for +key: List<&2, U32>
  for +s: T.State
  {I.encrypt(nk, nr, key, s) == S.encrypt(nk, nr, key, s) : T.State}

def encrypt_ok(nk, nr, key, s):
  %Equal.sym(List<&2, T.State>, I.expand(nk, nr, key), I.round_keys(S.key_expansion(nk, nr, key)), expand_ok(nk, nr, key)) : {I.cipher(nr, s, _) == S.cipher(nr, s, S.key_expansion(nk, nr, key)) : T.State}
  cipher_ok(nr, s, S.key_expansion(nk, nr, key))
