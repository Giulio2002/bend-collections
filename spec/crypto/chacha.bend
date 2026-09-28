import Base

# Executable specification of the ChaCha20 block function and stream cipher
# (RFC 8439 sections 2.1-2.4) and of HChaCha20 / XChaCha20
# (draft-irtf-cfrg-xchacha-03 sections 2.2-2.3), transcribed from the
# documents. Nothing is shared with the implementation (src/crypto/chacha/):
# the state is the RFC's list of sixteen words, indexed and updated by
# position, the quarter round is the RFC's sequence of twelve operations,
# keys and nonces are byte lists read as little-endian words, and the
# keystream is XORed byte by byte. The shape follows HACL*'s Spec.Chacha20.
#
# Bytes are U32 values (each < 256 in the byte convention). A word is read
# from the low 8 bits of four bytes; the stream XOR works on the whole U32,
# so encrypting twice is the identity for every list of U32.

# ---------------------------------------------------------------- lists

# Element i of a list, 0 past its end.
def get(xs: List<&2, U32>, i: Nat) -> U32:
  match xs i:
    case Nil{} _: 0
    case x <> rest 0n: x
    case x <> rest 1n+p: get(rest, p)

# The list with element i replaced (unchanged past its end).
def put(xs: List<&2, U32>, i: Nat, y: U32) -> List<&2, U32>:
  match xs i:
    case Nil{} _: Nil{}
    case x <> rest 0n: y <> rest
    case x <> rest 1n+p: x <> put(rest, p, y)

# ---------------------------------------------------------------- 2.1 quarter round

# x <<< n: rotation of a 32-bit word left by n bits (0 < n < 32).
def rotl(+x: U32, +n: Nat) -> U32:
  U32.or(U32.shln(x, n), U32.shrn(x, Nat.sub(32n, n)))

# 2.2: QUARTERROUND(a, b, c, d) applied to the state at those positions:
#   a += b; d ^= a; d <<<= 16;
#   c += d; b ^= c; b <<<= 12;
#   a += b; d ^= a; d <<<= 8;
#   c += d; b ^= c; b <<<= 7;
def quarter(+s: List<&2, U32>, +a: Nat, +b: Nat, +c: Nat, +d: Nat) -> List<&2, U32>:
  +a1 = U32.add(get(s, a), get(s, b))
  +d1 = rotl(U32.xor(get(s, d), a1), 16n)
  +c1 = U32.add(get(s, c), d1)
  +b1 = rotl(U32.xor(get(s, b), c1), 12n)
  +a2 = U32.add(a1, b1)
  +d2 = rotl(U32.xor(d1, a2), 8n)
  +c2 = U32.add(c1, d2)
  +b2 = rotl(U32.xor(b1, c2), 7n)
  put(put(put(put(s, a, a2), b, b2), c, c2), d, d2)

# ---------------------------------------------------------------- 2.3 block function

# inner_block: four column rounds, then four diagonal rounds.
def inner_block(s: List<&2, U32>) -> List<&2, U32>:
  s1 = quarter(s, 0n, 4n, 8n, 12n)
  s2 = quarter(s1, 1n, 5n, 9n, 13n)
  s3 = quarter(s2, 2n, 6n, 10n, 14n)
  s4 = quarter(s3, 3n, 7n, 11n, 15n)
  s5 = quarter(s4, 0n, 5n, 10n, 15n)
  s6 = quarter(s5, 1n, 6n, 11n, 12n)
  s7 = quarter(s6, 2n, 7n, 8n, 13n)
  quarter(s7, 3n, 4n, 9n, 14n)

# n applications of inner_block (ChaCha20: n = 10, twenty rounds).
def inner_blocks(n: Nat, s: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n: s
    case 1n+p: inner_blocks(p, inner_block(s))

# A little-endian word from the low 8 bits of four bytes.
def word(b0: U32, b1: U32, b2: U32, b3: U32) -> U32:
  U32.or(U32.or(U32.or(U32.and(b0, 255), U32.shln(U32.and(b1, 255), 8n)),
    U32.shln(U32.and(b2, 255), 16n)), U32.shln(U32.and(b3, 255), 24n))

# The words of a byte list, four bytes each (a partial tail is dropped).
def words(bytes: List<&2, U32>) -> List<&2, U32>:
  match bytes:
    case b0 <> b1 <> b2 <> b3 <> rest: word(b0, b1, b2, b3) <> words(rest)
    case _: Nil{}

# The four little-endian bytes of a word.
def octets(+w: U32) -> List<&2, U32>:
  [U32.and(w, 255), U32.and(U32.shrn(w, 8n), 255),
   U32.and(U32.shrn(w, 16n), 255), U32.shrn(w, 24n)]

def serialize(ws: List<&2, U32>) -> List<&2, U32>:
  match ws:
    case Nil{}: Nil{}
    case w <> rest: List.append(&2, U32, octets(w), serialize(rest))

# "expa" "nd 3" "2-by" "te k"
def constants() -> List<&2, U32>:
  [1634760805, 857760878, 2036477234, 1797285236]

# The initial state: constants, key (eight words), block counter, nonce
# (three words). Missing key or nonce words read as 0 (the public API
# rejects other lengths before this is reached).
def state(+k: List<&2, U32>, counter: U32, +n: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, constants(),
    [get(k, 0n), get(k, 1n), get(k, 2n), get(k, 3n), get(k, 4n), get(k, 5n), get(k, 6n), get(k, 7n),
     counter, get(n, 0n), get(n, 1n), get(n, 2n)])

def add_words(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs ys:
    case x <> xt y <> yt: U32.add(x, y) <> add_words(xt, yt)
    case _ _: Nil{}

# chacha20_block with n double rounds: working state after n inner blocks,
# added to the initial state, serialized little-endian (64 bytes).
def block_body(+n: Nat, +key: List<&2, U32>, counter: U32, +nonce: List<&2, U32>) -> List<&2, U32>:
  +s = state(words(key), counter, words(nonce))
  serialize(add_words(s, inner_blocks(n, s)))

# The same, entered through a match on the key's first cell. Both arms are
# block_body; the match only keeps the proof checker from evaluating the
# rounds on a symbolic key (it compares types by evaluating them).
def block_rounds(+n: Nat, key: List<&2, U32>, counter: U32, +nonce: List<&2, U32>) -> List<&2, U32>:
  match key:
    case Nil{}: block_body(n, Nil{}, counter, nonce)
    case b <> rest: block_body(n, b <> rest, counter, nonce)

def block(+key: List<&2, U32>, counter: U32, +nonce: List<&2, U32>) -> List<&2, U32>:
  block_rounds(10n, key, counter, nonce)

# ---------------------------------------------------------------- 2.4 encryption

# The first n bytes of a list, and the rest.
def prefix(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n xs:
    case 0n _: Nil{}
    case 1n+p Nil{}: Nil{}
    case 1n+p x <> rest: x <> prefix(p, rest)

def suffix(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n xs:
    case 0n _: xs
    case 1n+p Nil{}: Nil{}
    case 1n+p x <> rest: suffix(p, rest)

# The plaintext cut into 64-byte blocks; the last one may be shorter (and
# there is none for the empty plaintext). fuel bounds the number of blocks
# (the length of the plaintext is enough).
def blocks(fuel: Nat, +xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match fuel xs:
    case 0n _: Nil{}
    case 1n+p Nil{}: Nil{}
    case 1n+p x <> rest: prefix(64n, x <> rest) <> blocks(p, suffix(64n, x <> rest))

# Byte-wise XOR of a block with the keystream (as long as the block).
def xor_bytes(xs: List<&2, U32>, ks: List<&2, U32>) -> List<&2, U32>:
  match xs ks:
    case x <> xt k <> kt: U32.xor(x, k) <> xor_bytes(xt, kt)
    case _ _: Nil{}

# for j = 0 .. : block j is XORed with chacha20_block(key, counter + j, nonce).
def encrypt_blocks(bs: List<&2, List<&2, U32>>, +n: Nat, +key: List<&2, U32>, +counter: U32, +nonce: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}: Nil{}
    case b <> rest:
      List.append(&2, U32, xor_bytes(b, block_rounds(n, key, counter, nonce)),
        encrypt_blocks(rest, n, key, U32.add(counter, 1), nonce))

# chacha20_encrypt(key, counter, nonce, plaintext) with n double rounds.
def encrypt_rounds(+n: Nat, +key: List<&2, U32>, counter: U32, +nonce: List<&2, U32>, +plaintext: List<&2, U32>) -> List<&2, U32>:
  encrypt_blocks(blocks(List.length(&2, U32, plaintext), plaintext), n, key, counter, nonce)

def encrypt(+key: List<&2, U32>, counter: U32, +nonce: List<&2, U32>, +plaintext: List<&2, U32>) -> List<&2, U32>:
  encrypt_rounds(10n, key, counter, nonce, plaintext)

# ---------------------------------------------------------------- XChaCha20

# HChaCha20 (draft-irtf-cfrg-xchacha-03 section 2.2): the state is set up as
# for ChaCha20 with the 16-byte nonce in words 12..15; after twenty rounds
# (no feed-forward) words 0..3 and 12..15 are the 32-byte subkey.
def hstate(+k: List<&2, U32>, +n: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, constants(),
    [get(k, 0n), get(k, 1n), get(k, 2n), get(k, 3n), get(k, 4n), get(k, 5n), get(k, 6n), get(k, 7n),
     get(n, 0n), get(n, 1n), get(n, 2n), get(n, 3n)])

def hchacha_body(+n: Nat, +key: List<&2, U32>, +nonce: List<&2, U32>) -> List<&2, U32>:
  +s = inner_blocks(n, hstate(words(key), words(nonce)))
  serialize([get(s, 0n), get(s, 1n), get(s, 2n), get(s, 3n), get(s, 12n), get(s, 13n), get(s, 14n), get(s, 15n)])

# Entered through a match on the key, as block_rounds.
def hchacha_rounds(+n: Nat, key: List<&2, U32>, +nonce: List<&2, U32>) -> List<&2, U32>:
  match key:
    case Nil{}: hchacha_body(n, Nil{}, nonce)
    case b <> rest: hchacha_body(n, b <> rest, nonce)

def hchacha20(+key: List<&2, U32>, +nonce: List<&2, U32>) -> List<&2, U32>:
  hchacha_rounds(10n, key, nonce)

# Section 2.3: XChaCha20 is ChaCha20 under the HChaCha20 subkey of the
# first 16 nonce bytes, with the nonce 0x00000000 || nonce[16..24].
def xsubkey(+key: List<&2, U32>, +nonce: List<&2, U32>) -> List<&2, U32>:
  hchacha20(key, prefix(16n, nonce))

def xnonce(+nonce: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, [0, 0, 0, 0], suffix(16n, nonce))

def xencrypt(+key: List<&2, U32>, counter: U32, +nonce: List<&2, U32>, +plaintext: List<&2, U32>) -> List<&2, U32>:
  encrypt(xsubkey(key, nonce), counter, xnonce(nonce), plaintext)
