import Base
import ./core.bend as C

# ChaCha20 (RFC 8439 sections 2.3-2.4), HChaCha20 and XChaCha20
# (draft-irtf-cfrg-xchacha-03 sections 2.2-2.3) over byte lists.
#
# Bytes are U32 values (each < 256 in the byte convention); a key or nonce
# word is read from the low 8 bits of four bytes, and the keystream is XORed
# onto the whole U32 (so encrypting twice is the identity on every list).
# Keys are 32 bytes, ChaCha20 nonces 12, HChaCha20 nonces 16 and XChaCha20
# nonces 24; the checked functions return None for any other length. The
# *_rounds functions take the number of double rounds (ChaCha20: 10).
#
# Constant time: no branch or memory access depends on key, nonce, counter
# or data bytes; only the (public) lengths steer the loops. Bend has no
# timing model, so this is a property of the code's shape, not a proved fact.

type Key is Data:
  K{k0: U32, k1: U32, k2: U32, k3: U32, k4: U32, k5: U32, k6: U32, k7: U32}

type Nonce is Data:
  N{n0: U32, n1: U32, n2: U32}

# ---------------------------------------------------------------- bytes to words

def word(b0: U32, b1: U32, b2: U32, b3: U32) -> U32:
  U32.or(U32.or(U32.or(U32.and(b0, 255), U32.shln(U32.and(b1, 255), 8n)),
    U32.shln(U32.and(b2, 255), 16n)), U32.shln(U32.and(b3, 255), 24n))

def words(bytes: List<&2, U32>) -> List<&2, U32>:
  match bytes:
    case b0 <> b1 <> b2 <> b3 <> rest: word(b0, b1, b2, b3) <> words(rest)
    case _: Nil{}

def at(xs: List<&2, U32>, i: Nat) -> U32:
  match xs i:
    case Nil{} _: 0
    case x <> rest 0n: x
    case x <> rest 1n+p: at(rest, p)

def key_words(+ws: List<&2, U32>) -> Key:
  K{at(ws, 0n), at(ws, 1n), at(ws, 2n), at(ws, 3n), at(ws, 4n), at(ws, 5n), at(ws, 6n), at(ws, 7n)}

def nonce_words(+ws: List<&2, U32>) -> Nonce:
  N{at(ws, 0n), at(ws, 1n), at(ws, 2n)}

def key(bytes: List<&2, U32>) -> Key:
  key_words(words(bytes))

def nonce(bytes: List<&2, U32>) -> Nonce:
  nonce_words(words(bytes))

# ---------------------------------------------------------------- block

def state(k: Key, counter: U32, n: Nonce) -> C.State:
  match k n:
    case K{k0, k1, k2, k3, k4, k5, k6, k7} N{n0, n1, n2}:
      C.init(k0, k1, k2, k3, k4, k5, k6, k7, counter, n0, n1, n2)

# The 64 keystream bytes of block `counter`, with r double rounds.
def keystream(+r: Nat, k: Key, counter: U32, n: Nonce) -> List<&2, U32>:
  C.bytes(C.block(r, state(k, counter, n)))

# ---------------------------------------------------------------- stream

# XOR the keystream onto the front of xs, as far as both go.
def xor_front(ks: List<&2, U32>, xs: List<&2, U32>) -> List<&2, U32>:
  match ks xs:
    case k <> kt x <> xt: U32.xor(x, k) <> xor_front(kt, xt)
    case _ _: Nil{}

def skip(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n xs:
    case 0n _: xs
    case 1n+p Nil{}: Nil{}
    case 1n+p x <> rest: skip(p, rest)

# Blocks of 64 bytes, block j under counter + j; fuel bounds the number of
# blocks (the length of xs is enough).
def stream(fuel: Nat, +xs: List<&2, U32>, +r: Nat, +k: Key, +counter: U32, +n: Nonce) -> List<&2, U32>:
  match fuel xs:
    case 0n _: Nil{}
    case 1n+p Nil{}: Nil{}
    case 1n+p x <> xt:
      List.append(&2, U32, xor_front(keystream(r, k, counter, n), x <> xt),
        stream(p, skip(64n, x <> xt), r, k, U32.add(counter, 1), n))

def encrypt_rounds(+r: Nat, key_bytes: List<&2, U32>, counter: U32, nonce_bytes: List<&2, U32>, +plaintext: List<&2, U32>) -> List<&2, U32>:
  stream(List.length(&2, U32, plaintext), plaintext, r, key(key_bytes), counter, nonce(nonce_bytes))

def block_rounds(+r: Nat, key_bytes: List<&2, U32>, counter: U32, nonce_bytes: List<&2, U32>) -> List<&2, U32>:
  keystream(r, key(key_bytes), counter, nonce(nonce_bytes))

# ---------------------------------------------------------------- HChaCha20 / XChaCha20

def hstate(k: Key, +ws: List<&2, U32>) -> C.State:
  match k:
    case K{k0, k1, k2, k3, k4, k5, k6, k7}:
      C.hinit(k0, k1, k2, k3, k4, k5, k6, k7, at(ws, 0n), at(ws, 1n), at(ws, 2n), at(ws, 3n))

def hchacha20_unchecked(key_bytes: List<&2, U32>, nonce_bytes: List<&2, U32>) -> List<&2, U32>:
  C.hbytes(C.rounds(10n, hstate(key(key_bytes), words(nonce_bytes))))

def take(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n xs:
    case 0n _: Nil{}
    case 1n+p Nil{}: Nil{}
    case 1n+p x <> rest: x <> take(p, rest)

# XChaCha20: ChaCha20 under the HChaCha20 subkey of nonce[0..16], with the
# nonce 0x00000000 || nonce[16..24].
def xencrypt_unchecked(key_bytes: List<&2, U32>, counter: U32, +nonce_bytes: List<&2, U32>, +plaintext: List<&2, U32>) -> List<&2, U32>:
  +sub = hchacha20_unchecked(key_bytes, take(16n, nonce_bytes))
  encrypt_rounds(10n, sub, counter, 0 <> 0 <> 0 <> 0 <> skip(16n, nonce_bytes), plaintext)

# ---------------------------------------------------------------- checked API

def has_length(+xs: List<&2, U32>, n: Nat) -> Bool:
  Nat.is_eq(List.length(&2, U32, xs), n)

def valid(+key_bytes: List<&2, U32>, +nonce_bytes: List<&2, U32>, n: Nat) -> Bool:
  Bool.and(has_length(key_bytes, 32n), has_length(nonce_bytes, n))

def when(ok: Bool, x: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: Some{x}
    case False{}: None{}

# chacha20_block(key, counter, nonce): 64 bytes, or None unless the key has 32
# bytes and the nonce 12.
def chacha20_block(+key_bytes: List<&2, U32>, counter: U32, +nonce_bytes: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  when(valid(key_bytes, nonce_bytes, 12n), block_rounds(10n, key_bytes, counter, nonce_bytes))

# chacha20_encrypt(key, counter, nonce, plaintext) (encryption and decryption
# are the same operation).
def chacha20(+key_bytes: List<&2, U32>, counter: U32, +nonce_bytes: List<&2, U32>, +plaintext: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  when(valid(key_bytes, nonce_bytes, 12n), encrypt_rounds(10n, key_bytes, counter, nonce_bytes, plaintext))

# HChaCha20(key, nonce): the 32-byte subkey, or None unless 32 and 16 bytes.
def hchacha20(+key_bytes: List<&2, U32>, +nonce_bytes: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  when(valid(key_bytes, nonce_bytes, 16n), hchacha20_unchecked(key_bytes, nonce_bytes))

# XChaCha20 with a 24-byte nonce.
def xchacha20(+key_bytes: List<&2, U32>, counter: U32, +nonce_bytes: List<&2, U32>, +plaintext: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  when(valid(key_bytes, nonce_bytes, 24n), xencrypt_unchecked(key_bytes, counter, nonce_bytes, plaintext))
