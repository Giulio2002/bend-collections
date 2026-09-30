import Base
import ./limbs.bend as L
import ../subtle.bend as Subtle

# Poly1305 (RFC 8439 section 2.5) over byte lists, on radix-2^8 limbs
# (src/crypto/poly1305/limbs.bend). A byte is the low 8 bits of a U32. The
# key is r || s (32 bytes); mac reads missing key bytes as absent (zero), the
# checked poly1305 returns None unless the key has exactly 32 bytes.
# proofs/crypto/poly1305/ proves mac equal to spec/crypto/poly1305.bend for
# every key and message.

def mask(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}: Nil{}
    case x <> t: U32.and(x, 255) <> mask(t)

# r &= 0x0ffffffc0ffffffc0ffffffc0fffffff, byte by byte.
def clamp_mask(i: Nat) -> U32:
  match i:
    case 3n: 15
    case 7n: 15
    case 11n: 15
    case 15n: 15
    case 4n: 252
    case 8n: 252
    case 12n: 252
    case _: 255

def clamp(r: List<&2, U32>, +i: Nat) -> List<&2, U32>:
  match r:
    case Nil{}: Nil{}
    case b <> rest: U32.and(b, clamp_mask(i)) <> clamp(rest, 1n+i)

# A message block as limbs: its bytes, then the 0x01 byte.
def load(b: List<&2, U32>) -> List<&2, U32>:
  mask(List.append(&2, U32, b, [1]))

# The accumulator over 16-byte blocks (the last one possibly shorter); fuel
# bounds the number of blocks. (A one-byte message is its own case only so
# that a proof about a message b <> rest with rest unknown stays small.)
def absorb(fuel: Nat, +msg: List<&2, U32>, +r: List<&2, U32>, h: List<&2, U32>) -> List<&2, U32>:
  match fuel msg:
    case 0n _: h
    case 1n+k Nil{}: h
    case 1n+k b <> Nil{}:
      absorb(k, L.skip(16n, [b]), r, L.block(r, h, load(L.take(16n, [b]))))
    case 1n+k b <> c <> rest:
      absorb(k, L.skip(16n, b <> c <> rest), r, L.block(r, h, load(L.take(16n, b <> c <> rest))))

def zero() -> List<&2, U32>:
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

# r = clamp(key[0..16]) and s = key[16..32], as limbs.
def r_key(+key: List<&2, U32>) -> List<&2, U32>:
  L.fit(16n, mask(clamp(L.take(16n, key), 0n)))

def s_key(+key: List<&2, U32>) -> List<&2, U32>:
  mask(L.take(16n, L.skip(16n, key)))

def tag(+key: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  +r = r_key(key)
  +s = s_key(key)
  +h = absorb(List.length(&2, U32, msg), msg, r, zero())
  L.fin(h, s)

# The 16-byte tag of msg under key = r || s. (The match on msg only keeps a
# proof's goal small while msg is unknown; both arms are the same.)
def mac(+key: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  match msg:
    case Nil{}: tag(key, [])
    case b <> rest: tag(key, b <> rest)

def has_key(+key: List<&2, U32>) -> Bool:
  Nat.is_eq(List.length(&2, U32, key), 32n)

def when(ok: Bool, x: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: Some{x}
    case False{}: None{}

# The tag, or None unless the key has 32 bytes.
def poly1305(+key: List<&2, U32>, +msg: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  when(has_key(key), mac(key, msg))

# True exactly when the key has 32 bytes and tag is the tag of msg; the tags
# are compared in constant time (src/crypto/subtle.bend).
def verify(+key: List<&2, U32>, +msg: List<&2, U32>, +tag: List<&2, U32>) -> Bool:
  Bool.and(has_key(key), Subtle.eq(mac(key, msg), tag))
