import Base
import ./sha.bend as FIPS

# Executable specification of HMAC-SHA256: RFC 2104 section 2, in the
# step-by-step form of FIPS 198-1 section 4, over the FIPS 180-4 SHA-256
# specification spec/crypto/sha.bend (after HACL*'s Spec.HMAC). Nothing of
# the implementation (src/crypto/mac.bend) or of the SHA-256 implementation
# is used. Bytes are U32 values 0..255, as everywhere in the library.

# B, the block size of SHA-256 in bytes, and L, its output size.
def block_len() -> Nat:
  64n

def hash_len() -> Nat:
  32n

# RFC 2104: ipad = the byte 0x36 repeated B times, opad = 0x5C repeated B times.
def ipad() -> U32:
  54

def opad() -> U32:
  92

def hash(bytes: List<&2, U32>) -> List<&2, U32>:
  FIPS.sha256_bytes(bytes)

# FIPS 198-1 steps 1-3: a key of exactly B bytes is K0 itself; a longer key
# is hashed first (K0 = H(K) || zeros); a shorter one is zero-padded to B.
def shorten_if(+key: List<&2, U32>, fits: Bool) -> List<&2, U32>:
  match fits:
    case True{}:
      key
    case False{}:
      hash(key)

def shorten(+key: List<&2, U32>) -> List<&2, U32>:
  shorten_if(key, Nat.is_le(List.length(&2, U32, key), block_len()))

def zero_pad(+k: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, k,
    List.replicate(U32, Nat.sub(block_len(), List.length(&2, U32, k)), 0))

def k0(+key: List<&2, U32>) -> List<&2, U32>:
  zero_pad(shorten(key))

# Byte-wise exclusive or of K0 with a pad byte (steps 4 and 7).
def xor_pad(ks: List<&2, U32>, +pad: U32) -> List<&2, U32>:
  match ks:
    case Nil{}:
      Nil{}
    case k <> rest:
      U32.xor(k, pad) <> xor_pad(rest, pad)

# HMAC(K, text) = H((K0 ^ opad) || H((K0 ^ ipad) || text))   (steps 4-9).
def hmac(+key: List<&2, U32>, text: List<&2, U32>) -> List<&2, U32>:
  +k = k0(key)
  hash(List.append(&2, U32, xor_pad(k, opad()),
    hash(List.append(&2, U32, xor_pad(k, ipad()), text))))
