import Base
import ./sha/sha256.bend as SHA
import ./subtle.bend as Subtle

# HMAC-SHA256 (RFC 2104, FIPS 198-1), on the verified SHA-256.
#
#   sign(key, msg) -> tag          32-byte tag
#   verify(key, msg, tag) -> Bool  constant-time comparison of the tag
#
# Bytes are U32 values 0..255 (the library's byte convention). Keys of any
# length are accepted: a key longer than the 64-byte block is hashed first,
# a shorter one is zero-padded (RFC 2104 section 2). The specification is
# spec/crypto/hmac.bend; proofs/crypto/mac/proof.bend proves sign equal to
# it for every key and message, verify(k, m, sign(k, m)) == True, and that
# verify rejects every other tag.

def block_len() -> Nat:
  64n

# Whether a key fits in the block, looking at no more than 65 of its bytes
# (the length of a long key is never computed).
def fits(key: List<&2, U32>, n: Nat) -> Bool:
  match key n:
    case Nil{} _:
      True{}
    case k <> rest 0n:
      False{}
    case k <> rest 1n+p:
      fits(rest, p)

def block_key_if(+key: List<&2, U32>, short: Bool) -> List<&2, U32>:
  match short:
    case True{}:
      key
    case False{}:
      SHA.sha256_bytes(key)

# The key as it enters the block: itself, or its digest when too long.
def block_key(+key: List<&2, U32>) -> List<&2, U32>:
  block_key_if(key, fits(key, block_len()))

# The n-byte block (key zero-padded to n bytes) XOR the pad byte, in one
# pass: past the end of the key a byte is 0 XOR pad = pad.
def mask(key: List<&2, U32>, n: Nat, +pad: U32) -> List<&2, U32>:
  match key n:
    case Nil{} 0n:
      Nil{}
    case Nil{} 1n+p:
      pad <> mask(Nil{}, p, pad)
    case k <> rest 0n:
      Nil{}
    case k <> rest 1n+p:
      U32.xor(k, pad) <> mask(rest, p, pad)

def sign(+key: List<&2, U32>, msg: List<&2, U32>) -> List<&2, U32>:
  +k = block_key(key)
  SHA.sha256_bytes(List.append(&2, U32, mask(k, block_len(), 92),
    SHA.sha256_bytes(List.append(&2, U32, mask(k, block_len(), 54), msg))))

# The tag is compared in constant time (subtle.eq: no early exit on the
# contents; only the lengths, which are public, are compared directly).
def verify(+key: List<&2, U32>, msg: List<&2, U32>, tag: List<&2, U32>) -> Bool:
  Subtle.eq(sign(key, msg), tag)
