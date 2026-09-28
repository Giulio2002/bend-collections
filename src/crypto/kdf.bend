import Base
import ./mac.bend as MAC

# HKDF-SHA256 (RFC 5869), on HMAC-SHA256 (src/crypto/mac.bend).
#
#   extract(salt, ikm) -> prk                 32-byte pseudorandom key
#   expand(prk, info, len) -> Done{okm} | Fail{LengthTooLarge{}}
#   hkdf(salt, ikm, info, len)                expand(extract(salt, ikm), info, len)
#
# len is at most 255 * 32 = 8160 bytes; a larger len is the error value
# LengthTooLarge (never a crash). An empty salt means "no salt" (RFC 5869:
# HashLen zero bytes, which gives the same HMAC key). The specification is
# spec/crypto/hkdf.bend; proofs/crypto/kdf/proof.bend proves expand equal to
# it for every input, the output length, and that a shorter output is a
# prefix of a longer one.

type KdfError is Data:
  LengthTooLarge{}

def max_length() -> Nat:
  8160n

def extract(+salt: List<&2, U32>, ikm: List<&2, U32>) -> List<&2, U32>:
  MAC.sign(salt, ikm)

# The blocks T(i), T(i+1), ... cut to rem bytes: prev is T(i-1) and ctr the
# counter byte i. Generation stops as soon as rem bytes are out, and no
# block count is computed.
def blocks(rem: Nat, +prk: List<&2, U32>, +info: List<&2, U32>, prev: List<&2, U32>, +ctr: U32) -> List<&2, U32>:
  match rem:
    case 0n:
      Nil{}
    case 32n+r:
      +t = MAC.sign(prk, List.append(&2, U32, prev, List.append(&2, U32, info, [ctr])))
      List.append(&2, U32, t, blocks(r, prk, info, t, U32.inc(ctr)))
    case 1n+p:
      List.take(&2, U32, MAC.sign(prk, List.append(&2, U32, prev, List.append(&2, U32, info, [ctr]))), 1n+p)

def expand_if(+prk: List<&2, U32>, +info: List<&2, U32>, +len: Nat, ok: Bool) -> Result<&2, &2, KdfError, List<&2, U32>>:
  match ok:
    case True{}:
      Done{blocks(len, prk, info, Nil{}, 1)}
    case False{}:
      Fail{LengthTooLarge{}}

def expand(+prk: List<&2, U32>, +info: List<&2, U32>, +len: Nat) -> Result<&2, &2, KdfError, List<&2, U32>>:
  expand_if(prk, info, len, Nat.is_le(len, max_length()))

def hkdf(+salt: List<&2, U32>, ikm: List<&2, U32>, +info: List<&2, U32>, +len: Nat) -> Result<&2, &2, KdfError, List<&2, U32>>:
  expand(extract(salt, ikm), info, len)
