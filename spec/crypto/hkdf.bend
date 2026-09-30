import Base
import ./hmac.bend as HMAC

# Executable specification of HKDF-SHA256, RFC 5869 section 2, over the
# HMAC specification spec/crypto/hmac.bend (after HACL*'s Spec.HKDF).
# Nothing of the implementation (src/crypto/kdf.bend) is used.

def hash_len() -> Nat:
  32n

# RFC 5869: L <= 255*HashLen.
def max_length() -> Nat:
  8160n

# 2.2 Step 1: Extract. PRK = HMAC-Hash(salt, IKM). An absent salt is HashLen
# zero bytes; an empty salt gives the same HMAC key block (both are padded
# with zeros to the block size), so passing [] means "not provided".
def extract(+salt: List<&2, U32>, ikm: List<&2, U32>) -> List<&2, U32>:
  HMAC.hmac(salt, ikm)

# 2.3 Step 2: Expand. T(0) = empty string; for i = 1..N,
#   T(i) = HMAC-Hash(PRK, T(i-1) | info | the octet i).
# t_blocks(n, prk, info, T(i), i) is T(i+1) | ... | T(i+n).
def t_blocks(n: Nat, +prk: List<&2, U32>, +info: List<&2, U32>, prev: List<&2, U32>, +i: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      +t = HMAC.hmac(prk, List.append(&2, U32, prev,
        List.append(&2, U32, info, [U32.from_nat(1n+i)])))
      List.append(&2, U32, t, t_blocks(p, prk, info, t, 1n+i))

# N = ceil(L/HashLen).
def block_count(+len: Nat) -> Nat:
  Nat.div(Nat.add(len, 31n), hash_len())

# OKM = the first L octets of T = T(1) | T(2) | ... | T(N).
def okm(+prk: List<&2, U32>, +info: List<&2, U32>, +len: Nat) -> List<&2, U32>:
  List.take(&2, U32, t_blocks(block_count(len), prk, info, Nil{}, 0n), len)

# Expand is defined for L <= 255*HashLen only.
def expand_if(+prk: List<&2, U32>, +info: List<&2, U32>, +len: Nat, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{okm(prk, info, len)}
    case False{}:
      None{}

def expand(+prk: List<&2, U32>, +info: List<&2, U32>, +len: Nat) -> Maybe<&2, List<&2, U32>>:
  expand_if(prk, info, len, Nat.is_le(len, max_length()))

def hkdf(+salt: List<&2, U32>, ikm: List<&2, U32>, +info: List<&2, U32>, +len: Nat) -> Maybe<&2, List<&2, U32>>:
  expand(extract(salt, ikm), info, len)
