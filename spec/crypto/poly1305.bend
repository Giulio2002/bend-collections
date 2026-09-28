import Base
import ../lib/common.bend as C

# Specification of the Poly1305 one-time authenticator (RFC 8439 section
# 2.5), transcribed from the RFC's pseudocode over natural numbers. Nothing
# is shared with the implementation (src/crypto/poly1305/): the accumulator
# is one Nat reduced mod p = 2^130 - 5 after every block, as in HACL*'s
# Spec.Poly1305. Numbers are little-endian byte strings; a byte is the low 8
# bits of a U32. Multiplication by 256 is written C.shift(8n, x) (eight
# doublings, spec/lib/common.bend) and 2^k as C.pow2(k).
#
# Bend's native runtime keeps a Nat below 2^48, so this specification is a
# proof object; tools/check_poly1305.py runs a line-by-line mirror of it.

# p = 2^130 - 5
def p() -> Nat:
  Nat.sub(C.pow2(130n), 5n)

# le_bytes_to_num
def le_num(bytes: List<&2, U32>) -> Nat:
  match bytes:
    case Nil{}: 0n
    case b <> rest: Nat.add(U32.to_nat(U32.and(b, 255)), C.shift(8n, le_num(rest)))

# num_to_n_le_bytes: the low n bytes of x.
def le_bytes(n: Nat, +x: Nat) -> List<&2, U32>:
  match n:
    case 0n: Nil{}
    case 1n+k: U32.from_nat(C.low(8n, x)) <> le_bytes(k, C.high(8n, x))

def prefix(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n xs:
    case 0n _: Nil{}
    case 1n+k Nil{}: Nil{}
    case 1n+k x <> rest: x <> prefix(k, rest)

def suffix(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n xs:
    case 0n _: xs
    case 1n+k Nil{}: Nil{}
    case 1n+k x <> rest: suffix(k, rest)

# clamp(r): r &= 0x0ffffffc0ffffffc0ffffffc0fffffff, i.e. r[3], r[7], r[11]
# and r[15] keep their low four bits, r[4], r[8] and r[12] lose their low two.
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

def clamp_from(r: List<&2, U32>, +i: Nat) -> List<&2, U32>:
  match r:
    case Nil{}: Nil{}
    case b <> rest: U32.and(b, clamp_mask(i)) <> clamp_from(rest, 1n+i)

def clamp(r: List<&2, U32>) -> List<&2, U32>:
  clamp_from(r, 0n)

# The message cut into 16-byte blocks, the last one possibly shorter; fuel
# bounds the number of blocks (the length of the message is enough).
def blocks(fuel: Nat, +msg: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match fuel msg:
    case 0n _: Nil{}
    case 1n+k Nil{}: Nil{}
    case 1n+k b <> rest: prefix(16n, b <> rest) <> blocks(k, suffix(16n, b <> rest))

# for each block: n = le_bytes_to_num(block | [0x01]); a += n; a = (r * a) % p
def absorb(bs: List<&2, List<&2, U32>>, +r: Nat, a: Nat) -> Nat:
  match bs:
    case Nil{}: a
    case b <> rest:
      +n = le_num(List.append(&2, U32, b, [1]))
      absorb(rest, r, Nat.mod(Nat.mul(r, Nat.add(a, n)), p()))

# poly1305_mac(msg, key): r = clamp(key[0..16]), s = key[16..32];
# a = 0, absorb every block, a += s; the tag is num_to_16_le_bytes(a).
def mac(+key: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  +r = le_num(clamp(prefix(16n, key)))
  +s = le_num(prefix(16n, suffix(16n, key)))
  le_bytes(16n, Nat.add(absorb(blocks(List.length(&2, U32, msg), msg), r, 0n), s))
