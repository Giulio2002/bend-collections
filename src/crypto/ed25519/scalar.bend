import Base
import ../curve25519/field.bend as F
import ../curve25519/x25519.bend as X

# Scalars mod L = 2^252 + 27742317777372353535851937790883648493 (RFC 8032
# section 5.1), as 32 tight limbs (the field element representation of
# ../curve25519/field.bend), every value below L.
#
#   addm(a, b)          (a + b) mod L for a, b < L: the sum, then one
#                       conditional subtraction of L (carry of a + 2^256 - L)
#   mac(n, bs, s, acc)  acc 2^n + s * bits(n bits of bs, most significant
#                       first) mod L: double, then add s or 0 by selection
#   reduce(bs)          value(bs) mod L (a 64-byte SHA-512 digest, say)
#   mul_add(k, s, r)    (r + k s) mod L
#
# Every step is the same for every value (selection, fixed bit counts from
# the input's length): branch-free by construction.

# L, little-endian bytes
def ell() -> List<&2, U32>:
  [237, 211, 245, 92, 26, 99, 18, 88, 214, 156, 247, 162, 222, 249, 222, 20,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16]

# 2^256 - L
def comp_l() -> List<&2, U32>:
  [19, 44, 10, 163, 229, 156, 237, 167, 41, 99, 8, 93, 33, 6, 33, 235,
   255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 239]

# x - L when x >= L, else x (x tight, x < 2 L)
def csub(+x: List<&2, U32>) -> List<&2, U32>:
  F.csub_fin(F.carry(F.addl(x, comp_l()), 0), x)

def addm(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  csub(F.cr_limbs(F.carry(F.addl(a, b), 0)))

# bits t = n - 1 down to 0 of bs: acc = 2 acc + bit s (mod L)
def mac(n: Nat, +bs: List<&2, U32>, +s: List<&2, U32>, +acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+ +t:
      +a2 = addm(acc, acc)
      mac(t, bs, s, addm(a2, F.select(X.kbit(bs, t), F.zero(), s)))

def reduce(+bs: List<&2, U32>) -> List<&2, U32>:
  mac(X.bitlen(bs), bs, F.one(), F.zero())

def mul_add(+k: List<&2, U32>, +s: List<&2, U32>, r: List<&2, U32>) -> List<&2, U32>:
  addm(mac(X.bitlen(k), k, s, F.zero()), r)

# x < L: the carry of x + 2^256 - L is 0
def lt_l(+x: List<&2, U32>) -> Bool:
  U32.is_eq(F.cr_out(F.carry(F.addl(x, comp_l()), 0)), 0)
