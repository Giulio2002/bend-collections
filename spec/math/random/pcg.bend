import Base
import ../../lib/common.bend as C

# Executable specification of Go's PCG (math/rand/v2 pcg.go; O'Neill, "PCG:
# A Family of Simple Fast Space-Efficient Statistically Good Algorithms for
# Random Number Generation", 2014, with the DXSM output function of numpy
# and Go) on natural numbers:
#
#   lcg(mul, inc, s)       one step of the 128-bit state: s * mul + inc
#                          mod 2^128
#   dxsm(cm, hi, lo)       the output of the state hi * 2^64 + lo:
#                          hi ^= hi >> 32; hi *= cm; hi ^= hi >> 48;
#                          hi *= lo | 1, each product mod 2^64
#
# Go's constants are mul = 2549297995355413924 * 2^64 + 4865540595714422341,
# inc = 6364136223846793005 * 2^64 + 1442695040888963407 and
# cm = 0xda942042e4dd58b5 (src/math/random/pcg.bend holds them as 64-bit
# words); the functions take them as parameters, so no closed 64-bit
# constant is ever expanded by the checker (spec/lib/common.bend).

def b2n(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# the exclusive or of the low w bits of a and b
def xor_bits(w: Nat, +a: Nat, +b: Nat) -> Nat:
  match w:
    case 0n:
      0n
    case 1n+k:
      Nat.add(b2n(Bool.not(Nat.is_eq(C.bit(a), C.bit(b)))), Nat.double(xor_bits(k, C.half(a), C.half(b))))

def lcg(+mul: Nat, +inc: Nat, +s: Nat) -> Nat:
  C.low(128n, Nat.add(Nat.mul(s, mul), inc))

def dxsm3(+h: Nat, +lo: Nat) -> Nat:
  C.low(64n, Nat.mul(xor_bits(64n, h, C.high(48n, h)), Nat.add(Nat.double(C.half(lo)), 1n)))

def dxsm(+cm: Nat, +hi: Nat, +lo: Nat) -> Nat:
  dxsm3(C.low(64n, Nat.mul(xor_bits(64n, hi, C.high(32n, hi)), cm)), lo)
