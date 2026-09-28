import Base
import ../../../src/crypto/sha512/types.bend as T
import ../../../spec/crypto/sha512.bend as FIPS
import ../../../spec/lib/common.bend as C
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../math/typed/w64add.bend as W64A

# The specification's 64-bit words mean what FIPS 180-4 section 3.2 says: a
# word W{hi, lo} is the number lo + 2^32 hi, and the specification's addition
# is addition modulo 2^64. This does not rest on the implementation: it is
# the proved U64 addition of src/math/w64.bend (spec/math/w64.bend Add.value,
# proofs/math/typed/w64add.bend), which computes the same halves.

def value(w: T.Lane) -> Nat:
  match w:
    case T.W{hi, lo}:
      Nat.add(U32.to_nat(lo), C.shift(32n, U32.to_nat(hi)))

law carry_bit:
  for +b: Bool
  {X.b32(b) == Bool.to_u32(b) : U32}

def carry_bit(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

law add_value:
  for +a: T.Lane
  for +b: T.Lane
  {value(FIPS.add(a, b)) == C.low(64n, Nat.add(value(a), value(b))) : Nat}

def add_value(a, b):
  match a b:
    case T.W{ah, al} T.W{bh, bl}:
      %carry_bit(U32.is_lt(U32.add(al, bl), al)) :
        {Nat.add(U32.to_nat(U32.add(al, bl)), C.shift(32n, U32.to_nat(U32.add(U32.add(ah, bh), _)))) ==
          C.low(64n, Nat.add(value(T.W{ah, al}), value(T.W{bh, bl}))) : Nat}
      W64A.add_value(WU.U64{al, ah}, WU.U64{bl, bh})
