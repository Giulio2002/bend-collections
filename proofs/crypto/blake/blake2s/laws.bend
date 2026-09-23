import Base
import ../../../../src/crypto/blake/blake2s/types.bend as T
import ../../../../src/crypto/blake/blake2s/compress.bend as C
import ../../../../src/crypto/blake/blake2s/blake2s.bend as K
import ./spec.bend as R

# The public API: for every packed input array and every byte length, the
# implementation returns exactly what the RFC 7693 specification returns
# (Some digest when length <= 4 * capacity, None otherwise).
law blake2s:
  for a: Array<U32>
  for +length: Nat
  {K.blake2s(a,length) == R.blake2s(a,length) : Maybe<&1,Array<U32>>}

# The unrolled compression function is F with r = 10 rounds, for every
# chaining value, message block, counter and final-block flag.
law compress:
  for +h: T.State
  for +m0: U32
  for +m1: U32
  for +m2: U32
  for +m3: U32
  for +m4: U32
  for +m5: U32
  for +m6: U32
  for +m7: U32
  for +m8: U32
  for +m9: U32
  for +m10: U32
  for +m11: U32
  for +m12: U32
  for +m13: U32
  for +m14: U32
  for +m15: U32
  for +t0: U32
  for +t1: U32
  for +last: Bool
  {C.compress(h,m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,t0,t1,last) == R.compress(10n,h,[m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15],t0,t1,last) : T.State}

law digest_size:
  for s: T.State
  {Pair.snd(Array<U32>,U32,Array.size(U32,K.digest(s))) == 8 : U32}

law capacity_rejection:
  for a: Array<U32>
  for +n: Nat
  for +capacity: U32
  for invalid: {Nat.is_le(n,Nat.mul(4n,U32.to_nat(capacity))) == False{} : Bool}
  {K.sized(n,(a,capacity)) == None{} : Maybe<&1,Array<U32>>}
