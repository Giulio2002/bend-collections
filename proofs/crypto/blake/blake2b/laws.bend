import Base
import ../../../../src/crypto/blake/blake2b/types.bend as T
import ../../../../src/crypto/blake/blake2b/compress.bend as F
import ../../../../src/crypto/blake/blake2b/blake2b.bend as I
import ../../../../spec/crypto/blake/blake2b.bend as S

# The public BLAKE2b-512 API equals the RFC 7693 specification of spec/crypto/blake/blake2b.bend for
# every packed input array and every byte length: the same digest, or None for
# both when byte_length exceeds 4 * the array's capacity.
law blake2b_correct:
  for words: Array<U32>
  for +byte_length: Nat
  {I.blake2b(words,byte_length) == S.blake2b(words,byte_length) : Maybe<&1,Array<U32>>}

# The compression function F on a block that is not the last, for every chaining value h,
# counter t and message block.
law compress_correct:
  for +h: T.Chain
  for +t: T.Counter
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for +w8: U32
  for +w9: U32
  for +w10: U32
  for +w11: U32
  for +w12: U32
  for +w13: U32
  for +w14: U32
  for +w15: U32
  for +w16: U32
  for +w17: U32
  for +w18: U32
  for +w19: U32
  for +w20: U32
  for +w21: U32
  for +w22: U32
  for +w23: U32
  for +w24: U32
  for +w25: U32
  for +w26: U32
  for +w27: U32
  for +w28: U32
  for +w29: U32
  for +w30: U32
  for +w31: U32
  {F.compress(h,t,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31) == S.compress(h,[T.W{w0,w1},T.W{w2,w3},T.W{w4,w5},T.W{w6,w7},T.W{w8,w9},T.W{w10,w11},T.W{w12,w13},T.W{w14,w15},T.W{w16,w17},T.W{w18,w19},T.W{w20,w21},T.W{w22,w23},T.W{w24,w25},T.W{w26,w27},T.W{w28,w29},T.W{w30,w31}],t,False{}) : T.Chain}

# The compression function F on the last block, for every chaining value h,
# counter t and message block.
law compress_last_correct:
  for +h: T.Chain
  for +t: T.Counter
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for +w8: U32
  for +w9: U32
  for +w10: U32
  for +w11: U32
  for +w12: U32
  for +w13: U32
  for +w14: U32
  for +w15: U32
  for +w16: U32
  for +w17: U32
  for +w18: U32
  for +w19: U32
  for +w20: U32
  for +w21: U32
  for +w22: U32
  for +w23: U32
  for +w24: U32
  for +w25: U32
  for +w26: U32
  for +w27: U32
  for +w28: U32
  for +w29: U32
  for +w30: U32
  for +w31: U32
  {F.compress_last(h,t,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31) == S.compress(h,[T.W{w0,w1},T.W{w2,w3},T.W{w4,w5},T.W{w6,w7},T.W{w8,w9},T.W{w10,w11},T.W{w12,w13},T.W{w14,w15},T.W{w16,w17},T.W{w18,w19},T.W{w20,w21},T.W{w22,w23},T.W{w24,w25},T.W{w26,w27},T.W{w28,w29},T.W{w30,w31}],t,True{}) : T.Chain}

# Every digest is sixteen words (64 bytes).
law digest_size:
  for h: T.Chain
  {Pair.snd(Array<U32>,U32,Array.size(U32,I.digest(h))) == 16 : U32}

# Lengths past the array's capacity are rejected.
law capacity_rejection:
  for a: Array<U32>
  for +n: Nat
  for +capacity: U32
  for invalid: {Nat.is_le(n,Nat.mul(4n,U32.to_nat(capacity))) == False{} : Bool}
  {I.sized(n,(a,capacity)) == None{} : Maybe<&1,Array<U32>>}
