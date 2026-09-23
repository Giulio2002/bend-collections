import Base
import ../../../src/crypto/keccak/types.bend as T
import ../../../src/crypto/keccak/keccak.bend as K
import ../../../src/crypto/keccak/permutation.bend as P
import ./spec_permutation.bend as F
import ./spec.bend as R
import ./permutation.bend as Q
import ./array.bend as A

law mix_correct:
  for +s: T.State
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
  for +w32: U32
  for +w33: U32
  {K.mix(s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33) == R.inject(s,[w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33]) : T.State}

def mix_correct(s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33):
  match s:
    case T.S{T.W{a0,b0},T.W{a1,b1},T.W{a2,b2},T.W{a3,b3},T.W{a4,b4},T.W{a5,b5},T.W{a6,b6},T.W{a7,b7},T.W{a8,b8},T.W{a9,b9},T.W{a10,b10},T.W{a11,b11},T.W{a12,b12},T.W{a13,b13},T.W{a14,b14},T.W{a15,b15},T.W{a16,b16},T.W{a17,b17},T.W{a18,b18},T.W{a19,b19},T.W{a20,b20},T.W{a21,b21},T.W{a22,b22},T.W{a23,b23},T.W{a24,b24}}: {==}

law compress_correct:
  for +r: Nat
  for +s: T.State
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
  for +w32: U32
  for +w33: U32
  {P.rounds(r,0n,K.mix(s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33)) == F.rounds(r,0n,R.inject(s,[w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33])) : T.State}

def compress_correct(r,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33):
  Equal.trans(T.State,P.rounds(r,0n,K.mix(s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33)),F.rounds(r,0n,K.mix(s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33)),F.rounds(r,0n,R.inject(s,[w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33])),
    Q.rounds_correct(r,0n,K.mix(s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33)),
    Equal.cong(T.State,T.State,t => F.rounds(r,0n,t),K.mix(s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33),R.inject(s,[w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33]),mix_correct(s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33)))

law read33_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for +w32: U32
  for pair: Array<U32> & U32
  {K.read33(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,pair) == R.gather(r,0n,index,34,False{},0n,s,[w32,w31,w30,w29,w28,w27,w26,w25,w24,w23,w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read33_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,pair):
  (a,w33) = pair
  Equal.cong(T.State,Array<U32> & T.State,t => (a,t),P.rounds(r,0n,K.mix(s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33)),F.rounds(r,0n,R.inject(s,[w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33])),compress_correct(r,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33))

law read32_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read32(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,pair) == R.gather(r,1n,index,33,False{},0n,s,[w31,w30,w29,w28,w27,w26,w25,w24,w23,w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read32_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,pair):
  (a,w32) = pair
  read33_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,Array.get(U32,a,U32.add(index,33)))

law read31_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read31(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,pair) == R.gather(r,2n,index,32,False{},0n,s,[w30,w29,w28,w27,w26,w25,w24,w23,w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read31_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,pair):
  (a,w31) = pair
  read32_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,Array.get(U32,a,U32.add(index,32)))

law read30_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read30(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,pair) == R.gather(r,3n,index,31,False{},0n,s,[w29,w28,w27,w26,w25,w24,w23,w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read30_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,pair):
  (a,w30) = pair
  read31_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,Array.get(U32,a,U32.add(index,31)))

law read29_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read29(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,pair) == R.gather(r,4n,index,30,False{},0n,s,[w28,w27,w26,w25,w24,w23,w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read29_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,pair):
  (a,w29) = pair
  read30_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,Array.get(U32,a,U32.add(index,30)))

law read28_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read28(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,pair) == R.gather(r,5n,index,29,False{},0n,s,[w27,w26,w25,w24,w23,w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read28_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,pair):
  (a,w28) = pair
  read29_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,Array.get(U32,a,U32.add(index,29)))

law read27_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read27(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,pair) == R.gather(r,6n,index,28,False{},0n,s,[w26,w25,w24,w23,w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read27_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,pair):
  (a,w27) = pair
  read28_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,Array.get(U32,a,U32.add(index,28)))

law read26_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read26(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,pair) == R.gather(r,7n,index,27,False{},0n,s,[w25,w24,w23,w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read26_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,pair):
  (a,w26) = pair
  read27_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,Array.get(U32,a,U32.add(index,27)))

law read25_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read25(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,pair) == R.gather(r,8n,index,26,False{},0n,s,[w24,w23,w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read25_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,pair):
  (a,w25) = pair
  read26_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,Array.get(U32,a,U32.add(index,26)))

law read24_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read24(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,pair) == R.gather(r,9n,index,25,False{},0n,s,[w23,w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read24_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,pair):
  (a,w24) = pair
  read25_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,Array.get(U32,a,U32.add(index,25)))

law read23_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read23(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,pair) == R.gather(r,10n,index,24,False{},0n,s,[w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read23_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,pair):
  (a,w23) = pair
  read24_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,Array.get(U32,a,U32.add(index,24)))

law read22_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read22(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,pair) == R.gather(r,11n,index,23,False{},0n,s,[w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read22_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,pair):
  (a,w22) = pair
  read23_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,Array.get(U32,a,U32.add(index,23)))

law read21_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read21(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,pair) == R.gather(r,12n,index,22,False{},0n,s,[w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read21_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,pair):
  (a,w21) = pair
  read22_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,Array.get(U32,a,U32.add(index,22)))

law read20_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read20(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,pair) == R.gather(r,13n,index,21,False{},0n,s,[w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read20_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,pair):
  (a,w20) = pair
  read21_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,Array.get(U32,a,U32.add(index,21)))

law read19_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read19(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,pair) == R.gather(r,14n,index,20,False{},0n,s,[w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read19_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,pair):
  (a,w19) = pair
  read20_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,Array.get(U32,a,U32.add(index,20)))

law read18_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read18(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,pair) == R.gather(r,15n,index,19,False{},0n,s,[w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read18_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,pair):
  (a,w18) = pair
  read19_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,Array.get(U32,a,U32.add(index,19)))

law read17_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read17(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,pair) == R.gather(r,16n,index,18,False{},0n,s,[w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read17_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,pair):
  (a,w17) = pair
  read18_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,Array.get(U32,a,U32.add(index,18)))

law read16_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read16(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,pair) == R.gather(r,17n,index,17,False{},0n,s,[w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read16_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,pair):
  (a,w16) = pair
  read17_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,Array.get(U32,a,U32.add(index,17)))

law read15_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read15(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,pair) == R.gather(r,18n,index,16,False{},0n,s,[w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read15_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,pair):
  (a,w15) = pair
  read16_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,Array.get(U32,a,U32.add(index,16)))

law read14_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read14(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,pair) == R.gather(r,19n,index,15,False{},0n,s,[w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read14_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,pair):
  (a,w14) = pair
  read15_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,Array.get(U32,a,U32.add(index,15)))

law read13_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read13(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,pair) == R.gather(r,20n,index,14,False{},0n,s,[w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read13_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,pair):
  (a,w13) = pair
  read14_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,Array.get(U32,a,U32.add(index,14)))

law read12_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read12(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,pair) == R.gather(r,21n,index,13,False{},0n,s,[w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read12_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,pair):
  (a,w12) = pair
  read13_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,Array.get(U32,a,U32.add(index,13)))

law read11_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read11(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,pair) == R.gather(r,22n,index,12,False{},0n,s,[w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read11_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,pair):
  (a,w11) = pair
  read12_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,Array.get(U32,a,U32.add(index,12)))

law read10_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.read10(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,pair) == R.gather(r,23n,index,11,False{},0n,s,[w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read10_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,pair):
  (a,w10) = pair
  read11_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,Array.get(U32,a,U32.add(index,11)))

law read9_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for +w8: U32
  for pair: Array<U32> & U32
  {K.read9(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,pair) == R.gather(r,24n,index,10,False{},0n,s,[w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read9_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,pair):
  (a,w9) = pair
  read10_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,Array.get(U32,a,U32.add(index,10)))

law read8_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for pair: Array<U32> & U32
  {K.read8(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,pair) == R.gather(r,25n,index,9,False{},0n,s,[w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read8_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,pair):
  (a,w8) = pair
  read9_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,Array.get(U32,a,U32.add(index,9)))

law read7_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for pair: Array<U32> & U32
  {K.read7(r,index,s,w0,w1,w2,w3,w4,w5,w6,pair) == R.gather(r,26n,index,8,False{},0n,s,[w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read7_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,pair):
  (a,w7) = pair
  read8_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,w7,Array.get(U32,a,U32.add(index,8)))

law read6_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for pair: Array<U32> & U32
  {K.read6(r,index,s,w0,w1,w2,w3,w4,w5,pair) == R.gather(r,27n,index,7,False{},0n,s,[w5,w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read6_correct(r,index,s,w0,w1,w2,w3,w4,w5,pair):
  (a,w6) = pair
  read7_correct(r,index,s,w0,w1,w2,w3,w4,w5,w6,Array.get(U32,a,U32.add(index,7)))

law read5_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for pair: Array<U32> & U32
  {K.read5(r,index,s,w0,w1,w2,w3,w4,pair) == R.gather(r,28n,index,6,False{},0n,s,[w4,w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read5_correct(r,index,s,w0,w1,w2,w3,w4,pair):
  (a,w5) = pair
  read6_correct(r,index,s,w0,w1,w2,w3,w4,w5,Array.get(U32,a,U32.add(index,6)))

law read4_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for pair: Array<U32> & U32
  {K.read4(r,index,s,w0,w1,w2,w3,pair) == R.gather(r,29n,index,5,False{},0n,s,[w3,w2,w1,w0],pair) : Array<U32> & T.State}

def read4_correct(r,index,s,w0,w1,w2,w3,pair):
  (a,w4) = pair
  read5_correct(r,index,s,w0,w1,w2,w3,w4,Array.get(U32,a,U32.add(index,5)))

law read3_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for pair: Array<U32> & U32
  {K.read3(r,index,s,w0,w1,w2,pair) == R.gather(r,30n,index,4,False{},0n,s,[w2,w1,w0],pair) : Array<U32> & T.State}

def read3_correct(r,index,s,w0,w1,w2,pair):
  (a,w3) = pair
  read4_correct(r,index,s,w0,w1,w2,w3,Array.get(U32,a,U32.add(index,4)))

law read2_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
  for +w0: U32
  for +w1: U32
  for pair: Array<U32> & U32
  {K.read2(r,index,s,w0,w1,pair) == R.gather(r,31n,index,3,False{},0n,s,[w1,w0],pair) : Array<U32> & T.State}

def read2_correct(r,index,s,w0,w1,pair):
  (a,w2) = pair
  read3_correct(r,index,s,w0,w1,w2,Array.get(U32,a,U32.add(index,3)))

law read1_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
  for +w0: U32
  for pair: Array<U32> & U32
  {K.read1(r,index,s,w0,pair) == R.gather(r,32n,index,2,False{},0n,s,[w0],pair) : Array<U32> & T.State}

def read1_correct(r,index,s,w0,pair):
  (a,w1) = pair
  read2_correct(r,index,s,w0,w1,Array.get(U32,a,U32.add(index,2)))

law read0_correct:
  for +r: Nat
  for +index: U32
  for +s: T.State
  for pair: Array<U32> & U32
  {K.read0(r,index,s,pair) == R.gather(r,33n,index,1,False{},0n,s,[],pair) : Array<U32> & T.State}

def read0_correct(r,index,s,pair):
  (a,w0) = pair
  read1_correct(r,index,s,w0,Array.get(U32,a,U32.add(index,1)))

law padding_correct:
  for +remain: Nat
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
  for +w32: U32
  for +w33: U32
  {[K.pad_word(w0,0n,remain),K.pad_word(w1,4n,remain),K.pad_word(w2,8n,remain),K.pad_word(w3,12n,remain),K.pad_word(w4,16n,remain),K.pad_word(w5,20n,remain),K.pad_word(w6,24n,remain),K.pad_word(w7,28n,remain),K.pad_word(w8,32n,remain),K.pad_word(w9,36n,remain),K.pad_word(w10,40n,remain),K.pad_word(w11,44n,remain),K.pad_word(w12,48n,remain),K.pad_word(w13,52n,remain),K.pad_word(w14,56n,remain),K.pad_word(w15,60n,remain),K.pad_word(w16,64n,remain),K.pad_word(w17,68n,remain),K.pad_word(w18,72n,remain),K.pad_word(w19,76n,remain),K.pad_word(w20,80n,remain),K.pad_word(w21,84n,remain),K.pad_word(w22,88n,remain),K.pad_word(w23,92n,remain),K.pad_word(w24,96n,remain),K.pad_word(w25,100n,remain),K.pad_word(w26,104n,remain),K.pad_word(w27,108n,remain),K.pad_word(w28,112n,remain),K.pad_word(w29,116n,remain),K.pad_word(w30,120n,remain),K.pad_word(w31,124n,remain),K.pad_word(w32,128n,remain),U32.or(K.pad_word(w33,132n,remain),2147483648)] == R.prepare(True{},[w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33],remain) : List<&2,U32>}

def padding_correct(remain,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33):
  match remain:
    case 0n: {==}
    case 1n: {==}
    case 2n: {==}
    case 3n: {==}
    case 4n: {==}
    case 5n: {==}
    case 6n: {==}
    case 7n: {==}
    case 8n: {==}
    case 9n: {==}
    case 10n: {==}
    case 11n: {==}
    case 12n: {==}
    case 13n: {==}
    case 14n: {==}
    case 15n: {==}
    case 16n: {==}
    case 17n: {==}
    case 18n: {==}
    case 19n: {==}
    case 20n: {==}
    case 21n: {==}
    case 22n: {==}
    case 23n: {==}
    case 24n: {==}
    case 25n: {==}
    case 26n: {==}
    case 27n: {==}
    case 28n: {==}
    case 29n: {==}
    case 30n: {==}
    case 31n: {==}
    case 32n: {==}
    case 33n: {==}
    case 34n: {==}
    case 35n: {==}
    case 36n: {==}
    case 37n: {==}
    case 38n: {==}
    case 39n: {==}
    case 40n: {==}
    case 41n: {==}
    case 42n: {==}
    case 43n: {==}
    case 44n: {==}
    case 45n: {==}
    case 46n: {==}
    case 47n: {==}
    case 48n: {==}
    case 49n: {==}
    case 50n: {==}
    case 51n: {==}
    case 52n: {==}
    case 53n: {==}
    case 54n: {==}
    case 55n: {==}
    case 56n: {==}
    case 57n: {==}
    case 58n: {==}
    case 59n: {==}
    case 60n: {==}
    case 61n: {==}
    case 62n: {==}
    case 63n: {==}
    case 64n: {==}
    case 65n: {==}
    case 66n: {==}
    case 67n: {==}
    case 68n: {==}
    case 69n: {==}
    case 70n: {==}
    case 71n: {==}
    case 72n: {==}
    case 73n: {==}
    case 74n: {==}
    case 75n: {==}
    case 76n: {==}
    case 77n: {==}
    case 78n: {==}
    case 79n: {==}
    case 80n: {==}
    case 81n: {==}
    case 82n: {==}
    case 83n: {==}
    case 84n: {==}
    case 85n: {==}
    case 86n: {==}
    case 87n: {==}
    case 88n: {==}
    case 89n: {==}
    case 90n: {==}
    case 91n: {==}
    case 92n: {==}
    case 93n: {==}
    case 94n: {==}
    case 95n: {==}
    case 96n: {==}
    case 97n: {==}
    case 98n: {==}
    case 99n: {==}
    case 100n: {==}
    case 101n: {==}
    case 102n: {==}
    case 103n: {==}
    case 104n: {==}
    case 105n: {==}
    case 106n: {==}
    case 107n: {==}
    case 108n: {==}
    case 109n: {==}
    case 110n: {==}
    case 111n: {==}
    case 112n: {==}
    case 113n: {==}
    case 114n: {==}
    case 115n: {==}
    case 116n: {==}
    case 117n: {==}
    case 118n: {==}
    case 119n: {==}
    case 120n: {==}
    case 121n: {==}
    case 122n: {==}
    case 123n: {==}
    case 124n: {==}
    case 125n: {==}
    case 126n: {==}
    case 127n: {==}
    case 128n: {==}
    case 129n: {==}
    case 130n: {==}
    case 131n: {==}
    case 132n: {==}
    case 133n: {==}
    case 134n: {==}
    case 135n: {==}
    case 136n+p: {==}

law padded_compress_correct:
  for +r: Nat
  for +remain: Nat
  for +s: T.State
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
  for +w32: U32
  for +w33: U32
  {P.rounds(r,0n,K.mix(s,K.pad_word(w0,0n,remain),K.pad_word(w1,4n,remain),K.pad_word(w2,8n,remain),K.pad_word(w3,12n,remain),K.pad_word(w4,16n,remain),K.pad_word(w5,20n,remain),K.pad_word(w6,24n,remain),K.pad_word(w7,28n,remain),K.pad_word(w8,32n,remain),K.pad_word(w9,36n,remain),K.pad_word(w10,40n,remain),K.pad_word(w11,44n,remain),K.pad_word(w12,48n,remain),K.pad_word(w13,52n,remain),K.pad_word(w14,56n,remain),K.pad_word(w15,60n,remain),K.pad_word(w16,64n,remain),K.pad_word(w17,68n,remain),K.pad_word(w18,72n,remain),K.pad_word(w19,76n,remain),K.pad_word(w20,80n,remain),K.pad_word(w21,84n,remain),K.pad_word(w22,88n,remain),K.pad_word(w23,92n,remain),K.pad_word(w24,96n,remain),K.pad_word(w25,100n,remain),K.pad_word(w26,104n,remain),K.pad_word(w27,108n,remain),K.pad_word(w28,112n,remain),K.pad_word(w29,116n,remain),K.pad_word(w30,120n,remain),K.pad_word(w31,124n,remain),K.pad_word(w32,128n,remain),U32.or(K.pad_word(w33,132n,remain),2147483648))) == F.rounds(r,0n,R.inject(s,R.prepare(True{},[w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33],remain))) : T.State}

def padded_compress_correct(r,remain,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33):
  Equal.trans(T.State,
    P.rounds(r,0n,K.mix(s,K.pad_word(w0,0n,remain),K.pad_word(w1,4n,remain),K.pad_word(w2,8n,remain),K.pad_word(w3,12n,remain),K.pad_word(w4,16n,remain),K.pad_word(w5,20n,remain),K.pad_word(w6,24n,remain),K.pad_word(w7,28n,remain),K.pad_word(w8,32n,remain),K.pad_word(w9,36n,remain),K.pad_word(w10,40n,remain),K.pad_word(w11,44n,remain),K.pad_word(w12,48n,remain),K.pad_word(w13,52n,remain),K.pad_word(w14,56n,remain),K.pad_word(w15,60n,remain),K.pad_word(w16,64n,remain),K.pad_word(w17,68n,remain),K.pad_word(w18,72n,remain),K.pad_word(w19,76n,remain),K.pad_word(w20,80n,remain),K.pad_word(w21,84n,remain),K.pad_word(w22,88n,remain),K.pad_word(w23,92n,remain),K.pad_word(w24,96n,remain),K.pad_word(w25,100n,remain),K.pad_word(w26,104n,remain),K.pad_word(w27,108n,remain),K.pad_word(w28,112n,remain),K.pad_word(w29,116n,remain),K.pad_word(w30,120n,remain),K.pad_word(w31,124n,remain),K.pad_word(w32,128n,remain),U32.or(K.pad_word(w33,132n,remain),2147483648))),
    F.rounds(r,0n,R.inject(s,[K.pad_word(w0,0n,remain),K.pad_word(w1,4n,remain),K.pad_word(w2,8n,remain),K.pad_word(w3,12n,remain),K.pad_word(w4,16n,remain),K.pad_word(w5,20n,remain),K.pad_word(w6,24n,remain),K.pad_word(w7,28n,remain),K.pad_word(w8,32n,remain),K.pad_word(w9,36n,remain),K.pad_word(w10,40n,remain),K.pad_word(w11,44n,remain),K.pad_word(w12,48n,remain),K.pad_word(w13,52n,remain),K.pad_word(w14,56n,remain),K.pad_word(w15,60n,remain),K.pad_word(w16,64n,remain),K.pad_word(w17,68n,remain),K.pad_word(w18,72n,remain),K.pad_word(w19,76n,remain),K.pad_word(w20,80n,remain),K.pad_word(w21,84n,remain),K.pad_word(w22,88n,remain),K.pad_word(w23,92n,remain),K.pad_word(w24,96n,remain),K.pad_word(w25,100n,remain),K.pad_word(w26,104n,remain),K.pad_word(w27,108n,remain),K.pad_word(w28,112n,remain),K.pad_word(w29,116n,remain),K.pad_word(w30,120n,remain),K.pad_word(w31,124n,remain),K.pad_word(w32,128n,remain),U32.or(K.pad_word(w33,132n,remain),2147483648)])),
    F.rounds(r,0n,R.inject(s,R.prepare(True{},[w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33],remain))),
    compress_correct(r,s,K.pad_word(w0,0n,remain),K.pad_word(w1,4n,remain),K.pad_word(w2,8n,remain),K.pad_word(w3,12n,remain),K.pad_word(w4,16n,remain),K.pad_word(w5,20n,remain),K.pad_word(w6,24n,remain),K.pad_word(w7,28n,remain),K.pad_word(w8,32n,remain),K.pad_word(w9,36n,remain),K.pad_word(w10,40n,remain),K.pad_word(w11,44n,remain),K.pad_word(w12,48n,remain),K.pad_word(w13,52n,remain),K.pad_word(w14,56n,remain),K.pad_word(w15,60n,remain),K.pad_word(w16,64n,remain),K.pad_word(w17,68n,remain),K.pad_word(w18,72n,remain),K.pad_word(w19,76n,remain),K.pad_word(w20,80n,remain),K.pad_word(w21,84n,remain),K.pad_word(w22,88n,remain),K.pad_word(w23,92n,remain),K.pad_word(w24,96n,remain),K.pad_word(w25,100n,remain),K.pad_word(w26,104n,remain),K.pad_word(w27,108n,remain),K.pad_word(w28,112n,remain),K.pad_word(w29,116n,remain),K.pad_word(w30,120n,remain),K.pad_word(w31,124n,remain),K.pad_word(w32,128n,remain),U32.or(K.pad_word(w33,132n,remain),2147483648)),
    Equal.cong(List<&2,U32>,T.State,x => F.rounds(r,0n,R.inject(s,x)),[K.pad_word(w0,0n,remain),K.pad_word(w1,4n,remain),K.pad_word(w2,8n,remain),K.pad_word(w3,12n,remain),K.pad_word(w4,16n,remain),K.pad_word(w5,20n,remain),K.pad_word(w6,24n,remain),K.pad_word(w7,28n,remain),K.pad_word(w8,32n,remain),K.pad_word(w9,36n,remain),K.pad_word(w10,40n,remain),K.pad_word(w11,44n,remain),K.pad_word(w12,48n,remain),K.pad_word(w13,52n,remain),K.pad_word(w14,56n,remain),K.pad_word(w15,60n,remain),K.pad_word(w16,64n,remain),K.pad_word(w17,68n,remain),K.pad_word(w18,72n,remain),K.pad_word(w19,76n,remain),K.pad_word(w20,80n,remain),K.pad_word(w21,84n,remain),K.pad_word(w22,88n,remain),K.pad_word(w23,92n,remain),K.pad_word(w24,96n,remain),K.pad_word(w25,100n,remain),K.pad_word(w26,104n,remain),K.pad_word(w27,108n,remain),K.pad_word(w28,112n,remain),K.pad_word(w29,116n,remain),K.pad_word(w30,120n,remain),K.pad_word(w31,124n,remain),K.pad_word(w32,128n,remain),U32.or(K.pad_word(w33,132n,remain),2147483648)],R.prepare(True{},[w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33],remain),padding_correct(remain,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33)))

law pad33_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for +w32: U32
  for pair: Array<U32> & U32
  {K.pad33(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,0n,index,34,True{},remain,s,[w32,w31,w30,w29,w28,w27,w26,w25,w24,w23,w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad33_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,pair):
  (a,w33) = pair
  padded_compress_correct(r,remain,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33)

law pad32_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad32(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,1n,index,33,True{},remain,s,[w31,w30,w29,w28,w27,w26,w25,w24,w23,w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad32_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,pair):
  (a,w32) = pair
  pad33_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,Array.get(U32,a,U32.add(index,33)))

law pad31_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad31(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,2n,index,32,True{},remain,s,[w30,w29,w28,w27,w26,w25,w24,w23,w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad31_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,pair):
  (a,w31) = pair
  pad32_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,Array.get(U32,a,U32.add(index,32)))

law pad30_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad30(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,3n,index,31,True{},remain,s,[w29,w28,w27,w26,w25,w24,w23,w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad30_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,pair):
  (a,w30) = pair
  pad31_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,Array.get(U32,a,U32.add(index,31)))

law pad29_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad29(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,4n,index,30,True{},remain,s,[w28,w27,w26,w25,w24,w23,w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad29_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,pair):
  (a,w29) = pair
  pad30_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,Array.get(U32,a,U32.add(index,30)))

law pad28_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad28(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,5n,index,29,True{},remain,s,[w27,w26,w25,w24,w23,w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad28_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,pair):
  (a,w28) = pair
  pad29_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,Array.get(U32,a,U32.add(index,29)))

law pad27_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad27(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,6n,index,28,True{},remain,s,[w26,w25,w24,w23,w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad27_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,pair):
  (a,w27) = pair
  pad28_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,Array.get(U32,a,U32.add(index,28)))

law pad26_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad26(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,7n,index,27,True{},remain,s,[w25,w24,w23,w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad26_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,pair):
  (a,w26) = pair
  pad27_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,Array.get(U32,a,U32.add(index,27)))

law pad25_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad25(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,8n,index,26,True{},remain,s,[w24,w23,w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad25_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,pair):
  (a,w25) = pair
  pad26_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,Array.get(U32,a,U32.add(index,26)))

law pad24_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad24(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,9n,index,25,True{},remain,s,[w23,w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad24_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,pair):
  (a,w24) = pair
  pad25_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,Array.get(U32,a,U32.add(index,25)))

law pad23_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad23(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,10n,index,24,True{},remain,s,[w22,w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad23_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,pair):
  (a,w23) = pair
  pad24_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,Array.get(U32,a,U32.add(index,24)))

law pad22_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad22(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,11n,index,23,True{},remain,s,[w21,w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad22_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,pair):
  (a,w22) = pair
  pad23_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,Array.get(U32,a,U32.add(index,23)))

law pad21_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad21(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,12n,index,22,True{},remain,s,[w20,w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad21_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,pair):
  (a,w21) = pair
  pad22_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,Array.get(U32,a,U32.add(index,22)))

law pad20_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad20(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,13n,index,21,True{},remain,s,[w19,w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad20_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,pair):
  (a,w20) = pair
  pad21_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,Array.get(U32,a,U32.add(index,21)))

law pad19_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad19(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,14n,index,20,True{},remain,s,[w18,w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad19_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,pair):
  (a,w19) = pair
  pad20_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,Array.get(U32,a,U32.add(index,20)))

law pad18_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad18(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,15n,index,19,True{},remain,s,[w17,w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad18_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,pair):
  (a,w18) = pair
  pad19_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,Array.get(U32,a,U32.add(index,19)))

law pad17_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad17(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,16n,index,18,True{},remain,s,[w16,w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad17_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,pair):
  (a,w17) = pair
  pad18_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,Array.get(U32,a,U32.add(index,18)))

law pad16_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad16(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,17n,index,17,True{},remain,s,[w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad16_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,pair):
  (a,w16) = pair
  pad17_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,Array.get(U32,a,U32.add(index,17)))

law pad15_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad15(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,18n,index,16,True{},remain,s,[w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad15_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,pair):
  (a,w15) = pair
  pad16_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,Array.get(U32,a,U32.add(index,16)))

law pad14_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad14(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,19n,index,15,True{},remain,s,[w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad14_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,pair):
  (a,w14) = pair
  pad15_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,Array.get(U32,a,U32.add(index,15)))

law pad13_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad13(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,20n,index,14,True{},remain,s,[w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad13_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,pair):
  (a,w13) = pair
  pad14_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,Array.get(U32,a,U32.add(index,14)))

law pad12_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad12(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,21n,index,13,True{},remain,s,[w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad12_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,pair):
  (a,w12) = pair
  pad13_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,Array.get(U32,a,U32.add(index,13)))

law pad11_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad11(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,22n,index,12,True{},remain,s,[w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad11_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,pair):
  (a,w11) = pair
  pad12_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,Array.get(U32,a,U32.add(index,12)))

law pad10_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
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
  for pair: Array<U32> & U32
  {K.pad10(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,23n,index,11,True{},remain,s,[w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad10_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,pair):
  (a,w10) = pair
  pad11_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,Array.get(U32,a,U32.add(index,11)))

law pad9_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for +w8: U32
  for pair: Array<U32> & U32
  {K.pad9(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,24n,index,10,True{},remain,s,[w8,w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad9_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,pair):
  (a,w9) = pair
  pad10_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,Array.get(U32,a,U32.add(index,10)))

law pad8_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for pair: Array<U32> & U32
  {K.pad8(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,25n,index,9,True{},remain,s,[w7,w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad8_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,pair):
  (a,w8) = pair
  pad9_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,Array.get(U32,a,U32.add(index,9)))

law pad7_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for pair: Array<U32> & U32
  {K.pad7(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,26n,index,8,True{},remain,s,[w6,w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad7_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,pair):
  (a,w7) = pair
  pad8_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,Array.get(U32,a,U32.add(index,8)))

law pad6_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for pair: Array<U32> & U32
  {K.pad6(r,remain,index,s,w0,w1,w2,w3,w4,w5,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,27n,index,7,True{},remain,s,[w5,w4,w3,w2,w1,w0],pair)) : T.State}

def pad6_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,pair):
  (a,w6) = pair
  pad7_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,w6,Array.get(U32,a,U32.add(index,7)))

law pad5_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for pair: Array<U32> & U32
  {K.pad5(r,remain,index,s,w0,w1,w2,w3,w4,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,28n,index,6,True{},remain,s,[w4,w3,w2,w1,w0],pair)) : T.State}

def pad5_correct(r,remain,index,s,w0,w1,w2,w3,w4,pair):
  (a,w5) = pair
  pad6_correct(r,remain,index,s,w0,w1,w2,w3,w4,w5,Array.get(U32,a,U32.add(index,6)))

law pad4_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for pair: Array<U32> & U32
  {K.pad4(r,remain,index,s,w0,w1,w2,w3,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,29n,index,5,True{},remain,s,[w3,w2,w1,w0],pair)) : T.State}

def pad4_correct(r,remain,index,s,w0,w1,w2,w3,pair):
  (a,w4) = pair
  pad5_correct(r,remain,index,s,w0,w1,w2,w3,w4,Array.get(U32,a,U32.add(index,5)))

law pad3_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for pair: Array<U32> & U32
  {K.pad3(r,remain,index,s,w0,w1,w2,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,30n,index,4,True{},remain,s,[w2,w1,w0],pair)) : T.State}

def pad3_correct(r,remain,index,s,w0,w1,w2,pair):
  (a,w3) = pair
  pad4_correct(r,remain,index,s,w0,w1,w2,w3,Array.get(U32,a,U32.add(index,4)))

law pad2_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
  for +w0: U32
  for +w1: U32
  for pair: Array<U32> & U32
  {K.pad2(r,remain,index,s,w0,w1,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,31n,index,3,True{},remain,s,[w1,w0],pair)) : T.State}

def pad2_correct(r,remain,index,s,w0,w1,pair):
  (a,w2) = pair
  pad3_correct(r,remain,index,s,w0,w1,w2,Array.get(U32,a,U32.add(index,3)))

law pad1_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
  for +w0: U32
  for pair: Array<U32> & U32
  {K.pad1(r,remain,index,s,w0,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,32n,index,2,True{},remain,s,[w0],pair)) : T.State}

def pad1_correct(r,remain,index,s,w0,pair):
  (a,w1) = pair
  pad2_correct(r,remain,index,s,w0,w1,Array.get(U32,a,U32.add(index,2)))

law pad0_correct:
  for +r: Nat
  for +remain: Nat
  for +index: U32
  for +s: T.State
  for pair: Array<U32> & U32
  {K.pad0(r,remain,index,s,pair) == Pair.snd(Array<U32>,T.State,R.gather(r,33n,index,1,True{},remain,s,[],pair)) : T.State}

def pad0_correct(r,remain,index,s,pair):
  (a,w0) = pair
  pad1_correct(r,remain,index,s,w0,Array.get(U32,a,U32.add(index,1)))


law absorb_correct:
  for +r: Nat
  for a: Array<U32>
  for +index: U32
  for +s: T.State
  {K.absorb(r,a,index,s) == R.absorb(r,a,index,s) : Array<U32> & T.State}

def absorb_correct(r,a,index,s):
  read0_correct(r,index,s,Array.get(U32,a,index))

law finish_correct:
  for +r: Nat
  for a: Array<U32>
  for +index: U32
  for +remain: Nat
  for +s: T.State
  {K.finish(r,a,index,remain,s) == R.finish(r,a,index,remain,s) : T.State}

def finish_correct(r,a,index,remain,s):
  pad0_correct(r,remain,index,s,Array.get(U32,a,index))

law blocks_correct:
  for +r: Nat
  for +n: Nat
  for +index: U32
  for +remain: Nat
  for pair: Array<U32> & T.State
  {K.blocks(r,n,index,remain,pair) == R.blocks(r,n,index,remain,pair) : T.State}

law blocks_step:
  for +r: Nat
  for +n: Nat
  for +index: U32
  for +remain: Nat
  for -a: Array<U32>
  for +s: T.State
  for view: Sigma<&2,&1,A.Tree,t => {a == A.thaw(t) : Array<U32>}>
  for recurse: @pair: (Array<U32> & T.State) -> {K.blocks(r,n,U32.add(index,34),remain,pair) == R.blocks(r,n,U32.add(index,34),remain,pair) : T.State}
  {K.blocks(r,1n+n,index,remain,(a,s)) == R.blocks(r,1n+n,index,remain,(a,s)) : T.State}

def blocks_step(r,n,index,remain,a,s,view,recurse):
  match view:
    case Tuple{+tree,pf}:
      %Equal.sym(Array<U32>,a,A.thaw(tree),pf) : {K.blocks(r,1n+n,index,remain,(_,s)) == R.blocks(r,1n+n,index,remain,(_,s)) : T.State}
      Equal.trans(T.State,
        K.blocks(r,n,U32.add(index,34),remain,K.absorb(r,A.thaw(tree),index,s)),
        R.blocks(r,n,U32.add(index,34),remain,K.absorb(r,A.thaw(tree),index,s)),
        R.blocks(r,n,U32.add(index,34),remain,R.absorb(r,A.thaw(tree),index,s)),
        recurse(K.absorb(r,A.thaw(tree),index,s)),
        Equal.cong(Array<U32> & T.State,T.State,pair => R.blocks(r,n,U32.add(index,34),remain,pair),
          K.absorb(r,A.thaw(tree),index,s),R.absorb(r,A.thaw(tree),index,s),absorb_correct(r,A.thaw(tree),index,s)))

def blocks_correct(r,n,index,remain,pair):
  match n pair:
    case 0n Tuple{a,s}: finish_correct(r,a,index,remain,s)
    case 1n+p Tuple{a,s}:
      blocks_step(r,p,index,remain,a,s,A.reify(a),pair => blocks_correct(r,p,U32.add(index,34),remain,pair))

law unchecked_correct:
  for +r: Nat
  for a: Array<U32>
  for +length: Nat
  {K.unchecked(r,a,length) == R.unchecked(r,a,length) : T.State}

def unchecked_correct(r,a,length):
  blocks_correct(r,Nat.div(length,136n),0,Nat.mod(length,136n),(a,P.initial()))

law digest_correct:
  for +s: T.State
  {K.digest(s) == R.digest(s) : Array<U32>}

def digest_correct(s):
  match s:
    case T.S{T.W{a0,b0},T.W{a1,b1},T.W{a2,b2},T.W{a3,b3},a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}: {==}

law checked_true_reified:
  for +r: Nat
  for -a: Array<U32>
  for +length: Nat
  for view: Sigma<&2,&1,A.Tree,t => {a == A.thaw(t) : Array<U32>}>
  {K.checked(r,True{},a,length) == R.checked(r,True{},a,length) : Maybe<&1,Array<U32>>}

def checked_true_reified(r,a,length,view):
  match view:
    case Tuple{+tree,pf}:
      %Equal.sym(Array<U32>,a,A.thaw(tree),pf) : {K.checked(r,True{},_,length) == R.checked(r,True{},_,length) : Maybe<&1,Array<U32>>}
      Equal.trans(Maybe<&1,Array<U32>>,
        Some{K.digest(K.unchecked(r,A.thaw(tree),length))},
        Some{K.digest(R.unchecked(r,A.thaw(tree),length))},
        Some{R.digest(R.unchecked(r,A.thaw(tree),length))},
        Equal.cong(T.State,Maybe<&1,Array<U32>>,s => Some{K.digest(s)},K.unchecked(r,A.thaw(tree),length),R.unchecked(r,A.thaw(tree),length),unchecked_correct(r,A.thaw(tree),length)),
        Equal.cong(Array<U32>,Maybe<&1,Array<U32>>,a => Some{a},K.digest(R.unchecked(r,A.thaw(tree),length)),R.digest(R.unchecked(r,A.thaw(tree),length)),digest_correct(R.unchecked(r,A.thaw(tree),length))))

law checked_correct:
  for +r: Nat
  for +valid: Bool
  for a: Array<U32>
  for +length: Nat
  {K.checked(r,valid,a,length) == R.checked(r,valid,a,length) : Maybe<&1,Array<U32>>}

def checked_correct(r,valid,a,length):
  match valid:
    case False{}: {==}
    case True{}: checked_true_reified(r,a,length,A.reify(a))

law sized_correct:
  for +r: Nat
  for +length: Nat
  for pair: Array<U32> & U32
  {K.sized(r,length,pair) == R.sized(r,length,pair) : Maybe<&1,Array<U32>>}

def sized_correct(r,length,pair):
  (a,capacity) = pair
  checked_correct(r,Nat.is_le(length,Nat.mul(4n,U32.to_nat(capacity))),a,length)

law hash_correct:
  for +r: Nat
  for a: Array<U32>
  for +length: Nat
  {K.keccak256_rounds(r,a,length) == R.keccak256_rounds(r,a,length) : Maybe<&1,Array<U32>>}

def hash_correct(r,a,length):
  sized_correct(r,length,Array.size(U32,a))

law ethereum_round_count:
  for a: Array<U32>
  for +length: Nat
  {K.keccak256(a,length) == K.keccak256_rounds(24n,a,length) : Maybe<&1,Array<U32>>}

def ethereum_round_count(a,length): {==}

law public_correct:
  for a: Array<U32>
  for +length: Nat
  {K.keccak256(a,length) == R.keccak256_rounds(24n,a,length) : Maybe<&1,Array<U32>>}

def public_correct(a,length): hash_correct(24n,a,length)
