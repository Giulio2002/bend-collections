import Base
import ./types.bend as T
import ./lane.bend as L
import ./permutation.bend as P

def mix(s: T.State,w0: U32,w1: U32,w2: U32,w3: U32,w4: U32,w5: U32,w6: U32,w7: U32,w8: U32,w9: U32,w10: U32,w11: U32,w12: U32,w13: U32,w14: U32,w15: U32,w16: U32,w17: U32,w18: U32,w19: U32,w20: U32,w21: U32,w22: U32,w23: U32,w24: U32,w25: U32,w26: U32,w27: U32,w28: U32,w29: U32,w30: U32,w31: U32,w32: U32,w33: U32) -> T.State:
  match s:
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}:
      T.S{L.xor(a0,T.W{w0,w1}),L.xor(a1,T.W{w2,w3}),L.xor(a2,T.W{w4,w5}),L.xor(a3,T.W{w6,w7}),L.xor(a4,T.W{w8,w9}),L.xor(a5,T.W{w10,w11}),L.xor(a6,T.W{w12,w13}),L.xor(a7,T.W{w14,w15}),L.xor(a8,T.W{w16,w17}),L.xor(a9,T.W{w18,w19}),L.xor(a10,T.W{w20,w21}),L.xor(a11,T.W{w22,w23}),L.xor(a12,T.W{w24,w25}),L.xor(a13,T.W{w26,w27}),L.xor(a14,T.W{w28,w29}),L.xor(a15,T.W{w30,w31}),L.xor(a16,T.W{w32,w33}),a17,a18,a19,a20,a21,a22,a23,a24}

def read33(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, w23: U32, w24: U32, w25: U32, w26: U32, w27: U32, w28: U32, w29: U32, w30: U32, w31: U32, w32: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w33) = pair
  (a,P.rounds(round_count,0n,mix(s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,w33)))

def read32(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, w23: U32, w24: U32, w25: U32, w26: U32, w27: U32, w28: U32, w29: U32, w30: U32, w31: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w32) = pair
  read33(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,Array.get(U32,a,U32.add(index,33)))

def read31(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, w23: U32, w24: U32, w25: U32, w26: U32, w27: U32, w28: U32, w29: U32, w30: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w31) = pair
  read32(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,Array.get(U32,a,U32.add(index,32)))

def read30(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, w23: U32, w24: U32, w25: U32, w26: U32, w27: U32, w28: U32, w29: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w30) = pair
  read31(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,Array.get(U32,a,U32.add(index,31)))

def read29(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, w23: U32, w24: U32, w25: U32, w26: U32, w27: U32, w28: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w29) = pair
  read30(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,Array.get(U32,a,U32.add(index,30)))

def read28(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, w23: U32, w24: U32, w25: U32, w26: U32, w27: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w28) = pair
  read29(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,Array.get(U32,a,U32.add(index,29)))

def read27(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, w23: U32, w24: U32, w25: U32, w26: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w27) = pair
  read28(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,Array.get(U32,a,U32.add(index,28)))

def read26(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, w23: U32, w24: U32, w25: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w26) = pair
  read27(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,Array.get(U32,a,U32.add(index,27)))

def read25(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, w23: U32, w24: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w25) = pair
  read26(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,Array.get(U32,a,U32.add(index,26)))

def read24(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, w23: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w24) = pair
  read25(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,Array.get(U32,a,U32.add(index,25)))

def read23(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w23) = pair
  read24(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,Array.get(U32,a,U32.add(index,24)))

def read22(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w22) = pair
  read23(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,Array.get(U32,a,U32.add(index,23)))

def read21(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w21) = pair
  read22(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,Array.get(U32,a,U32.add(index,22)))

def read20(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w20) = pair
  read21(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,Array.get(U32,a,U32.add(index,21)))

def read19(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w19) = pair
  read20(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,Array.get(U32,a,U32.add(index,20)))

def read18(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w18) = pair
  read19(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,Array.get(U32,a,U32.add(index,19)))

def read17(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w17) = pair
  read18(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,Array.get(U32,a,U32.add(index,18)))

def read16(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w16) = pair
  read17(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,Array.get(U32,a,U32.add(index,17)))

def read15(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w15) = pair
  read16(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,Array.get(U32,a,U32.add(index,16)))

def read14(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w14) = pair
  read15(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,Array.get(U32,a,U32.add(index,15)))

def read13(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w13) = pair
  read14(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,Array.get(U32,a,U32.add(index,14)))

def read12(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w12) = pair
  read13(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,Array.get(U32,a,U32.add(index,13)))

def read11(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w11) = pair
  read12(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,Array.get(U32,a,U32.add(index,12)))

def read10(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w10) = pair
  read11(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,Array.get(U32,a,U32.add(index,11)))

def read9(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w9) = pair
  read10(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,Array.get(U32,a,U32.add(index,10)))

def read8(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w8) = pair
  read9(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,Array.get(U32,a,U32.add(index,9)))

def read7(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w7) = pair
  read8(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,w7,Array.get(U32,a,U32.add(index,8)))

def read6(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w6) = pair
  read7(round_count,index,s,w0,w1,w2,w3,w4,w5,w6,Array.get(U32,a,U32.add(index,7)))

def read5(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w5) = pair
  read6(round_count,index,s,w0,w1,w2,w3,w4,w5,Array.get(U32,a,U32.add(index,6)))

def read4(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w4) = pair
  read5(round_count,index,s,w0,w1,w2,w3,w4,Array.get(U32,a,U32.add(index,5)))

def read3(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, w2: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w3) = pair
  read4(round_count,index,s,w0,w1,w2,w3,Array.get(U32,a,U32.add(index,4)))

def read2(+round_count: Nat,+index: U32, s: T.State, w0: U32, w1: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w2) = pair
  read3(round_count,index,s,w0,w1,w2,Array.get(U32,a,U32.add(index,3)))

def read1(+round_count: Nat,+index: U32, s: T.State, w0: U32, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w1) = pair
  read2(round_count,index,s,w0,w1,Array.get(U32,a,U32.add(index,2)))

def read0(+round_count: Nat,+index: U32, s: T.State, pair: Array<U32> & U32) -> Array<U32> & T.State:
  (a,w0) = pair
  read1(round_count,index,s,w0,Array.get(U32,a,U32.add(index,1)))

def absorb(+round_count: Nat,a: Array<U32>, +index: U32, s: T.State) -> Array<U32> & T.State:
  read0(round_count,index,s,Array.get(U32,a,index))

# Little-endian Keccak pad10*1, domain suffix 0x01.
def partial(w: U32, delta: Nat) -> U32:
  match delta:
    case 0n: 1
    case 1n: U32.or(U32.and(w,255),256)
    case 2n: U32.or(U32.and(w,65535),65536)
    case 3n: U32.or(U32.and(w,16777215),16777216)
    case _: w

def pad_choose(c: Cmp, w: U32, delta: Nat) -> U32:
  match c:
    case GT{}: 0
    case EQ{}: 1
    case LT{}: partial(w,delta)

def pad_word(w: U32, +pos: Nat, +remain: Nat) -> U32:
  pad_choose(Nat.cmp(pos,remain),w,Nat.sub(remain,pos))

def pad33(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, w23: U32, w24: U32, w25: U32, w26: U32, w27: U32, w28: U32, w29: U32, w30: U32, w31: U32, w32: U32, pair: Array<U32> & U32) -> T.State:
  (a,w33) = pair
  P.rounds(round_count,0n,mix(s,pad_word(w0,0n,remain),pad_word(w1,4n,remain),pad_word(w2,8n,remain),pad_word(w3,12n,remain),pad_word(w4,16n,remain),pad_word(w5,20n,remain),pad_word(w6,24n,remain),pad_word(w7,28n,remain),pad_word(w8,32n,remain),pad_word(w9,36n,remain),pad_word(w10,40n,remain),pad_word(w11,44n,remain),pad_word(w12,48n,remain),pad_word(w13,52n,remain),pad_word(w14,56n,remain),pad_word(w15,60n,remain),pad_word(w16,64n,remain),pad_word(w17,68n,remain),pad_word(w18,72n,remain),pad_word(w19,76n,remain),pad_word(w20,80n,remain),pad_word(w21,84n,remain),pad_word(w22,88n,remain),pad_word(w23,92n,remain),pad_word(w24,96n,remain),pad_word(w25,100n,remain),pad_word(w26,104n,remain),pad_word(w27,108n,remain),pad_word(w28,112n,remain),pad_word(w29,116n,remain),pad_word(w30,120n,remain),pad_word(w31,124n,remain),pad_word(w32,128n,remain),U32.or(pad_word(w33,132n,remain),2147483648)))

def pad32(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, w23: U32, w24: U32, w25: U32, w26: U32, w27: U32, w28: U32, w29: U32, w30: U32, w31: U32, pair: Array<U32> & U32) -> T.State:
  (a,w32) = pair
  pad33(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,w32,Array.get(U32,a,U32.add(index,33)))

def pad31(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, w23: U32, w24: U32, w25: U32, w26: U32, w27: U32, w28: U32, w29: U32, w30: U32, pair: Array<U32> & U32) -> T.State:
  (a,w31) = pair
  pad32(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31,Array.get(U32,a,U32.add(index,32)))

def pad30(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, w23: U32, w24: U32, w25: U32, w26: U32, w27: U32, w28: U32, w29: U32, pair: Array<U32> & U32) -> T.State:
  (a,w30) = pair
  pad31(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,Array.get(U32,a,U32.add(index,31)))

def pad29(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, w23: U32, w24: U32, w25: U32, w26: U32, w27: U32, w28: U32, pair: Array<U32> & U32) -> T.State:
  (a,w29) = pair
  pad30(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,Array.get(U32,a,U32.add(index,30)))

def pad28(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, w23: U32, w24: U32, w25: U32, w26: U32, w27: U32, pair: Array<U32> & U32) -> T.State:
  (a,w28) = pair
  pad29(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,Array.get(U32,a,U32.add(index,29)))

def pad27(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, w23: U32, w24: U32, w25: U32, w26: U32, pair: Array<U32> & U32) -> T.State:
  (a,w27) = pair
  pad28(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,Array.get(U32,a,U32.add(index,28)))

def pad26(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, w23: U32, w24: U32, w25: U32, pair: Array<U32> & U32) -> T.State:
  (a,w26) = pair
  pad27(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,Array.get(U32,a,U32.add(index,27)))

def pad25(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, w23: U32, w24: U32, pair: Array<U32> & U32) -> T.State:
  (a,w25) = pair
  pad26(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,Array.get(U32,a,U32.add(index,26)))

def pad24(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, w23: U32, pair: Array<U32> & U32) -> T.State:
  (a,w24) = pair
  pad25(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,Array.get(U32,a,U32.add(index,25)))

def pad23(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, w22: U32, pair: Array<U32> & U32) -> T.State:
  (a,w23) = pair
  pad24(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,Array.get(U32,a,U32.add(index,24)))

def pad22(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, w21: U32, pair: Array<U32> & U32) -> T.State:
  (a,w22) = pair
  pad23(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,Array.get(U32,a,U32.add(index,23)))

def pad21(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, w20: U32, pair: Array<U32> & U32) -> T.State:
  (a,w21) = pair
  pad22(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,Array.get(U32,a,U32.add(index,22)))

def pad20(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, w19: U32, pair: Array<U32> & U32) -> T.State:
  (a,w20) = pair
  pad21(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,Array.get(U32,a,U32.add(index,21)))

def pad19(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, w18: U32, pair: Array<U32> & U32) -> T.State:
  (a,w19) = pair
  pad20(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,Array.get(U32,a,U32.add(index,20)))

def pad18(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, w17: U32, pair: Array<U32> & U32) -> T.State:
  (a,w18) = pair
  pad19(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,Array.get(U32,a,U32.add(index,19)))

def pad17(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, w16: U32, pair: Array<U32> & U32) -> T.State:
  (a,w17) = pair
  pad18(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,Array.get(U32,a,U32.add(index,18)))

def pad16(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, pair: Array<U32> & U32) -> T.State:
  (a,w16) = pair
  pad17(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,Array.get(U32,a,U32.add(index,17)))

def pad15(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, pair: Array<U32> & U32) -> T.State:
  (a,w15) = pair
  pad16(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,Array.get(U32,a,U32.add(index,16)))

def pad14(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, pair: Array<U32> & U32) -> T.State:
  (a,w14) = pair
  pad15(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,Array.get(U32,a,U32.add(index,15)))

def pad13(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, pair: Array<U32> & U32) -> T.State:
  (a,w13) = pair
  pad14(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,Array.get(U32,a,U32.add(index,14)))

def pad12(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, pair: Array<U32> & U32) -> T.State:
  (a,w12) = pair
  pad13(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,Array.get(U32,a,U32.add(index,13)))

def pad11(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, pair: Array<U32> & U32) -> T.State:
  (a,w11) = pair
  pad12(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,Array.get(U32,a,U32.add(index,12)))

def pad10(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, pair: Array<U32> & U32) -> T.State:
  (a,w10) = pair
  pad11(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,Array.get(U32,a,U32.add(index,11)))

def pad9(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, pair: Array<U32> & U32) -> T.State:
  (a,w9) = pair
  pad10(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,Array.get(U32,a,U32.add(index,10)))

def pad8(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, pair: Array<U32> & U32) -> T.State:
  (a,w8) = pair
  pad9(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,Array.get(U32,a,U32.add(index,9)))

def pad7(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, pair: Array<U32> & U32) -> T.State:
  (a,w7) = pair
  pad8(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,w7,Array.get(U32,a,U32.add(index,8)))

def pad6(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, pair: Array<U32> & U32) -> T.State:
  (a,w6) = pair
  pad7(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,w6,Array.get(U32,a,U32.add(index,7)))

def pad5(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, pair: Array<U32> & U32) -> T.State:
  (a,w5) = pair
  pad6(round_count,remain,index,s,w0,w1,w2,w3,w4,w5,Array.get(U32,a,U32.add(index,6)))

def pad4(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, w3: U32, pair: Array<U32> & U32) -> T.State:
  (a,w4) = pair
  pad5(round_count,remain,index,s,w0,w1,w2,w3,w4,Array.get(U32,a,U32.add(index,5)))

def pad3(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, w2: U32, pair: Array<U32> & U32) -> T.State:
  (a,w3) = pair
  pad4(round_count,remain,index,s,w0,w1,w2,w3,Array.get(U32,a,U32.add(index,4)))

def pad2(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, w1: U32, pair: Array<U32> & U32) -> T.State:
  (a,w2) = pair
  pad3(round_count,remain,index,s,w0,w1,w2,Array.get(U32,a,U32.add(index,3)))

def pad1(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, w0: U32, pair: Array<U32> & U32) -> T.State:
  (a,w1) = pair
  pad2(round_count,remain,index,s,w0,w1,Array.get(U32,a,U32.add(index,2)))

def pad0(+round_count: Nat,+remain: Nat, +index: U32, s: T.State, pair: Array<U32> & U32) -> T.State:
  (a,w0) = pair
  pad1(round_count,remain,index,s,w0,Array.get(U32,a,U32.add(index,1)))

def finish(+round_count: Nat,a: Array<U32>, +index: U32, remain: Nat, s: T.State) -> T.State:
  pad0(round_count,remain,index,s,Array.get(U32,a,index))

def blocks(+round_count: Nat,n: Nat, +index: U32, remain: Nat, pair: Array<U32> & T.State) -> T.State:
  match n pair:
    case 0n Tuple{a,s}: finish(round_count,a,index,remain,s)
    case 1n+p Tuple{a,s}: blocks(round_count,p,U32.add(index,34),remain,absorb(round_count,a,index,s))

def unchecked(+round_count: Nat,a: Array<U32>, +length: Nat) -> T.State:
  blocks(round_count,Nat.div(length,136n),0,Nat.mod(length,136n),(a,P.initial()))

def digest(s: T.State) -> Array<U32>:
  match s:
    case T.S{T.W{l0,h0},T.W{l1,h1},T.W{l2,h2},T.W{l3,h3},a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}:
      a = Array.new(U32,3n,0)
      a = Array.set(U32,a,0,l0)
      a = Array.set(U32,a,1,h0)
      a = Array.set(U32,a,2,l1)
      a = Array.set(U32,a,3,h1)
      a = Array.set(U32,a,4,l2)
      a = Array.set(U32,a,5,h2)
      a = Array.set(U32,a,6,l3)
      a = Array.set(U32,a,7,h3)
      a

def checked(+round_count: Nat,valid: Bool, a: Array<U32>, length: Nat) -> Maybe<&1,Array<U32>>:
  match valid:
    case False{}: None{}
    case True{}: Some{digest(unchecked(round_count,a,length))}

def sized(+round_count: Nat,+length: Nat, pair: Array<U32> & U32) -> Maybe<&1,Array<U32>>:
  (a,capacity) = pair
  checked(round_count,Nat.is_le(length,Nat.mul(4n,U32.to_nat(capacity))),a,length)

def keccak256_rounds(+round_count: Nat,a: Array<U32>, length: Nat) -> Maybe<&1,Array<U32>>:
  sized(round_count,length,Array.size(U32,a))


def keccak256(a: Array<U32>, length: Nat) -> Maybe<&1,Array<U32>>:
  keccak256_rounds(24n,a,length)
