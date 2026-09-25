import Base
import ./core.bend as Core
import ../state.bend as S

# Packed big-endian words: four bytes per U32. Array<U32> is flat u32 storage in native C.
def at(a: Array<U32>, i: U32) -> Array<U32> & U32:
  Array.get(U32,a,i)

def partial(+w: U32, delta: Nat) -> U32:
  match delta:
    case 0n: 2147483648
    case 1n: U32.or(U32.and(w,4278190080),8388608)
    case 2n: U32.or(U32.and(w,4294901760),32768)
    case 3n: U32.or(U32.and(w,4294967040),128)
    case _: w

def pad_choose(c: Cmp, w: U32, delta: Nat) -> U32:
  match c:
    case GT{}: 0
    case EQ{}: 2147483648
    case LT{}: partial(w,delta)

def pad_word(w: U32, +pos: Nat, +remain: Nat) -> U32:
  pad_choose(Nat.cmp(pos,remain),w,Nat.sub(remain,pos))

def length_word(short: Bool, w: U32, length: U32) -> U32:
  match short:
    case True{}: length
    case False{}: w

def read16(+extra: Nat,+index: U32, s: S.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w15) = pair
  (a,Core.fips_compress16(w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,extra,s))

def read15(+extra: Nat,+index: U32, s: S.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w14) = pair
  read16(extra,U32.inc(index),s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,at(a,U32.inc(index)))

def read14(+extra: Nat,+index: U32, s: S.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w13) = pair
  read15(extra,U32.inc(index),s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,at(a,U32.inc(index)))

def read13(+extra: Nat,+index: U32, s: S.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w12) = pair
  read14(extra,U32.inc(index),s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,at(a,U32.inc(index)))

def read12(+extra: Nat,+index: U32, s: S.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w11) = pair
  read13(extra,U32.inc(index),s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,at(a,U32.inc(index)))

def read11(+extra: Nat,+index: U32, s: S.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w10) = pair
  read12(extra,U32.inc(index),s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,at(a,U32.inc(index)))

def read10(+extra: Nat,+index: U32, s: S.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w9) = pair
  read11(extra,U32.inc(index),s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,at(a,U32.inc(index)))

def read9(+extra: Nat,+index: U32, s: S.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w8) = pair
  read10(extra,U32.inc(index),s,w0,w1,w2,w3,w4,w5,w6,w7,w8,at(a,U32.inc(index)))

def read8(+extra: Nat,+index: U32, s: S.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w7) = pair
  read9(extra,U32.inc(index),s,w0,w1,w2,w3,w4,w5,w6,w7,at(a,U32.inc(index)))

def read7(+extra: Nat,+index: U32, s: S.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w6) = pair
  read8(extra,U32.inc(index),s,w0,w1,w2,w3,w4,w5,w6,at(a,U32.inc(index)))

def read6(+extra: Nat,+index: U32, s: S.State, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w5) = pair
  read7(extra,U32.inc(index),s,w0,w1,w2,w3,w4,w5,at(a,U32.inc(index)))

def read5(+extra: Nat,+index: U32, s: S.State, w0: U32, w1: U32, w2: U32, w3: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w4) = pair
  read6(extra,U32.inc(index),s,w0,w1,w2,w3,w4,at(a,U32.inc(index)))

def read4(+extra: Nat,+index: U32, s: S.State, w0: U32, w1: U32, w2: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w3) = pair
  read5(extra,U32.inc(index),s,w0,w1,w2,w3,at(a,U32.inc(index)))

def read3(+extra: Nat,+index: U32, s: S.State, w0: U32, w1: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w2) = pair
  read4(extra,U32.inc(index),s,w0,w1,w2,at(a,U32.inc(index)))

def read2(+extra: Nat,+index: U32, s: S.State, w0: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w1) = pair
  read3(extra,U32.inc(index),s,w0,w1,at(a,U32.inc(index)))

def read1(+extra: Nat,+index: U32, s: S.State, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w0) = pair
  read2(extra,U32.inc(index),s,w0,at(a,U32.inc(index)))

def pad16(+extra: Nat,+index: U32, s: S.State, +remain: Nat, +total: Nat, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w15) = pair
  (a,Core.fips_compress16(pad_word(w0,0n,remain),pad_word(w1,4n,remain),pad_word(w2,8n,remain),pad_word(w3,12n,remain),pad_word(w4,16n,remain),pad_word(w5,20n,remain),pad_word(w6,24n,remain),pad_word(w7,28n,remain),pad_word(w8,32n,remain),pad_word(w9,36n,remain),pad_word(w10,40n,remain),pad_word(w11,44n,remain),pad_word(w12,48n,remain),pad_word(w13,52n,remain),length_word(Nat.is_lt(remain,56n),pad_word(w14,56n,remain),Core.len_hi(total)),length_word(Nat.is_lt(remain,56n),pad_word(w15,60n,remain),Core.len_lo(total)),extra,s))

def pad15(+extra: Nat,+index: U32, s: S.State, +remain: Nat, +total: Nat, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w14) = pair
  pad16(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,at(a,U32.inc(index)))

def pad14(+extra: Nat,+index: U32, s: S.State, +remain: Nat, +total: Nat, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w13) = pair
  pad15(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,at(a,U32.inc(index)))

def pad13(+extra: Nat,+index: U32, s: S.State, +remain: Nat, +total: Nat, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w12) = pair
  pad14(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,at(a,U32.inc(index)))

def pad12(+extra: Nat,+index: U32, s: S.State, +remain: Nat, +total: Nat, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w11) = pair
  pad13(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,at(a,U32.inc(index)))

def pad11(+extra: Nat,+index: U32, s: S.State, +remain: Nat, +total: Nat, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w10) = pair
  pad12(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,at(a,U32.inc(index)))

def pad10(+extra: Nat,+index: U32, s: S.State, +remain: Nat, +total: Nat, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w9) = pair
  pad11(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,at(a,U32.inc(index)))

def pad9(+extra: Nat,+index: U32, s: S.State, +remain: Nat, +total: Nat, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w8) = pair
  pad10(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,at(a,U32.inc(index)))

def pad8(+extra: Nat,+index: U32, s: S.State, +remain: Nat, +total: Nat, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w7) = pair
  pad9(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,at(a,U32.inc(index)))

def pad7(+extra: Nat,+index: U32, s: S.State, +remain: Nat, +total: Nat, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w6) = pair
  pad8(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,w5,w6,at(a,U32.inc(index)))

def pad6(+extra: Nat,+index: U32, s: S.State, +remain: Nat, +total: Nat, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w5) = pair
  pad7(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,w5,at(a,U32.inc(index)))

def pad5(+extra: Nat,+index: U32, s: S.State, +remain: Nat, +total: Nat, w0: U32, w1: U32, w2: U32, w3: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w4) = pair
  pad6(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,at(a,U32.inc(index)))

def pad4(+extra: Nat,+index: U32, s: S.State, +remain: Nat, +total: Nat, w0: U32, w1: U32, w2: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w3) = pair
  pad5(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,at(a,U32.inc(index)))

def pad3(+extra: Nat,+index: U32, s: S.State, +remain: Nat, +total: Nat, w0: U32, w1: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w2) = pair
  pad4(extra,U32.inc(index),s,remain,total,w0,w1,w2,at(a,U32.inc(index)))

def pad2(+extra: Nat,+index: U32, s: S.State, +remain: Nat, +total: Nat, w0: U32, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w1) = pair
  pad3(extra,U32.inc(index),s,remain,total,w0,w1,at(a,U32.inc(index)))

def pad1(+extra: Nat,+index: U32, s: S.State, +remain: Nat, +total: Nat, pair: Array<U32> & U32) -> Array<U32> & S.State:
  (a, w0) = pair
  pad2(extra,U32.inc(index),s,remain,total,w0,at(a,U32.inc(index)))

def final_extra(+extra: Nat,more: Bool, +total: Nat, pair: Array<U32> & S.State) -> Array<U32> & S.State:
  match more pair:
    case False{} Tuple{a,s}: (a,s)
    case True{} Tuple{a,s}:
      (a,Core.fips_compress16(0,0,0,0,0,0,0,0,0,0,0,0,0,0,Core.len_hi(total),Core.len_lo(total),extra,s))

def blocks(+extra: Nat,n: Nat, +index: U32, +remain: Nat, +total: Nat, pair: Array<U32> & S.State) -> Array<U32> & S.State:
  match n pair:
    case 0n Tuple{a,s}:
      final_extra(extra,Nat.is_ge(remain,56n),total,pad1(extra,index,s,remain,total,at(a,index)))
    case 1n+p Tuple{a,s}:
      blocks(extra,p,U32.add(index,16),remain,total,read1(extra,index,s,at(a,index)))

def take_state(pair: Array<U32> & S.State) -> S.State:
  Pair.snd(Array<U32>,S.State,pair)

# Internal entry; callers must establish length <= 4*array capacity.
def hash_unchecked(a: Array<U32>, +length: Nat) -> S.State:
  take_state(blocks(48n,Nat.div(length,64n),0,Nat.mod(length,64n),length,(a,Core.initial())))

def checked(valid: Bool, a: Array<U32>, length: Nat) -> Maybe<&2,S.State>:
  match valid:
    case False{}: None{}
    case True{}: Some{hash_unchecked(a,length)}

def sized(+length: Nat, pair: Array<U32> & U32) -> Maybe<&2,S.State>:
  (a,capacity) = pair
  checked(Nat.is_le(length,Nat.mul(4n,U32.to_nat(capacity))),a,length)

# Public bounded API; consumes the input array, without constructing a byte list.
def hash(a: Array<U32>, length: Nat) -> Maybe<&2,S.State>:
  sized(length,Array.size(U32,a))
