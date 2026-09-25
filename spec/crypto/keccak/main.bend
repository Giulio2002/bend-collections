import Base
import ../../../src/crypto/keccak/types.bend as T
import ./permutation.bend as F

def initial() -> T.State:
  T.S{T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0}}

def low_tail(w: U32, n: Nat) -> U32:
  match n:
    case 0n: 1
    case 1n: U32.or(U32.and(w,255),256)
    case 2n: U32.or(U32.and(w,65535),65536)
    case 3n: U32.or(U32.and(w,16777215),16777216)
    case _: w

def select_tail(c: Cmp, w: U32, n: Nat) -> U32:
  match c:
    case GT{}: 0
    case EQ{}: 1
    case LT{}: low_tail(w,n)

def tail_word(w: U32, +pos: Nat, +remain: Nat) -> U32:
  select_tail(Nat.cmp(pos,remain),w,Nat.sub(remain,pos))

def last_bit(w: U32, last: Bool) -> U32:
  match last:
    case False{}: w
    case True{}: U32.or(w,2147483648)

def pad(ws: List<&2,U32>, +pos: Nat, +remain: Nat) -> List<&2,U32>:
  match ws:
    case Nil{}: Nil{}
    case w <> rest:
      last_bit(tail_word(w,pos,remain),Nat.is_eq(pos,132n)) <> pad(rest,Nat.add(pos,4n),remain)

def prepare(padding: Bool, ws: List<&2,U32>, remain: Nat) -> List<&2,U32>:
  match padding:
    case False{}: ws
    case True{}: pad(ws,0n,remain)

def inject(s: T.State, ws: List<&2,U32>) -> T.State:
  match s ws:
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> w15 <> w16 <> w17 <> w18 <> w19 <> w20 <> w21 <> w22 <> w23 <> w24 <> w25 <> w26 <> w27 <> w28 <> w29 <> w30 <> w31 <> w32 <> w33 <> Nil{}:
      T.S{F.xor(a0,T.W{w0,w1}),F.xor(a1,T.W{w2,w3}),F.xor(a2,T.W{w4,w5}),F.xor(a3,T.W{w6,w7}),F.xor(a4,T.W{w8,w9}),F.xor(a5,T.W{w10,w11}),F.xor(a6,T.W{w12,w13}),F.xor(a7,T.W{w14,w15}),F.xor(a8,T.W{w16,w17}),F.xor(a9,T.W{w18,w19}),F.xor(a10,T.W{w20,w21}),F.xor(a11,T.W{w22,w23}),F.xor(a12,T.W{w24,w25}),F.xor(a13,T.W{w26,w27}),F.xor(a14,T.W{w28,w29}),F.xor(a15,T.W{w30,w31}),F.xor(a16,T.W{w32,w33}),a17,a18,a19,a20,a21,a22,a23,a24}
    case s _: s

def gather(+round_count: Nat, n: Nat, +base: U32, +next: U32, +padding: Bool, +remain: Nat, s: T.State, acc: List<&2,U32>, pair: Array<U32> & U32) -> Array<U32> & T.State:
  match n pair:
    case 0n Tuple{a,w}:
      (a,F.rounds(round_count,0n,inject(s,prepare(padding,List.reverse(&2,U32,w <> acc),remain))))
    case 1n+p Tuple{a,w}:
      gather(round_count,p,base,U32.inc(next),padding,remain,s,w <> acc,Array.get(U32,a,U32.add(base,next)))

def absorb(+round_count: Nat, a: Array<U32>, +index: U32, s: T.State) -> Array<U32> & T.State:
  gather(round_count,33n,index,1,False{},0n,s,Nil{},Array.get(U32,a,index))

def finish(round_count: Nat, a: Array<U32>, +index: U32, remain: Nat, s: T.State) -> T.State:
  Pair.snd(Array<U32>,T.State,gather(round_count,33n,index,1,True{},remain,s,Nil{},Array.get(U32,a,index)))

def blocks(+round_count: Nat, n: Nat, +index: U32, remain: Nat, pair: Array<U32> & T.State) -> T.State:
  match n pair:
    case 0n Tuple{a,s}: finish(round_count,a,index,remain,s)
    case 1n+p Tuple{a,s}: blocks(round_count,p,U32.add(index,34),remain,absorb(round_count,a,index,s))

def unchecked(+round_count: Nat, a: Array<U32>, +length: Nat) -> T.State:
  blocks(round_count,Nat.div(length,136n),0,Nat.mod(length,136n),(a,initial()))

def digest(s: T.State) -> Array<U32>:
  match s:
    case T.S{T.W{l0,h0},T.W{l1,h1},T.W{l2,h2},T.W{l3,h3},a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}:
      ANode{ANode{ANode{ALeaf{l0},ALeaf{h0}},ANode{ALeaf{l1},ALeaf{h1}}},ANode{ANode{ALeaf{l2},ALeaf{h2}},ANode{ALeaf{l3},ALeaf{h3}}}}

def checked(round_count: Nat, valid: Bool, a: Array<U32>, length: Nat) -> Maybe<&1,Array<U32>>:
  match valid:
    case False{}: None{}
    case True{}: Some{digest(unchecked(round_count,a,length))}

def sized(round_count: Nat, +length: Nat, pair: Array<U32> & U32) -> Maybe<&1,Array<U32>>:
  (a,capacity) = pair
  checked(round_count,Nat.is_le(length,Nat.mul(4n,U32.to_nat(capacity))),a,length)

def keccak256_rounds(round_count: Nat, a: Array<U32>, length: Nat) -> Maybe<&1,Array<U32>>:
  sized(round_count,length,Array.size(U32,a))
