import Base
import ../sha.bend as F
import ../../../src/crypto/sha/state.bend as S

# Packed-format reference: logical input byte j is the big-endian byte j%4
# of array word floor(j/4). Only the declared prefix is part of the message.
# Block collection uses a generic list reader, not the optimized 16-read chain.
def len_hi(+n: Nat) -> U32:
  +d0 = Nat.div(n, 32n)
  +d1 = Nat.div(d0, 256n)
  +d2 = Nat.div(d1, 256n)
  +d3 = Nat.div(d2, 256n)
  +d4 = Nat.div(d3, 256n)
  +d5 = Nat.div(d4, 256n)
  +d6 = Nat.div(d5, 256n)
  F.decode(U32.from_nat(Nat.mod(d6, 256n)), U32.from_nat(Nat.mod(d5, 256n)),
    U32.from_nat(Nat.mod(d4, 256n)), U32.from_nat(Nat.mod(d3, 256n)))

def len_lo(+n: Nat) -> U32:
  +d0 = Nat.div(n, 32n)
  +d1 = Nat.div(d0, 256n)
  +d2 = Nat.div(d1, 256n)
  F.decode(U32.from_nat(Nat.mod(d2, 256n)), U32.from_nat(Nat.mod(d1, 256n)),
    U32.from_nat(Nat.mod(d0, 256n)), U32.shln(U32.from_nat(Nat.mod(n, 32n)), 3n))

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


def padded_word(+position: Nat, w: U32, +remain: Nat, total: Nat) -> U32:
  match position:
    case 56n: length_word(Nat.is_lt(remain,56n),pad_word(w,56n,remain),len_hi(total))
    case 60n: length_word(Nat.is_lt(remain,56n),pad_word(w,60n,remain),len_lo(total))
    case _: pad_word(w,position,remain)

def padded_words(ws: List<&2,U32>, +position: Nat, +remain: Nat, +total: Nat) -> List<&2,U32>:
  match ws:
    case Nil{}: Nil{}
    case w <> tail:
      padded_word(position,w,remain,total) <> padded_words(tail,Nat.add(position,4n),remain,total)

def prepare(padding: Bool, ws: List<&2,U32>, remain: Nat, total: Nat) -> List<&2,U32>:
  match padding:
    case False{}: ws
    case True{}: padded_words(ws,0n,remain,total)

def compress(ws: List<&2,U32>, extra: Nat, s: S.State) -> S.State:
  F.compress(F.schedule(extra,ws),F.constants(),s)

def gather(+extra: Nat,n: Nat, +index: U32, +padding: Bool, +remain: Nat, +total: Nat,
    s: S.State, acc: List<&2,U32>, pair: Array<U32> & U32) -> Array<U32> & S.State:
  match n pair:
    case 0n Tuple{a,w}:
      (a,compress(prepare(padding,List.reverse(&2,U32,w <> acc),remain,total),extra,s))
    case 1n+p Tuple{a,w}:
      gather(extra,p,U32.inc(index),padding,remain,total,s,w <> acc,Array.get(U32,a,U32.inc(index)))

def final_extra(+extra: Nat,more: Bool, +total: Nat, pair: Array<U32> & S.State) -> Array<U32> & S.State:
  match more pair:
    case False{} Tuple{a,s}: (a,s)
    case True{} Tuple{a,s}:
      (a,compress([0,0,0,0,0,0,0,0,0,0,0,0,0,0,len_hi(total),len_lo(total)],extra,s))

def blocks(+extra: Nat,n: Nat, +index: U32, +remain: Nat, +total: Nat, pair: Array<U32> & S.State) -> Array<U32> & S.State:
  match n pair:
    case 0n Tuple{a,s}:
      final_extra(extra,Nat.is_ge(remain,56n),total,gather(extra,15n,index,True{},remain,total,s,Nil{},Array.get(U32,a,index)))
    case 1n+p Tuple{a,s}:
      blocks(extra,p,U32.add(index,16),remain,total,gather(extra,15n,index,False{},0n,0n,s,Nil{},Array.get(U32,a,index)))

def take_state(pair: Array<U32> & S.State) -> S.State:
  Pair.snd(Array<U32>,S.State,pair)

def hash_unchecked(a: Array<U32>, +length: Nat) -> S.State:
  take_state(blocks(48n,Nat.div(length,64n),0,Nat.mod(length,64n),length,(a,F.initial())))

def checked(valid: Bool, a: Array<U32>, length: Nat) -> Maybe<&2,S.State>:
  match valid:
    case False{}: None{}
    case True{}: Some{hash_unchecked(a,length)}

def sized(+length: Nat, pair: Array<U32> & U32) -> Maybe<&2,S.State>:
  (a,capacity) = pair
  checked(Nat.is_le(length,Nat.mul(4n,U32.to_nat(capacity))),a,length)

def hash(a: Array<U32>, length: Nat) -> Maybe<&2,S.State>:
  sized(length,Array.size(U32,a))

def digest_result(r: Maybe<&2,S.State>) -> Maybe<&2,List<&2,U32>>:
  match r:
    case None{}: None{}
    case Some{s}: Some{F.digest(s)}

def sha256(a: Array<U32>, length: Nat) -> Maybe<&2,List<&2,U32>>:
  digest_result(hash(a,length))
