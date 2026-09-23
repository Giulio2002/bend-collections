import Base
import ../../../src/crypto/keccak/keccak.bend as K
import ../../../src/crypto/keccak/types.bend as T

law rejected:
  for a: Array<U32>
  for n: Nat
  {K.checked(24n,False{},a,n) == None{} : Maybe<&1,Array<U32>>}

def rejected(a,n):
  {==}

law digest_size:
  for s: T.State
  {Pair.snd(Array<U32>,U32,Array.size(U32,K.digest(s))) == 8 : U32}

def digest_size(s):
  match s:
    case T.S{T.W{a0,b0},T.W{a1,b1},T.W{a2,b2},T.W{a3,b3},a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}: {==}

def word0(s: T.State) -> U32:
  match s:
    case T.S{T.W{a0,b0},T.W{a1,b1},T.W{a2,b2},T.W{a3,b3},a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}: a0

law digest_word0:
  for +s: T.State
  {Pair.snd(Array<U32>,U32,Array.get(U32,K.digest(s),0)) == word0(s) : U32}

def digest_word0(s):
  match s:
    case T.S{T.W{a0,b0},T.W{a1,b1},T.W{a2,b2},T.W{a3,b3},a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}: {==}

def word1(s: T.State) -> U32:
  match s:
    case T.S{T.W{a0,b0},T.W{a1,b1},T.W{a2,b2},T.W{a3,b3},a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}: b0

law digest_word1:
  for +s: T.State
  {Pair.snd(Array<U32>,U32,Array.get(U32,K.digest(s),1)) == word1(s) : U32}

def digest_word1(s):
  match s:
    case T.S{T.W{a0,b0},T.W{a1,b1},T.W{a2,b2},T.W{a3,b3},a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}: {==}

def word2(s: T.State) -> U32:
  match s:
    case T.S{T.W{a0,b0},T.W{a1,b1},T.W{a2,b2},T.W{a3,b3},a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}: a1

law digest_word2:
  for +s: T.State
  {Pair.snd(Array<U32>,U32,Array.get(U32,K.digest(s),2)) == word2(s) : U32}

def digest_word2(s):
  match s:
    case T.S{T.W{a0,b0},T.W{a1,b1},T.W{a2,b2},T.W{a3,b3},a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}: {==}

def word3(s: T.State) -> U32:
  match s:
    case T.S{T.W{a0,b0},T.W{a1,b1},T.W{a2,b2},T.W{a3,b3},a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}: b1

law digest_word3:
  for +s: T.State
  {Pair.snd(Array<U32>,U32,Array.get(U32,K.digest(s),3)) == word3(s) : U32}

def digest_word3(s):
  match s:
    case T.S{T.W{a0,b0},T.W{a1,b1},T.W{a2,b2},T.W{a3,b3},a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}: {==}

def word4(s: T.State) -> U32:
  match s:
    case T.S{T.W{a0,b0},T.W{a1,b1},T.W{a2,b2},T.W{a3,b3},a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}: a2

law digest_word4:
  for +s: T.State
  {Pair.snd(Array<U32>,U32,Array.get(U32,K.digest(s),4)) == word4(s) : U32}

def digest_word4(s):
  match s:
    case T.S{T.W{a0,b0},T.W{a1,b1},T.W{a2,b2},T.W{a3,b3},a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}: {==}

def word5(s: T.State) -> U32:
  match s:
    case T.S{T.W{a0,b0},T.W{a1,b1},T.W{a2,b2},T.W{a3,b3},a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}: b2

law digest_word5:
  for +s: T.State
  {Pair.snd(Array<U32>,U32,Array.get(U32,K.digest(s),5)) == word5(s) : U32}

def digest_word5(s):
  match s:
    case T.S{T.W{a0,b0},T.W{a1,b1},T.W{a2,b2},T.W{a3,b3},a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}: {==}

def word6(s: T.State) -> U32:
  match s:
    case T.S{T.W{a0,b0},T.W{a1,b1},T.W{a2,b2},T.W{a3,b3},a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}: a3

law digest_word6:
  for +s: T.State
  {Pair.snd(Array<U32>,U32,Array.get(U32,K.digest(s),6)) == word6(s) : U32}

def digest_word6(s):
  match s:
    case T.S{T.W{a0,b0},T.W{a1,b1},T.W{a2,b2},T.W{a3,b3},a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}: {==}

def word7(s: T.State) -> U32:
  match s:
    case T.S{T.W{a0,b0},T.W{a1,b1},T.W{a2,b2},T.W{a3,b3},a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}: b3

law digest_word7:
  for +s: T.State
  {Pair.snd(Array<U32>,U32,Array.get(U32,K.digest(s),7)) == word7(s) : U32}

def digest_word7(s):
  match s:
    case T.S{T.W{a0,b0},T.W{a1,b1},T.W{a2,b2},T.W{a3,b3},a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}: {==}

law capacity_gate:
  for a: Array<U32>
  for +n: Nat
  for +capacity: U32
  for invalid: {Nat.is_le(n,Nat.mul(4n,U32.to_nat(capacity))) == False{} : Bool}
  {K.sized(24n,n,(a,capacity)) == None{} : Maybe<&1,Array<U32>>}

def capacity_gate(a,n,capacity,invalid):
  Equal.cong(Bool,Maybe<&1,Array<U32>>,b => K.checked(24n,b,a,n),
    Nat.is_le(n,Nat.mul(4n,U32.to_nat(capacity))),False{},invalid)

law suffix0:
  for w: U32
  {K.partial(w,0n) == 1 : U32}

def suffix0(w): {==}

law suffix1:
  for +w: U32
  {K.partial(w,1n) == U32.or(U32.and(w,255),256) : U32}

def suffix1(w): {==}

law suffix2:
  for +w: U32
  {K.partial(w,2n) == U32.or(U32.and(w,65535),65536) : U32}

def suffix2(w): {==}

law suffix3:
  for +w: U32
  {K.partial(w,3n) == U32.or(U32.and(w,16777215),16777216) : U32}

def suffix3(w): {==}

law whole_word:
  for +w: U32
  for n: Nat
  {K.partial(w,4n+n) == w : U32}

def whole_word(w,n): {==}

law empty_suffix:
  for w: U32
  {K.pad_word(w,0n,0n) == 1 : U32}

def empty_suffix(w): {==}

law empty_last_word:
  for w: U32
  {U32.or(K.pad_word(w,132n,0n),2147483648) == 2147483648 : U32}

def empty_last_word(w): {==}

law combined_padding:
  for +w: U32
  {U32.or(K.pad_word(w,132n,135n),2147483648) == U32.or(U32.or(U32.and(w,16777215),16777216),2147483648) : U32}

def combined_padding(w): {==}
