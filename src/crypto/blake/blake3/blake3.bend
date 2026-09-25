import Base
import ./types.bend as T
import ./compress.bend as C

# BLAKE3 hash mode, 32-byte output.
#
# blake3(words, byte_length): the message is packed little-endian, four bytes
# per U32 word, and byte_length is its logical length. The result is None when
# byte_length exceeds 4 * the array's capacity, else the 32-byte digest as
# eight little-endian U32 words. Bytes past byte_length in the last word do not
# influence the result.
#
# The message is split into 1024-byte chunks (the last one holds the remaining
# 1..1024 bytes, or 0 for the empty message). Every chunk but the last is
# compressed to its chaining value as soon as it is read and pushed on a stack
# of subtree chaining values, merged like a binary counter: a slot holds the
# chaining value of a complete subtree of 2^i chunks, and pushing into a full
# slot merges both into a parent node carried to the next slot. The last chunk
# stays pending; at the end the stack is folded into it from the smallest
# subtree up, and the resulting root node is compressed with ROOT.

def iv() -> T.CV:
  T.CV{1779033703,3144134277,1013904242,2773480762,1359893119,2600822924,528734635,1541459225}

# GENERATED BEGIN (tools/generators/blake3/gen.py)
# Reads the 16 words of a block at word `index`, threading the array.
def read15(+index: U32, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, pair: Array<U32> & U32) -> Array<U32> & T.Block:
  (a,w15) = pair
  (a,T.B{w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15})

def read14(+index: U32, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, pair: Array<U32> & U32) -> Array<U32> & T.Block:
  (a,w14) = pair
  read15(index,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,Array.get(U32,a,U32.add(index,15)))

def read13(+index: U32, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, pair: Array<U32> & U32) -> Array<U32> & T.Block:
  (a,w13) = pair
  read14(index,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,Array.get(U32,a,U32.add(index,14)))

def read12(+index: U32, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, pair: Array<U32> & U32) -> Array<U32> & T.Block:
  (a,w12) = pair
  read13(index,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,Array.get(U32,a,U32.add(index,13)))

def read11(+index: U32, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, pair: Array<U32> & U32) -> Array<U32> & T.Block:
  (a,w11) = pair
  read12(index,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,Array.get(U32,a,U32.add(index,12)))

def read10(+index: U32, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, pair: Array<U32> & U32) -> Array<U32> & T.Block:
  (a,w10) = pair
  read11(index,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,Array.get(U32,a,U32.add(index,11)))

def read9(+index: U32, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, pair: Array<U32> & U32) -> Array<U32> & T.Block:
  (a,w9) = pair
  read10(index,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,Array.get(U32,a,U32.add(index,10)))

def read8(+index: U32, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, pair: Array<U32> & U32) -> Array<U32> & T.Block:
  (a,w8) = pair
  read9(index,w0,w1,w2,w3,w4,w5,w6,w7,w8,Array.get(U32,a,U32.add(index,9)))

def read7(+index: U32, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, pair: Array<U32> & U32) -> Array<U32> & T.Block:
  (a,w7) = pair
  read8(index,w0,w1,w2,w3,w4,w5,w6,w7,Array.get(U32,a,U32.add(index,8)))

def read6(+index: U32, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, pair: Array<U32> & U32) -> Array<U32> & T.Block:
  (a,w6) = pair
  read7(index,w0,w1,w2,w3,w4,w5,w6,Array.get(U32,a,U32.add(index,7)))

def read5(+index: U32, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, pair: Array<U32> & U32) -> Array<U32> & T.Block:
  (a,w5) = pair
  read6(index,w0,w1,w2,w3,w4,w5,Array.get(U32,a,U32.add(index,6)))

def read4(+index: U32, w0: U32, w1: U32, w2: U32, w3: U32, pair: Array<U32> & U32) -> Array<U32> & T.Block:
  (a,w4) = pair
  read5(index,w0,w1,w2,w3,w4,Array.get(U32,a,U32.add(index,5)))

def read3(+index: U32, w0: U32, w1: U32, w2: U32, pair: Array<U32> & U32) -> Array<U32> & T.Block:
  (a,w3) = pair
  read4(index,w0,w1,w2,w3,Array.get(U32,a,U32.add(index,4)))

def read2(+index: U32, w0: U32, w1: U32, pair: Array<U32> & U32) -> Array<U32> & T.Block:
  (a,w2) = pair
  read3(index,w0,w1,w2,Array.get(U32,a,U32.add(index,3)))

def read1(+index: U32, w0: U32, pair: Array<U32> & U32) -> Array<U32> & T.Block:
  (a,w1) = pair
  read2(index,w0,w1,Array.get(U32,a,U32.add(index,2)))

def read0(+index: U32, pair: Array<U32> & U32) -> Array<U32> & T.Block:
  (a,w0) = pair
  read1(index,w0,Array.get(U32,a,U32.add(index,1)))

def read_block(a: Array<U32>, +index: U32) -> Array<U32> & T.Block:
  read0(index,Array.get(U32,a,index))
# GENERATED END

# The block truncated to its first `len` bytes: the word at byte offset pos
# keeps its low len - pos bytes (all four when at least four remain).
def partial(w: U32, delta: Nat) -> U32:
  match delta:
    case 0n: 0
    case 1n: U32.and(w,255)
    case 2n: U32.and(w,65535)
    case 3n: U32.and(w,16777215)
    case 4n+q: w

def mask(w: U32, +pos: Nat, +len: Nat) -> U32:
  partial(w,Nat.sub(len,pos))

def mask_block(b: T.Block, +len: Nat) -> T.Block:
  match b:
    case T.B{m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15}:
      T.B{mask(m0,0n,len),mask(m1,4n,len),mask(m2,8n,len),mask(m3,12n,len),mask(m4,16n,len),mask(m5,20n,len),mask(m6,24n,len),mask(m7,28n,len),mask(m8,32n,len),mask(m9,36n,len),mask(m10,40n,len),mask(m11,44n,len),mask(m12,48n,len),mask(m13,52n,len),mask(m14,56n,len),mask(m15,60n,len)}

# A chunk that is not the last: n more full blocks after the current one, the
# current block in `pair`; flags is CHUNK_START on the first block and 0 after.
# Returns the chunk's chaining value.
def full_go(n: Nat, +counter: U32, +index: U32, +flags: U32, cv: T.CV, pair: Array<U32> & T.Block) -> Array<U32> & T.CV:
  match n pair:
    case 0n Tuple{a,b}: (a,C.compress(cv,b,counter,64,U32.or(flags,2)))
    case 1n+p Tuple{a,b}: full_go(p,counter,U32.add(index,16),0,C.compress(cv,b,counter,64,flags),read_block(a,U32.add(index,16)))

def full_chunk(a: Array<U32>, +counter: U32, +index: U32) -> Array<U32> & T.CV:
  full_go(15n,counter,index,1,iv(),read_block(a,index))

# The last chunk: n full blocks before its last block of len bytes (1..64, or
# 0 for the empty message). Returns the pending output of the last block.
def last_go(n: Nat, +counter: U32, +index: U32, +flags: U32, +len: Nat, cv: T.CV, pair: Array<U32> & T.Block) -> Array<U32> & T.Out:
  match n pair:
    case 0n Tuple{a,b}: (a,T.Out{cv,mask_block(b,len),counter,U32.from_nat(len),U32.or(flags,2)})
    case 1n+p Tuple{a,b}: last_go(p,counter,U32.add(index,16),0,len,C.compress(cv,b,counter,64,flags),read_block(a,U32.add(index,16)))

def last_chunk(a: Array<U32>, +counter: U32, +index: U32, +len: Nat) -> Array<U32> & T.Out:
  +n = Nat.div(Nat.sub(len,1n),64n)
  last_go(n,counter,index,1,Nat.sub(len,Nat.mul(n,64n)),iv(),read_block(a,index))

def out_cv(o: T.Out) -> T.CV:
  match o:
    case T.Out{cv,b,t,len,flags}: C.compress(cv,b,t,len,flags)

def root_cv(o: T.Out) -> T.CV:
  match o:
    case T.Out{cv,b,t,len,flags}: C.compress(cv,b,t,len,U32.or(flags,8))

def parent_block(l: T.CV, r: T.CV) -> T.Block:
  match l r:
    case T.CV{l0,l1,l2,l3,l4,l5,l6,l7} T.CV{r0,r1,r2,r3,r4,r5,r6,r7}:
      T.B{l0,l1,l2,l3,l4,l5,l6,l7,r0,r1,r2,r3,r4,r5,r6,r7}

def parent_out(l: T.CV, r: T.CV) -> T.Out:
  T.Out{iv(),parent_block(l,r),0,64,4}

def parent_cv(l: T.CV, r: T.CV) -> T.CV:
  C.compress(iv(),parent_block(l,r),0,64,4)

# The subtree stack, smallest subtree first: slot i is empty or holds the
# chaining value of a complete subtree of 2^i chunks.
type Stack is Data:
  StkNil{}
  SEmpty{rest: Stack}
  SFull{cv: T.CV, rest: Stack}

def push(s: Stack, c: T.CV) -> Stack:
  match s:
    case StkNil{}: SFull{c,StkNil{}}
    case SEmpty{r}: SFull{c,r}
    case SFull{d,r}: SEmpty{push(r,parent_cv(d,c))}

# Folds the stack into the pending output of the rightmost subtree.
def finish(s: Stack, o: T.Out) -> T.Out:
  match s:
    case StkNil{}: o
    case SEmpty{r}: finish(r,o)
    case SFull{d,r}: finish(r,parent_out(d,out_cv(o)))

def pushed(s: Stack, pair: Array<U32> & T.CV) -> Array<U32> & Stack:
  (a,c) = pair
  (a,push(s,c))

# n chunks before the last; len is the byte length of the last chunk.
def chunks(n: Nat, +counter: U32, +index: U32, +len: Nat, pair: Array<U32> & Stack) -> T.Out:
  match n pair:
    case 0n Tuple{a,s}: finish(s,Pair.snd(Array<U32>,T.Out,last_chunk(a,counter,index,len)))
    case 1n+p Tuple{a,s}: chunks(p,U32.inc(counter),U32.add(index,256),len,pushed(s,full_chunk(a,counter,index)))

def unchecked(a: Array<U32>, +length: Nat) -> T.CV:
  +n = Nat.div(Nat.sub(length,1n),1024n)
  root_cv(chunks(n,0,0,Nat.sub(length,Nat.mul(n,1024n)),(a,StkNil{})))

def digest(c: T.CV) -> Array<U32>:
  match c:
    case T.CV{h0,h1,h2,h3,h4,h5,h6,h7}:
      a = Array.new(U32,3n,0)
      a = Array.set(U32,a,0,h0)
      a = Array.set(U32,a,1,h1)
      a = Array.set(U32,a,2,h2)
      a = Array.set(U32,a,3,h3)
      a = Array.set(U32,a,4,h4)
      a = Array.set(U32,a,5,h5)
      a = Array.set(U32,a,6,h6)
      a = Array.set(U32,a,7,h7)
      a

def checked(valid: Bool, a: Array<U32>, +length: Nat) -> Maybe<&1,Array<U32>>:
  match valid:
    case False{}: None{}
    case True{}: Some{digest(unchecked(a,length))}

def sized(+length: Nat, pair: Array<U32> & U32) -> Maybe<&1,Array<U32>>:
  (a,capacity) = pair
  checked(Nat.is_le(length,Nat.mul(4n,U32.to_nat(capacity))),a,length)

def blake3(words: Array<U32>, byte_length: Nat) -> Maybe<&1,Array<U32>>:
  sized(byte_length,Array.size(U32,words))
