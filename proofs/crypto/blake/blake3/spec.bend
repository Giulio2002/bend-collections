import Base
import ../../../../src/crypto/blake/blake3/types.bend as T
import ../../../lib/spec_common.bend as SC

# BLAKE3 in hash mode with a 32-byte output, written from the BLAKE3
# specification document (O'Connor, Aumasson, Neves, Wilcox-O'Hearn, 2020):
# section 2.2 (the compression function), 2.3 (modes: hash mode keys with IV),
# 2.4 (chunks), 2.5 (the tree) and 2.6 (the root and its output).
#
# This file is independent of the implementation in src/crypto/blake/blake3/:
# it shares only the plain record types CV, Block and Out and never calls the
# implementation. It favours the document's structure over speed: the state
# and the message are lists indexed by position, the message schedule comes
# from repeatedly applying the permutation table, and the tree is defined
# recursively by its shape rather than by the implementation's stack.
#
# Input convention: the message is an array of U32 words holding its bytes
# little-endian, four per word (byte 4i+j is bits 8j..8j+7 of word i);
# byte_length is the logical length. A 64-byte block is therefore sixteen
# consecutive words, and a block of len < 64 bytes is zero past its len bytes.

# ---- constants (2.2, 2.3) ----

def iv() -> List<&2,U32>:
  [1779033703,3144134277,1013904242,2773480762,1359893119,2600822924,528734635,1541459225]

def msg_permutation() -> List<&2,Nat>:
  [2n,6n,3n,10n,7n,0n,4n,13n,1n,11n,12n,5n,9n,14n,15n,8n]

def chunk_start() -> U32:
  1

def chunk_end() -> U32:
  2

def parent_flag() -> U32:
  4

def root_flag() -> U32:
  8

# ---- word lists ----

def at(xs: List<&2,U32>, i: Nat) -> U32:
  match xs i:
    case Nil{} _: 0
    case Con{x,r} 0n: x
    case Con{x,r} 1n+j: at(r,j)

def put(xs: List<&2,U32>, i: Nat, +v: U32) -> List<&2,U32>:
  match xs i:
    case Nil{} _: Nil{}
    case Con{x,r} 0n: Con{v,r}
    case Con{x,r} 1n+j: Con{x,put(r,j,v)}

def cv_words(c: T.CV) -> List<&2,U32>:
  match c:
    case T.CV{h0,h1,h2,h3,h4,h5,h6,h7}: [h0,h1,h2,h3,h4,h5,h6,h7]

# (Each list consumer below starts by matching its list, so that it stays an
# unevaluated call on a symbolic list; the Nil cases agree with the general
# formula, since at(Nil, i) = 0 and put(Nil, i, x) = Nil.)
def cv_of(+ws: List<&2,U32>) -> T.CV:
  match ws:
    case Nil{}: T.CV{0,0,0,0,0,0,0,0}
    case Con{+x,+r}:
      +l = {Con{x,r} : List<&2,U32>}
      T.CV{at(l,0n),at(l,1n),at(l,2n),at(l,3n),at(l,4n),at(l,5n),at(l,6n),at(l,7n)}

def block_of(+ws: List<&2,U32>) -> T.Block:
  match ws:
    case Nil{}: T.B{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0}
    case Con{+x,+r}:
      +l = {Con{x,r} : List<&2,U32>}
      T.B{at(l,0n),at(l,1n),at(l,2n),at(l,3n),at(l,4n),at(l,5n),at(l,6n),at(l,7n),at(l,8n),at(l,9n),at(l,10n),at(l,11n),at(l,12n),at(l,13n),at(l,14n),at(l,15n)}

# ---- the compression function (2.2) ----

# Right rotation by n bits, 0 < n < 32.
def rotr(+x: U32, +n: Nat) -> U32:
  U32.or(U32.shrn(x,n),U32.shln(x,Nat.sub(32n,n)))

# The quarter-round G on state positions a, b, c, d with message words mx, my.
def g(+v: List<&2,U32>, +a: Nat, +b: Nat, +c: Nat, +d: Nat, +mx: U32, +my: U32) -> List<&2,U32>:
  +va = U32.add(U32.add(at(v,a),at(v,b)),mx)
  +vd = rotr(U32.xor(at(v,d),va),16n)
  +vc = U32.add(at(v,c),vd)
  +vb = rotr(U32.xor(at(v,b),vc),12n)
  +va2 = U32.add(U32.add(va,vb),my)
  +vd2 = rotr(U32.xor(vd,va2),8n)
  +vc2 = U32.add(vc,vd2)
  +vb2 = rotr(U32.xor(vb,vc2),7n)
  put(put(put(put(v,a,va2),b,vb2),c,vc2),d,vd2)

# A round mixes the columns, then the diagonals, of the 4x4 state.
def columns(+v: List<&2,U32>, +m: List<&2,U32>) -> List<&2,U32>:
  +v1 = g(v,0n,4n,8n,12n,at(m,0n),at(m,1n))
  +v2 = g(v1,1n,5n,9n,13n,at(m,2n),at(m,3n))
  +v3 = g(v2,2n,6n,10n,14n,at(m,4n),at(m,5n))
  g(v3,3n,7n,11n,15n,at(m,6n),at(m,7n))

def diagonals(+v: List<&2,U32>, +m: List<&2,U32>) -> List<&2,U32>:
  +v1 = g(v,0n,5n,10n,15n,at(m,8n),at(m,9n))
  +v2 = g(v1,1n,6n,11n,12n,at(m,10n),at(m,11n))
  +v3 = g(v2,2n,7n,8n,13n,at(m,12n),at(m,13n))
  g(v3,3n,4n,9n,14n,at(m,14n),at(m,15n))

def round(v: List<&2,U32>, +m: List<&2,U32>) -> List<&2,U32>:
  match v:
    case Nil{}: Nil{}
    case Con{+x,+r}: diagonals(columns(Con{x,r},m),m)

# The message words are permuted between rounds: word i of the next round is
# word msg_permutation[i] of this one.
def permute_go(ps: List<&2,Nat>, +m: List<&2,U32>) -> List<&2,U32>:
  match ps:
    case Nil{}: Nil{}
    case Con{p,r}: Con{at(m,p),permute_go(r,m)}

def permute(+m: List<&2,U32>) -> List<&2,U32>:
  permute_go(msg_permutation(),m)

def rounds(n: Nat, +v: List<&2,U32>, +m: List<&2,U32>) -> List<&2,U32>:
  match n:
    case 0n: v
    case 1n+k: rounds(k,round(v,m),permute(m))

# The initial state of compress(h, m, t, len, flags): h[0..7], IV[0..3], the
# counter t (low word, then the high word, always 0 here: an input has fewer
# than 2^32 chunks), the block length and the flags.
def init(c: T.CV, +t: U32, +len: U32, +flags: U32) -> List<&2,U32>:
  SC.append(U32,cv_words(c),[at(iv(),0n),at(iv(),1n),at(iv(),2n),at(iv(),3n),t,0,len,flags])

# The new chaining value: word i xor word i+8 of the final state (the 64-byte
# extended output is not needed for a 32-byte digest).
def output(+v: List<&2,U32>) -> T.CV:
  T.CV{U32.xor(at(v,0n),at(v,8n)),U32.xor(at(v,1n),at(v,9n)),U32.xor(at(v,2n),at(v,10n)),U32.xor(at(v,3n),at(v,11n)),U32.xor(at(v,4n),at(v,12n)),U32.xor(at(v,5n),at(v,13n)),U32.xor(at(v,6n),at(v,14n)),U32.xor(at(v,7n),at(v,15n))}

# Seven rounds over the block's words.
def compress(c: T.CV, b: T.Block, +t: U32, +len: U32, +flags: U32) -> T.CV:
  match b:
    case T.B{m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15}:
      output(rounds(7n,init(c,t,len,flags),[m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15]))

# ---- reading blocks ----

# The sixteen words of the block at word `index`, in order.
def gather(n: Nat, +base: U32, +next: U32, acc: List<&2,U32>, pair: Array<U32> & U32) -> Array<U32> & List<&2,U32>:
  match n pair:
    case 0n Tuple{a,w}: (a,List.reverse(&2,U32,Con{w,acc}))
    case 1n+p Tuple{a,w}: gather(p,base,U32.inc(next),Con{w,acc},Array.get(U32,a,U32.add(base,next)))

def as_block(pair: Array<U32> & List<&2,U32>) -> Array<U32> & T.Block:
  (a,ws) = pair
  (a,block_of(ws))

def read_block(a: Array<U32>, +index: U32) -> Array<U32> & T.Block:
  as_block(gather(15n,index,1,Nil{},Array.get(U32,a,index)))

# A block holding len bytes (len <= 64) is zero past them: the word at byte
# offset pos keeps its min(4, len - pos) low bytes.
def low_bytes(w: U32, k: Nat) -> U32:
  match k:
    case 0n: 0
    case 1n: U32.and(w,255)
    case 2n: U32.and(w,65535)
    case 3n: U32.and(w,16777215)
    case 4n+q: w

def keep(w: U32, +pos: Nat, +len: Nat) -> U32:
  low_bytes(w,Nat.min(4n,Nat.sub(len,pos)))

def zero_tail(b: T.Block, +len: Nat) -> T.Block:
  match b:
    case T.B{m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15}:
      T.B{keep(m0,0n,len),keep(m1,4n,len),keep(m2,8n,len),keep(m3,12n,len),keep(m4,16n,len),keep(m5,20n,len),keep(m6,24n,len),keep(m7,28n,len),keep(m8,32n,len),keep(m9,36n,len),keep(m10,40n,len),keep(m11,44n,len),keep(m12,48n,len),keep(m13,52n,len),keep(m14,56n,len),keep(m15,60n,len)}

# ---- chunks (2.4) ----

# The blocks of a chunk are compressed in order starting from the key (IV in
# hash mode), all with the chunk counter t; the first block carries
# CHUNK_START and the last CHUNK_END. The last block is not compressed here:
# it is the chunk's output node (2.5, 2.6 decide its flags and use).
# n blocks follow the current block (in pair); the last block has len bytes.
def chunk_blocks(n: Nat, +t: U32, +index: U32, +flags: U32, +len: Nat, cv: T.CV, pair: Array<U32> & T.Block) -> Array<U32> & T.Out:
  match n pair:
    case 0n Tuple{a,b}: (a,T.Out{cv,zero_tail(b,len),t,U32.from_nat(len),U32.or(flags,chunk_end())})
    case 1n+p Tuple{a,b}: chunk_blocks(p,t,U32.add(index,16),0,len,compress(cv,zero_tail(b,64n),t,64,flags),read_block(a,U32.add(index,16)))

# A chunk of len bytes (1..1024; 0 only for the empty message) at word index
# has max(1, ceil(len/64)) blocks: n = (len - 1) div 64 full blocks, then a
# last block of len - 64n bytes.
def chunk(a: Array<U32>, +t: U32, +index: U32, +len: Nat) -> Array<U32> & T.Out:
  +n = Nat.div(Nat.sub(len,1n),64n)
  chunk_blocks(n,t,index,chunk_start(),Nat.sub(len,Nat.mul(n,64n)),cv_of(iv()),read_block(a,index))

# Every chunk but the last holds 1024 bytes; chunk t starts at word 256t.
def chunk_at(more: Nat, +t: U32, +index: U32, +len: Nat, a: Array<U32>) -> Array<U32> & T.Out:
  match more:
    case 0n: chunk(a,t,index,len)
    case 1n+q: chunk(a,t,index,1024n)

# The outputs of the chunks, in order; `pair` holds the current chunk, n
# chunks follow it, the last one of len bytes.
def chunks(+n: Nat, +t: U32, +index: U32, +len: Nat, pair: Array<U32> & T.Out) -> List<&2,T.Out>:
  match n pair:
    case 0n Tuple{a,o}: Con{o,Nil{}}
    case 1n+p Tuple{a,o}: Con{o,chunks(p,U32.inc(t),U32.add(index,256),len,chunk_at(p,U32.inc(t),U32.add(index,256),len,a))}

# A message of `length` bytes has max(1, ceil(length/1024)) chunks: n =
# (length - 1) div 1024 full ones, then the last of length - 1024n bytes.
def message_chunks(a: Array<U32>, +length: Nat) -> List<&2,T.Out>:
  +n = Nat.div(Nat.sub(length,1n),1024n)
  +last = Nat.sub(length,Nat.mul(n,1024n))
  chunks(n,0,0,last,chunk_at(n,0,0,last,a))

# ---- the tree (2.5) ----

# A node's chaining value: its compression with its own flags.
def cv(o: T.Out) -> T.CV:
  match o:
    case T.Out{c,b,t,len,flags}: compress(c,b,t,len,flags)

# A parent node: key IV, block = left child CV ++ right child CV, counter 0,
# length 64, flag PARENT.
def parent(l: T.CV, r: T.CV) -> T.Out:
  T.Out{cv_of(iv()),block_of(SC.append(U32,cv_words(l),cv_words(r))),0,64,parent_flag()}

def is_nil(xs: List<&2,T.Out>) -> Bool:
  match xs:
    case Nil{}: True{}
    case Con{x,r}: False{}

def first(xs: List<&2,T.Out>) -> T.Out:
  match xs:
    case Nil{}: T.Out{cv_of(iv()),block_of(Nil{}),0,0,0}
    case Con{x,r}: x

def join(l: T.Out, r: T.Out, alone: Bool) -> T.Out:
  match alone:
    case True{}: l
    case False{}: parent(cv(l),cv(r))

# The tree over the chunk outputs xs, 1 <= |xs| <= 2^h. The chunks are its
# leaves in order; a left subtree is always complete with a power of two of
# chunks, the largest one that leaves at least one chunk to its right: with
# h = g+1 and |xs| > 2^g the left subtree takes the first 2^g chunks and the
# right one the rest, while |xs| <= 2^g (nothing left for the right) means the
# tree already fits in height g.
def tree(+h: Nat, +xs: List<&2,T.Out>) -> T.Out:
  match h xs:
    case 0n Nil{}: first(Nil{})
    case 0n Con{+x,+r}: first(Con{x,r})
    case 1n+g Nil{}: first(Nil{})
    case 1n+g Con{+x,+r}:
      +k = SC.pow2(g)
      join(tree(g,SC.take(T.Out,Con{x,r},k)),tree(g,SC.drop(T.Out,Con{x,r},k)),is_nil(SC.drop(T.Out,Con{x,r},k)))

# ---- the root and the digest (2.6) ----

# The root node is compressed with ROOT added to its flags; the 32-byte digest
# is the resulting chaining value, words in little-endian order. A single
# chunk is itself the root.
def root(o: T.Out) -> T.CV:
  match o:
    case T.Out{c,b,t,len,flags}: compress(c,b,t,len,U32.or(flags,root_flag()))

def hash(a: Array<U32>, +length: Nat) -> T.CV:
  +cs = message_chunks(a,length)
  root(tree(SC.length(T.Out,cs),cs))

def digest(c: T.CV) -> Array<U32>:
  match c:
    case T.CV{h0,h1,h2,h3,h4,h5,h6,h7}:
      ANode{ANode{ANode{ALeaf{h0},ALeaf{h1}},ANode{ALeaf{h2},ALeaf{h3}}},ANode{ANode{ALeaf{h4},ALeaf{h5}},ANode{ALeaf{h6},ALeaf{h7}}}}

def checked(valid: Bool, a: Array<U32>, +length: Nat) -> Maybe<&1,Array<U32>>:
  match valid:
    case False{}: None{}
    case True{}: Some{digest(hash(a,length))}

# None when byte_length exceeds the 4 * capacity bytes the array can hold.
def sized(+length: Nat, pair: Array<U32> & U32) -> Maybe<&1,Array<U32>>:
  (a,capacity) = pair
  checked(Nat.is_le(length,Nat.mul(4n,U32.to_nat(capacity))),a,length)

def blake3(words: Array<U32>, byte_length: Nat) -> Maybe<&1,Array<U32>>:
  sized(byte_length,Array.size(U32,words))
