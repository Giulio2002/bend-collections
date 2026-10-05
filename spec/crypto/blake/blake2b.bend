import Base
import ../../../src/crypto/blake/blake2b/types.bend as T

# BLAKE2b-512 (RFC 7693), unkeyed, as an executable specification.
#
# Written from the RFC; it never calls the implementation. It shares only the
# record types of src/crypto/blake/blake2b/types.bend: a 64-bit word is a pair
# of U32 halves T.W{lo, hi} (low half first), the working vector v[0..15] is
# T.V{..}, the chaining value h[0..7] is T.H{..} and the 128-bit byte counter t
# is four little-endian U32 limbs T.C{..}. The state is indexed with at/put and
# the message schedule is read from the SIGMA table, as in the RFC's pseudocode.
#
# Input convention (shared with the public API): the message bytes are packed
# little-endian, four per U32 word, in an Array<U32>; byte_length is the number
# of message bytes. Bytes of the last block past byte_length are zero.

# ---------------------------------------------------------------- 64-bit words

# (a + b) mod 2^64: the low halves add modulo 2^32; the high halves add the
# carry out of the low half, which is 1 exactly when the low sum wrapped.
def add(a: T.Lane, b: T.Lane) -> T.Lane:
  match a b:
    case T.W{+al,ah} T.W{bl,bh}:
      +lo = U32.add(al,bl)
      T.W{lo,U32.add(U32.add(ah,bh),Bool.to_u32(U32.is_lt(lo,al)))}

def xor(a: T.Lane, b: T.Lane) -> T.Lane:
  match a b:
    case T.W{al,ah} T.W{bl,bh}: T.W{U32.xor(al,bl),U32.xor(ah,bh)}

# x >>> n for 0 < n < 32: each half takes its own bits shifted right and the
# other half's low bits shifted in from the top.
def rotr_small(+lo: U32, +hi: U32, +n: Nat) -> T.Lane:
  T.W{U32.or(U32.shrn(lo,n),U32.shln(hi,Nat.sub(32n,n))),U32.or(U32.shrn(hi,n),U32.shln(lo,Nat.sub(32n,n)))}

# n > 32 rotates the swapped halves by n - 32.
def rotr_split(lo: U32, hi: U32, +n: Nat, small: Bool) -> T.Lane:
  match small:
    case True{}: rotr_small(lo,hi,n)
    case False{}: rotr_small(hi,lo,Nat.sub(n,32n))

# Right rotation of a 64-bit word by n (0 <= n < 64).
def rotr(a: T.Lane, +n: Nat) -> T.Lane:
  match a n:
    case T.W{lo,hi} 0n: T.W{lo,hi}
    case T.W{lo,hi} 32n: T.W{hi,lo}
    case T.W{lo,hi} n: rotr_split(lo,hi,n,Nat.is_lt(n,32n))

# ---------------------------------------------------------------- constants

# RFC 7693 section 2.6: IV[i], the SHA-512 initial hash values.
def iv(i: Nat) -> T.Lane:
  match i:
    case 0n: T.W{4089235720,1779033703}
    case 1n: T.W{2227873595,3144134277}
    case 2n: T.W{4271175723,1013904242}
    case 3n: T.W{1595750129,2773480762}
    case 4n: T.W{2917565137,1359893119}
    case 5n: T.W{725511199,2600822924}
    case 6n: T.W{4215389547,528734635}
    case 7n: T.W{327033209,1541459225}
    case _: T.W{0,0}

# RFC 7693 section 2.7: the message word schedule SIGMA[r].
def sigma(r: Nat) -> List<&2,Nat>:
  match r:
    case 0n: [0n,1n,2n,3n,4n,5n,6n,7n,8n,9n,10n,11n,12n,13n,14n,15n]
    case 1n: [14n,10n,4n,8n,9n,15n,13n,6n,1n,12n,0n,2n,11n,7n,5n,3n]
    case 2n: [11n,8n,12n,0n,5n,2n,15n,13n,10n,14n,3n,6n,7n,1n,9n,4n]
    case 3n: [7n,9n,3n,1n,13n,12n,11n,14n,2n,6n,5n,10n,4n,0n,15n,8n]
    case 4n: [9n,0n,5n,7n,2n,4n,10n,15n,14n,1n,11n,12n,6n,8n,3n,13n]
    case 5n: [2n,12n,6n,10n,0n,11n,8n,3n,4n,13n,7n,5n,15n,14n,1n,9n]
    case 6n: [12n,5n,1n,15n,14n,13n,4n,10n,0n,7n,6n,3n,9n,2n,8n,11n]
    case 7n: [13n,11n,7n,14n,12n,1n,3n,9n,5n,0n,15n,4n,8n,6n,2n,10n]
    case 8n: [6n,15n,14n,9n,11n,3n,0n,8n,12n,2n,13n,7n,1n,4n,10n,5n]
    case 9n: [10n,2n,8n,4n,7n,6n,1n,5n,15n,11n,9n,14n,3n,12n,13n,0n]
    case _: []

def nth(-A: Data, xs: List<&2,A>, n: Nat, +zero: A) -> A:
  match xs n:
    case Nil{} _: zero
    case x <> rest 0n: x
    case x <> rest 1n+p: nth(A,rest,p,zero)

# ---------------------------------------------------------------- the working vector

def at(s: T.State, i: Nat) -> T.Lane:
  match s i:
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 0n: v0
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 1n: v1
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 2n: v2
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 3n: v3
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 4n: v4
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 5n: v5
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 6n: v6
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 7n: v7
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 8n: v8
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 9n: v9
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 10n: v10
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 11n: v11
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 12n: v12
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 13n: v13
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 14n: v14
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 15n: v15
    case _ _: T.W{0,0}

def put(s: T.State, i: Nat, x: T.Lane) -> T.State:
  match s i:
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 0n: T.V{x,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15}
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 1n: T.V{v0,x,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15}
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 2n: T.V{v0,v1,x,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15}
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 3n: T.V{v0,v1,v2,x,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15}
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 4n: T.V{v0,v1,v2,v3,x,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15}
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 5n: T.V{v0,v1,v2,v3,v4,x,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15}
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 6n: T.V{v0,v1,v2,v3,v4,v5,x,v7,v8,v9,v10,v11,v12,v13,v14,v15}
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 7n: T.V{v0,v1,v2,v3,v4,v5,v6,x,v8,v9,v10,v11,v12,v13,v14,v15}
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 8n: T.V{v0,v1,v2,v3,v4,v5,v6,v7,x,v9,v10,v11,v12,v13,v14,v15}
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 9n: T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,x,v10,v11,v12,v13,v14,v15}
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 10n: T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,x,v11,v12,v13,v14,v15}
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 11n: T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,x,v12,v13,v14,v15}
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 12n: T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,x,v13,v14,v15}
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 13n: T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,x,v14,v15}
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 14n: T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,x,v15}
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15} 15n: T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,x}
    case s _: s

# ---------------------------------------------------------------- G, the round, F

# RFC 7693 section 3.1, the mixing function G with R1..R4 = 32, 24, 16, 63:
#   v[a] := (v[a] + v[b] + x) mod 2^64;  v[d] := (v[d] ^ v[a]) >>> R1
#   v[c] := (v[c] + v[d])     mod 2^64;  v[b] := (v[b] ^ v[c]) >>> R2
#   v[a] := (v[a] + v[b] + y) mod 2^64;  v[d] := (v[d] ^ v[a]) >>> R3
#   v[c] := (v[c] + v[d])     mod 2^64;  v[b] := (v[b] ^ v[c]) >>> R4
def mix(+s: T.State, +a: Nat, +b: Nat, +c: Nat, +d: Nat, x: T.Lane, y: T.Lane) -> T.State:
  +a1 = add(add(at(s,a),at(s,b)),x)
  +d1 = rotr(xor(at(s,d),a1),32n)
  +c1 = add(at(s,c),d1)
  +b1 = rotr(xor(at(s,b),c1),24n)
  +a2 = add(add(a1,b1),y)
  +d2 = rotr(xor(d1,a2),16n)
  +c2 = add(c1,d2)
  +b2 = rotr(xor(b1,c2),63n)
  put(put(put(put(s,a,a2),b,b2),c,c2),d,d2)

# G reads the vector's sixteen words and mixes the four at a, b, c, d.
def G(v: T.State, +a: Nat, +b: Nat, +c: Nat, +d: Nat, x: T.Lane, y: T.Lane) -> T.State:
  match v:
    case T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15}:
      mix(T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15},a,b,c,d,x,y)

# m[s[j]]: the j-th message word of the round's schedule s.
def word(+m: List<&2,T.Lane>, +s: List<&2,Nat>, +j: Nat) -> T.Lane:
  nth(T.Lane,m,nth(Nat,s,j,0n),T.W{0,0})

# RFC 7693 section 3.2, one round of F with schedule s = SIGMA[i mod 10].
def round(v: T.State, +m: List<&2,T.Lane>, +s: List<&2,Nat>) -> T.State:
  v = G(v,0n,4n,8n,12n,word(m,s,0n),word(m,s,1n))
  v = G(v,1n,5n,9n,13n,word(m,s,2n),word(m,s,3n))
  v = G(v,2n,6n,10n,14n,word(m,s,4n),word(m,s,5n))
  v = G(v,3n,7n,11n,15n,word(m,s,6n),word(m,s,7n))
  v = G(v,0n,5n,10n,15n,word(m,s,8n),word(m,s,9n))
  v = G(v,1n,6n,11n,12n,word(m,s,10n),word(m,s,11n))
  v = G(v,2n,7n,8n,13n,word(m,s,12n),word(m,s,13n))
  G(v,3n,4n,9n,14n,word(m,s,14n),word(m,s,15n))

# Rounds i, i+1, .., i+n-1.
def rounds(n: Nat, +i: Nat, v: T.State, +m: List<&2,T.Lane>) -> T.State:
  match n:
    case 0n: v
    case 1n+p: rounds(p,1n+i,round(v,m,sigma(Nat.mod(i,10n))),m)

def invert_if(last: Bool, x: T.Lane) -> T.Lane:
  match last:
    case True{}: xor(x,T.W{4294967295,4294967295})
    case False{}: x

# v[0..7] := h[0..7]; v[8..15] := IV[0..7]; v[12] ^= t mod 2^64;
# v[13] ^= t >> 64; if last block, v[14] := ~v[14].
def start(h: T.Chain, t: T.Counter, last: Bool) -> T.State:
  match h t:
    case T.H{h0,h1,h2,h3,h4,h5,h6,h7} T.C{t0,t1,t2,t3}:
      T.V{h0,h1,h2,h3,h4,h5,h6,h7,iv(0n),iv(1n),iv(2n),iv(3n),xor(iv(4n),T.W{t0,t1}),xor(iv(5n),T.W{t2,t3}),invert_if(last,iv(6n)),iv(7n)}

# h[i] := h[i] ^ v[i] ^ v[i + 8].
def finish(h: T.Chain, v: T.State) -> T.Chain:
  match h v:
    case T.H{h0,h1,h2,h3,h4,h5,h6,h7} T.V{v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15}:
      T.H{xor(xor(h0,v0),v8),xor(xor(h1,v1),v9),xor(xor(h2,v2),v10),xor(xor(h3,v3),v11),xor(xor(h4,v4),v12),xor(xor(h5,v5),v13),xor(xor(h6,v6),v14),xor(xor(h7,v7),v15)}

# RFC 7693 section 3.2: F(h, m, t, f) with twelve rounds.
def compress(+h: T.Chain, +m: List<&2,T.Lane>, t: T.Counter, last: Bool) -> T.Chain:
  finish(h,rounds(12n,0n,start(h,t,last),m))

# ---------------------------------------------------------------- message blocks

# t := t + x on the 128-bit counter, carrying from limb to limb.
def advance(c: T.Counter, +x: U32) -> T.Counter:
  match c:
    case T.C{c0,c1,c2,c3}:
      +s0 = U32.add(c0,x)
      +k0 = Bool.to_u32(U32.is_lt(s0,x))
      +s1 = U32.add(c1,k0)
      +k1 = Bool.to_u32(U32.is_lt(s1,k0))
      +s2 = U32.add(c2,k1)
      T.C{s0,s1,s2,U32.add(c3,Bool.to_u32(U32.is_lt(s2,k1)))}

# The low n bytes of a little-endian word (all four when n >= 4).
def keep(w: U32, n: Nat) -> U32:
  match n:
    case 0n: 0
    case 1n: U32.and(w,255)
    case 2n: U32.and(w,65535)
    case 3n: U32.and(w,16777215)
    case _: w

# The word holding block bytes pos..pos+3 when only `remain` bytes are message:
# the bytes at or past `remain` are zero padding.
def mask(w: U32, +pos: Nat, +remain: Nat) -> U32:
  keep(w,Nat.sub(remain,pos))

def trim(ws: List<&2,U32>, +pos: Nat, +remain: Nat) -> List<&2,U32>:
  match ws:
    case Nil{}: Nil{}
    case w <> rest: mask(w,pos,remain) <> trim(rest,Nat.add(pos,4n),remain)

def prepare(last: Bool, ws: List<&2,U32>, remain: Nat) -> List<&2,U32>:
  match last:
    case False{}: ws
    case True{}: trim(ws,0n,remain)

# m[i] = the little-endian 64-bit word of block bytes 8i..8i+7.
def lanes(ws: List<&2,U32>) -> List<&2,T.Lane>:
  match ws:
    case lo <> hi <> rest: T.W{lo,hi} <> lanes(rest)
    case _: Nil{}

# Reads the block's 32 words base+0 .. base+31 from the array, then compresses.
def gather(n: Nat, +base: U32, +next: U32, +last: Bool, +remain: Nat, t: T.Counter, h: T.Chain, acc: List<&2,U32>, pair: Array<U32> & U32) -> Array<U32> & T.Chain:
  match n pair:
    case 0n Tuple{a,w}:
      (a,compress(h,lanes(prepare(last,List.reverse(&2,U32,w <> acc),remain)),t,last))
    case 1n+p Tuple{a,w}:
      gather(p,base,U32.inc(next),last,remain,t,h,w <> acc,Array.get(U32,a,U32.add(base,next)))

# A block that is not the last: t already counts its 128 bytes.
def absorb(a: Array<U32>, +index: U32, t: T.Counter, h: T.Chain) -> Array<U32> & T.Chain:
  gather(31n,index,1,False{},0n,t,h,Nil{},Array.get(U32,a,index))

# The last block: remain message bytes (1..128; 0 for the empty message), t := t + remain.
def final(a: Array<U32>, +index: U32, +remain: Nat, t: T.Counter, h: T.Chain) -> T.Chain:
  Pair.snd(Array<U32>,T.Chain,gather(31n,index,1,True{},remain,advance(t,U32.from_nat(remain)),h,Nil{},Array.get(U32,a,index)))

# n blocks that are not the last, then the last one.
def blocks(n: Nat, +index: U32, +remain: Nat, t: T.Counter, pair: Array<U32> & T.Chain) -> T.Chain:
  match n pair:
    case 0n Tuple{a,h}: final(a,index,remain,t,h)
    case 1n+p Tuple{a,h}:
      +t2 = advance(t,128)
      blocks(p,U32.add(index,32),remain,t2,absorb(a,index,t2,h))

# h[0..7] := IV[0..7]; h[0] ^= 0x01010000 ^ (kk << 8) ^ nn with kk = 0, nn = 64.
def initial() -> T.Chain:
  T.H{xor(iv(0n),T.W{16842816,0}),iv(1n),iv(2n),iv(3n),iv(4n),iv(5n),iv(6n),iv(7n)}

# dd = max(1, ceil(ll / 128)) blocks: dd - 1 = (ll - 1) div 128 full blocks
# (0 when ll = 0), then the last block with the remaining ll - 128 (dd - 1) bytes.
def unchecked(a: Array<U32>, +length: Nat) -> T.Chain:
  +n = Nat.div(Nat.sub(length,1n),128n)
  blocks(n,0,Nat.sub(length,Nat.mul(n,128n)),T.C{0,0,0,0},(a,initial()))

# The 64-byte digest h[0..7] as sixteen little-endian words.
def digest(h: T.Chain) -> Array<U32>:
  match h:
    case T.H{T.W{l0,u0},T.W{l1,u1},T.W{l2,u2},T.W{l3,u3},T.W{l4,u4},T.W{l5,u5},T.W{l6,u6},T.W{l7,u7}}:
      ANode{ANode{ANode{ANode{ALeaf{l0},ALeaf{u0}},ANode{ALeaf{l1},ALeaf{u1}}},ANode{ANode{ALeaf{l2},ALeaf{u2}},ANode{ALeaf{l3},ALeaf{u3}}}},ANode{ANode{ANode{ALeaf{l4},ALeaf{u4}},ANode{ALeaf{l5},ALeaf{u5}}},ANode{ANode{ALeaf{l6},ALeaf{u6}},ANode{ALeaf{l7},ALeaf{u7}}}}}

def checked(valid: Bool, a: Array<U32>, length: Nat) -> Maybe<&1,Array<U32>>:
  match valid:
    case False{}: None{}
    case True{}: Some{digest(unchecked(a,length))}

def sized(+length: Nat, pair: Array<U32> & U32) -> Maybe<&1,Array<U32>>:
  (a,capacity) = pair
  checked(Nat.is_le(length,Nat.mul(4n,U32.to_nat(capacity))),a,length)

# BLAKE2b-512 of the first byte_length bytes of the packed words; None when
# byte_length exceeds the array's 4 * capacity bytes.
def blake2b(words: Array<U32>, byte_length: Nat) -> Maybe<&1,Array<U32>>:
  sized(byte_length,Array.size(U32,words))

# ---------------------------------------------------------------- the parameter block
#
# BLAKE2b with every sequential-mode parameter of RFC 7693 section 2.5 and the
# BLAKE2 paper's parameter block (fanout = depth = 1, leaf length, node offset,
# node depth and inner length zero): digest length nn (1..64 bytes), key length
# kk (0..64 bytes) and key, a 16-byte salt and a 16-byte personalization. The
# salt and the personalization are four little-endian words each (T.X4{..}),
# the key is packed like the message (its first kk bytes are the key).

# Four bytes as one little-endian word.
def pack4(+b0: U32, +b1: U32, +b2: U32, +b3: U32) -> U32:
  U32.add(U32.add(b0,U32.mul(b1,256)),U32.add(U32.mul(b2,65536),U32.mul(b3,16777216)))

# The 64-byte parameter block as sixteen little-endian words:
#   bytes  0..3   digest length nn, key length kk, fanout 1, depth 1
#   bytes  4..7   leaf length 0
#   bytes  8..15  node offset 0
#   bytes 16..31  node depth 0, inner length 0, reserved zeros
#   bytes 32..47  salt
#   bytes 48..63  personalization
def param_block(+nn: U32, +kk: U32, salt: T.Words4, personal: T.Words4) -> List<&2,U32>:
  match salt personal:
    case T.X4{s0,s1,s2,s3} T.X4{p0,p1,p2,p3}:
      [pack4(nn,kk,1,1),0,0,0,0,0,0,0,s0,s1,s2,s3,p0,p1,p2,p3]

def iv_xor(+i: Nat, +p: List<&2,T.Lane>) -> T.Lane:
  xor(iv(i),nth(T.Lane,p,i,T.W{0,0}))

# h[0..7] := IV[0..7] xor P[0..7], P the parameter block's eight 64-bit words.
def param_chain(+p: List<&2,T.Lane>) -> T.Chain:
  T.H{iv_xor(0n,p),iv_xor(1n,p),iv_xor(2n,p),iv_xor(3n,p),iv_xor(4n,p),iv_xor(5n,p),iv_xor(6n,p),iv_xor(7n,p)}

def init_chain(+nn: Nat, +kk: Nat, salt: T.Words4, personal: T.Words4) -> T.Chain:
  param_chain(lanes(param_block(U32.from_nat(nn),U32.from_nat(kk),salt,personal)))

# Words next, next+1, .. of the array, n + 1 of them counting the one in pair.
def read(n: Nat, +next: U32, acc: List<&2,U32>, pair: Array<U32> & U32) -> List<&2,U32>:
  match n pair:
    case 0n Tuple{a,w}: List.reverse(&2,U32,w <> acc)
    case 1n+p Tuple{a,w}: read(p,U32.inc(next),w <> acc,Array.get(U32,a,next))

# The key block (RFC 7693 section 3.3): the kk key bytes padded with zeros to
# 128 bytes, compressed as block 0 with t = 128; it is the last block exactly
# when the message is empty.
def key_block(key: Array<U32>, +kk: Nat, t: T.Counter, +h: T.Chain, last: Bool) -> T.Chain:
  compress(h,lanes(trim(read(31n,1,Nil{},Array.get(U32,key,0)),0n,kk)),t,last)

# Keyed: the data is the key block followed by the ll message bytes; after the
# key block the message is split as in `unchecked`, with t starting at 128.
def keyed(key: Array<U32>, +kk: Nat, a: Array<U32>, +ll: Nat, h: T.Chain) -> T.Chain:
  match ll:
    case 0n: key_block(key,kk,T.C{128,0,0,0},h,True{})
    case 1n+p:
      +n = Nat.div(p,128n)
      blocks(n,0,Nat.sub(1n+p,Nat.mul(n,128n)),T.C{128,0,0,0},(a,key_block(key,kk,T.C{128,0,0,0},h,False{})))

# The chaining value after the last block, from the initial chaining value h
# (RFC 7693 section 3.3): unkeyed, the message alone, split as in `unchecked`.
def from_chain(key: Array<U32>, +kk: Nat, a: Array<U32>, +ll: Nat, h: T.Chain) -> T.Chain:
  match kk:
    case 0n:
      +n = Nat.div(Nat.sub(ll,1n),128n)
      blocks(n,0,Nat.sub(ll,Nat.mul(n,128n)),T.C{0,0,0,0},(a,h))
    case 1n+q: keyed(key,1n+q,a,ll,h)

def param_hash(+nn: Nat, key: Array<U32>, +kk: Nat, salt: T.Words4, personal: T.Words4, a: Array<U32>, +ll: Nat) -> T.Chain:
  from_chain(key,kk,a,ll,init_chain(nn,kk,salt,personal))

# The four little-endian bytes of a word, each a U32 below 256.
def word_bytes(+w: U32) -> List<&2,U32>:
  [U32.and(w,255),U32.and(U32.shrn(w,8n),255),U32.and(U32.shrn(w,16n),255),U32.shrn(w,24n)]

# The first nn bytes of h[0..7] in little-endian order (RFC 7693 section 3.3).
def out_bytes(h: T.Chain, +nn: Nat) -> List<&2,U32>:
  match h:
    case T.H{T.W{l0,u0},T.W{l1,u1},T.W{l2,u2},T.W{l3,u3},T.W{l4,u4},T.W{l5,u5},T.W{l6,u6},T.W{l7,u7}}:
      List.take(&2,U32,List.concat(&2,U32,[word_bytes(l0),word_bytes(u0),word_bytes(l1),word_bytes(u1),word_bytes(l2),word_bytes(u2),word_bytes(l3),word_bytes(u3),word_bytes(l4),word_bytes(u4),word_bytes(l5),word_bytes(u5),word_bytes(l6),word_bytes(u6),word_bytes(l7),word_bytes(u7)]),nn)

# Valid parameters: 1 <= nn <= 64, kk <= 64, and the key and the message fit
# their arrays (kk <= 4 * key capacity, ll <= 4 * message capacity).
def param_valid(+nn: Nat, +kk: Nat, +ll: Nat, +kcap: U32, +mcap: U32) -> Bool:
  Bool.and(Bool.and(Nat.is_lt(0n,nn),Nat.is_le(nn,64n)),Bool.and(Bool.and(Nat.is_le(kk,64n),Nat.is_le(kk,Nat.mul(4n,U32.to_nat(kcap)))),Nat.is_le(ll,Nat.mul(4n,U32.to_nat(mcap)))))

def param_checked(valid: Bool, +nn: Nat, key: Array<U32>, +kk: Nat, salt: T.Words4, personal: T.Words4, a: Array<U32>, +ll: Nat) -> Maybe<&1,List<&2,U32>>:
  match valid:
    case False{}: None{}
    case True{}: Some{out_bytes(param_hash(nn,key,kk,salt,personal,a,ll),nn)}

def param_sized(+nn: Nat, +kk: Nat, salt: T.Words4, personal: T.Words4, +ll: Nat, kpair: Array<U32> & U32, mpair: Array<U32> & U32) -> Maybe<&1,List<&2,U32>>:
  (key,kcap) = kpair
  (a,mcap) = mpair
  param_checked(param_valid(nn,kk,ll,kcap,mcap),nn,key,kk,salt,personal,a,ll)

# BLAKE2b with an nn-byte digest, a kk-byte key, a salt and a personalization,
# of the first ll bytes of the packed message words: the nn digest bytes, or
# None when a parameter is out of range.
def blake2b_params(+nn: Nat, key: Array<U32>, +kk: Nat, salt: T.Words4, personal: T.Words4, words: Array<U32>, +ll: Nat) -> Maybe<&1,List<&2,U32>>:
  param_sized(nn,kk,salt,personal,ll,Array.size(U32,key),Array.size(U32,words))
