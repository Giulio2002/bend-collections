import Base
import ../../../../src/crypto/blake/blake3/types.bend as T
import ../../../../src/crypto/blake/blake3/compress.bend as C
import ../../../../src/crypto/blake/blake3/blake3.bend as K
import ../../../../spec/crypto/blake/blake3.bend as S
import ./compress.bend as P
import ./read.bend as R
import ./array.bend as A

# The implementation's chunk loops equal the specification's chunk: a full
# chunk's chaining value is the chaining value of the specification's chunk
# output, and the last chunk's pending output is the specification's.

def outcv(q: Array<U32> & T.Out) -> Array<U32> & T.CV:
  (a,o) = q
  (a,S.cv(o))

# A full (64-byte) block: the implementation compresses the raw block, the
# specification the block truncated to 64 bytes.
law compress_full:
  for +cv: T.CV
  for +b: T.Block
  for +t: U32
  for +flags: U32
  {C.compress(cv,b,t,64,flags) == S.compress(cv,S.zero_tail(b,64n),t,64,flags) : T.CV}

def compress_full(cv,b,t,flags):
  %Equal.sym(T.Block,S.zero_tail(b,64n),b,R.zero_tail_full(b)) : {C.compress(cv,b,t,64,flags) == S.compress(cv,_,t,64,flags) : T.CV}
  P.compress_correct(cv,b,t,64,flags)

# ---- the last chunk ----

law last_step:
  for +p: Nat
  for +t: U32
  for +index: U32
  for +flags: U32
  for +len: Nat
  for +cv: T.CV
  for -a: Array<U32>
  for +b: T.Block
  for view: Sigma<&2,&1,A.Tree,x => {a == A.thaw(x) : Array<U32>}>
  for recurse: @c: T.CV -> @q: (Array<U32> & T.Block) -> {K.last_go(p,t,U32.add(index,16),0,len,c,q) == S.chunk_blocks(p,t,U32.add(index,16),0,len,c,q) : Array<U32> & T.Out}
  {K.last_go(1n+p,t,index,flags,len,cv,(a,b)) == S.chunk_blocks(1n+p,t,index,flags,len,cv,(a,b)) : Array<U32> & T.Out}

def last_step(p,t,index,flags,len,cv,a,b,view,recurse):
  match view:
    case Tuple{+tree,pf}:
      %Equal.sym(Array<U32>,a,A.thaw(tree),pf) : {K.last_go(1n+p,t,index,flags,len,cv,(_,b)) == S.chunk_blocks(1n+p,t,index,flags,len,cv,(_,b)) : Array<U32> & T.Out}
      Equal.trans(Array<U32> & T.Out,
        K.last_go(p,t,U32.add(index,16),0,len,C.compress(cv,b,t,64,flags),K.read_block(A.thaw(tree),U32.add(index,16))),
        S.chunk_blocks(p,t,U32.add(index,16),0,len,C.compress(cv,b,t,64,flags),K.read_block(A.thaw(tree),U32.add(index,16))),
        S.chunk_blocks(p,t,U32.add(index,16),0,len,S.compress(cv,S.zero_tail(b,64n),t,64,flags),S.read_block(A.thaw(tree),U32.add(index,16))),
        recurse(C.compress(cv,b,t,64,flags),K.read_block(A.thaw(tree),U32.add(index,16))),
        Equal.trans(Array<U32> & T.Out,
          S.chunk_blocks(p,t,U32.add(index,16),0,len,C.compress(cv,b,t,64,flags),K.read_block(A.thaw(tree),U32.add(index,16))),
          S.chunk_blocks(p,t,U32.add(index,16),0,len,C.compress(cv,b,t,64,flags),S.read_block(A.thaw(tree),U32.add(index,16))),
          S.chunk_blocks(p,t,U32.add(index,16),0,len,S.compress(cv,S.zero_tail(b,64n),t,64,flags),S.read_block(A.thaw(tree),U32.add(index,16))),
          Equal.cong(Array<U32> & T.Block,Array<U32> & T.Out,q => S.chunk_blocks(p,t,U32.add(index,16),0,len,C.compress(cv,b,t,64,flags),q),
            K.read_block(A.thaw(tree),U32.add(index,16)),S.read_block(A.thaw(tree),U32.add(index,16)),R.read_block_correct(A.thaw(tree),U32.add(index,16))),
          Equal.cong(T.CV,Array<U32> & T.Out,c => S.chunk_blocks(p,t,U32.add(index,16),0,len,c,S.read_block(A.thaw(tree),U32.add(index,16))),
            C.compress(cv,b,t,64,flags),S.compress(cv,S.zero_tail(b,64n),t,64,flags),compress_full(cv,b,t,flags))))

law last_base:
  for +t: U32
  for +index: U32
  for +flags: U32
  for +len: Nat
  for +cv: T.CV
  for -a: Array<U32>
  for +b: T.Block
  {K.last_go(0n,t,index,flags,len,cv,(a,b)) == S.chunk_blocks(0n,t,index,flags,len,cv,(a,b)) : Array<U32> & T.Out}

def last_base(t,index,flags,len,cv,a,b):
  %R.mask_block_correct(b,len) : {(a,T.Out{cv,K.mask_block(b,len),t,U32.from_nat(len),U32.or(flags,2)}) == (a,T.Out{cv,_,t,U32.from_nat(len),U32.or(flags,2)}) : Array<U32> & T.Out}
  {==}

law last_go_correct:
  for +n: Nat
  for +t: U32
  for +index: U32
  for +flags: U32
  for +len: Nat
  for +cv: T.CV
  for pair: Array<U32> & T.Block
  {K.last_go(n,t,index,flags,len,cv,pair) == S.chunk_blocks(n,t,index,flags,len,cv,pair) : Array<U32> & T.Out}

def last_go_correct(n,t,index,flags,len,cv,pair):
  match n pair:
    case 0n Tuple{a,b}: last_base(t,index,flags,len,cv,a,b)
    case 1n+p Tuple{a,b}:
      last_step(p,t,index,flags,len,cv,a,b,A.reify(a),c => q => last_go_correct(p,t,U32.add(index,16),0,len,c,q))

# ---- full chunks ----

law full_step:
  for +p: Nat
  for +t: U32
  for +index: U32
  for +flags: U32
  for +cv: T.CV
  for -a: Array<U32>
  for +b: T.Block
  for view: Sigma<&2,&1,A.Tree,x => {a == A.thaw(x) : Array<U32>}>
  for recurse: @c: T.CV -> @q: (Array<U32> & T.Block) -> {K.full_go(p,t,U32.add(index,16),0,c,q) == outcv(S.chunk_blocks(p,t,U32.add(index,16),0,64n,c,q)) : Array<U32> & T.CV}
  {K.full_go(1n+p,t,index,flags,cv,(a,b)) == outcv(S.chunk_blocks(1n+p,t,index,flags,64n,cv,(a,b))) : Array<U32> & T.CV}

def full_step(p,t,index,flags,cv,a,b,view,recurse):
  match view:
    case Tuple{+tree,pf}:
      %Equal.sym(Array<U32>,a,A.thaw(tree),pf) : {K.full_go(1n+p,t,index,flags,cv,(_,b)) == outcv(S.chunk_blocks(1n+p,t,index,flags,64n,cv,(_,b))) : Array<U32> & T.CV}
      Equal.trans(Array<U32> & T.CV,
        K.full_go(p,t,U32.add(index,16),0,C.compress(cv,b,t,64,flags),K.read_block(A.thaw(tree),U32.add(index,16))),
        outcv(S.chunk_blocks(p,t,U32.add(index,16),0,64n,C.compress(cv,b,t,64,flags),K.read_block(A.thaw(tree),U32.add(index,16)))),
        outcv(S.chunk_blocks(p,t,U32.add(index,16),0,64n,S.compress(cv,S.zero_tail(b,64n),t,64,flags),S.read_block(A.thaw(tree),U32.add(index,16)))),
        recurse(C.compress(cv,b,t,64,flags),K.read_block(A.thaw(tree),U32.add(index,16))),
        Equal.trans(Array<U32> & T.CV,
          outcv(S.chunk_blocks(p,t,U32.add(index,16),0,64n,C.compress(cv,b,t,64,flags),K.read_block(A.thaw(tree),U32.add(index,16)))),
          outcv(S.chunk_blocks(p,t,U32.add(index,16),0,64n,C.compress(cv,b,t,64,flags),S.read_block(A.thaw(tree),U32.add(index,16)))),
          outcv(S.chunk_blocks(p,t,U32.add(index,16),0,64n,S.compress(cv,S.zero_tail(b,64n),t,64,flags),S.read_block(A.thaw(tree),U32.add(index,16)))),
          Equal.cong(Array<U32> & T.Block,Array<U32> & T.CV,q => outcv(S.chunk_blocks(p,t,U32.add(index,16),0,64n,C.compress(cv,b,t,64,flags),q)),
            K.read_block(A.thaw(tree),U32.add(index,16)),S.read_block(A.thaw(tree),U32.add(index,16)),R.read_block_correct(A.thaw(tree),U32.add(index,16))),
          Equal.cong(T.CV,Array<U32> & T.CV,c => outcv(S.chunk_blocks(p,t,U32.add(index,16),0,64n,c,S.read_block(A.thaw(tree),U32.add(index,16)))),
            C.compress(cv,b,t,64,flags),S.compress(cv,S.zero_tail(b,64n),t,64,flags),compress_full(cv,b,t,flags))))

law full_base:
  for +t: U32
  for +index: U32
  for +flags: U32
  for +cv: T.CV
  for -a: Array<U32>
  for +b: T.Block
  {K.full_go(0n,t,index,flags,cv,(a,b)) == outcv(S.chunk_blocks(0n,t,index,flags,64n,cv,(a,b))) : Array<U32> & T.CV}

def full_base(t,index,flags,cv,a,b):
  Equal.cong(T.CV,Array<U32> & T.CV,c => (a,c),C.compress(cv,b,t,64,U32.or(flags,2)),S.compress(cv,S.zero_tail(b,64n),t,64,U32.or(flags,2)),compress_full(cv,b,t,U32.or(flags,2)))

law full_go_correct:
  for +n: Nat
  for +t: U32
  for +index: U32
  for +flags: U32
  for +cv: T.CV
  for pair: Array<U32> & T.Block
  {K.full_go(n,t,index,flags,cv,pair) == outcv(S.chunk_blocks(n,t,index,flags,64n,cv,pair)) : Array<U32> & T.CV}

def full_go_correct(n,t,index,flags,cv,pair):
  match n pair:
    case 0n Tuple{a,b}: full_base(t,index,flags,cv,a,b)
    case 1n+p Tuple{a,b}:
      full_step(p,t,index,flags,cv,a,b,A.reify(a),c => q => full_go_correct(p,t,U32.add(index,16),0,c,q))

# ---- whole chunks ----

law full_chunk_view:
  for -a: Array<U32>
  for +t: U32
  for +index: U32
  for view: Sigma<&2,&1,A.Tree,x => {a == A.thaw(x) : Array<U32>}>
  {K.full_chunk(a,t,index) == outcv(S.chunk(a,t,index,1024n)) : Array<U32> & T.CV}

def full_chunk_view(a,t,index,view):
  match view:
    case Tuple{+tree,pf}:
      %Equal.sym(Array<U32>,a,A.thaw(tree),pf) : {K.full_chunk(_,t,index) == outcv(S.chunk(_,t,index,1024n)) : Array<U32> & T.CV}
      Equal.trans(Array<U32> & T.CV,
        K.full_go(15n,t,index,1,K.iv(),K.read_block(A.thaw(tree),index)),
        outcv(S.chunk_blocks(15n,t,index,1,64n,K.iv(),K.read_block(A.thaw(tree),index))),
        outcv(S.chunk_blocks(15n,t,index,1,64n,K.iv(),S.read_block(A.thaw(tree),index))),
        full_go_correct(15n,t,index,1,K.iv(),K.read_block(A.thaw(tree),index)),
        Equal.cong(Array<U32> & T.Block,Array<U32> & T.CV,q => outcv(S.chunk_blocks(15n,t,index,1,64n,K.iv(),q)),
          K.read_block(A.thaw(tree),index),S.read_block(A.thaw(tree),index),R.read_block_correct(A.thaw(tree),index)))

law full_chunk_correct:
  for a: Array<U32>
  for +t: U32
  for +index: U32
  {K.full_chunk(a,t,index) == outcv(S.chunk(a,t,index,1024n)) : Array<U32> & T.CV}

def full_chunk_correct(a,t,index):
  full_chunk_view(a,t,index,A.reify(a))

law last_chunk_view:
  for -a: Array<U32>
  for +t: U32
  for +index: U32
  for +len: Nat
  for view: Sigma<&2,&1,A.Tree,x => {a == A.thaw(x) : Array<U32>}>
  {K.last_chunk(a,t,index,len) == S.chunk(a,t,index,len) : Array<U32> & T.Out}

def last_chunk_view(a,t,index,len,view):
  match view:
    case Tuple{+tree,pf}:
      %Equal.sym(Array<U32>,a,A.thaw(tree),pf) : {K.last_chunk(_,t,index,len) == S.chunk(_,t,index,len) : Array<U32> & T.Out}
      Equal.trans(Array<U32> & T.Out,
        K.last_go(Nat.div(Nat.sub(len,1n),64n),t,index,1,Nat.sub(len,Nat.mul(Nat.div(Nat.sub(len,1n),64n),64n)),K.iv(),K.read_block(A.thaw(tree),index)),
        S.chunk_blocks(Nat.div(Nat.sub(len,1n),64n),t,index,1,Nat.sub(len,Nat.mul(Nat.div(Nat.sub(len,1n),64n),64n)),K.iv(),K.read_block(A.thaw(tree),index)),
        S.chunk_blocks(Nat.div(Nat.sub(len,1n),64n),t,index,1,Nat.sub(len,Nat.mul(Nat.div(Nat.sub(len,1n),64n),64n)),K.iv(),S.read_block(A.thaw(tree),index)),
        last_go_correct(Nat.div(Nat.sub(len,1n),64n),t,index,1,Nat.sub(len,Nat.mul(Nat.div(Nat.sub(len,1n),64n),64n)),K.iv(),K.read_block(A.thaw(tree),index)),
        Equal.cong(Array<U32> & T.Block,Array<U32> & T.Out,q => S.chunk_blocks(Nat.div(Nat.sub(len,1n),64n),t,index,1,Nat.sub(len,Nat.mul(Nat.div(Nat.sub(len,1n),64n),64n)),K.iv(),q),
          K.read_block(A.thaw(tree),index),S.read_block(A.thaw(tree),index),R.read_block_correct(A.thaw(tree),index)))

law last_chunk_correct:
  for a: Array<U32>
  for +t: U32
  for +index: U32
  for +len: Nat
  {K.last_chunk(a,t,index,len) == S.chunk(a,t,index,len) : Array<U32> & T.Out}

def last_chunk_correct(a,t,index,len):
  last_chunk_view(a,t,index,len,A.reify(a))
