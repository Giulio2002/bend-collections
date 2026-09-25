import Base
import ../../../../src/crypto/blake/blake3/types.bend as T
import ../../../../src/crypto/blake/blake3/blake3.bend as K
import ../../../../spec/lib/common.bend as SC
import ../../../../spec/crypto/blake/blake3.bend as S
import ./array.bend as A
import ./compress.bend as P
import ./loop.bend as LP

# BLAKE3 public API theorem: for every packed input array and every
# byte_length, the implementation's blake3 equals the specification's
# (spec/crypto/blake/blake3.bend), including the rejection of lengths
# past 4 * capacity. No axioms, no holes.
#
# The chain: compress.bend (the unrolled compression function is the list
# specification's), read.bend (block reads and the final-block mask),
# chunk.bend (chunk loops), tree.bend (the subtree stack computes the
# specification's tree), loop.bend (the chunk loop runs the stack over the
# specification's chunk list), and here the root, the digest and the API.

law root_correct:
  for +o: T.Out
  {K.root_cv(o) == S.root(o) : T.CV}

def root_correct(o):
  match o:
    case T.Out{+c,+b,+t,+len,+flags}: P.compress_correct(c,b,t,len,U32.or(flags,8))

law unchecked_view:
  for -a: Array<U32>
  for +length: Nat
  for view: Sigma<&2,&1,A.Tree,x => {a == A.thaw(x) : Array<U32>}>
  {K.unchecked(a,length) == S.hash(a,length) : T.CV}

def unchecked_view(a,length,view):
  match view:
    case Tuple{+tree,pf}:
      +n = Nat.div(Nat.sub(length,1n),1024n)
      +last = Nat.sub(length,Nat.mul(n,1024n))
      +cs = S.chunks(n,0,0,last,S.chunk_at(n,0,0,last,A.thaw(tree)))
      %Equal.sym(Array<U32>,a,A.thaw(tree),pf) : {K.unchecked(_,length) == S.hash(_,length) : T.CV}
      Equal.trans(T.CV,
        K.root_cv(K.chunks(n,0,0,last,(A.thaw(tree),K.StkNil{}))),
        K.root_cv(LP.run(K.StkNil{},cs)),
        S.root(S.tree(SC.length(T.Out,cs),cs)),
        Equal.cong(T.Out,T.CV,o => K.root_cv(o),K.chunks(n,0,0,last,(A.thaw(tree),K.StkNil{})),LP.run(K.StkNil{},cs),LP.fuse(n,0,0,last,A.thaw(tree),K.StkNil{})),
        Equal.trans(T.CV,
          K.root_cv(LP.run(K.StkNil{},cs)),
          K.root_cv(S.tree(SC.length(T.Out,cs),cs)),
          S.root(S.tree(SC.length(T.Out,cs),cs)),
          Equal.cong(T.Out,T.CV,o => K.root_cv(o),LP.run(K.StkNil{},cs),S.tree(SC.length(T.Out,cs),cs),LP.run_chunks(n,0,0,last,S.chunk_at(n,0,0,last,A.thaw(tree)))),
          root_correct(S.tree(SC.length(T.Out,cs),cs))))

law digest_correct:
  for +c: T.CV
  {K.digest(c) == S.digest(c) : Array<U32>}

def digest_correct(c):
  match c:
    case T.CV{h0,h1,h2,h3,h4,h5,h6,h7}: {==}

law checked_view:
  for -a: Array<U32>
  for +length: Nat
  for view: Sigma<&2,&1,A.Tree,x => {a == A.thaw(x) : Array<U32>}>
  {K.checked(True{},a,length) == S.checked(True{},a,length) : Maybe<&1,Array<U32>>}

def checked_view(a,length,view):
  match view:
    case Tuple{+tree,pf}:
      %Equal.sym(Array<U32>,a,A.thaw(tree),pf) : {K.checked(True{},_,length) == S.checked(True{},_,length) : Maybe<&1,Array<U32>>}
      Equal.trans(Maybe<&1,Array<U32>>,
        Some{K.digest(K.unchecked(A.thaw(tree),length))},
        Some{K.digest(S.hash(A.thaw(tree),length))},
        Some{S.digest(S.hash(A.thaw(tree),length))},
        Equal.cong(T.CV,Maybe<&1,Array<U32>>,c => Some{K.digest(c)},K.unchecked(A.thaw(tree),length),S.hash(A.thaw(tree),length),unchecked_view(A.thaw(tree),length,A.reify(A.thaw(tree)))),
        Equal.cong(Array<U32>,Maybe<&1,Array<U32>>,d => Some{d},K.digest(S.hash(A.thaw(tree),length)),S.digest(S.hash(A.thaw(tree),length)),digest_correct(S.hash(A.thaw(tree),length))))

law checked_correct:
  for +valid: Bool
  for a: Array<U32>
  for +length: Nat
  {K.checked(valid,a,length) == S.checked(valid,a,length) : Maybe<&1,Array<U32>>}

def checked_correct(valid,a,length):
  match valid:
    case False{}: {==}
    case True{}: checked_view(a,length,A.reify(a))

law sized_correct:
  for +length: Nat
  for pair: Array<U32> & U32
  {K.sized(length,pair) == S.sized(length,pair) : Maybe<&1,Array<U32>>}

def sized_correct(length,pair):
  (a,capacity) = pair
  checked_correct(Nat.is_le(length,Nat.mul(4n,U32.to_nat(capacity))),a,length)

# The public API: for every packed word array and every byte length.
law blake3_correct:
  for words: Array<U32>
  for +byte_length: Nat
  {K.blake3(words,byte_length) == S.blake3(words,byte_length) : Maybe<&1,Array<U32>>}

def blake3_correct(words,byte_length):
  sized_correct(byte_length,Array.size(U32,words))

# Rejection: a length past 4 * capacity gives None.
law blake3_rejects:
  for a: Array<U32>
  for +n: Nat
  for +capacity: U32
  for invalid: {Nat.is_le(n,Nat.mul(4n,U32.to_nat(capacity))) == False{} : Bool}
  {K.sized(n,(a,capacity)) == None{} : Maybe<&1,Array<U32>>}

def blake3_rejects(a,n,capacity,invalid):
  Equal.cong(Bool,Maybe<&1,Array<U32>>,b => K.checked(b,a,n),Nat.is_le(n,Nat.mul(4n,U32.to_nat(capacity))),False{},invalid)

# The digest is eight words.
law digest_size:
  for +c: T.CV
  {Pair.snd(Array<U32>,U32,Array.size(U32,K.digest(c))) == 8 : U32}

def digest_size(c):
  match c:
    case T.CV{h0,h1,h2,h3,h4,h5,h6,h7}: {==}
