import Base
import ../../../../spec/crypto/sha.bend as F
import ../../../../src/crypto/sha/packed/buffer.bend as B
import ../../../../src/crypto/sha/packed/packed.bend as P
import ../../../../spec/crypto/sha/packed.bend as R
import ./packed_proof.bend as Proof
import ./packed_array_proof.bend as A
import ../../../../src/crypto/sha/state.bend as S
import ../../../../src/crypto/sha/packed/sha256.bend as SHA

law correct:
  for a: Array<U32>
  for +length: Nat
  {SHA.sha256(a,length) == B.result(R.hash(a,length)) : Maybe<&1,Array<U32>>}

def correct(a,length):
  Equal.cong(Maybe<&2,S.State>,Maybe<&1,Array<U32>>,r => B.result(r),
    P.hash(a,length),R.hash(a,length),Proof.hash_correct(a,length))

law digest_size:
  for s: S.State
  {Pair.snd(Array<U32>,U32,Array.size(U32,B.digest(s))) == 8 : U32}

def digest_size(s):
  match s:
    case S.H{a,b,c,d,e,f,g,h}: {==}

# Proof-only observation; never called by the buffer hashing API.
def words(a: Array<U32>) -> List<&2,U32>:
  match a:
    case ALeaf{x}: [x]
    case ANode{l,r}: List.append(&2,U32,words(l),words(r))

law digest_words:
  for +s: S.State
  {words(B.digest(s)) == F.digest(s) : List<&2,U32>}

def digest_words(s):
  match s:
    case S.H{a,b,c,d,e,f,g,h}: {==}

# Full public-result observation against the independent packed specification.
def observe(r: Maybe<&1,Array<U32>>) -> Maybe<&2,List<&2,U32>>:
  match r:
    case None{}: None{}
    case Some{a}: Some{words(a)}

law observe_digest:
  for +r: Maybe<&2,S.State>
  {observe(B.result(r)) == R.digest_result(r) : Maybe<&2,List<&2,U32>>}

def observe_digest(r):
  match r:
    case None{}: {==}
    case Some{s}:
      Equal.cong(List<&2,U32>,Maybe<&2,List<&2,U32>>,ws => Some{ws},
        words(B.digest(s)),F.digest(s),digest_words(s))

law full_reified:
  for -a: Array<U32>
  for +length: Nat
  for view: Sigma<&2,&1,A.Tree,t => {a == A.thaw(t) : Array<U32>}>
  {observe(SHA.sha256(a,length)) == R.sha256(a,length) : Maybe<&2,List<&2,U32>>}

def full_reified(a,length,view):
  match view:
    case Tuple{+tree,pf}:
      %Equal.sym(Array<U32>,a,A.thaw(tree),pf) : {observe(SHA.sha256(_,length)) == R.sha256(_,length) : Maybe<&2,List<&2,U32>>}
      Equal.trans(Maybe<&2,List<&2,U32>>,
        observe(SHA.sha256(A.thaw(tree),length)),
        observe(B.result(R.hash(A.thaw(tree),length))),
        R.sha256(A.thaw(tree),length),
        Equal.cong(Maybe<&1,Array<U32>>,Maybe<&2,List<&2,U32>>,r => observe(r),
          SHA.sha256(A.thaw(tree),length),B.result(R.hash(A.thaw(tree),length)),correct(A.thaw(tree),length)),
        observe_digest(R.hash(A.thaw(tree),length)))

law full_correct:
  for a: Array<U32>
  for +length: Nat
  {observe(SHA.sha256(a,length)) == R.sha256(a,length) : Maybe<&2,List<&2,U32>>}

def full_correct(a,length):
  full_reified(a,length,A.reify(a))
