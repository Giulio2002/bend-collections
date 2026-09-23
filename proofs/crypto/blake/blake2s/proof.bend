import Base
import ../../../../src/crypto/blake/blake2s/types.bend as T
import ../../../../src/crypto/blake/blake2s/blake2s.bend as K
import ./laws.bend as Laws
import ./compress.bend as P
import ./reads.bend as Q

# Entry point: `bend proofs/crypto/blake/blake2s/proof.bend` checks every law.
def Laws.blake2s(a,length): Q.blake2s_correct(a,length)

def Laws.compress(h,m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,t0,t1,last): P.compress_correct(h,m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,t0,t1,last)

def Laws.digest_size(s):
  match s:
    case T.H{h0,h1,h2,h3,h4,h5,h6,h7}: {==}

def Laws.capacity_rejection(a,n,capacity,invalid):
  Equal.cong(Bool,Maybe<&1,Array<U32>>,b => K.checked(b,a,n),Nat.is_le(n,Nat.mul(4n,U32.to_nat(capacity))),False{},invalid)
