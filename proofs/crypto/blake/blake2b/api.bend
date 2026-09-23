import Base
import ../../../../src/crypto/blake/blake2b/types.bend as T
import ../../../../src/crypto/blake/blake2b/blake2b.bend as I

law digest_size:
  for h: T.Chain
  {Pair.snd(Array<U32>,U32,Array.size(U32,I.digest(h))) == 16 : U32}

def digest_size(h):
  match h:
    case T.H{T.W{l0,u0},T.W{l1,u1},T.W{l2,u2},T.W{l3,u3},T.W{l4,u4},T.W{l5,u5},T.W{l6,u6},T.W{l7,u7}}: {==}

law capacity_gate:
  for a: Array<U32>
  for +n: Nat
  for +capacity: U32
  for invalid: {Nat.is_le(n,Nat.mul(4n,U32.to_nat(capacity))) == False{} : Bool}
  {I.sized(n,(a,capacity)) == None{} : Maybe<&1,Array<U32>>}

def capacity_gate(a,n,capacity,invalid):
  Equal.cong(Bool,Maybe<&1,Array<U32>>,b => I.checked(b,a,n),
    Nat.is_le(n,Nat.mul(4n,U32.to_nat(capacity))),False{},invalid)
