import Base
import ../state.bend as S
import ./packed.bend as P

# Exactly eight big-endian U32 words (32 bytes), with no list allocation.
def digest(s: S.State) -> Array<U32>:
  match s:
    case S.H{a,b,c,d,e,f,g,h}:
      ANode{ANode{ANode{ALeaf{a},ALeaf{b}},ANode{ALeaf{c},ALeaf{d}}},ANode{ANode{ALeaf{e},ALeaf{f}},ANode{ALeaf{g},ALeaf{h}}}}

def result(r: Maybe<&2,S.State>) -> Maybe<&1,Array<U32>>:
  match r:
    case None{}: None{}
    case Some{s}: Some{digest(s)}

def sha256(input: Array<U32>, length: Nat) -> Maybe<&1,Array<U32>>:
  result(P.hash(input,length))
