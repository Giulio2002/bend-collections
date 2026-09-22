# Retained proof dependency: bend-collections@87deb98^:proofs/graph/nbrops.bend
# Only declarations needed by the LRU refinement are kept; no retired runtime is imported.
# Proof-only dependency extracted from retained LRU support; no retired collection API.
import Base
import ../../lib/logic.bend as L
import ../../lib/order.bend as O

def is_eq_cmp(+c: Cmp, +h: {Cmp.is_eq(c) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, L.false_true(h))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, L.false_true(h))

# Replacing a present Unit entry by itself changes nothing.

def is_eq_eq(+a: U32, +b: U32, +h: {Cmp.is_eq(U32.cmp(a, b)) == True{} : Bool}) -> {a == b : U32}:
  O.u32_antisym(a, b, is_eq_cmp(U32.cmp(a, b), h))
