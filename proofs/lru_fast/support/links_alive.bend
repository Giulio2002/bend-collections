# Retained proof dependency: history/retired-doubly-linked-list/proofs/dlist/alive.bend
# Only declarations needed by the LRU refinement are kept; no retired runtime is imported.
# Proof-only dependency extracted from retained LRU support; no retired collection API.
import Base
import ../../lib/nat.bend as N

def or_true_r(a: Bool, +b: Bool, +h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h


def lmem_self(+y: Nat) -> {Nat.is_eq(y, y) == True{} : Bool}:
  N.is_eq_refl(y)
