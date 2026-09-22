# Retained proof dependency: bend-collections@87deb98^:proofs/graph/shift.bend
# Only declarations needed by the LRU refinement are kept; no retired runtime is imported.
# Proof-only dependency extracted from retained LRU support; no retired collection API.
import Base
import ../../lib/nat.bend as N

def ne_of_lt_go(+i: Nat, +j: Nat, +h: {Nat.is_lt(i, j) == True{} : Bool}, e: Bool, +ee: {Nat.is_eq(i, j) == e : Bool}) -> {Nat.is_eq(i, j) == False{} : Bool}:
  match e:
    case False{}:
      ee
    case True{}:
      Empty.absurd({Nat.is_eq(i, j) == False{} : Bool}, N.lt_ne(i, j, h, N.eq_from_is_eq(i, j, ee)))

# One mirror update, seen through `nth`.

def ne_of_lt(+i: Nat, +j: Nat, +h: {Nat.is_lt(i, j) == True{} : Bool}) -> {Nat.is_eq(i, j) == False{} : Bool}:
  ne_of_lt_go(i, j, h, Nat.is_eq(i, j), {==})


def ne_flip(+i: Nat, +j: Nat, +h: {Nat.is_eq(i, j) == False{} : Bool}) -> {Nat.is_eq(j, i) == False{} : Bool}:
  match i j:
    case 0n 0n:
      h
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ne_flip(p, q, h)
