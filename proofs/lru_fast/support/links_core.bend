# Retained proof dependency: history/retired-doubly-linked-list/proofs/dlist/core.bend
# Only declarations needed by the LRU refinement are kept; no retired runtime is imported.
# Proof-only dependency extracted from retained LRU support; no retired collection API.
import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import array_shift.bend as SH
import links_state.bend as ST
import links_items.bend as IT

def alllt_mono(+xs: List<&2, Nat>, +a: Nat, +b: Nat, +hab: {Nat.is_le(a, b) == True{} : Bool}, +h: {ST.alllt(xs, a) == True{} : Bool}) -> {ST.alllt(xs, b) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.and_intro(Nat.is_lt(x, b), ST.alllt(t, b), N.lt_le_trans(x, a, b, IT.lt_head(x, t, a, h), hab), alllt_mono(t, a, b, hab, IT.lt_tail(x, t, a, h)))


def lmem_ge(+xs: List<&2, Nat>, +n: Nat, +i: Nat, +h: {ST.alllt(xs, n) == True{} : Bool}, +hi: {Nat.is_le(n, i) == True{} : Bool}) -> {ST.lmem(i, xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +e1 = SH.ne_of_lt(x, i, N.lt_le_trans(x, n, i, IT.lt_head(x, t, n, h), hi))
      L.subst(Bool, b => {Bool.or(b, ST.lmem(i, t)) == False{} : Bool}, False{}, Nat.is_eq(x, i), Equal.sym(Bool, Nat.is_eq(x, i), False{}, e1), lmem_ge(t, n, i, IT.lt_tail(x, t, n, h), hi))

# A handle below fresh: the model's lookup is the value arena.
