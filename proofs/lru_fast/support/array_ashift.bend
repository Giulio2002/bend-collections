# Retained proof dependency: bend-collections@87deb98^:proofs/graph/ashift.bend
# Only declarations needed by the LRU refinement are kept; no retired runtime is imported.
# Proof-only dependency extracted from retained LRU support; no retired collection API.
import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/array.bend as AR
import ../../../spec/common.bend as SC
import array_zip.bend as ZP

def sat(-T: Data, +xs: List<&2, T>, +i: Nat, +d: T, +h: {Nat.is_lt(i, SC.length(T, xs)) == True{} : Bool}) -> {SC.nth(T, xs, i) == Some{ZP.vget(T, d, xs, i)} : Maybe<&2, T>}:
  match xs i:
    case Nil{} i0:
      Empty.absurd({SC.nth(T, Nil{}, i0) == Some{ZP.vget(T, d, Nil{}, i0)} : Maybe<&2, T>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(i0, 0n), True{}, Equal.sym(Bool, Nat.is_lt(i0, 0n), False{}, N.not_lt_zero(i0)), h)))
    case Con{+hh, +t} 0n:
      {==}
    case Con{+hh, +t} 1n+p:
      sat(T, t, p, d, h)


def tsat(-T: Data, +dp: Nat, +t: AR.Tree<T>, +i: Nat, +d: T, +pf: {AR.perfect(T, dp, t) == True{} : Bool}, +h: {Nat.is_lt(i, SC.pow2(dp)) == True{} : Bool}) -> {SC.nth(T, AR.slots(T, t), i) == Some{ZP.vget(T, d, AR.slots(T, t), i)} : Maybe<&2, T>}:
  sat(T, AR.slots(T, t), i, d, AR.len_lt(T, dp, t, i, pf, h))

# ---- the id table ----
