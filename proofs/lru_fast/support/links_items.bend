# Retained proof dependency: history/retired-doubly-linked-list/proofs/dlist/items.bend
# Only declarations needed by the LRU refinement are kept; no retired runtime is imported.
# Proof-only dependency extracted from retained LRU support; no retired collection API.
import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../../spec/common.bend as SC
import links_state.bend as ST
import links_facts.bend as F

def lt_head(+x: Nat, +t: List<&2, Nat>, +n: Nat, +h: {ST.alllt(Con{x, t}, n) == True{} : Bool}) -> {Nat.is_lt(x, n) == True{} : Bool}:
  L.and_left(Nat.is_lt(x, n), ST.alllt(t, n), h)


def lt_tail(+x: Nat, +t: List<&2, Nat>, +n: Nat, +h: {ST.alllt(Con{x, t}, n) == True{} : Bool}) -> {ST.alllt(t, n) == True{} : Bool}:
  L.and_right(Nat.is_lt(x, n), ST.alllt(t, n), h)

# The spec compares ids as U32: exact below 2^depth.

def ueq(+p: Nat, +i: U32, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hp: {Nat.is_lt(p, SC.pow2(depth)) == True{} : Bool}) -> {U32.is_eq(U32.from_nat(p), i) == Nat.is_eq(p, U32.to_nat(i)) : Bool}:
  Equal.trans(Bool, U32.is_eq(U32.from_nat(p), i), Nat.is_eq(U32.to_nat(U32.from_nat(p)), U32.to_nat(i)), Nat.is_eq(p, U32.to_nat(i)),
    F.u32_eq_nat(U32.from_nat(p), i),
    Equal.cong(Nat, Bool, z => Nat.is_eq(z, U32.to_nat(i)), U32.to_nat(U32.from_nat(p)), p, F.id_nat(p, depth, hd, hp)))


def eq_nat_true(+a: Nat, +b: Nat, +h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  N.eq_from_is_eq(a, b, h)
