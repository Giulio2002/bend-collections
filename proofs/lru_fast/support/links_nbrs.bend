# Retained proof dependency: history/retired-doubly-linked-list/proofs/dlist/nbrs.bend
# Only declarations needed by the LRU refinement are kept; no retired runtime is imported.
# Proof-only dependency extracted from retained LRU support; no retired collection API.
import Base
import ../../lib/logic.bend as L
import array_nbrops.bend as NO
import links_state.bend as ST

def ueq_true(+a: U32, +b: U32, +h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  NO.is_eq_eq(a, b, h)

# The handle a link denotes, against the spec's handle of the linked id.

def lmem_nil(+n: Nat, +h: {ST.lmem(n, Nil{}) == True{} : Bool}) -> Empty:
  L.false_true(h)
