# Retained proof dependency: history/retired-doubly-linked-list/proofs/dlist/facts.bend
# Only declarations needed by the LRU refinement are kept; no retired runtime is imported.
# Proof-only dependency extracted from retained LRU support; no retired collection API.
import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/u32.bend as U
import ../../binary_heap/u32idx.bend as IX
import ../../../spec/common.bend as SC
import link_primitives.bend as D
import links_state.bend as ST

def u32_eq_nat(+a: U32, +b: U32) -> {U32.is_eq(a, b) == Nat.is_eq(U32.to_nat(a), U32.to_nat(b)) : Bool}:
  Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), U.u32_cmp(a, b))

# p < 2^depth, depth <= 31: the id and its link are exact.

def id_nat(+p: Nat, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hp: {Nat.is_lt(p, SC.pow2(depth)) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(p)) == p : Nat}:
  IX.nat_round(p, depth, N.le_trans(depth, 31n, 32n, hd, N.le_succ(31n)), hp)


def ln_nat(+p: Nat, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hp: {Nat.is_lt(p, SC.pow2(depth)) == True{} : Bool}) -> {U32.to_nat(ST.ln(p)) == 1n+p : Nat}:
  IX.nat_round(1n+p, 1n+depth, hd, N.le_lt_trans(1n+p, SC.pow2(depth), SC.pow2(1n+depth), N.lt_succ_le_succ(p, SC.pow2(depth), hp), N.pow2_lt_succ(depth)))

# A link is never nil.

def ln_ne_nil(+p: Nat, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hp: {Nat.is_lt(p, SC.pow2(depth)) == True{} : Bool}) -> {U32.is_eq(ST.ln(p), D.nil()) == False{} : Bool}:
  Equal.trans(Bool, U32.is_eq(ST.ln(p), D.nil()), Nat.is_eq(U32.to_nat(ST.ln(p)), U32.to_nat(D.nil())), False{},
    u32_eq_nat(ST.ln(p), D.nil()),
    L.subst(Nat, z => {Nat.is_eq(z, U32.to_nat(D.nil())) == False{} : Bool}, 1n+p, U32.to_nat(ST.ln(p)), Equal.sym(Nat, U32.to_nat(ST.ln(p)), 1n+p, ln_nat(p, depth, hd, hp)), {==}))

# Following a link: slot(ln p) is the id p.

def slot_ln(+p: Nat, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hp: {Nat.is_lt(p, SC.pow2(depth)) == True{} : Bool}) -> {D.slot(ST.ln(p)) == U32.from_nat(p) : U32}:
  Equal.trans(U32, U32.sub(U32.from_nat(1n+p), 1), U32.from_nat(Nat.sub(1n+p, 1n)), U32.from_nat(p),
    IX.sub_one(1n+p, 1n+depth, hd, N.le_lt_trans(1n+p, SC.pow2(depth), SC.pow2(1n+depth), N.lt_succ_le_succ(p, SC.pow2(depth), hp), N.pow2_lt_succ(depth)), N.lt_succ_le_succ(0n, 1n+p, {==})),
    Equal.cong(Nat, U32, z => U32.from_nat(z), Nat.sub(1n+p, 1n), p, N.sub_zero(p)))

# The link to a runtime id x that stands for p.
