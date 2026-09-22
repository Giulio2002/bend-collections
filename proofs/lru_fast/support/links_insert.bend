# Retained proof dependency: history/retired-doubly-linked-list/proofs/dlist/insert.bend
# Only declarations needed by the LRU refinement are kept; no retired runtime is imported.
# Proof-only dependency extracted from retained LRU support; no retired collection API.
import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/array.bend as AR
import array_ashift.bend as AS2
import ../../../spec/common.bend as SC
import links_facts.bend as F
import array_zip.bend as ZP

def set_f(-A: Data, +depth: Nat, +t: AR.Tree<A>, +f: Nat, +w: A, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hr: {Nat.is_lt(f, SC.pow2(depth)) == True{} : Bool}, +pf: {AR.perfect(A, depth, t) == True{} : Bool}) -> {Array.set(A, AR.thaw(A, t), U32.from_nat(f), w) == AR.thaw(A, AR.upd(A, depth, t, f, w)) : Array<A>}:
  +hid = F.id_nat(f, depth, hd, hr)
  +hi = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(depth)) == True{} : Bool}, f, U32.to_nat(U32.from_nat(f)), Equal.sym(Nat, U32.to_nat(U32.from_nat(f)), f, hid), hr)
  Equal.trans(Array<A>, Array.set(A, AR.thaw(A, t), U32.from_nat(f), w), AR.thaw(A, AR.upd(A, depth, t, U32.to_nat(U32.from_nat(f)), w)), AR.thaw(A, AR.upd(A, depth, t, f, w)),
    AR.set(A, depth, t, U32.from_nat(f), w, ZP.vget(A, w, AR.slots(A, t), U32.to_nat(U32.from_nat(f))), N.le_lt_trans(depth, 31n, 32n, hd, N.lt_succ(31n)), hi, AS2.tsat(A, depth, t, U32.to_nat(U32.from_nat(f)), w, pf, hi), pf),
    Equal.cong(Nat, Array<A>, z => AR.thaw(A, AR.upd(A, depth, t, z, w)), U32.to_nat(U32.from_nat(f)), f, hid))
