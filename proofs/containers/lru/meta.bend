import Base
import ../../lib/logic.bend as L
import ../../lib/array.bend as AR
import ../../../spec/lib/common.bend as SC
import ../../lib/u32div.bend as UD
import ./state.bend as ST
import ../../lib/words32.bend as W32
import ../../lib/u32_tree.bend as UT

# Arrays through their mirror trees, and updates of the meta words m.


# ---- arrays ----


# a U32 array read

# a U32 array write: the new tree, still perfect, with its slots updated
def uset(+d: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +t: AR.Tree<U32>, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +i: U32, +hi: {Nat.is_lt(UD.v(i), SC.pow2(d)) == True{} : Bool}, +x: U32) -> {Array.set(U32, AR.thaw(U32, t), i, x) == AR.thaw(U32, AR.upd(U32, d, t, UD.v(i), x)) : Array<U32>} & ({AR.perfect(U32, d, AR.upd(U32, d, t, UD.v(i), x)) == True{} : Bool} & {AR.slots(U32, AR.upd(U32, d, t, UD.v(i), x)) == SC.update(U32, AR.slots(U32, t), UD.v(i), x) : List<&2, U32>}):
  (AR.set(U32, d, t, i, x, W32.nth0(AR.slots(U32, t), UD.v(i)), hd, hi, W32.nth_some(AR.slots(U32, t), UD.v(i), UT.len_of(U32, d, t, pf, UD.v(i), hi)), pf), (AR.upd_perfect(U32, d, t, UD.v(i), x, pf), AR.upd_slots(U32, d, t, UD.v(i), x, hi, pf)))

# nth0 after an update elsewhere, and at the update
def nth_other(+t: AR.Tree<U32>, +i: Nat, +x: U32, +t2: AR.Tree<U32>, +hs: {AR.slots(U32, t2) == SC.update(U32, AR.slots(U32, t), i, x) : List<&2, U32>}, +j: Nat, +hne: {Nat.is_eq(i, j) == False{} : Bool}) -> {W32.nth0(AR.slots(U32, t2), j) == W32.nth0(AR.slots(U32, t), j) : U32}:
  Equal.trans(U32, W32.nth0(AR.slots(U32, t2), j), W32.nth0(SC.update(U32, AR.slots(U32, t), i, x), j), W32.nth0(AR.slots(U32, t), j), Equal.cong(List<&2, U32>, U32, z => W32.nth0(z, j), AR.slots(U32, t2), SC.update(U32, AR.slots(U32, t), i, x), hs), W32.nth0_upd_other(AR.slots(U32, t), i, j, x, hne))

def nth_same(+d: Nat, +t: AR.Tree<U32>, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +x: U32, +t2: AR.Tree<U32>, +hs: {AR.slots(U32, t2) == SC.update(U32, AR.slots(U32, t), i, x) : List<&2, U32>}) -> {W32.nth0(AR.slots(U32, t2), i) == x : U32}:
  Equal.trans(U32, W32.nth0(AR.slots(U32, t2), i), W32.nth0(SC.update(U32, AR.slots(U32, t), i, x), i), x, Equal.cong(List<&2, U32>, U32, z => W32.nth0(z, i), AR.slots(U32, t2), SC.update(U32, AR.slots(U32, t), i, x), hs), W32.nth0_upd_same(AR.slots(U32, t), i, x, UT.len_of(U32, d, t, pf, i, hi)))

# ---- the invariant under a meta tree with the same five words ----

def good_m(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +mT2: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +sl: List<&2, Nat>, +fl: List<&2, Nat>, +hg: {ST.good(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}) == True{} : Bool}, +e0: {W32.nth0(AR.slots(U32, mT2), 0n) == W32.nth0(AR.slots(U32, mT), 0n) : U32}, +e1: {W32.nth0(AR.slots(U32, mT2), 1n) == W32.nth0(AR.slots(U32, mT), 1n) : U32}, +e2: {W32.nth0(AR.slots(U32, mT2), 2n) == W32.nth0(AR.slots(U32, mT), 2n) : U32}, +e6: {W32.nth0(AR.slots(U32, mT2), 6n) == W32.nth0(AR.slots(U32, mT), 6n) : U32}, +e7: {W32.nth0(AR.slots(U32, mT2), 7n) == W32.nth0(AR.slots(U32, mT), 7n) : U32}, +hp: {AR.perfect(U32, 5n, mT2) == True{} : Bool}) -> {ST.good(~V, ST.LS{cap, n, head, tail, free, mT2, k, sd, tabT, ksT, eT, lkT, sl, fl}) == True{} : Bool}:
  +pm = ST.g_cpm(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg)
  +epm = Equal.trans(Bool, AR.perfect(U32, 5n, mT), True{}, AR.perfect(U32, 5n, mT2), pm, Equal.sym(Bool, AR.perfect(U32, 5n, mT2), True{}, hp))
  +g1 = L.subst(U32, z => {ST.goodF(~V, cap, n, head, tail, free,  z, W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl) == True{} : Bool}, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT2), 0n), Equal.sym(U32, W32.nth0(AR.slots(U32, mT2), 0n), W32.nth0(AR.slots(U32, mT), 0n), e0), hg)
  +g2 = L.subst(U32, z => {ST.goodF(~V, cap, n, head, tail, free,  W32.nth0(AR.slots(U32, mT2), 0n), z, W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl) == True{} : Bool}, W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT2), 1n), Equal.sym(U32, W32.nth0(AR.slots(U32, mT2), 1n), W32.nth0(AR.slots(U32, mT), 1n), e1), g1)
  +g3 = L.subst(U32, z => {ST.goodF(~V, cap, n, head, tail, free,  W32.nth0(AR.slots(U32, mT2), 0n), W32.nth0(AR.slots(U32, mT2), 1n), z, W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl) == True{} : Bool}, W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT2), 2n), Equal.sym(U32, W32.nth0(AR.slots(U32, mT2), 2n), W32.nth0(AR.slots(U32, mT), 2n), e2), g2)
  +g4 = L.subst(U32, z => {ST.goodF(~V, cap, n, head, tail, free,  W32.nth0(AR.slots(U32, mT2), 0n), W32.nth0(AR.slots(U32, mT2), 1n), W32.nth0(AR.slots(U32, mT2), 2n), z, W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl) == True{} : Bool}, W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT2), 6n), Equal.sym(U32, W32.nth0(AR.slots(U32, mT2), 6n), W32.nth0(AR.slots(U32, mT), 6n), e6), g3)
  +g5 = L.subst(U32, z => {ST.goodF(~V, cap, n, head, tail, free,  W32.nth0(AR.slots(U32, mT2), 0n), W32.nth0(AR.slots(U32, mT2), 1n), W32.nth0(AR.slots(U32, mT2), 2n), W32.nth0(AR.slots(U32, mT2), 6n), z, AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl) == True{} : Bool}, W32.nth0(AR.slots(U32, mT), 7n), W32.nth0(AR.slots(U32, mT2), 7n), Equal.sym(U32, W32.nth0(AR.slots(U32, mT2), 7n), W32.nth0(AR.slots(U32, mT), 7n), e7), g4)
  L.subst(Bool, z => {ST.goodF(~V, cap, n, head, tail, free,  W32.nth0(AR.slots(U32, mT2), 0n), W32.nth0(AR.slots(U32, mT2), 1n), W32.nth0(AR.slots(U32, mT2), 2n), W32.nth0(AR.slots(U32, mT2), 6n), W32.nth0(AR.slots(U32, mT2), 7n), z, k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl) == True{} : Bool}, AR.perfect(U32, 5n, mT), AR.perfect(U32, 5n, mT2), epm, g5)



