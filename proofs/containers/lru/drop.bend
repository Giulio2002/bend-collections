import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/array.bend as AR
import ../../lib/spec_common.bend as SC
import ../../lib/u32div.bend as UD
import ../../../src/containers/hash_table.bend as H
import ../../../src/containers/lru.bend as LR
import ../hash_table/state.bend as HT
import ./state.bend as ST
import ./idx.bend as ID
import ./unlink.bend as UL
import ../../lib/u32_tree.bend as UT

# drop_core: a detached slot's value is taken out, the slot is pushed on the
# free list, the count goes down and counter c goes up.


# THEOREM (drop_core)
def drop_ok(~V: Data, +one: Nat, +h1: {one == 1n : Nat}, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +sd: Nat, +hsd: {Nat.is_lt(3n+sd, 32n) == True{} : Bool}, +hpl: {AR.perfect(U32, 3n+sd, lkT) == True{} : Bool}, +hpe: {AR.perfect(Maybe<&2, V>, sd, eT) == True{} : Bool}, +su: U32, +s: Nat, +hsv: {UD.v(su) == s : Nat}, +hs0: {Nat.is_lt(s, SC.pow2(sd)) == True{} : Bool}, +c: U32) -> {LR.drop_core(&2, V, LR.F{cap, n, head, tail, free, AR.thaw(U32, mT), AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, su, c) == (LR.fbump(&2, V, c, LR.F{cap, U32.sub(n, 1), head, tail, H.link(su), AR.thaw(U32, mT), AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, AR.upd(Maybe<&2, V>, sd, eT, UD.v(su), None{})), AR.thaw(U32, AR.upd(U32, 3n+sd, lkT, UD.v(LR.nidx(su)), free))}), HT.nthm(~V, AR.slots(Maybe<&2, V>, eT), s)) : LR.LRU<&2, V> & Maybe<&2, V>}:
  +hsu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(sd)) == True{} : Bool}, s, UD.v(su), Equal.sym(Nat, UD.v(su), s, hsv), hs0)
  +hd = N.lt_trans(sd, 3n+sd, 32n, N.lt_le_trans(sd, 1n+sd, 3n+sd, N.lt_succ(sd), N.le_trans(1n+sd, 2n+sd, 3n+sd, N.le_succ(1n+sd), N.le_succ(2n+sd))), hsd)
  +hx = HT.nthm_some(~V, AR.slots(Maybe<&2, V>, eT), UD.v(su), UT.len_of(Maybe<&2, V>, sd, eT, hpe, UD.v(su), hsu))
  +es = AR.swap(Maybe<&2, V>, sd, eT, su, None{}, HT.nthm(~V, AR.slots(Maybe<&2, V>, eT), UD.v(su)), hd, hsu, hx, hpe)
  +iN = Equal.trans(Nat, UD.v(LR.nidx(su)), ST.off(UD.v(su), 1n), ST.off(s, 1n), ID.w1(one, h1, su, sd, UL.sd3(sd, hsd), hsu), Equal.cong(Nat, Nat, z => ST.off(z, 1n), UD.v(su), s, hsv))
  +el = UL.wr(one, h1, lkT, sd, hsd, hpl, LR.nidx(su), s, 1n, {==}, hs0, iN, free)
  +E1 = Equal.cong(Array<Maybe<&2, V>> & Maybe<&2, V>, LR.LRU<&2, V> & Maybe<&2, V>, r => LR.drop_e(&2, V, cap, n, head, tail, free, AR.thaw(U32, mT), AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(U32, lkT), su, c, r), Array.swap(Maybe<&2, V>, AR.thaw(Maybe<&2, V>, eT), su, None{}), (AR.thaw(Maybe<&2, V>, AR.upd(Maybe<&2, V>, sd, eT, UD.v(su), None{})), HT.nthm(~V, AR.slots(Maybe<&2, V>, eT), UD.v(su))), es)
  +E2 = Equal.cong(Array<U32>, LR.LRU<&2, V> & Maybe<&2, V>, z => (LR.F{cap, U32.sub(n, 1), head, tail, H.link(su), LR.bump(c, AR.thaw(U32, mT)), AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, AR.upd(Maybe<&2, V>, sd, eT, UD.v(su), None{})), z}, HT.nthm(~V, AR.slots(Maybe<&2, V>, eT), UD.v(su))), Array.set(U32, AR.thaw(U32, lkT), LR.nidx(su), free), AR.thaw(U32, AR.upd(U32, 3n+sd, lkT, UD.v(LR.nidx(su)), free)), el)
  +E3 = Equal.cong(Nat, LR.LRU<&2, V> & Maybe<&2, V>, z => (LR.fbump(&2, V, c, LR.F{cap, U32.sub(n, 1), head, tail, H.link(su), AR.thaw(U32, mT), AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, AR.upd(Maybe<&2, V>, sd, eT, UD.v(su), None{})), AR.thaw(U32, AR.upd(U32, 3n+sd, lkT, UD.v(LR.nidx(su)), free))}), HT.nthm(~V, AR.slots(Maybe<&2, V>, eT), z)), UD.v(su), s, hsv)
  Equal.trans(LR.LRU<&2, V> & Maybe<&2, V>, LR.drop_e(&2, V, cap, n, head, tail, free, AR.thaw(U32, mT), AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(U32, lkT), su, c, Array.swap(Maybe<&2, V>, AR.thaw(Maybe<&2, V>, eT), su, None{})), LR.drop_e(&2, V, cap, n, head, tail, free, AR.thaw(U32, mT), AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(U32, lkT), su, c, (AR.thaw(Maybe<&2, V>, AR.upd(Maybe<&2, V>, sd, eT, UD.v(su), None{})), HT.nthm(~V, AR.slots(Maybe<&2, V>, eT), UD.v(su)))), (LR.fbump(&2, V, c, LR.F{cap, U32.sub(n, 1), head, tail, H.link(su), AR.thaw(U32, mT), AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, AR.upd(Maybe<&2, V>, sd, eT, UD.v(su), None{})), AR.thaw(U32, AR.upd(U32, 3n+sd, lkT, UD.v(LR.nidx(su)), free))}), HT.nthm(~V, AR.slots(Maybe<&2, V>, eT), s)), E1, Equal.trans(LR.LRU<&2, V> & Maybe<&2, V>, (LR.F{cap, U32.sub(n, 1), head, tail, H.link(su), LR.bump(c, AR.thaw(U32, mT)), AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, AR.upd(Maybe<&2, V>, sd, eT, UD.v(su), None{})), Array.set(U32, AR.thaw(U32, lkT), LR.nidx(su), free)}, HT.nthm(~V, AR.slots(Maybe<&2, V>, eT), UD.v(su))), (LR.fbump(&2, V, c, LR.F{cap, U32.sub(n, 1), head, tail, H.link(su), AR.thaw(U32, mT), AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, AR.upd(Maybe<&2, V>, sd, eT, UD.v(su), None{})), AR.thaw(U32, AR.upd(U32, 3n+sd, lkT, UD.v(LR.nidx(su)), free))}), HT.nthm(~V, AR.slots(Maybe<&2, V>, eT), UD.v(su))), (LR.fbump(&2, V, c, LR.F{cap, U32.sub(n, 1), head, tail, H.link(su), AR.thaw(U32, mT), AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, AR.upd(Maybe<&2, V>, sd, eT, UD.v(su), None{})), AR.thaw(U32, AR.upd(U32, 3n+sd, lkT, UD.v(LR.nidx(su)), free))}), HT.nthm(~V, AR.slots(Maybe<&2, V>, eT), s)), E2, E3))
