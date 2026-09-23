import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/u32alg.bend as A
import ../lib/array.bend as AR
import ../spec/common.bend as SC
import ../spec/hash_table.bend as S
import ../spec/lru.bend as SP
import ../math/u32div.bend as UD
import ../../src/math/u64.bend as W
import ../../src/containers/hash_table.bend as H
import ../../src/containers/lru.bend as LR
import ../hash_table/table.bend as TB
import ../hash_table/buckets.bend as B
import ../hash_table/cyc.bend as CY
import ../hash_table/inv.bend as IV
import ../hash_table/state.bend as HT
import ../hash_table/keys.bend as K
import ./state.bend as ST
import ./basic.bend as BA
import ./bump.bend as BU
import ./bumpsh.bend as BS
import ./find.bend as FD
import ./tfind.bend as TF
import ./touch.bend as TO
import ./touchsh.bend as TSH
import ./rmat.bend as RM
import ./gone.bend as GO
import ./unlink.bend as UL
import ./lists.bend as LS
import ./meta.bend as MT
import ../hash_table/get.bend as G
import ../../src/math/hash.bend as HS
import ../hash_table/probe_impl.bend as PI
import ../hash_table/probe_all.bend as PA

import ./read.bend as RD
import ./dellink.bend as DK
import ./tabsl.bend as TS
import ./linktail.bend as LT
import ./dll.bend as DL
import ./idx.bend as ID

# Removing the oldest entry: evict_oldest (an eviction) and drop_head (a
# removal, for keys).

import ./evict.bend as EV
import ./rmatk.bend as RK
import ./bumpk.bend as BK


# eviction, keeping k

def dv_evk(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +s0: Nat, +t: List<&2, Nat>, +fl: List<&2, Nat>, +v: V, +hm: {HT.nthm(~V, AR.slots(Maybe<&2, V>, eT), s0) == Some{v} : Maybe<&2, V>}, -r: LR.LRU<&2, V> & Maybe<&2, V>, pk: RK.POKk(~V, Maybe<&2, V>, (SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), SP.drop(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), Con{s0, t}), ST.skey(AR.slots(U32, lkT), AR.slots(String, ksT), s0)), SP.c_ev(ST.ctr(AR.slots(U32, mT)))}, Some{v}), r, k)) -> BK.CountOKk(~V, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), SP.tail(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), Con{s0, t})), SP.c_ev(ST.ctr(AR.slots(U32, mT)))}, LR.drop_v(&2, V, r), k):
  match pk:
    case Tuple{+sh2, Tuple{+x, Tuple{+er, Tuple{+es, Tuple{+g2, hk2}}}}}:
      +hm2 = L.pair_fst(SP.Lru<V>, Maybe<&2, V>, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), SP.drop(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), Con{s0, t}), ST.skey(AR.slots(U32, lkT), AR.slots(String, ksT), s0)), SP.c_ev(ST.ctr(AR.slots(U32, mT)))}, Some{v}, ST.model(~V, sh2), x, es)
      +ed = Equal.cong(List<&2, SP.Ent<V>>, SP.Lru<V>, z => SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), z, SP.c_ev(ST.ctr(AR.slots(U32, mT)))}, SP.drop(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), Con{s0, t}), ST.skey(AR.slots(U32, lkT), AR.slots(String, ksT), s0)), SP.tail(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), Con{s0, t})), EV.drop_first(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), s0, t, v, hm))
      +em = Equal.trans(SP.Lru<V>, ST.model(~V, sh2), SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), SP.drop(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), Con{s0, t}), ST.skey(AR.slots(U32, lkT), AR.slots(String, ksT), s0)), SP.c_ev(ST.ctr(AR.slots(U32, mT)))}, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), SP.tail(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), Con{s0, t})), SP.c_ev(ST.ctr(AR.slots(U32, mT)))}, Equal.sym(SP.Lru<V>, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), SP.drop(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), Con{s0, t}), ST.skey(AR.slots(U32, lkT), AR.slots(String, ksT), s0)), SP.c_ev(ST.ctr(AR.slots(U32, mT)))}, ST.model(~V, sh2), hm2), ed)
      (sh2, (Equal.cong(LR.LRU<&2, V> & Maybe<&2, V>, LR.LRU<&2, V>, z => LR.drop_v(&2, V, z), r, (ST.real(~V, sh2), x), er), (em, (g2, hk2))))

def eb_evk(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +s0: Nat, +t: List<&2, Nat>, +fl: List<&2, Nat>, +hg: {ST.good(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, Con{s0, t}, fl}) == True{} : Bool}, +one: Nat, +h1: {one == 1n : Nat}, +v: V, +hm: {HT.nthm(~V, AR.slots(Maybe<&2, V>, eT), s0) == Some{v} : Maybe<&2, V>}, +hsv: {UD.v(H.slot(head)) == s0 : Nat}, +e: Nat, +he: {Nat.is_lt(e, SC.pow2(k)) == True{} : Bool}, +b: B.Bk, +hbe0: {B.at(TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), e) == b : B.Bk}, +hb: {ST.isbf(b, ST.lw(AR.slots(U32, lkT), s0, 2n), ST.lnk(s0)) == True{} : Bool}, +hk31: {Nat.is_lt(k, 31n) == True{} : Bool}, +el: {H.link(H.slot(head)) == ST.lnk(s0) : U32}) -> BK.CountOKk(~V, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), SP.tail(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), Con{s0, t})), SP.c_ev(ST.ctr(AR.slots(U32, mT)))}, LR.drop_v(&2, V, LR.drop_slot(&2, V, LR.F{cap, n, head, tail, free, AR.thaw(U32, mT), LR.del_link(AR.thaw(U32, tabT), CY.msk(k), ST.lw(AR.slots(U32, lkT), s0, 2n), H.link(H.slot(head))), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, H.slot(head), 1)), k):
  match b:
    case B.BE{}:
      Empty.absurd(BK.CountOKk(~V, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), SP.tail(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), Con{s0, t})), SP.c_ev(ST.ctr(AR.slots(U32, mT)))}, LR.drop_v(&2, V, LR.drop_slot(&2, V, LR.F{cap, n, head, tail, free, AR.thaw(U32, mT), LR.del_link(AR.thaw(U32, tabT), CY.msk(k), ST.lw(AR.slots(U32, lkT), s0, 2n), H.link(H.slot(head))), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, H.slot(head), 1)), k), L.false_true(hb))
    case B.BF{+w2, +l2, +k2}:
      +ew = A.eq_of(w2, ST.lw(AR.slots(U32, lkT), s0, 2n), L.and_left(U32.is_eq(w2, ST.lw(AR.slots(U32, lkT), s0, 2n)), U32.is_eq(l2, ST.lnk(s0)), hb))
      +elk = A.eq_of(l2, ST.lnk(s0), L.and_right(U32.is_eq(w2, ST.lw(AR.slots(U32, lkT), s0, 2n)), U32.is_eq(l2, ST.lnk(s0)), hb))
      +hbe = Equal.trans(B.Bk, B.at(TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), e), B.BF{w2, l2, k2}, B.BF{ST.lw(AR.slots(U32, lkT), s0, 2n), ST.lnk(s0), k2}, hbe0, Equal.trans(B.Bk, B.BF{w2, l2, k2}, B.BF{ST.lw(AR.slots(U32, lkT), s0, 2n), l2, k2}, B.BF{ST.lw(AR.slots(U32, lkT), s0, 2n), ST.lnk(s0), k2}, Equal.cong(U32, B.Bk, z => B.BF{z, l2, k2}, w2, ST.lw(AR.slots(U32, lkT), s0, 2n), ew), Equal.cong(U32, B.Bk, z => B.BF{ST.lw(AR.slots(U32, lkT), s0, 2n), z, k2}, l2, ST.lnk(s0), elk)))
      +hoi = L.subst(B.Bk, z => {B.occ(z) == True{} : Bool}, B.BF{ST.lw(AR.slots(U32, lkT), s0, 2n), ST.lnk(s0), k2}, B.at(TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), e), Equal.sym(B.Bk, B.at(TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), e), B.BF{ST.lw(AR.slots(U32, lkT), s0, 2n), ST.lnk(s0), k2}, hbe), {==})
      +hsd = RD.f_hsd(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, Con{s0, t}, fl, hg)
      +hs0 = RD.f_s0(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, Con{s0, t}, fl, hg, s0, UL.self_in(s0, t))
      +hsi = Equal.trans(Nat, UD.v(H.slot(B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), e)))), UD.v(H.slot(ST.lnk(s0))), s0, Equal.cong(B.Bk, Nat, z => UD.v(H.slot(B.lnk(z))), B.at(TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), e), B.BF{ST.lw(AR.slots(U32, lkT), s0, 2n), ST.lnk(s0), k2}, hbe), UL.ix_o(one, h1, s0, sd, hsd, hs0))
      +edl = Equal.trans(Array<U32>, LR.del_link(AR.thaw(U32, tabT), CY.msk(k), ST.lw(AR.slots(U32, lkT), s0, 2n), H.link(H.slot(head))), LR.del_link(AR.thaw(U32, tabT), CY.msk(k), ST.lw(AR.slots(U32, lkT), s0, 2n), ST.lnk(s0)), H.del_at(AR.thaw(U32, tabT), CY.msk(k), U32.from_nat(e)), Equal.cong(U32, Array<U32>, z => LR.del_link(AR.thaw(U32, tabT), CY.msk(k), ST.lw(AR.slots(U32, lkT), s0, 2n), z), H.link(H.slot(head)), ST.lnk(s0), el), DK.del_link_ok(one, h1, k, hk31, tabT, ST.g_cpt(~V, cap, n, head, tail, free, TB.nth0(AR.slots(U32, mT), 0n), TB.nth0(AR.slots(U32, mT), 1n), TB.nth0(AR.slots(U32, mT), 2n), TB.nth0(AR.slots(U32, mT), 6n), TB.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, Con{s0, t}, fl, hg), AR.slots(String, ksT), ST.g_cclus(~V, cap, n, head, tail, free, TB.nth0(AR.slots(U32, mT), 0n), TB.nth0(AR.slots(U32, mT), 1n), TB.nth0(AR.slots(U32, mT), 2n), TB.nth0(AR.slots(U32, mT), 6n), TB.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, Con{s0, t}, fl, hg), ST.g_cuniq(~V, cap, n, head, tail, free, TB.nth0(AR.slots(U32, mT), 0n), TB.nth0(AR.slots(U32, mT), 1n), TB.nth0(AR.slots(U32, mT), 2n), TB.nth0(AR.slots(U32, mT), 6n), TB.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, Con{s0, t}, fl, hg), e, he, ST.lw(AR.slots(U32, lkT), s0, 2n), ST.lnk(s0), k2, hbe))
      ok = dv_evk(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, s0, t, fl, v, hm, LR.drop_slot(&2, V, LR.F{cap, n, head, tail, free, AR.thaw(U32, mT), H.del_at(AR.thaw(U32, tabT), CY.msk(k), U32.from_nat(e)), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, H.slot(head), 1), RK.rm_at_evk(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, Con{s0, t}, fl, hg, s0, UL.self_in(s0, t), one, h1, e, he, hoi, hsi, H.slot(head), hsv, v, hm, ST.skey(AR.slots(U32, lkT), AR.slots(String, ksT), s0), K.str_refl(ST.skey(AR.slots(U32, lkT), AR.slots(String, ksT), s0))))
      L.subst(Array<U32>, z => BK.CountOKk(~V, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), SP.tail(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), Con{s0, t})), SP.c_ev(ST.ctr(AR.slots(U32, mT)))}, LR.drop_v(&2, V, LR.drop_slot(&2, V, LR.F{cap, n, head, tail, free, AR.thaw(U32, mT), z, AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, H.slot(head), 1)), k), H.del_at(AR.thaw(U32, tabT), CY.msk(k), U32.from_nat(e)), LR.del_link(AR.thaw(U32, tabT), CY.msk(k), ST.lw(AR.slots(U32, lkT), s0, 2n), H.link(H.slot(head))), Equal.sym(Array<U32>, LR.del_link(AR.thaw(U32, tabT), CY.msk(k), ST.lw(AR.slots(U32, lkT), s0, 2n), H.link(H.slot(head))), H.del_at(AR.thaw(U32, tabT), CY.msk(k), U32.from_nat(e)), edl), ok)


def ek_evk(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +s0: Nat, +t: List<&2, Nat>, +fl: List<&2, Nat>, +hg: {ST.good(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, Con{s0, t}, fl}) == True{} : Bool}, +one: Nat, +h1: {one == 1n : Nat}, +v: V, +hm: {HT.nthm(~V, AR.slots(Maybe<&2, V>, eT), s0) == Some{v} : Maybe<&2, V>}, +hsv: {UD.v(H.slot(head)) == s0 : Nat}, ea: TS.AnybAt(TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), SC.pow2(k), ST.lnk(s0), ST.lw(AR.slots(U32, lkT), s0, 2n))) -> BK.CountOKk(~V, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), SP.tail(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), Con{s0, t})), SP.c_ev(ST.ctr(AR.slots(U32, mT)))}, LR.drop_v(&2, V, LR.drop_slot(&2, V, LR.F{cap, n, head, tail, free, AR.thaw(U32, mT), LR.del_link(AR.thaw(U32, tabT), CY.msk(k), ST.lw(AR.slots(U32, lkT), s0, 2n), H.link(H.slot(head))), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, H.slot(head), 1)), k):
  match ea:
    case Tuple{+e, Tuple{+he, hb}}:
      +hsd = RD.f_hsd(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, Con{s0, t}, fl, hg)
      +hs0 = RD.f_s0(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, Con{s0, t}, fl, hg, s0, UL.self_in(s0, t))
      +el = LT.lnk_su(H.slot(head), s0, sd, hsd, hsv, hs0)
      +hk31 = N.lt_trans(k, 30n, 31n, L.and_left(Nat.is_lt(k, 30n), Nat.is_lt(0n, k), ST.g_ck(~V, cap, n, head, tail, free, TB.nth0(AR.slots(U32, mT), 0n), TB.nth0(AR.slots(U32, mT), 1n), TB.nth0(AR.slots(U32, mT), 2n), TB.nth0(AR.slots(U32, mT), 6n), TB.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, Con{s0, t}, fl, hg)), {==})
      eb_evk(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, s0, t, fl, hg, one, h1, v, hm, hsv, e, he, B.at(TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), e), {==}, hb, hk31, el)


def ev_m_evk(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +s0: Nat, +t: List<&2, Nat>, +fl: List<&2, Nat>, +hg: {ST.good(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, Con{s0, t}, fl}) == True{} : Bool}, +one: Nat, +h1: {one == 1n : Nat}, +m: Maybe<&2, V>, +hmm: {HT.nthm(~V, AR.slots(Maybe<&2, V>, eT), s0) == m : Maybe<&2, V>}, +hsm: {HT.some_b(~V, m) == True{} : Bool}, +hsv: {UD.v(H.slot(head)) == s0 : Nat}) -> BK.CountOKk(~V, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), SP.tail(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), Con{s0, t})), SP.c_ev(ST.ctr(AR.slots(U32, mT)))}, LR.drop_v(&2, V, LR.remove_slot(&2, V, ST.real(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, Con{s0, t}, fl}), H.slot(head), 1)), k):
  match m:
    case None{}:
      Empty.absurd(BK.CountOKk(~V, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), SP.tail(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), Con{s0, t})), SP.c_ev(ST.ctr(AR.slots(U32, mT)))}, LR.drop_v(&2, V, LR.remove_slot(&2, V, ST.real(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, Con{s0, t}, fl}), H.slot(head), 1)), k), L.false_true(hsm))
    case Some{+v}:
      +hm = {hmm : {HT.nthm(~V, AR.slots(Maybe<&2, V>, eT), s0) == Some{v} : Maybe<&2, V>}}
      +hsd = RD.f_hsd(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, Con{s0, t}, fl, hg)
      +hs0 = RD.f_s0(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, Con{s0, t}, fl, hg, s0, UL.self_in(s0, t))
      +hk31 = N.lt_trans(k, 30n, 31n, L.and_left(Nat.is_lt(k, 30n), Nat.is_lt(0n, k), ST.g_ck(~V, cap, n, head, tail, free, TB.nth0(AR.slots(U32, mT), 0n), TB.nth0(AR.slots(U32, mT), 1n), TB.nth0(AR.slots(U32, mT), 2n), TB.nth0(AR.slots(U32, mT), 6n), TB.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, Con{s0, t}, fl, hg)), {==})
      +ha = L.and_left(ST.anyb(TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), SC.pow2(k), ST.lnk(s0), ST.lw(AR.slots(U32, lkT), s0, 2n)), ST.hasall(~V, TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), SC.pow2(k), AR.slots(U32, lkT), t), ST.g_chas(~V, cap, n, head, tail, free, TB.nth0(AR.slots(U32, mT), 0n), TB.nth0(AR.slots(U32, mT), 1n), TB.nth0(AR.slots(U32, mT), 2n), TB.nth0(AR.slots(U32, mT), 6n), TB.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, Con{s0, t}, fl, hg))
      ok = ek_evk(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, s0, t, fl, hg, one, h1, v, hm, hsv, TS.find_anyb(TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), SC.pow2(k), ST.lnk(s0), ST.lw(AR.slots(U32, lkT), s0, 2n), ha))
      +hsu = GO.su_lt(H.slot(head), s0, sd, hsv, hs0)
      +i2 = Equal.trans(Nat, UD.v(LR.hidx(H.slot(head))), ST.off(UD.v(H.slot(head)), 2n), ST.off(s0, 2n), ID.w2(one, h1, H.slot(head), sd, UL.sd3(sd, hsd), hsu), Equal.cong(Nat, Nat, z => ST.off(z, 2n), UD.v(H.slot(head)), s0, hsv))
      +E2 = Equal.cong(Array<U32> & U32, LR.LRU<&2, V> & Maybe<&2, V>, r => LR.dl_h(&2, V, cap, n, head, tail, free, AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), H.slot(head), 1, CY.msk(k), AR.thaw(U32, mT), r), Array.get(U32, AR.thaw(U32, lkT), LR.hidx(H.slot(head))), (AR.thaw(U32, lkT), ST.lw(AR.slots(U32, lkT), s0, 2n)), GO.rd(one, h1, lkT, sd, hsd, ST.g_cpl(~V, cap, n, head, tail, free, TB.nth0(AR.slots(U32, mT), 0n), TB.nth0(AR.slots(U32, mT), 1n), TB.nth0(AR.slots(U32, mT), 2n), TB.nth0(AR.slots(U32, mT), 6n), TB.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, Con{s0, t}, fl, hg), LR.hidx(H.slot(head)), s0, 2n, {==}, hs0, i2))
      +G6 = Equal.trans(Array<U32> & U32, Array.get(U32, AR.thaw(U32, mT), 6), (AR.thaw(U32, mT), TB.nth0(AR.slots(U32, mT), 6n)), (AR.thaw(U32, mT), CY.msk(k)), MT.uget(5n, {==}, mT, ST.g_cpm(~V, cap, n, head, tail, free, TB.nth0(AR.slots(U32, mT), 0n), TB.nth0(AR.slots(U32, mT), 1n), TB.nth0(AR.slots(U32, mT), 2n), TB.nth0(AR.slots(U32, mT), 6n), TB.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, Con{s0, t}, fl, hg), 6, {==}), Equal.cong(U32, Array<U32> & U32, z => (AR.thaw(U32, mT), z), TB.nth0(AR.slots(U32, mT), 6n), CY.msk(k), A.eq_of(TB.nth0(AR.slots(U32, mT), 6n), CY.msk(k), ST.g_cmask(~V, cap, n, head, tail, free, TB.nth0(AR.slots(U32, mT), 0n), TB.nth0(AR.slots(U32, mT), 1n), TB.nth0(AR.slots(U32, mT), 2n), TB.nth0(AR.slots(U32, mT), 6n), TB.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, Con{s0, t}, fl, hg))))
      +E1 = Equal.cong(Array<U32> & U32, LR.LRU<&2, V> & Maybe<&2, V>, r => LR.dl_m(&2, V, cap, n, head, tail, free, AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT), H.slot(head), 1, r), Array.get(U32, AR.thaw(U32, mT), 6), (AR.thaw(U32, mT), CY.msk(k)), G6)
      +E = Equal.trans(LR.LRU<&2, V> & Maybe<&2, V>, LR.remove_slot(&2, V, ST.real(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, Con{s0, t}, fl}), H.slot(head), 1), LR.dl_h(&2, V, cap, n, head, tail, free, AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), H.slot(head), 1, CY.msk(k), AR.thaw(U32, mT), Array.get(U32, AR.thaw(U32, lkT), LR.hidx(H.slot(head)))), LR.drop_slot(&2, V, LR.F{cap, n, head, tail, free, AR.thaw(U32, mT), LR.del_link(AR.thaw(U32, tabT), CY.msk(k), ST.lw(AR.slots(U32, lkT), s0, 2n), H.link(H.slot(head))), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, H.slot(head), 1), E1, E2)
      L.subst(LR.LRU<&2, V> & Maybe<&2, V>, z => BK.CountOKk(~V, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), SP.tail(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), Con{s0, t})), SP.c_ev(ST.ctr(AR.slots(U32, mT)))}, LR.drop_v(&2, V, z), k), LR.drop_slot(&2, V, LR.F{cap, n, head, tail, free, AR.thaw(U32, mT), LR.del_link(AR.thaw(U32, tabT), CY.msk(k), ST.lw(AR.slots(U32, lkT), s0, 2n), H.link(H.slot(head))), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, H.slot(head), 1), LR.remove_slot(&2, V, ST.real(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, Con{s0, t}, fl}), H.slot(head), 1), Equal.sym(LR.LRU<&2, V> & Maybe<&2, V>, LR.remove_slot(&2, V, ST.real(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, Con{s0, t}, fl}), H.slot(head), 1), LR.drop_slot(&2, V, LR.F{cap, n, head, tail, free, AR.thaw(U32, mT), LR.del_link(AR.thaw(U32, tabT), CY.msk(k), ST.lw(AR.slots(U32, lkT), s0, 2n), H.link(H.slot(head))), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, H.slot(head), 1), E), ok)


def old_evk(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +s0: Nat, +t: List<&2, Nat>, +fl: List<&2, Nat>, +hg: {ST.good(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, Con{s0, t}, fl}) == True{} : Bool}, +one: Nat, +h1: {one == 1n : Nat}) -> BK.CountOKk(~V, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), SP.tail(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), Con{s0, t})), SP.c_ev(ST.ctr(AR.slots(U32, mT)))}, LR.drop_v(&2, V, LR.remove_slot(&2, V, ST.real(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, Con{s0, t}, fl}), H.slot(head), 1)), k):
  +hsd = RD.f_hsd(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, Con{s0, t}, fl, hg)
  +hs0 = RD.f_s0(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, Con{s0, t}, fl, hg, s0, UL.self_in(s0, t))
  +eh = A.eq_of(head, ST.lnk(s0), ST.g_chead(~V, cap, n, head, tail, free, TB.nth0(AR.slots(U32, mT), 0n), TB.nth0(AR.slots(U32, mT), 1n), TB.nth0(AR.slots(U32, mT), 2n), TB.nth0(AR.slots(U32, mT), 6n), TB.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, Con{s0, t}, fl, hg))
  +hsv = Equal.trans(Nat, UD.v(H.slot(head)), UD.v(H.slot(ST.lnk(s0))), s0, Equal.cong(U32, Nat, z => UD.v(H.slot(z)), head, ST.lnk(s0), eh), UL.ix_o(one, h1, s0, sd, hsd, hs0))
  +hls = L.and_left(Bool.and(Nat.is_lt(s0, UD.v(TB.nth0(AR.slots(U32, mT), 0n))), ST.live(~V, AR.slots(Maybe<&2, V>, eT), s0)), ST.slok(~V, t, UD.v(TB.nth0(AR.slots(U32, mT), 0n)), AR.slots(Maybe<&2, V>, eT)), ST.g_csl(~V, cap, n, head, tail, free, TB.nth0(AR.slots(U32, mT), 0n), TB.nth0(AR.slots(U32, mT), 1n), TB.nth0(AR.slots(U32, mT), 2n), TB.nth0(AR.slots(U32, mT), 6n), TB.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, Con{s0, t}, fl, hg))
  ev_m_evk(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, s0, t, fl, hg, one, h1, HT.nthm(~V, AR.slots(Maybe<&2, V>, eT), s0), {==}, L.and_right(Nat.is_lt(s0, UD.v(TB.nth0(AR.slots(U32, mT), 0n))), ST.live(~V, AR.slots(Maybe<&2, V>, eT), s0), hls), hsv)


