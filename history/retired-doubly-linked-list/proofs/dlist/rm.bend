import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../binary_heap/u32idx.bend as IX
import ../graph/shift.bend as SH
import ../graph/ashift.bend as AS2
import ../../spec/common.bend as SC
import ../../spec/doubly_linked_list.bend as DS
import ../../src/doubly_linked_list.bend as D
import ../../types/doubly_linked_list.bend as E
import ./state.bend as ST
import ./facts.bend as F
import ./links.bend as LK
import ./items.bend as IT
import ./core.bend as K
import ./alive.bend as AL

# length and get, and the handle validation every handle operation shares.
import ./reads.bend as RD
import ./nbrs.bend as NB
import ./mu0.bend as MU0
import ./split.bend as SP
import ./retarget.bend as RT
import ./rmfacts.bend as RF
import ./tset.bend as TS
import ./mut.bend as MU
import ./tolist.bend as TL

# remove: cut the live id out of the order and relink its neighbours.

def RML(~T: Data, +tag: U32, +fresh: Nat, +ord: List<&2, Nat>, +depth: Nat, vals: Array<Maybe<&2, T>>, +v: T, pr: Array<U32> & U32, nx: Array<U32> & U32) -> D.DList<T> & E.Obs<T>:
  D.obs_val(~T, D.rm_links(~T, tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), vals, v, pr, nx))

def RDL(~T: Data, +tag: U32, +fresh: Nat, +cnt: Nat, +hdv: U32, +tlv: U32, +depth: Nat, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, nexts: Array<U32>, +v: T) -> D.DList<T> & E.Obs<T>:
  (D.DL{tag, U32.from_nat(fresh), 0, cnt, hdv, tlv, depth, U.pow2u(depth), vals, prevs, nexts}, E.OVal{Done{v}})

def rdone(~T: Data, +tag: U32, +fresh: Nat, +its: List<&2, E.Item<T>>, +v: T) -> DS.Model<T> & E.Obs<T>:
  (DS.DM{tag, fresh, its}, E.OVal{Done{v}})

def lpair(+t: AR.Tree<U32>, +x: U32) -> Array<U32> & U32:
  (AR.thaw(U32, t), x)

def rm_cut(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +b: List<&2, Nat>, +i: U32, +v: T, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b})}) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}, +em: {RD.xv(~T, tv, i) == Some{v} : Maybe<&2, T>}) -> K.GCore(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b})}, RML(~T, tag, fresh, SC.append(Nat, a, Con{U32.to_nat(i), b}), depth, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), i, None{}), v, D.link_at(AR.thaw(U32, tp), i), D.link_at(AR.thaw(U32, tn), i)), rdone(~T, tag, fresh, DS.del(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), SC.append(Nat, a, Con{U32.to_nat(i), b})), i), v), 0n):
  +n = U32.to_nat(i)
  +xs = AR.slots(Maybe<&2, T>, tv)
  +ps = AR.slots(U32, tp)
  +ns = AR.slots(U32, tn)
  +p = LK.lastl(a, D.nil())
  +q = ST.hd_or(b, D.nil())
  +hd = F.g_depth(~T, tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b}), h)
  +pfv = F.g_tv(~T, tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b}), h)
  +pfp = F.g_tp(~T, tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b}), h)
  +pfn = F.g_tn(~T, tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b}), h)
  +hn = RD.hi_of(~T, tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b}), i, h, hi)
  +hd32 = N.le_lt_trans(depth, 31n, 32n, hd, N.lt_succ(31n))
  +hlo = K.alllt_mono(SC.append(Nat, a, Con{U32.to_nat(i), b}), fresh, SC.pow2(depth), F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b}), h), F.g_lt(~T, tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b}), h))
  +hla = TL.alllt_l(a, Con{n, b}, SC.pow2(depth), hlo)
  +hlb = IT.lt_tail(n, b, SC.pow2(depth), TL.alllt_r(a, Con{n, b}, SC.pow2(depth), hlo))
  +hnd = F.g_nd(~T, tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b}), h)
  +hdisj = SP.nodup_disj(a, Con{n, b}, hnd)
  +hna = SP.disj_mem(a, Con{n, b}, n, hdisj, L.subst(Bool, z => {Bool.or(z, ST.lmem(n, b)) == True{} : Bool}, True{}, Nat.is_eq(n, n), Equal.sym(Bool, Nat.is_eq(n, n), True{}, N.is_eq_refl(n)), {==}))
  +hnb = MU0.not_true(ST.lmem(n, b), L.and_left(Bool.not(ST.lmem(n, b)), ST.nodup(b), SP.nodup_app_r(a, Con{n, b}, hnd)))
  +hk = F.g_lk(~T, tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b}), h)
  +lenp = AR.slots_length(U32, depth, tp, pfp)
  +lenn = AR.slots_length(U32, depth, tn, pfn)
  +hlp = L.subst(Nat, z => {ST.alllt(SC.append(Nat, a, Con{U32.to_nat(i), b}), z) == True{} : Bool}, SC.pow2(depth), SC.length(U32, ps), Equal.sym(Nat, SC.length(U32, ps), SC.pow2(depth), lenp), hlo)
  +hln = L.subst(Nat, z => {ST.alllt(SC.append(Nat, a, Con{U32.to_nat(i), b}), z) == True{} : Bool}, SC.pow2(depth), SC.length(U32, ns), Equal.sym(Nat, SC.length(U32, ns), SC.pow2(depth), lenn), hlo)
  +tv2 = AR.upd(Maybe<&2, T>, depth, tv, n, None{})
  +tp2 = TS.tpup(depth, tp, b, p)
  +tn2 = TS.tnup(depth, tn, a, q)
  +evals = AR.set(Maybe<&2, T>, depth, tv, i, None{}, RD.xv(~T, tv, i), hd32, hn, AS2.tsat(Maybe<&2, T>, depth, tv, n, None{}, pfv, hn), pfv)
  +epr = Equal.trans(Array<U32> & U32, D.link_at(AR.thaw(U32, tp), i), (AR.thaw(U32, tp), ST.lat(ps, n)), (AR.thaw(U32, tp), p), NB.read_l(~T, tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b}), tp, i, h, pfp, hi), Equal.cong(U32, Array<U32> & U32, z => lpair(tp, z), ST.lat(ps, n), p, RF.plink(a, n, b, ps, ns, hk)))
  +enx = Equal.trans(Array<U32> & U32, D.link_at(AR.thaw(U32, tn), i), (AR.thaw(U32, tn), ST.lat(ns, n)), (AR.thaw(U32, tn), q), NB.read_l(~T, tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b}), tn, i, h, pfn, hi), Equal.cong(U32, Array<U32> & U32, z => lpair(tn, z), ST.lat(ns, n), q, RF.nlink(a, n, b, ps, ns, hk)))
  +c1 = Equal.cong(Array<Maybe<&2, T>>, D.DList<T> & E.Obs<T>, z => RML(~T, tag, fresh, SC.append(Nat, a, Con{U32.to_nat(i), b}), depth, z, v, D.link_at(AR.thaw(U32, tp), i), D.link_at(AR.thaw(U32, tn), i)), Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), i, None{}), AR.thaw(Maybe<&2, T>, tv2), evals)
  +c2 = Equal.cong(Array<U32> & U32, D.DList<T> & E.Obs<T>, z => RML(~T, tag, fresh, SC.append(Nat, a, Con{U32.to_nat(i), b}), depth, AR.thaw(Maybe<&2, T>, tv2), v, z, D.link_at(AR.thaw(U32, tn), i)), D.link_at(AR.thaw(U32, tp), i), (AR.thaw(U32, tp), p), epr)
  +c3 = Equal.cong(Array<U32> & U32, D.DList<T> & E.Obs<T>, z => RML(~T, tag, fresh, SC.append(Nat, a, Con{U32.to_nat(i), b}), depth, AR.thaw(Maybe<&2, T>, tv2), v, (AR.thaw(U32, tp), p), z), D.link_at(AR.thaw(U32, tn), i), (AR.thaw(U32, tn), q), enx)
  +d1 = Equal.cong(Nat, D.DList<T> & E.Obs<T>, z => RDL(~T, tag, fresh, z, D.pick_end(U32.is_eq(p, D.nil()), q, ST.hd(SC.append(Nat, a, Con{U32.to_nat(i), b}))), D.pick_end(U32.is_eq(q, D.nil()), p, ST.lst(SC.append(Nat, a, Con{U32.to_nat(i), b}))), depth, AR.thaw(Maybe<&2, T>, tv2), D.set_next(AR.thaw(U32, tp), q, p), D.set_next(AR.thaw(U32, tn), p, q), v), Nat.sub(SC.length(Nat, SC.append(Nat, a, Con{U32.to_nat(i), b})), 1n), SC.length(Nat, SC.append(Nat, a, b)), RF.cnt_cut(a, n, b))
  +d2 = Equal.cong(U32, D.DList<T> & E.Obs<T>, z => RDL(~T, tag, fresh, SC.length(Nat, SC.append(Nat, a, b)), z, D.pick_end(U32.is_eq(q, D.nil()), p, ST.lst(SC.append(Nat, a, Con{U32.to_nat(i), b}))), depth, AR.thaw(Maybe<&2, T>, tv2), D.set_next(AR.thaw(U32, tp), q, p), D.set_next(AR.thaw(U32, tn), p, q), v), D.pick_end(U32.is_eq(p, D.nil()), q, ST.hd(SC.append(Nat, a, Con{U32.to_nat(i), b}))), ST.hd(SC.append(Nat, a, b)), RF.hd_cut(a, n, b, depth, hd, hla))
  +d3 = Equal.cong(U32, D.DList<T> & E.Obs<T>, z => RDL(~T, tag, fresh, SC.length(Nat, SC.append(Nat, a, b)), ST.hd(SC.append(Nat, a, b)), z, depth, AR.thaw(Maybe<&2, T>, tv2), D.set_next(AR.thaw(U32, tp), q, p), D.set_next(AR.thaw(U32, tn), p, q), v), D.pick_end(U32.is_eq(q, D.nil()), p, ST.lst(SC.append(Nat, a, Con{U32.to_nat(i), b}))), ST.lst(SC.append(Nat, a, b)), RF.tl_cut(a, n, b, depth, hd, hlb))
  +d4 = Equal.cong(Array<U32>, D.DList<T> & E.Obs<T>, z => RDL(~T, tag, fresh, SC.length(Nat, SC.append(Nat, a, b)), ST.hd(SC.append(Nat, a, b)), ST.lst(SC.append(Nat, a, b)), depth, AR.thaw(Maybe<&2, T>, tv2), z, D.set_next(AR.thaw(U32, tn), p, q), v), D.set_next(AR.thaw(U32, tp), q, p), AR.thaw(U32, tp2), TS.sn_first(depth, tp, b, p, hd, pfp, hlb))
  +d5 = Equal.cong(Array<U32>, D.DList<T> & E.Obs<T>, z => RDL(~T, tag, fresh, SC.length(Nat, SC.append(Nat, a, b)), ST.hd(SC.append(Nat, a, b)), ST.lst(SC.append(Nat, a, b)), depth, AR.thaw(Maybe<&2, T>, tv2), AR.thaw(U32, tp2), z, v), D.set_next(AR.thaw(U32, tn), p, q), AR.thaw(U32, tn2), TS.sn_last(depth, tn, a, q, hd, pfn, hla))
  +e1 = Equal.trans(D.DList<T> & E.Obs<T>, RML(~T, tag, fresh, SC.append(Nat, a, Con{U32.to_nat(i), b}), depth, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), i, None{}), v, D.link_at(AR.thaw(U32, tp), i), D.link_at(AR.thaw(U32, tn), i)), RML(~T, tag, fresh, SC.append(Nat, a, Con{U32.to_nat(i), b}), depth, AR.thaw(Maybe<&2, T>, tv2), v, (AR.thaw(U32, tp), p), (AR.thaw(U32, tn), q)), RDL(~T, tag, fresh, SC.length(Nat, SC.append(Nat, a, b)), ST.hd(SC.append(Nat, a, b)), ST.lst(SC.append(Nat, a, b)), depth, AR.thaw(Maybe<&2, T>, tv2), AR.thaw(U32, tp2), AR.thaw(U32, tn2), v),
    Equal.trans(D.DList<T> & E.Obs<T>, RML(~T, tag, fresh, SC.append(Nat, a, Con{U32.to_nat(i), b}), depth, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), i, None{}), v, D.link_at(AR.thaw(U32, tp), i), D.link_at(AR.thaw(U32, tn), i)), RML(~T, tag, fresh, SC.append(Nat, a, Con{U32.to_nat(i), b}), depth, AR.thaw(Maybe<&2, T>, tv2), v, D.link_at(AR.thaw(U32, tp), i), D.link_at(AR.thaw(U32, tn), i)), RML(~T, tag, fresh, SC.append(Nat, a, Con{U32.to_nat(i), b}), depth, AR.thaw(Maybe<&2, T>, tv2), v, (AR.thaw(U32, tp), p), (AR.thaw(U32, tn), q)), c1,
      Equal.trans(D.DList<T> & E.Obs<T>, RML(~T, tag, fresh, SC.append(Nat, a, Con{U32.to_nat(i), b}), depth, AR.thaw(Maybe<&2, T>, tv2), v, D.link_at(AR.thaw(U32, tp), i), D.link_at(AR.thaw(U32, tn), i)), RML(~T, tag, fresh, SC.append(Nat, a, Con{U32.to_nat(i), b}), depth, AR.thaw(Maybe<&2, T>, tv2), v, (AR.thaw(U32, tp), p), D.link_at(AR.thaw(U32, tn), i)), RML(~T, tag, fresh, SC.append(Nat, a, Con{U32.to_nat(i), b}), depth, AR.thaw(Maybe<&2, T>, tv2), v, (AR.thaw(U32, tp), p), (AR.thaw(U32, tn), q)), c2, c3)),
    Equal.trans(D.DList<T> & E.Obs<T>, RDL(~T, tag, fresh, Nat.sub(SC.length(Nat, SC.append(Nat, a, Con{U32.to_nat(i), b})), 1n), D.pick_end(U32.is_eq(p, D.nil()), q, ST.hd(SC.append(Nat, a, Con{U32.to_nat(i), b}))), D.pick_end(U32.is_eq(q, D.nil()), p, ST.lst(SC.append(Nat, a, Con{U32.to_nat(i), b}))), depth, AR.thaw(Maybe<&2, T>, tv2), D.set_next(AR.thaw(U32, tp), q, p), D.set_next(AR.thaw(U32, tn), p, q), v), RDL(~T, tag, fresh, SC.length(Nat, SC.append(Nat, a, b)), D.pick_end(U32.is_eq(p, D.nil()), q, ST.hd(SC.append(Nat, a, Con{U32.to_nat(i), b}))), D.pick_end(U32.is_eq(q, D.nil()), p, ST.lst(SC.append(Nat, a, Con{U32.to_nat(i), b}))), depth, AR.thaw(Maybe<&2, T>, tv2), D.set_next(AR.thaw(U32, tp), q, p), D.set_next(AR.thaw(U32, tn), p, q), v), RDL(~T, tag, fresh, SC.length(Nat, SC.append(Nat, a, b)), ST.hd(SC.append(Nat, a, b)), ST.lst(SC.append(Nat, a, b)), depth, AR.thaw(Maybe<&2, T>, tv2), AR.thaw(U32, tp2), AR.thaw(U32, tn2), v), d1,
      Equal.trans(D.DList<T> & E.Obs<T>, RDL(~T, tag, fresh, SC.length(Nat, SC.append(Nat, a, b)), D.pick_end(U32.is_eq(p, D.nil()), q, ST.hd(SC.append(Nat, a, Con{U32.to_nat(i), b}))), D.pick_end(U32.is_eq(q, D.nil()), p, ST.lst(SC.append(Nat, a, Con{U32.to_nat(i), b}))), depth, AR.thaw(Maybe<&2, T>, tv2), D.set_next(AR.thaw(U32, tp), q, p), D.set_next(AR.thaw(U32, tn), p, q), v), RDL(~T, tag, fresh, SC.length(Nat, SC.append(Nat, a, b)), ST.hd(SC.append(Nat, a, b)), D.pick_end(U32.is_eq(q, D.nil()), p, ST.lst(SC.append(Nat, a, Con{U32.to_nat(i), b}))), depth, AR.thaw(Maybe<&2, T>, tv2), D.set_next(AR.thaw(U32, tp), q, p), D.set_next(AR.thaw(U32, tn), p, q), v), RDL(~T, tag, fresh, SC.length(Nat, SC.append(Nat, a, b)), ST.hd(SC.append(Nat, a, b)), ST.lst(SC.append(Nat, a, b)), depth, AR.thaw(Maybe<&2, T>, tv2), AR.thaw(U32, tp2), AR.thaw(U32, tn2), v), d2,
        Equal.trans(D.DList<T> & E.Obs<T>, RDL(~T, tag, fresh, SC.length(Nat, SC.append(Nat, a, b)), ST.hd(SC.append(Nat, a, b)), D.pick_end(U32.is_eq(q, D.nil()), p, ST.lst(SC.append(Nat, a, Con{U32.to_nat(i), b}))), depth, AR.thaw(Maybe<&2, T>, tv2), D.set_next(AR.thaw(U32, tp), q, p), D.set_next(AR.thaw(U32, tn), p, q), v), RDL(~T, tag, fresh, SC.length(Nat, SC.append(Nat, a, b)), ST.hd(SC.append(Nat, a, b)), ST.lst(SC.append(Nat, a, b)), depth, AR.thaw(Maybe<&2, T>, tv2), D.set_next(AR.thaw(U32, tp), q, p), D.set_next(AR.thaw(U32, tn), p, q), v), RDL(~T, tag, fresh, SC.length(Nat, SC.append(Nat, a, b)), ST.hd(SC.append(Nat, a, b)), ST.lst(SC.append(Nat, a, b)), depth, AR.thaw(Maybe<&2, T>, tv2), AR.thaw(U32, tp2), AR.thaw(U32, tn2), v), d3,
          Equal.trans(D.DList<T> & E.Obs<T>, RDL(~T, tag, fresh, SC.length(Nat, SC.append(Nat, a, b)), ST.hd(SC.append(Nat, a, b)), ST.lst(SC.append(Nat, a, b)), depth, AR.thaw(Maybe<&2, T>, tv2), D.set_next(AR.thaw(U32, tp), q, p), D.set_next(AR.thaw(U32, tn), p, q), v), RDL(~T, tag, fresh, SC.length(Nat, SC.append(Nat, a, b)), ST.hd(SC.append(Nat, a, b)), ST.lst(SC.append(Nat, a, b)), depth, AR.thaw(Maybe<&2, T>, tv2), AR.thaw(U32, tp2), D.set_next(AR.thaw(U32, tn), p, q), v), RDL(~T, tag, fresh, SC.length(Nat, SC.append(Nat, a, b)), ST.hd(SC.append(Nat, a, b)), ST.lst(SC.append(Nat, a, b)), depth, AR.thaw(Maybe<&2, T>, tv2), AR.thaw(U32, tp2), AR.thaw(U32, tn2), v), d4, d5)))))
  +es_v = AR.upd_slots(Maybe<&2, T>, depth, tv, n, None{}, hn, pfv)
  +hlv = L.subst(List<&2, Maybe<&2, T>>, z => {ST.lv(T, fresh, z, 0n, SC.append(Nat, a, b)) == True{} : Bool}, SC.update(Maybe<&2, T>, xs, n, None{}), AR.slots(Maybe<&2, T>, tv2), Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, tv2), SC.update(Maybe<&2, T>, xs, n, None{}), es_v),
    RF.lv_del(T, fresh, xs, 0n, a, n, b, hna, hnb, AR.len_lt(Maybe<&2, T>, depth, tv, n, pfv, hn), F.g_lv(~T, tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b}), h)))
  +hlk0 = RF.lk_cut(a, n, b, ps, ns, hnd, hlp, hln, hk)
  +hlk = L.subst(List<&2, U32>, z => {ST.lk(SC.append(Nat, a, b), D.nil(), D.nil(), z, AR.slots(U32, tn2)) == True{} : Bool}, RT.pupd(ps, b, p), AR.slots(U32, tp2), Equal.sym(List<&2, U32>, AR.slots(U32, tp2), RT.pupd(ps, b, p), TS.tpup_slots(depth, tp, b, p, pfp, hlb)),
    L.subst(List<&2, U32>, z => {ST.lk(SC.append(Nat, a, b), D.nil(), D.nil(), RT.pupd(ps, b, p), z) == True{} : Bool}, RT.nupd(ns, a, q), AR.slots(U32, tn2), Equal.sym(List<&2, U32>, AR.slots(U32, tn2), RT.nupd(ns, a, q), TS.tnup_slots(depth, tn, a, q, pfn, hla)), hlk0))
  +hlt = F.g_lt(~T, tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b}), h)
  +hl2 = SP.alllt_join(a, b, fresh, TL.alllt_l(a, Con{n, b}, fresh, hlt), IT.lt_tail(n, b, fresh, TL.alllt_r(a, Con{n, b}, fresh, hlt)))
  +g2 = F.good_mk(~T, tag, fresh, depth, tv2, tp2, tn2, SC.append(Nat, a, b), hd, AR.upd_perfect(Maybe<&2, T>, depth, tv, n, None{}, pfv), TS.tpup_pf(depth, tp, b, p, pfp), TS.tnup_pf(depth, tn, a, q, pfn), F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b}), h), hl2, SP.nodup_cut(a, n, b, hnd), hlv, hlk)
  +hnab = Equal.trans(Bool, ST.lmem(n, SC.append(Nat, a, b)), Bool.or(ST.lmem(n, a), ST.lmem(n, b)), False{}, SP.lmem_app(n, a, b), SP.or_ff(ST.lmem(n, a), ST.lmem(n, b), hna, hnb))
  +eit = Equal.trans(List<&2, E.Item<T>>, ST.items(T, AR.slots(Maybe<&2, T>, tv2), SC.append(Nat, a, b)), ST.items(T, xs, SC.append(Nat, a, b)), DS.del(T, ST.items(T, xs, SC.append(Nat, a, Con{U32.to_nat(i), b})), i),
    Equal.trans(List<&2, E.Item<T>>, ST.items(T, AR.slots(Maybe<&2, T>, tv2), SC.append(Nat, a, b)), ST.items(T, SC.update(Maybe<&2, T>, xs, n, None{}), SC.append(Nat, a, b)), ST.items(T, xs, SC.append(Nat, a, b)),
      Equal.cong(List<&2, Maybe<&2, T>>, List<&2, E.Item<T>>, z => ST.items(T, z, SC.append(Nat, a, b)), AR.slots(Maybe<&2, T>, tv2), SC.update(Maybe<&2, T>, xs, n, None{}), es_v),
      MU.items_frame(T, xs, SC.append(Nat, a, b), n, None{}, hnab)),
    Equal.sym(List<&2, E.Item<T>>, DS.del(T, ST.items(T, xs, SC.append(Nat, a, Con{U32.to_nat(i), b})), i), ST.items(T, xs, SC.append(Nat, a, b)), RF.items_del(T, xs, a, b, i, depth, hd, hlo, AL.g_alive(~T, tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b}), h), hnd)))
  K.gmk(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b})}, RML(~T, tag, fresh, SC.append(Nat, a, Con{U32.to_nat(i), b}), depth, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), i, None{}), v, D.link_at(AR.thaw(U32, tp), i), D.link_at(AR.thaw(U32, tn), i)), rdone(~T, tag, fresh, DS.del(T, ST.items(T, xs, SC.append(Nat, a, Con{U32.to_nat(i), b})), i), v), 0n, ST.Sh{tag, fresh, depth, tv2, tp2, tn2, SC.append(Nat, a, b)}, E.OVal{Done{v}},
    e1, g2,
    Equal.cong(List<&2, E.Item<T>>, DS.Model<T> & E.Obs<T>, z => rdone(~T, tag, fresh, z, v), ST.items(T, AR.slots(Maybe<&2, T>, tv2), SC.append(Nat, a, b)), DS.del(T, ST.items(T, xs, SC.append(Nat, a, Con{U32.to_nat(i), b})), i), eit),
    N.le_add_right(fresh, 0n))


def rm_some(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +v: T, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}, +em: {RD.xv(~T, tv, i) == Some{v} : Maybe<&2, T>}) -> K.GCore(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, RML(~T, tag, fresh, ord, depth, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), i, None{}), v, D.link_at(AR.thaw(U32, tp), i), D.link_at(AR.thaw(U32, tn), i)), rdone(~T, tag, fresh, DS.del(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), v), 0n):
  +n = U32.to_nat(i)
  +hm = NB.live_of(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi, v, em)
  +es = SP.split_eq(ord, n, hm)
  +a = SP.spre(ord, n)
  +b = SP.spost(ord, n)
  +h2 = L.subst(List<&2, Nat>, z => {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, z}) == True{} : Bool}, ord, SC.append(Nat, a, Con{n, b}), es, h)
  L.subst(List<&2, Nat>, z => K.GCore(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, z}, RML(~T, tag, fresh, z, depth, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), i, None{}), v, D.link_at(AR.thaw(U32, tp), i), D.link_at(AR.thaw(U32, tn), i)), rdone(~T, tag, fresh, DS.del(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), z), i), v), 0n),
    SC.append(Nat, a, Con{n, b}), ord, Equal.sym(List<&2, Nat>, ord, SC.append(Nat, a, Con{n, b}), es),
    rm_cut(~T, tag, fresh, depth, tv, tp, tn, a, b, i, v, h2, hi, em))

def RRT(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, ok: Bool, same: Bool) -> D.DList<T> & E.Obs<T>:
  D.obs_val(~T, D.remove_checked(~T, ok, tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn), i, same))

def RSP(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, same: Bool) -> DS.Model<T> & E.Obs<T>:
  DS.remove_at(T, same, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), tag, fresh, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i)

def rfound(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> D.DList<T> & E.Obs<T>:
  D.obs_val(~T, D.rm_found(~T, tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(U32, tp), AR.thaw(U32, tn), i, r))

def rm_m(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}, m: Maybe<&2, T>, +em: {RD.xv(~T, tv, i) == m : Maybe<&2, T>}) -> K.GCore(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, rfound(~T, tag, fresh, depth, tv, tp, tn, ord, i, (AR.thaw(Maybe<&2, T>, tv), m)), DS.remove_at(T, True{}, m, tag, fresh, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), 0n):
  match m:
    case None{}:
      K.gsame(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, rfound(~T, tag, fresh, depth, tv, tp, tn, ord, i, (AR.thaw(Maybe<&2, T>, tv), None{})), DS.remove_at(T, True{}, None{}, tag, fresh, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), 0n, h, E.OVal{Fail{E.StaleHandle{}}}, {==}, {==})
    case Some{v}:
      rm_some(~T, tag, fresh, depth, tv, tp, tn, ord, i, v, h, hi, em)

def remove_core(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +l: U32, +i: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, ok: Bool, +eok: {U32.is_lt(i, U32.from_nat(fresh)) == ok : Bool}, same: Bool) -> K.GCore(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, RRT(~T, tag, fresh, depth, tv, tp, tn, ord, i, ok, same), RSP(~T, tag, fresh, depth, tv, tp, tn, ord, i, same), 0n):
  match ok same:
    case True{} False{}:
      K.gsame(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, RRT(~T, tag, fresh, depth, tv, tp, tn, ord, i, True{}, False{}), RSP(~T, tag, fresh, depth, tv, tp, tn, ord, i, False{}), 0n, h, E.OVal{Fail{E.ForeignHandle{}}}, {==}, {==})
    case False{} False{}:
      K.gsame(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, RRT(~T, tag, fresh, depth, tv, tp, tn, ord, i, False{}, False{}), RSP(~T, tag, fresh, depth, tv, tp, tn, ord, i, False{}), 0n, h, E.OVal{Fail{E.ForeignHandle{}}}, {==}, {==})
    case False{} True{}:
      K.gsame(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, RRT(~T, tag, fresh, depth, tv, tp, tn, ord, i, False{}, True{}), RSP(~T, tag, fresh, depth, tv, tp, tn, ord, i, True{}), 0n, h, E.OVal{Fail{E.StaleHandle{}}}, {==},
        Equal.cong(Maybe<&2, T>, DS.Model<T> & E.Obs<T>, mm => DS.remove_at(T, True{}, mm, tag, fresh, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), None{}, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), Equal.sym(Maybe<&2, T>, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), None{}, RD.getv_ok_false(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, eok))))
    case True{} True{}:
      +hi = RD.hi_ok(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, eok)
      K.gconv(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, RRT(~T, tag, fresh, depth, tv, tp, tn, ord, i, True{}, True{}), rfound(~T, tag, fresh, depth, tv, tp, tn, ord, i, (AR.thaw(Maybe<&2, T>, tv), RD.xv(~T, tv, i))), RSP(~T, tag, fresh, depth, tv, tp, tn, ord, i, True{}), DS.remove_at(T, True{}, RD.xv(~T, tv, i), tag, fresh, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), 0n,
        Equal.cong(Array<Maybe<&2, T>> & Maybe<&2, T>, D.DList<T> & E.Obs<T>, r => rfound(~T, tag, fresh, depth, tv, tp, tn, ord, i, r), (AR.thaw(Maybe<&2, T>, tv), RD.xv(~T, tv, i)), Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), i), Equal.sym(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), i), (AR.thaw(Maybe<&2, T>, tv), RD.xv(~T, tv, i)), RD.read_v(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi))),
        Equal.cong(Maybe<&2, T>, DS.Model<T> & E.Obs<T>, mm => DS.remove_at(T, True{}, mm, tag, fresh, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), RD.xv(~T, tv, i), DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), Equal.sym(Maybe<&2, T>, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), RD.xv(~T, tv, i), RD.getv_xv(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi))),
        rm_m(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi, RD.xv(~T, tv, i), {==}))

def remove_ok(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +l: U32, +i: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.Remove{E.H{l, i}}):
  remove_core(~T, tag, fresh, depth, tv, tp, tn, ord, l, i, h, U32.is_lt(i, U32.from_nat(fresh)), {==}, U32.is_eq(l, tag))
