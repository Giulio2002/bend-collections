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
import ./reads.bend as RD
import ./nbrs.bend as NB
import ./mu0.bend as MU0
import ./split.bend as SP
import ./retarget.bend as RT
import ./rmfacts.bend as RF
import ./tset.bend as TS
import ./mut.bend as MU
import ./tolist.bend as TL
import ../graph/zip.bend as ZP
import ./insfacts.bend as IF
import ./inslk.bend as IL
import ./insitems.bend as II

# link_in with room: the fresh id is stored at its own slot and spliced into
# the order x ++ y between a = the last id of x and b = the first id of y.

def lsh(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: T) -> ST.Shadow<T>:
  ST.Sh{tag, 1n+fresh, depth, AR.upd(Maybe<&2, T>, depth, tv, fresh, Some{v}), TS.tpup(depth, AR.upd(U32, depth, tp, fresh, LK.lastl(x, D.nil())), y, ST.ln(fresh)), TS.tnup(depth, AR.upd(U32, depth, tn, fresh, ST.hd_or(y, D.nil())), x, ST.ln(fresh)), SC.append(Nat, x, Con{fresh, y})}

# the runtime list and handle link_in returns, by its parts
def LIX(~T: Data, +tag: U32, +fr: U32, +n: U32, +cnt: Nat, +hdv: U32, +tlv: U32, +depth: Nat, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, nexts: Array<U32>) -> D.DList<T> & E.Handle:
  (D.DL{tag, fr, 0, cnt, hdv, tlv, depth, U.pow2u(depth), vals, prevs, nexts}, E.H{tag, n})

# writing slot f of an array built from a tree
def set_f(-A: Data, +depth: Nat, +t: AR.Tree<A>, +f: Nat, +w: A, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hr: {Nat.is_lt(f, SC.pow2(depth)) == True{} : Bool}, +pf: {AR.perfect(A, depth, t) == True{} : Bool}) -> {Array.set(A, AR.thaw(A, t), U32.from_nat(f), w) == AR.thaw(A, AR.upd(A, depth, t, f, w)) : Array<A>}:
  +hid = F.id_nat(f, depth, hd, hr)
  +hi = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(depth)) == True{} : Bool}, f, U32.to_nat(U32.from_nat(f)), Equal.sym(Nat, U32.to_nat(U32.from_nat(f)), f, hid), hr)
  Equal.trans(Array<A>, Array.set(A, AR.thaw(A, t), U32.from_nat(f), w), AR.thaw(A, AR.upd(A, depth, t, U32.to_nat(U32.from_nat(f)), w)), AR.thaw(A, AR.upd(A, depth, t, f, w)),
    AR.set(A, depth, t, U32.from_nat(f), w, ZP.vget(A, w, AR.slots(A, t), U32.to_nat(U32.from_nat(f))), N.le_lt_trans(depth, 31n, 32n, hd, N.lt_succ(31n)), hi, AS2.tsat(A, depth, t, U32.to_nat(U32.from_nat(f)), w, pf, hi), pf),
    Equal.cong(Nat, Array<A>, z => AR.thaw(A, AR.upd(A, depth, t, z, w)), U32.to_nat(U32.from_nat(f)), f, hid))

def li_rt(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: T, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, x, y)}) == True{} : Bool}, +hr: {Nat.is_lt(fresh, SC.pow2(depth)) == True{} : Bool}) -> {D.link_in(~T, tag, U32.from_nat(fresh), U32.inc(U32.from_nat(fresh)), 0, SC.length(Nat, SC.append(Nat, x, y)), ST.hd(SC.append(Nat, x, y)), ST.lst(SC.append(Nat, x, y)), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn), LK.lastl(x, D.nil()), ST.hd_or(y, D.nil()), v) == (ST.real(~T, lsh(~T, tag, fresh, depth, tv, tp, tn, x, y, v)), E.H{tag, U32.from_nat(fresh)}) : D.DList<T> & E.Handle}:
  +o = SC.append(Nat, x, y)
  +o2 = SC.append(Nat, x, Con{fresh, y})
  +a = LK.lastl(x, D.nil())
  +b = ST.hd_or(y, D.nil())
  +fr = U32.from_nat(fresh)
  +lf = ST.ln(fresh)
  +hd = F.g_depth(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +pfv = F.g_tv(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +pfp = F.g_tp(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +pfn = F.g_tn(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +hlo = K.alllt_mono(o, fresh, SC.pow2(depth), F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, o, h), F.g_lt(~T, tag, fresh, depth, tv, tp, tn, o, h))
  +hlx = TL.alllt_l(x, y, SC.pow2(depth), hlo)
  +hly = TL.alllt_r(x, y, SC.pow2(depth), hlo)
  +tv2 = AR.upd(Maybe<&2, T>, depth, tv, fresh, Some{v})
  +tp1 = AR.upd(U32, depth, tp, fresh, a)
  +tn1 = AR.upd(U32, depth, tn, fresh, b)
  +tp2 = TS.tpup(depth, tp1, y, lf)
  +tn2 = TS.tnup(depth, tn1, x, lf)
  +ep = Equal.trans(Array<U32>, D.set_next(Array.set(U32, AR.thaw(U32, tp), fr, a), b, lf), D.set_next(AR.thaw(U32, tp1), b, lf), AR.thaw(U32, tp2),
    Equal.cong(Array<U32>, Array<U32>, z => D.set_next(z, b, lf), Array.set(U32, AR.thaw(U32, tp), fr, a), AR.thaw(U32, tp1), set_f(U32, depth, tp, fresh, a, hd, hr, pfp)),
    TS.sn_first(depth, tp1, y, lf, hd, AR.upd_perfect(U32, depth, tp, fresh, a, pfp), hly))
  +en = Equal.trans(Array<U32>, D.set_next(Array.set(U32, AR.thaw(U32, tn), fr, b), a, lf), D.set_next(AR.thaw(U32, tn1), a, lf), AR.thaw(U32, tn2),
    Equal.cong(Array<U32>, Array<U32>, z => D.set_next(z, a, lf), Array.set(U32, AR.thaw(U32, tn), fr, b), AR.thaw(U32, tn1), set_f(U32, depth, tn, fresh, b, hd, hr, pfn)),
    TS.sn_last(depth, tn1, x, lf, hd, AR.upd_perfect(U32, depth, tn, fresh, b, pfn), hlx))
  %Equal.sym(U32, U32.inc(fr), lf, IX.inc_bridge(fresh)) : {LIX(~T, tag, _, fr, 1n+SC.length(Nat, o), D.pick_end(U32.is_eq(a, D.nil()), _, ST.hd(o)), D.pick_end(U32.is_eq(b, D.nil()), _, ST.lst(o)), depth, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), fr, Some{v}), D.set_next(Array.set(U32, AR.thaw(U32, tp), fr, a), b, _), D.set_next(Array.set(U32, AR.thaw(U32, tn), fr, b), a, _)) == (ST.real(~T, lsh(~T, tag, fresh, depth, tv, tp, tn, x, y, v)), E.H{tag, fr}) : D.DList<T> & E.Handle}
  %Equal.sym(Nat, 1n+SC.length(Nat, o), SC.length(Nat, o2), II.cnt_ins(x, fresh, y)) : {LIX(~T, tag, lf, fr, _, D.pick_end(U32.is_eq(a, D.nil()), lf, ST.hd(o)), D.pick_end(U32.is_eq(b, D.nil()), lf, ST.lst(o)), depth, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), fr, Some{v}), D.set_next(Array.set(U32, AR.thaw(U32, tp), fr, a), b, lf), D.set_next(Array.set(U32, AR.thaw(U32, tn), fr, b), a, lf)) == (ST.real(~T, lsh(~T, tag, fresh, depth, tv, tp, tn, x, y, v)), E.H{tag, fr}) : D.DList<T> & E.Handle}
  %Equal.sym(U32, D.pick_end(U32.is_eq(a, D.nil()), lf, ST.hd(o)), ST.hd(o2), II.hd_ins(x, fresh, y, depth, hd, hlx)) : {LIX(~T, tag, lf, fr, SC.length(Nat, o2), _, D.pick_end(U32.is_eq(b, D.nil()), lf, ST.lst(o)), depth, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), fr, Some{v}), D.set_next(Array.set(U32, AR.thaw(U32, tp), fr, a), b, lf), D.set_next(Array.set(U32, AR.thaw(U32, tn), fr, b), a, lf)) == (ST.real(~T, lsh(~T, tag, fresh, depth, tv, tp, tn, x, y, v)), E.H{tag, fr}) : D.DList<T> & E.Handle}
  %Equal.sym(U32, D.pick_end(U32.is_eq(b, D.nil()), lf, ST.lst(o)), ST.lst(o2), II.tl_ins(x, fresh, y, depth, hd, hly)) : {LIX(~T, tag, lf, fr, SC.length(Nat, o2), ST.hd(o2), _, depth, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), fr, Some{v}), D.set_next(Array.set(U32, AR.thaw(U32, tp), fr, a), b, lf), D.set_next(Array.set(U32, AR.thaw(U32, tn), fr, b), a, lf)) == (ST.real(~T, lsh(~T, tag, fresh, depth, tv, tp, tn, x, y, v)), E.H{tag, fr}) : D.DList<T> & E.Handle}
  %Equal.sym(Array<Maybe<&2, T>>, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), fr, Some{v}), AR.thaw(Maybe<&2, T>, tv2), set_f(Maybe<&2, T>, depth, tv, fresh, Some{v}, hd, hr, pfv)) : {LIX(~T, tag, lf, fr, SC.length(Nat, o2), ST.hd(o2), ST.lst(o2), depth, _, D.set_next(Array.set(U32, AR.thaw(U32, tp), fr, a), b, lf), D.set_next(Array.set(U32, AR.thaw(U32, tn), fr, b), a, lf)) == (ST.real(~T, lsh(~T, tag, fresh, depth, tv, tp, tn, x, y, v)), E.H{tag, fr}) : D.DList<T> & E.Handle}
  %Equal.sym(Array<U32>, D.set_next(Array.set(U32, AR.thaw(U32, tp), fr, a), b, lf), AR.thaw(U32, tp2), ep) : {LIX(~T, tag, lf, fr, SC.length(Nat, o2), ST.hd(o2), ST.lst(o2), depth, AR.thaw(Maybe<&2, T>, tv2), _, D.set_next(Array.set(U32, AR.thaw(U32, tn), fr, b), a, lf)) == (ST.real(~T, lsh(~T, tag, fresh, depth, tv, tp, tn, x, y, v)), E.H{tag, fr}) : D.DList<T> & E.Handle}
  %Equal.sym(Array<U32>, D.set_next(Array.set(U32, AR.thaw(U32, tn), fr, b), a, lf), AR.thaw(U32, tn2), en) : {LIX(~T, tag, lf, fr, SC.length(Nat, o2), ST.hd(o2), ST.lst(o2), depth, AR.thaw(Maybe<&2, T>, tv2), AR.thaw(U32, tp2), _) == (ST.real(~T, lsh(~T, tag, fresh, depth, tv, tp, tn, x, y, v)), E.H{tag, fr}) : D.DList<T> & E.Handle}
  {==}

def li_good(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: T, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, x, y)}) == True{} : Bool}, +hr: {Nat.is_lt(fresh, SC.pow2(depth)) == True{} : Bool}) -> {ST.good(~T, lsh(~T, tag, fresh, depth, tv, tp, tn, x, y, v)) == True{} : Bool}:
  +o = SC.append(Nat, x, y)
  +o2 = SC.append(Nat, x, Con{fresh, y})
  +a = LK.lastl(x, D.nil())
  +b = ST.hd_or(y, D.nil())
  +lf = ST.ln(fresh)
  +xs = AR.slots(Maybe<&2, T>, tv)
  +ps = AR.slots(U32, tp)
  +ns = AR.slots(U32, tn)
  +hd = F.g_depth(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +pfv = F.g_tv(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +pfp = F.g_tp(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +pfn = F.g_tn(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +hlt = F.g_lt(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +hnd = F.g_nd(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +hfo = IF.f_notin(o, fresh, hlt)
  +hlo = K.alllt_mono(o, fresh, SC.pow2(depth), F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, o, h), hlt)
  +hlx = TL.alllt_l(x, y, SC.pow2(depth), hlo)
  +hly = TL.alllt_r(x, y, SC.pow2(depth), hlo)
  +lenp = AR.slots_length(U32, depth, tp, pfp)
  +lenn = AR.slots_length(U32, depth, tn, pfn)
  +hxn = L.subst(Nat, z => {ST.alllt(x, z) == True{} : Bool}, SC.pow2(depth), SC.length(U32, ns), Equal.sym(Nat, SC.length(U32, ns), SC.pow2(depth), lenn), hlx)
  +hyp = L.subst(Nat, z => {ST.alllt(y, z) == True{} : Bool}, SC.pow2(depth), SC.length(U32, ps), Equal.sym(Nat, SC.length(U32, ps), SC.pow2(depth), lenp), hly)
  +hfp = L.subst(Nat, z => {Nat.is_lt(fresh, z) == True{} : Bool}, SC.pow2(depth), SC.length(U32, ps), Equal.sym(Nat, SC.length(U32, ps), SC.pow2(depth), lenp), hr)
  +hfn = L.subst(Nat, z => {Nat.is_lt(fresh, z) == True{} : Bool}, SC.pow2(depth), SC.length(U32, ns), Equal.sym(Nat, SC.length(U32, ns), SC.pow2(depth), lenn), hr)
  +tv2 = AR.upd(Maybe<&2, T>, depth, tv, fresh, Some{v})
  +tp1 = AR.upd(U32, depth, tp, fresh, a)
  +tn1 = AR.upd(U32, depth, tn, fresh, b)
  +pf1p = AR.upd_perfect(U32, depth, tp, fresh, a, pfp)
  +pf1n = AR.upd_perfect(U32, depth, tn, fresh, b, pfn)
  +esp = Equal.trans(List<&2, U32>, AR.slots(U32, TS.tpup(depth, tp1, y, lf)), RT.pupd(AR.slots(U32, tp1), y, lf), RT.pupd(SC.update(U32, ps, fresh, a), y, lf),
    TS.tpup_slots(depth, tp1, y, lf, pf1p, hly),
    Equal.cong(List<&2, U32>, List<&2, U32>, z => RT.pupd(z, y, lf), AR.slots(U32, tp1), SC.update(U32, ps, fresh, a), AR.upd_slots(U32, depth, tp, fresh, a, hr, pfp)))
  +esn = Equal.trans(List<&2, U32>, AR.slots(U32, TS.tnup(depth, tn1, x, lf)), RT.nupd(AR.slots(U32, tn1), x, lf), RT.nupd(SC.update(U32, ns, fresh, b), x, lf),
    TS.tnup_slots(depth, tn1, x, lf, pf1n, hlx),
    Equal.cong(List<&2, U32>, List<&2, U32>, z => RT.nupd(z, x, lf), AR.slots(U32, tn1), SC.update(U32, ns, fresh, b), AR.upd_slots(U32, depth, tn, fresh, b, hr, pfn)))
  +hlk0 = IL.lk_ins(x, y, fresh, ps, ns, hnd, hfo, hxn, hyp, hfp, hfn, F.g_lk(~T, tag, fresh, depth, tv, tp, tn, o, h))
  +hlk = L.subst(List<&2, U32>, z => {ST.lk(o2, D.nil(), D.nil(), z, AR.slots(U32, TS.tnup(depth, tn1, x, lf))) == True{} : Bool}, RT.pupd(SC.update(U32, ps, fresh, a), y, lf), AR.slots(U32, TS.tpup(depth, tp1, y, lf)), Equal.sym(List<&2, U32>, AR.slots(U32, TS.tpup(depth, tp1, y, lf)), RT.pupd(SC.update(U32, ps, fresh, a), y, lf), esp),
    L.subst(List<&2, U32>, z => {ST.lk(o2, D.nil(), D.nil(), RT.pupd(SC.update(U32, ps, fresh, a), y, lf), z) == True{} : Bool}, RT.nupd(SC.update(U32, ns, fresh, b), x, lf), AR.slots(U32, TS.tnup(depth, tn1, x, lf)), Equal.sym(List<&2, U32>, AR.slots(U32, TS.tnup(depth, tn1, x, lf)), RT.nupd(SC.update(U32, ns, fresh, b), x, lf), esn), hlk0))
  +hxs = AR.len_lt(Maybe<&2, T>, depth, tv, fresh, pfv, hr)
  +hlv0 = IF.lv_new(T, xs, fresh, x, y, v, hxs, F.g_lv(~T, tag, fresh, depth, tv, tp, tn, o, h))
  +hlv = L.subst(List<&2, Maybe<&2, T>>, z => {ST.lv(T, 1n+fresh, z, 0n, o2) == True{} : Bool}, SC.update(Maybe<&2, T>, xs, fresh, Some{v}), AR.slots(Maybe<&2, T>, tv2), Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, tv2), SC.update(Maybe<&2, T>, xs, fresh, Some{v}), AR.upd_slots(Maybe<&2, T>, depth, tv, fresh, Some{v}, hr, pfv)), hlv0)
  F.good_mk(~T, tag, 1n+fresh, depth, tv2, TS.tpup(depth, tp1, y, lf), TS.tnup(depth, tn1, x, lf), o2, hd,
    AR.upd_perfect(Maybe<&2, T>, depth, tv, fresh, Some{v}, pfv), TS.tpup_pf(depth, tp1, y, lf, pf1p), TS.tnup_pf(depth, tn1, x, lf, pf1n),
    N.lt_succ_le_succ(fresh, SC.pow2(depth), hr), IF.alllt_ins(x, y, fresh, hlt), IF.nodup_ins(x, y, fresh, hfo, hnd), hlv, hlk)

def li_model(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: T, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, x, y)}) == True{} : Bool}, +hr: {Nat.is_lt(fresh, SC.pow2(depth)) == True{} : Bool}) -> {ST.model(~T, lsh(~T, tag, fresh, depth, tv, tp, tn, x, y, v)) == DS.DM{tag, 1n+fresh, SC.append(E.Item<T>, ST.items(T, AR.slots(Maybe<&2, T>, tv), x), Con{E.Item{U32.from_nat(fresh), v}, ST.items(T, AR.slots(Maybe<&2, T>, tv), y)})} : DS.Model<T>}:
  +o = SC.append(Nat, x, y)
  +o2 = SC.append(Nat, x, Con{fresh, y})
  +xs = AR.slots(Maybe<&2, T>, tv)
  +pfv = F.g_tv(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +hfo = IF.f_notin(o, fresh, F.g_lt(~T, tag, fresh, depth, tv, tp, tn, o, h))
  +tv2 = AR.upd(Maybe<&2, T>, depth, tv, fresh, Some{v})
  Equal.cong(List<&2, E.Item<T>>, DS.Model<T>, z => DS.DM{tag, 1n+fresh, z}, ST.items(T, AR.slots(Maybe<&2, T>, tv2), o2), SC.append(E.Item<T>, ST.items(T, xs, x), Con{E.Item{U32.from_nat(fresh), v}, ST.items(T, xs, y)}),
    Equal.trans(List<&2, E.Item<T>>, ST.items(T, AR.slots(Maybe<&2, T>, tv2), o2), ST.items(T, SC.update(Maybe<&2, T>, xs, fresh, Some{v}), o2), SC.append(E.Item<T>, ST.items(T, xs, x), Con{E.Item{U32.from_nat(fresh), v}, ST.items(T, xs, y)}),
      Equal.cong(List<&2, Maybe<&2, T>>, List<&2, E.Item<T>>, z => ST.items(T, z, o2), AR.slots(Maybe<&2, T>, tv2), SC.update(Maybe<&2, T>, xs, fresh, Some{v}), AR.upd_slots(Maybe<&2, T>, depth, tv, fresh, Some{v}, hr, pfv)),
      II.items_ins(T, xs, x, y, fresh, v, IL.notin_l(fresh, x, y, hfo), IL.notin_r(fresh, x, y, hfo), AR.len_lt(Maybe<&2, T>, depth, tv, fresh, pfv, hr))))
