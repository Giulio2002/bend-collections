import Base
import ./insert.bend as IN
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

import ./reuse_facts.bend as RF2

# Reinsert an issued, retired slot without increasing the issued-slot bound.
def lsh(~T: Data, +tag: U32, +fresh: Nat, +idx: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: T) -> ST.Shadow<T>:
  ST.Sh{tag, fresh, depth, AR.upd(Maybe<&2, T>, depth, tv, idx, Some{v}), TS.tpup(depth, AR.upd(U32, depth, tp, idx, LK.lastl(x, D.nil())), y, ST.ln(idx)), TS.tnup(depth, AR.upd(U32, depth, tn, idx, ST.hd_or(y, D.nil())), x, ST.ln(idx)), SC.append(Nat, x, Con{idx, y})}

def li_good(~T: Data, +tag: U32, +fresh: Nat, +idx: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: T, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, x, y)}) == True{} : Bool}, +hr: {Nat.is_lt(idx, SC.pow2(depth)) == True{} : Bool}, +hidx: {Nat.is_lt(idx, fresh) == True{} : Bool}, +hfree: {ST.lmem(idx, SC.append(Nat, x, y)) == False{} : Bool}) -> {ST.good(~T, lsh(~T, tag, fresh, idx, depth, tv, tp, tn, x, y, v)) == True{} : Bool}:
  +o = SC.append(Nat, x, y)
  +o2 = SC.append(Nat, x, Con{idx, y})
  +a = LK.lastl(x, D.nil())
  +b = ST.hd_or(y, D.nil())
  +lf = ST.ln(idx)
  +xs = AR.slots(Maybe<&2, T>, tv)
  +ps = AR.slots(U32, tp)
  +ns = AR.slots(U32, tn)
  +hd = F.g_depth(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +pfv = F.g_tv(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +pfp = F.g_tp(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +pfn = F.g_tn(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +hlt = F.g_lt(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +hnd = F.g_nd(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +hfo = hfree
  +hlo = K.alllt_mono(o, fresh, SC.pow2(depth), F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, o, h), hlt)
  +hlx = TL.alllt_l(x, y, SC.pow2(depth), hlo)
  +hly = TL.alllt_r(x, y, SC.pow2(depth), hlo)
  +lenp = AR.slots_length(U32, depth, tp, pfp)
  +lenn = AR.slots_length(U32, depth, tn, pfn)
  +hxn = L.subst(Nat, z => {ST.alllt(x, z) == True{} : Bool}, SC.pow2(depth), SC.length(U32, ns), Equal.sym(Nat, SC.length(U32, ns), SC.pow2(depth), lenn), hlx)
  +hyp = L.subst(Nat, z => {ST.alllt(y, z) == True{} : Bool}, SC.pow2(depth), SC.length(U32, ps), Equal.sym(Nat, SC.length(U32, ps), SC.pow2(depth), lenp), hly)
  +hfp = L.subst(Nat, z => {Nat.is_lt(idx, z) == True{} : Bool}, SC.pow2(depth), SC.length(U32, ps), Equal.sym(Nat, SC.length(U32, ps), SC.pow2(depth), lenp), hr)
  +hfn = L.subst(Nat, z => {Nat.is_lt(idx, z) == True{} : Bool}, SC.pow2(depth), SC.length(U32, ns), Equal.sym(Nat, SC.length(U32, ns), SC.pow2(depth), lenn), hr)
  +tv2 = AR.upd(Maybe<&2, T>, depth, tv, idx, Some{v})
  +tp1 = AR.upd(U32, depth, tp, idx, a)
  +tn1 = AR.upd(U32, depth, tn, idx, b)
  +pf1p = AR.upd_perfect(U32, depth, tp, idx, a, pfp)
  +pf1n = AR.upd_perfect(U32, depth, tn, idx, b, pfn)
  +esp = Equal.trans(List<&2, U32>, AR.slots(U32, TS.tpup(depth, tp1, y, lf)), RT.pupd(AR.slots(U32, tp1), y, lf), RT.pupd(SC.update(U32, ps, idx, a), y, lf),
    TS.tpup_slots(depth, tp1, y, lf, pf1p, hly),
    Equal.cong(List<&2, U32>, List<&2, U32>, z => RT.pupd(z, y, lf), AR.slots(U32, tp1), SC.update(U32, ps, idx, a), AR.upd_slots(U32, depth, tp, idx, a, hr, pfp)))
  +esn = Equal.trans(List<&2, U32>, AR.slots(U32, TS.tnup(depth, tn1, x, lf)), RT.nupd(AR.slots(U32, tn1), x, lf), RT.nupd(SC.update(U32, ns, idx, b), x, lf),
    TS.tnup_slots(depth, tn1, x, lf, pf1n, hlx),
    Equal.cong(List<&2, U32>, List<&2, U32>, z => RT.nupd(z, x, lf), AR.slots(U32, tn1), SC.update(U32, ns, idx, b), AR.upd_slots(U32, depth, tn, idx, b, hr, pfn)))
  +hlk0 = IL.lk_ins(x, y, idx, ps, ns, hnd, hfo, hxn, hyp, hfp, hfn, F.g_lk(~T, tag, fresh, depth, tv, tp, tn, o, h))
  +hlk = L.subst(List<&2, U32>, z => {ST.lk(o2, D.nil(), D.nil(), z, AR.slots(U32, TS.tnup(depth, tn1, x, lf))) == True{} : Bool}, RT.pupd(SC.update(U32, ps, idx, a), y, lf), AR.slots(U32, TS.tpup(depth, tp1, y, lf)), Equal.sym(List<&2, U32>, AR.slots(U32, TS.tpup(depth, tp1, y, lf)), RT.pupd(SC.update(U32, ps, idx, a), y, lf), esp),
    L.subst(List<&2, U32>, z => {ST.lk(o2, D.nil(), D.nil(), RT.pupd(SC.update(U32, ps, idx, a), y, lf), z) == True{} : Bool}, RT.nupd(SC.update(U32, ns, idx, b), x, lf), AR.slots(U32, TS.tnup(depth, tn1, x, lf)), Equal.sym(List<&2, U32>, AR.slots(U32, TS.tnup(depth, tn1, x, lf)), RT.nupd(SC.update(U32, ns, idx, b), x, lf), esn), hlk0))
  +hxs = AR.len_lt(Maybe<&2, T>, depth, tv, idx, pfv, hr)
  +hlv0 = RF2.values_insert(T, fresh, xs, 0n, x, y, idx, v, hxs, F.g_lv(~T, tag, fresh, depth, tv, tp, tn, o, h))
  +hlv = L.subst(List<&2, Maybe<&2, T>>, z => {ST.lv(T, fresh, z, 0n, o2) == True{} : Bool}, SC.update(Maybe<&2, T>, xs, idx, Some{v}), AR.slots(Maybe<&2, T>, tv2), Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, tv2), SC.update(Maybe<&2, T>, xs, idx, Some{v}), AR.upd_slots(Maybe<&2, T>, depth, tv, idx, Some{v}, hr, pfv)), hlv0)
  F.good_mk(~T, tag, fresh, depth, tv2, TS.tpup(depth, tp1, y, lf), TS.tnup(depth, tn1, x, lf), o2, hd,
    AR.upd_perfect(Maybe<&2, T>, depth, tv, idx, Some{v}, pfv), TS.tpup_pf(depth, tp1, y, lf, pf1p), TS.tnup_pf(depth, tn1, x, lf, pf1n),
    F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, o, h), RF2.bounds_insert(x, y, idx, fresh, hidx, hlt), IF.nodup_ins(x, y, idx, hfo, hnd), hlv, hlk)

def li_model(~T: Data, +tag: U32, +fresh: Nat, +idx: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: T, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, x, y)}) == True{} : Bool}, +hr: {Nat.is_lt(idx, SC.pow2(depth)) == True{} : Bool}, +hidx: {Nat.is_lt(idx, fresh) == True{} : Bool}, +hfree: {ST.lmem(idx, SC.append(Nat, x, y)) == False{} : Bool}) -> {ST.model(~T, lsh(~T, tag, fresh, idx, depth, tv, tp, tn, x, y, v)) == DS.DM{tag, fresh, SC.append(E.Item<T>, ST.items(T, AR.slots(Maybe<&2, T>, tv), x), Con{E.Item{U32.from_nat(idx), v}, ST.items(T, AR.slots(Maybe<&2, T>, tv), y)})} : DS.Model<T>}:
  +o = SC.append(Nat, x, y)
  +o2 = SC.append(Nat, x, Con{idx, y})
  +xs = AR.slots(Maybe<&2, T>, tv)
  +pfv = F.g_tv(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +hfo = hfree
  +tv2 = AR.upd(Maybe<&2, T>, depth, tv, idx, Some{v})
  Equal.cong(List<&2, E.Item<T>>, DS.Model<T>, z => DS.DM{tag, fresh, z}, ST.items(T, AR.slots(Maybe<&2, T>, tv2), o2), SC.append(E.Item<T>, ST.items(T, xs, x), Con{E.Item{U32.from_nat(idx), v}, ST.items(T, xs, y)}),
    Equal.trans(List<&2, E.Item<T>>, ST.items(T, AR.slots(Maybe<&2, T>, tv2), o2), ST.items(T, SC.update(Maybe<&2, T>, xs, idx, Some{v}), o2), SC.append(E.Item<T>, ST.items(T, xs, x), Con{E.Item{U32.from_nat(idx), v}, ST.items(T, xs, y)}),
      Equal.cong(List<&2, Maybe<&2, T>>, List<&2, E.Item<T>>, z => ST.items(T, z, o2), AR.slots(Maybe<&2, T>, tv2), SC.update(Maybe<&2, T>, xs, idx, Some{v}), AR.upd_slots(Maybe<&2, T>, depth, tv, idx, Some{v}, hr, pfv)),
      II.items_ins(T, xs, x, y, idx, v, IL.notin_l(idx, x, y, hfo), IL.notin_r(idx, x, y, hfo), AR.len_lt(Maybe<&2, T>, depth, tv, idx, pfv, hr))))


# Free-chain metadata is irrelevant to the live-order shadow, but is retained
# exactly by this realization. Its disjointness invariant is a separate layer.
def real_with_free(~T: Data, sh: ST.Shadow<T>, free: U32) -> D.DList<T>:
  ST.Sh{+tag, +fresh, +depth, tv, tp, tn, +ord} = sh
  D.DL{tag, U32.from_nat(fresh), free, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn)}

def LIX(~T: Data, +tag: U32, +free: U32, +fr: U32, +n: U32, +cnt: Nat, +hdv: U32, +tlv: U32, +depth: Nat, vals: Array<Maybe<&2, T>>, prevs: Array<U32>, nexts: Array<U32>) -> D.DList<T> & E.Handle:
  (D.DL{tag, fr, free, cnt, hdv, tlv, depth, U.pow2u(depth), vals, prevs, nexts}, E.H{tag, n})

def li_rt(~T: Data, +tag: U32, +fresh: Nat, +idx: Nat, +free: U32, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: T, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, x, y)}) == True{} : Bool}, +hr: {Nat.is_lt(idx, SC.pow2(depth)) == True{} : Bool}) -> {D.link_in(~T, tag, U32.from_nat(idx), U32.from_nat(fresh), free, SC.length(Nat, SC.append(Nat, x, y)), ST.hd(SC.append(Nat, x, y)), ST.lst(SC.append(Nat, x, y)), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn), LK.lastl(x, D.nil()), ST.hd_or(y, D.nil()), v) == (real_with_free(~T, lsh(~T, tag, fresh, idx, depth, tv, tp, tn, x, y, v), free), E.H{tag, U32.from_nat(idx)}) : D.DList<T> & E.Handle}:
  +o = SC.append(Nat, x, y)
  +o2 = SC.append(Nat, x, Con{idx, y})
  +a = LK.lastl(x, D.nil())
  +b = ST.hd_or(y, D.nil())
  +fr = U32.from_nat(idx)
  +lf = ST.ln(idx)
  +hd = F.g_depth(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +pfv = F.g_tv(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +pfp = F.g_tp(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +pfn = F.g_tn(~T, tag, fresh, depth, tv, tp, tn, o, h)
  +hlo = K.alllt_mono(o, fresh, SC.pow2(depth), F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, o, h), F.g_lt(~T, tag, fresh, depth, tv, tp, tn, o, h))
  +hlx = TL.alllt_l(x, y, SC.pow2(depth), hlo)
  +hly = TL.alllt_r(x, y, SC.pow2(depth), hlo)
  +tv2 = AR.upd(Maybe<&2, T>, depth, tv, idx, Some{v})
  +tp1 = AR.upd(U32, depth, tp, idx, a)
  +tn1 = AR.upd(U32, depth, tn, idx, b)
  +tp2 = TS.tpup(depth, tp1, y, lf)
  +tn2 = TS.tnup(depth, tn1, x, lf)
  +ep = Equal.trans(Array<U32>, D.set_next(Array.set(U32, AR.thaw(U32, tp), fr, a), b, lf), D.set_next(AR.thaw(U32, tp1), b, lf), AR.thaw(U32, tp2),
    Equal.cong(Array<U32>, Array<U32>, z => D.set_next(z, b, lf), Array.set(U32, AR.thaw(U32, tp), fr, a), AR.thaw(U32, tp1), IN.set_f(U32, depth, tp, idx, a, hd, hr, pfp)),
    TS.sn_first(depth, tp1, y, lf, hd, AR.upd_perfect(U32, depth, tp, idx, a, pfp), hly))
  +en = Equal.trans(Array<U32>, D.set_next(Array.set(U32, AR.thaw(U32, tn), fr, b), a, lf), D.set_next(AR.thaw(U32, tn1), a, lf), AR.thaw(U32, tn2),
    Equal.cong(Array<U32>, Array<U32>, z => D.set_next(z, a, lf), Array.set(U32, AR.thaw(U32, tn), fr, b), AR.thaw(U32, tn1), IN.set_f(U32, depth, tn, idx, b, hd, hr, pfn)),
    TS.sn_last(depth, tn1, x, lf, hd, AR.upd_perfect(U32, depth, tn, idx, b, pfn), hlx))
  %Equal.sym(U32, U32.inc(fr), lf, IX.inc_bridge(idx)) : {LIX(~T, tag, free, U32.from_nat(fresh), fr, 1n+SC.length(Nat, o), D.pick_end(U32.is_eq(a, D.nil()), _, ST.hd(o)), D.pick_end(U32.is_eq(b, D.nil()), _, ST.lst(o)), depth, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), fr, Some{v}), D.set_next(Array.set(U32, AR.thaw(U32, tp), fr, a), b, _), D.set_next(Array.set(U32, AR.thaw(U32, tn), fr, b), a, _)) == (real_with_free(~T, lsh(~T, tag, fresh, idx, depth, tv, tp, tn, x, y, v), free), E.H{tag, fr}) : D.DList<T> & E.Handle}
  %Equal.sym(Nat, 1n+SC.length(Nat, o), SC.length(Nat, o2), II.cnt_ins(x, idx, y)) : {LIX(~T, tag, free, U32.from_nat(fresh), fr, _, D.pick_end(U32.is_eq(a, D.nil()), lf, ST.hd(o)), D.pick_end(U32.is_eq(b, D.nil()), lf, ST.lst(o)), depth, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), fr, Some{v}), D.set_next(Array.set(U32, AR.thaw(U32, tp), fr, a), b, lf), D.set_next(Array.set(U32, AR.thaw(U32, tn), fr, b), a, lf)) == (real_with_free(~T, lsh(~T, tag, fresh, idx, depth, tv, tp, tn, x, y, v), free), E.H{tag, fr}) : D.DList<T> & E.Handle}
  %Equal.sym(U32, D.pick_end(U32.is_eq(a, D.nil()), lf, ST.hd(o)), ST.hd(o2), II.hd_ins(x, idx, y, depth, hd, hlx)) : {LIX(~T, tag, free, U32.from_nat(fresh), fr, SC.length(Nat, o2), _, D.pick_end(U32.is_eq(b, D.nil()), lf, ST.lst(o)), depth, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), fr, Some{v}), D.set_next(Array.set(U32, AR.thaw(U32, tp), fr, a), b, lf), D.set_next(Array.set(U32, AR.thaw(U32, tn), fr, b), a, lf)) == (real_with_free(~T, lsh(~T, tag, fresh, idx, depth, tv, tp, tn, x, y, v), free), E.H{tag, fr}) : D.DList<T> & E.Handle}
  %Equal.sym(U32, D.pick_end(U32.is_eq(b, D.nil()), lf, ST.lst(o)), ST.lst(o2), II.tl_ins(x, idx, y, depth, hd, hly)) : {LIX(~T, tag, free, U32.from_nat(fresh), fr, SC.length(Nat, o2), ST.hd(o2), _, depth, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), fr, Some{v}), D.set_next(Array.set(U32, AR.thaw(U32, tp), fr, a), b, lf), D.set_next(Array.set(U32, AR.thaw(U32, tn), fr, b), a, lf)) == (real_with_free(~T, lsh(~T, tag, fresh, idx, depth, tv, tp, tn, x, y, v), free), E.H{tag, fr}) : D.DList<T> & E.Handle}
  %Equal.sym(Array<Maybe<&2, T>>, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), fr, Some{v}), AR.thaw(Maybe<&2, T>, tv2), IN.set_f(Maybe<&2, T>, depth, tv, idx, Some{v}, hd, hr, pfv)) : {LIX(~T, tag, free, U32.from_nat(fresh), fr, SC.length(Nat, o2), ST.hd(o2), ST.lst(o2), depth, _, D.set_next(Array.set(U32, AR.thaw(U32, tp), fr, a), b, lf), D.set_next(Array.set(U32, AR.thaw(U32, tn), fr, b), a, lf)) == (real_with_free(~T, lsh(~T, tag, fresh, idx, depth, tv, tp, tn, x, y, v), free), E.H{tag, fr}) : D.DList<T> & E.Handle}
  %Equal.sym(Array<U32>, D.set_next(Array.set(U32, AR.thaw(U32, tp), fr, a), b, lf), AR.thaw(U32, tp2), ep) : {LIX(~T, tag, free, U32.from_nat(fresh), fr, SC.length(Nat, o2), ST.hd(o2), ST.lst(o2), depth, AR.thaw(Maybe<&2, T>, tv2), _, D.set_next(Array.set(U32, AR.thaw(U32, tn), fr, b), a, lf)) == (real_with_free(~T, lsh(~T, tag, fresh, idx, depth, tv, tp, tn, x, y, v), free), E.H{tag, fr}) : D.DList<T> & E.Handle}
  %Equal.sym(Array<U32>, D.set_next(Array.set(U32, AR.thaw(U32, tn), fr, b), a, lf), AR.thaw(U32, tn2), en) : {LIX(~T, tag, free, U32.from_nat(fresh), fr, SC.length(Nat, o2), ST.hd(o2), ST.lst(o2), depth, AR.thaw(Maybe<&2, T>, tv2), AR.thaw(U32, tp2), _) == (real_with_free(~T, lsh(~T, tag, fresh, idx, depth, tv, tp, tn, x, y, v), free), E.H{tag, fr}) : D.DList<T> & E.Handle}
  {==}

