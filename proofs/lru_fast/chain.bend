import Base
import ../lib/logic.bend as L
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../binary_heap/u32idx.bend as IX
import ../../spec/common.bend as SC
import ../../src/lru/fast.bend as F
import support/link_primitives.bend as D
import support/links_state.bend as DST
import support/links_links.bend as LK
import support/links_rmfacts.bend as RF
import support/links_tset.bend as TS
import support/links_tolist.bend as TL
import support/links_insitems.bend as II
import support/links_insert.bend as IN

# The recency chain of the indexed LRU (src/lru/fast.bend `Chain`) computed
# on Data mirror trees. The chain's links are slot + 1 with 0 = none, the
# encoding of the doubly linked list (proofs/dlist), so its link lemmas are
# reused: the runtime helpers are first shown equal to the DLL's.

def pick_eq(b: Bool, +x: U32, +y: U32) -> {F.pick(b, x, y) == D.pick_end(b, x, y) : U32}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sal_eq(-a: Array<U32>, +l: U32, +x: U32, b: Bool) -> {F.set_at_link(a, l, x, b) == D.set_next_go(a, l, x, b) : Array<U32>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def link_ln(+s: Nat) -> {F.link(U32.from_nat(s)) == DST.ln(s) : U32}:
  IX.inc_bridge(s)

def cpair(+t: AR.Tree<U32>, +x: U32) -> Array<U32> & U32:
  (AR.thaw(U32, t), x)

# reading the link stored for slot s
def get_link(+depth: Nat, +t: AR.Tree<U32>, +s: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pf: {AR.perfect(U32, depth, t) == True{} : Bool}, +hs: {Nat.is_lt(s, SC.pow2(depth)) == True{} : Bool}) -> {Array.get(U32, AR.thaw(U32, t), U32.from_nat(s)) == cpair(t, DST.lat(AR.slots(U32, t), s)) : Array<U32> & U32}:
  TL.get_at(U32, depth, t, s, 0, hd, pf, hs)

# ---- unlink ----

def ul_fin_ok(+depth: Nat, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +fh: U32, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfp: {AR.perfect(U32, depth, tp) == True{} : Bool}, +pfn: {AR.perfect(U32, depth, tn) == True{} : Bool}, +hla: {DST.alllt(a, SC.pow2(depth)) == True{} : Bool}, +hlb: {DST.alllt(b, SC.pow2(depth)) == True{} : Bool}) -> {F.ul_fin(DST.hd(SC.append(Nat, a, Con{s, b})), DST.lst(SC.append(Nat, a, Con{s, b})), fh, AR.thaw(U32, tp), AR.thaw(U32, tn), LK.lastl(a, D.nil()), DST.hd_or(b, D.nil())) == F.CH{DST.hd(SC.append(Nat, a, b)), DST.lst(SC.append(Nat, a, b)), fh, AR.thaw(U32, TS.tpup(depth, tp, b, LK.lastl(a, D.nil()))), AR.thaw(U32, TS.tnup(depth, tn, a, DST.hd_or(b, D.nil())))} : F.Chain}:
  +o = SC.append(Nat, a, Con{s, b})
  +p = LK.lastl(a, D.nil())
  +q = DST.hd_or(b, D.nil())
  %Equal.sym(U32, F.pick(U32.is_eq(p, F.nil()), q, DST.hd(o)), DST.hd(SC.append(Nat, a, b)), Equal.trans(U32, F.pick(U32.is_eq(p, F.nil()), q, DST.hd(o)), D.pick_end(U32.is_eq(p, D.nil()), q, DST.hd(o)), DST.hd(SC.append(Nat, a, b)), pick_eq(U32.is_eq(p, F.nil()), q, DST.hd(o)), RF.hd_cut(a, s, b, depth, hd, hla))) : {F.CH{_, F.pick(U32.is_eq(q, F.nil()), p, DST.lst(o)), fh, F.set_at_link(AR.thaw(U32, tp), q, p, U32.is_eq(q, F.nil())), F.set_at_link(AR.thaw(U32, tn), p, q, U32.is_eq(p, F.nil()))} == F.CH{DST.hd(SC.append(Nat, a, b)), DST.lst(SC.append(Nat, a, b)), fh, AR.thaw(U32, TS.tpup(depth, tp, b, p)), AR.thaw(U32, TS.tnup(depth, tn, a, q))} : F.Chain}
  %Equal.sym(U32, F.pick(U32.is_eq(q, F.nil()), p, DST.lst(o)), DST.lst(SC.append(Nat, a, b)), Equal.trans(U32, F.pick(U32.is_eq(q, F.nil()), p, DST.lst(o)), D.pick_end(U32.is_eq(q, D.nil()), p, DST.lst(o)), DST.lst(SC.append(Nat, a, b)), pick_eq(U32.is_eq(q, F.nil()), p, DST.lst(o)), RF.tl_cut(a, s, b, depth, hd, hlb))) : {F.CH{DST.hd(SC.append(Nat, a, b)), _, fh, F.set_at_link(AR.thaw(U32, tp), q, p, U32.is_eq(q, F.nil())), F.set_at_link(AR.thaw(U32, tn), p, q, U32.is_eq(p, F.nil()))} == F.CH{DST.hd(SC.append(Nat, a, b)), DST.lst(SC.append(Nat, a, b)), fh, AR.thaw(U32, TS.tpup(depth, tp, b, p)), AR.thaw(U32, TS.tnup(depth, tn, a, q))} : F.Chain}
  %Equal.sym(Array<U32>, F.set_at_link(AR.thaw(U32, tp), q, p, U32.is_eq(q, F.nil())), AR.thaw(U32, TS.tpup(depth, tp, b, p)), Equal.trans(Array<U32>, F.set_at_link(AR.thaw(U32, tp), q, p, U32.is_eq(q, F.nil())), D.set_next(AR.thaw(U32, tp), q, p), AR.thaw(U32, TS.tpup(depth, tp, b, p)), sal_eq(AR.thaw(U32, tp), q, p, U32.is_eq(q, F.nil())), TS.sn_first(depth, tp, b, p, hd, pfp, hlb))) : {F.CH{DST.hd(SC.append(Nat, a, b)), DST.lst(SC.append(Nat, a, b)), fh, _, F.set_at_link(AR.thaw(U32, tn), p, q, U32.is_eq(p, F.nil()))} == F.CH{DST.hd(SC.append(Nat, a, b)), DST.lst(SC.append(Nat, a, b)), fh, AR.thaw(U32, TS.tpup(depth, tp, b, p)), AR.thaw(U32, TS.tnup(depth, tn, a, q))} : F.Chain}
  %Equal.sym(Array<U32>, F.set_at_link(AR.thaw(U32, tn), p, q, U32.is_eq(p, F.nil())), AR.thaw(U32, TS.tnup(depth, tn, a, q)), Equal.trans(Array<U32>, F.set_at_link(AR.thaw(U32, tn), p, q, U32.is_eq(p, F.nil())), D.set_next(AR.thaw(U32, tn), p, q), AR.thaw(U32, TS.tnup(depth, tn, a, q)), sal_eq(AR.thaw(U32, tn), p, q, U32.is_eq(p, F.nil())), TS.sn_last(depth, tn, a, q, hd, pfn, hla))) : {F.CH{DST.hd(SC.append(Nat, a, b)), DST.lst(SC.append(Nat, a, b)), fh, AR.thaw(U32, TS.tpup(depth, tp, b, p)), _} == F.CH{DST.hd(SC.append(Nat, a, b)), DST.lst(SC.append(Nat, a, b)), fh, AR.thaw(U32, TS.tpup(depth, tp, b, p)), AR.thaw(U32, TS.tnup(depth, tn, a, q))} : F.Chain}
  {==}

# Detaching live slot s from the chain of the order a ++ [s] ++ b.
def unlink_ok(+depth: Nat, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +fh: U32, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfp: {AR.perfect(U32, depth, tp) == True{} : Bool}, +pfn: {AR.perfect(U32, depth, tn) == True{} : Bool}, +hl: {DST.alllt(SC.append(Nat, a, Con{s, b}), SC.pow2(depth)) == True{} : Bool}, +hk: {DST.lk(SC.append(Nat, a, Con{s, b}), D.nil(), D.nil(), AR.slots(U32, tp), AR.slots(U32, tn)) == True{} : Bool}) -> {F.unlink(F.CH{DST.hd(SC.append(Nat, a, Con{s, b})), DST.lst(SC.append(Nat, a, Con{s, b})), fh, AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)) == F.CH{DST.hd(SC.append(Nat, a, b)), DST.lst(SC.append(Nat, a, b)), fh, AR.thaw(U32, TS.tpup(depth, tp, b, LK.lastl(a, D.nil()))), AR.thaw(U32, TS.tnup(depth, tn, a, DST.hd_or(b, D.nil())))} : F.Chain}:
  +o = SC.append(Nat, a, Con{s, b})
  +p = LK.lastl(a, D.nil())
  +q = DST.hd_or(b, D.nil())
  +ps = AR.slots(U32, tp)
  +ns = AR.slots(U32, tn)
  +hla = TL.alllt_l(a, Con{s, b}, SC.pow2(depth), hl)
  +hlsb = TL.alllt_r(a, Con{s, b}, SC.pow2(depth), hl)
  +hs = L.and_left(Nat.is_lt(s, SC.pow2(depth)), DST.alllt(b, SC.pow2(depth)), hlsb)
  +hlb = L.and_right(Nat.is_lt(s, SC.pow2(depth)), DST.alllt(b, SC.pow2(depth)), hlsb)
  %Equal.sym(Array<U32> & U32, Array.get(U32, AR.thaw(U32, tp), U32.from_nat(s)), cpair(tp, p), Equal.trans(Array<U32> & U32, Array.get(U32, AR.thaw(U32, tp), U32.from_nat(s)), cpair(tp, DST.lat(ps, s)), cpair(tp, p), get_link(depth, tp, s, hd, pfp, hs), Equal.cong(U32, Array<U32> & U32, z => cpair(tp, z), DST.lat(ps, s), p, RF.plink(a, s, b, ps, ns, hk)))) : {F.ul_p(U32.from_nat(s), DST.hd(o), DST.lst(o), fh, AR.thaw(U32, tn), _) == F.CH{DST.hd(SC.append(Nat, a, b)), DST.lst(SC.append(Nat, a, b)), fh, AR.thaw(U32, TS.tpup(depth, tp, b, p)), AR.thaw(U32, TS.tnup(depth, tn, a, q))} : F.Chain}
  %Equal.sym(Array<U32> & U32, Array.get(U32, AR.thaw(U32, tn), U32.from_nat(s)), cpair(tn, q), Equal.trans(Array<U32> & U32, Array.get(U32, AR.thaw(U32, tn), U32.from_nat(s)), cpair(tn, DST.lat(ns, s)), cpair(tn, q), get_link(depth, tn, s, hd, pfn, hs), Equal.cong(U32, Array<U32> & U32, z => cpair(tn, z), DST.lat(ns, s), q, RF.nlink(a, s, b, ps, ns, hk)))) : {F.ul_q(DST.hd(o), DST.lst(o), fh, AR.thaw(U32, tp), p, _) == F.CH{DST.hd(SC.append(Nat, a, b)), DST.lst(SC.append(Nat, a, b)), fh, AR.thaw(U32, TS.tpup(depth, tp, b, p)), AR.thaw(U32, TS.tnup(depth, tn, a, q))} : F.Chain}
  ul_fin_ok(depth, tp, tn, a, s, b, fh, hd, pfp, pfn, hla, hlb)

# ---- link_tail ----

# Attaching slot s (not in the order) as the newest element.
def link_tail_ok(+depth: Nat, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +s: Nat, +fh: U32, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfp: {AR.perfect(U32, depth, tp) == True{} : Bool}, +pfn: {AR.perfect(U32, depth, tn) == True{} : Bool}, +hs: {Nat.is_lt(s, SC.pow2(depth)) == True{} : Bool}, +hl: {DST.alllt(ord, SC.pow2(depth)) == True{} : Bool}) -> {F.link_tail(F.CH{DST.hd(ord), DST.lst(ord), fh, AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)) == F.CH{DST.hd(SC.append(Nat, ord, Con{s, Nil{}})), DST.lst(SC.append(Nat, ord, Con{s, Nil{}})), fh, AR.thaw(U32, AR.upd(U32, depth, tp, s, LK.lastl(ord, D.nil()))), AR.thaw(U32, TS.tnup(depth, AR.upd(U32, depth, tn, s, D.nil()), ord, DST.ln(s)))} : F.Chain}:
  +t = DST.lst(ord)
  +L = LK.lastl(ord, D.nil())
  +o2 = SC.append(Nat, ord, Con{s, Nil{}})
  +tn1 = AR.upd(U32, depth, tn, s, D.nil())
  +pf1 = AR.upd_perfect(U32, depth, tn, s, D.nil(), pfn)
  +ehd = Equal.trans(U32, F.pick(U32.is_eq(L, F.nil()), DST.ln(s), DST.hd(ord)), D.pick_end(U32.is_eq(L, D.nil()), DST.ln(s), DST.hd(ord)), DST.hd(o2),
    pick_eq(U32.is_eq(L, F.nil()), DST.ln(s), DST.hd(ord)),
    Equal.trans(U32, D.pick_end(U32.is_eq(L, D.nil()), DST.ln(s), DST.hd(ord)), D.pick_end(U32.is_eq(L, D.nil()), DST.ln(s), DST.hd(SC.append(Nat, ord, Nil{}))), DST.hd(o2),
      Equal.cong(List<&2, Nat>, U32, z => D.pick_end(U32.is_eq(L, D.nil()), DST.ln(s), DST.hd(z)), ord, SC.append(Nat, ord, Nil{}), Equal.sym(List<&2, Nat>, SC.append(Nat, ord, Nil{}), ord, LL.append_nil(Nat, ord))),
      II.hd_ins(ord, s, Nil{}, depth, hd, hl)))
  +enx = Equal.trans(Array<U32>, F.set_at_link(Array.set(U32, AR.thaw(U32, tn), U32.from_nat(s), F.nil()), L, DST.ln(s), U32.is_eq(L, F.nil())), F.set_at_link(AR.thaw(U32, tn1), L, DST.ln(s), U32.is_eq(L, F.nil())), AR.thaw(U32, TS.tnup(depth, tn1, ord, DST.ln(s))),
    Equal.cong(Array<U32>, Array<U32>, z => F.set_at_link(z, L, DST.ln(s), U32.is_eq(L, F.nil())), Array.set(U32, AR.thaw(U32, tn), U32.from_nat(s), F.nil()), AR.thaw(U32, tn1), IN.set_f(U32, depth, tn, s, D.nil(), hd, hs, pfn)),
    Equal.trans(Array<U32>, F.set_at_link(AR.thaw(U32, tn1), L, DST.ln(s), U32.is_eq(L, F.nil())), D.set_next(AR.thaw(U32, tn1), L, DST.ln(s)), AR.thaw(U32, TS.tnup(depth, tn1, ord, DST.ln(s))),
      sal_eq(AR.thaw(U32, tn1), L, DST.ln(s), U32.is_eq(L, F.nil())),
      TS.sn_last(depth, tn1, ord, DST.ln(s), hd, pf1, hl)))
  %link_ln(s) : {F.CH{F.pick(U32.is_eq(t, F.nil()), _, DST.hd(ord)), _, fh, Array.set(U32, AR.thaw(U32, tp), U32.from_nat(s), t), F.set_at_link(Array.set(U32, AR.thaw(U32, tn), U32.from_nat(s), F.nil()), t, _, U32.is_eq(t, F.nil()))} == F.CH{DST.hd(o2), DST.lst(o2), fh, AR.thaw(U32, AR.upd(U32, depth, tp, s, L)), AR.thaw(U32, TS.tnup(depth, tn1, ord, DST.ln(s)))} : F.Chain}
  %Equal.sym(U32, t, L, TL.lst_lastl(ord)) : {F.CH{F.pick(U32.is_eq(_, F.nil()), DST.ln(s), DST.hd(ord)), DST.ln(s), fh, Array.set(U32, AR.thaw(U32, tp), U32.from_nat(s), _), F.set_at_link(Array.set(U32, AR.thaw(U32, tn), U32.from_nat(s), F.nil()), _, DST.ln(s), U32.is_eq(_, F.nil()))} == F.CH{DST.hd(o2), DST.lst(o2), fh, AR.thaw(U32, AR.upd(U32, depth, tp, s, L)), AR.thaw(U32, TS.tnup(depth, tn1, ord, DST.ln(s)))} : F.Chain}
  %Equal.sym(U32, F.pick(U32.is_eq(L, F.nil()), DST.ln(s), DST.hd(ord)), DST.hd(o2), ehd) : {F.CH{_, DST.ln(s), fh, Array.set(U32, AR.thaw(U32, tp), U32.from_nat(s), L), F.set_at_link(Array.set(U32, AR.thaw(U32, tn), U32.from_nat(s), F.nil()), L, DST.ln(s), U32.is_eq(L, F.nil()))} == F.CH{DST.hd(o2), DST.lst(o2), fh, AR.thaw(U32, AR.upd(U32, depth, tp, s, L)), AR.thaw(U32, TS.tnup(depth, tn1, ord, DST.ln(s)))} : F.Chain}
  %Equal.sym(U32, DST.lst(o2), DST.ln(s), RF.lst_app_cons(ord, s, Nil{})) : {F.CH{DST.hd(o2), DST.ln(s), fh, Array.set(U32, AR.thaw(U32, tp), U32.from_nat(s), L), F.set_at_link(Array.set(U32, AR.thaw(U32, tn), U32.from_nat(s), F.nil()), L, DST.ln(s), U32.is_eq(L, F.nil()))} == F.CH{DST.hd(o2), _, fh, AR.thaw(U32, AR.upd(U32, depth, tp, s, L)), AR.thaw(U32, TS.tnup(depth, tn1, ord, DST.ln(s)))} : F.Chain}
  %Equal.sym(Array<U32>, Array.set(U32, AR.thaw(U32, tp), U32.from_nat(s), L), AR.thaw(U32, AR.upd(U32, depth, tp, s, L)), IN.set_f(U32, depth, tp, s, L, hd, hs, pfp)) : {F.CH{DST.hd(o2), DST.ln(s), fh, _, F.set_at_link(Array.set(U32, AR.thaw(U32, tn), U32.from_nat(s), F.nil()), L, DST.ln(s), U32.is_eq(L, F.nil()))} == F.CH{DST.hd(o2), DST.ln(s), fh, AR.thaw(U32, AR.upd(U32, depth, tp, s, L)), AR.thaw(U32, TS.tnup(depth, tn1, ord, DST.ln(s)))} : F.Chain}
  %Equal.sym(Array<U32>, F.set_at_link(Array.set(U32, AR.thaw(U32, tn), U32.from_nat(s), F.nil()), L, DST.ln(s), U32.is_eq(L, F.nil())), AR.thaw(U32, TS.tnup(depth, tn1, ord, DST.ln(s))), enx) : {F.CH{DST.hd(o2), DST.ln(s), fh, AR.thaw(U32, AR.upd(U32, depth, tp, s, L)), _} == F.CH{DST.hd(o2), DST.ln(s), fh, AR.thaw(U32, AR.upd(U32, depth, tp, s, L)), AR.thaw(U32, TS.tnup(depth, tn1, ord, DST.ln(s)))} : F.Chain}
  {==}

# ---- the free list ----

# Releasing slot s: it becomes the head of the free chain.
def push_free_ok(+depth: Nat, +tn: AR.Tree<U32>, +fl: List<&2, Nat>, +s: Nat, +h: U32, +t: U32, -prevs: Array<U32>, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfn: {AR.perfect(U32, depth, tn) == True{} : Bool}, +hs: {Nat.is_lt(s, SC.pow2(depth)) == True{} : Bool}) -> {F.push_free(F.CH{h, t, DST.hd(fl), prevs, AR.thaw(U32, tn)}, U32.from_nat(s)) == F.CH{h, t, DST.hd(Con{s, fl}), prevs, AR.thaw(U32, AR.upd(U32, depth, tn, s, DST.hd(fl)))} : F.Chain}:
  %link_ln(s) : {F.CH{h, t, _, prevs, Array.set(U32, AR.thaw(U32, tn), U32.from_nat(s), DST.hd(fl))} == F.CH{h, t, DST.ln(s), prevs, AR.thaw(U32, AR.upd(U32, depth, tn, s, DST.hd(fl)))} : F.Chain}
  %Equal.sym(Array<U32>, Array.set(U32, AR.thaw(U32, tn), U32.from_nat(s), DST.hd(fl)), AR.thaw(U32, AR.upd(U32, depth, tn, s, DST.hd(fl))), IN.set_f(U32, depth, tn, s, DST.hd(fl), hd, hs, pfn)) : {F.CH{h, t, DST.ln(s), prevs, _} == F.CH{h, t, DST.ln(s), prevs, AR.thaw(U32, AR.upd(U32, depth, tn, s, DST.hd(fl)))} : F.Chain}
  {==}
