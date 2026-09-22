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

# Growth: when fresh = 2^depth the runtime doubles the three blocks, the old
# block becoming the lower half; ids below 2^depth keep their slots, so the
# abstraction and the invariant are unchanged.

def gsh(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>) -> ST.Shadow<T>:
  ST.Sh{tag, fresh, 1n+depth, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}, AR.TNode{tp, AR.trep(U32, depth, D.nil())}, AR.TNode{tn, AR.trep(U32, depth, D.nil())}, ord}

def vat_app(-T: Data, +xs: List<&2, Maybe<&2, T>>, +zs: List<&2, Maybe<&2, T>>, +p: Nat, +h: {Nat.is_lt(p, SC.length(Maybe<&2, T>, xs)) == True{} : Bool}) -> {ST.vat(T, SC.append(Maybe<&2, T>, xs, zs), p) == ST.vat(T, xs, p) : Maybe<&2, T>}:
  Equal.cong(Maybe<&2, Maybe<&2, T>>, Maybe<&2, T>, m => ST.flat(T, m), SC.nth(Maybe<&2, T>, SC.append(Maybe<&2, T>, xs, zs), p), SC.nth(Maybe<&2, T>, xs, p), LL.nth_append_left(Maybe<&2, T>, xs, zs, p, h))

def lat_app(+ps: List<&2, U32>, +zs: List<&2, U32>, +p: Nat, +h: {Nat.is_lt(p, SC.length(U32, ps)) == True{} : Bool}) -> {ST.lat(SC.append(U32, ps, zs), p) == ST.lat(ps, p) : U32}:
  Equal.cong(Maybe<&2, U32>, U32, m => L.some_value(U32, m, 0), SC.nth(U32, SC.append(U32, ps, zs), p), SC.nth(U32, ps, p), LL.nth_append_left(U32, ps, zs, p, h))

def lv_grow(-T: Data, k: Nat, +xs: List<&2, Maybe<&2, T>>, +zs: List<&2, Maybe<&2, T>>, +p: Nat, +ord: List<&2, Nat>, +hk: {Nat.is_le(Nat.add(k, p), SC.length(Maybe<&2, T>, xs)) == True{} : Bool}) -> {ST.lv(T, k, SC.append(Maybe<&2, T>, xs, zs), p, ord) == ST.lv(T, k, xs, p, ord) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +k1:
      +hp = N.lt_le_trans(p, 1n+Nat.add(k1, p), SC.length(Maybe<&2, T>, xs), N.le_lt_trans(p, Nat.add(k1, p), 1n+Nat.add(k1, p), L.subst(Nat, z => {Nat.is_le(p, z) == True{} : Bool}, Nat.add(p, k1), Nat.add(k1, p), N.add_comm(p, k1), N.le_add_right(p, k1)), N.lt_succ(Nat.add(k1, p))), hk)
      +ih = lv_grow(T, k1, xs, zs, 1n+p, ord, L.subst(Nat, z => {Nat.is_le(z, SC.length(Maybe<&2, T>, xs)) == True{} : Bool}, Nat.add(1n+k1, p), Nat.add(k1, 1n+p), Equal.sym(Nat, Nat.add(k1, 1n+p), Nat.add(1n+k1, p), N.add_succ(k1, p)), hk))
      %Equal.sym(Maybe<&2, T>, ST.vat(T, SC.append(Maybe<&2, T>, xs, zs), p), ST.vat(T, xs, p), vat_app(T, xs, zs, p, hp)) : {Bool.and(ST.beq(ST.is_some(T, _), ST.lmem(p, ord)), ST.lv(T, k1, SC.append(Maybe<&2, T>, xs, zs), 1n+p, ord)) == Bool.and(ST.beq(ST.is_some(T, ST.vat(T, xs, p)), ST.lmem(p, ord)), ST.lv(T, k1, xs, 1n+p, ord)) : Bool}
      %Equal.sym(Bool, ST.lv(T, k1, SC.append(Maybe<&2, T>, xs, zs), 1n+p, ord), ST.lv(T, k1, xs, 1n+p, ord), ih) : {Bool.and(ST.beq(ST.is_some(T, ST.vat(T, xs, p)), ST.lmem(p, ord)), _) == Bool.and(ST.beq(ST.is_some(T, ST.vat(T, xs, p)), ST.lmem(p, ord)), ST.lv(T, k1, xs, 1n+p, ord)) : Bool}
      {==}

def lk_grow(+ord: List<&2, Nat>, +pv: U32, +e: U32, +ps: List<&2, U32>, +zs: List<&2, U32>, +ns: List<&2, U32>, +ws: List<&2, U32>, +hp: {ST.alllt(ord, SC.length(U32, ps)) == True{} : Bool}, +hn: {ST.alllt(ord, SC.length(U32, ns)) == True{} : Bool}) -> {ST.lk(ord, pv, e, SC.append(U32, ps, zs), SC.append(U32, ns, ws)) == ST.lk(ord, pv, e, ps, ns) : Bool}:
  match ord:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +ih = lk_grow(t, ST.ln(x), e, ps, zs, ns, ws, IT.lt_tail(x, t, SC.length(U32, ps), hp), IT.lt_tail(x, t, SC.length(U32, ns), hn))
      %Equal.sym(U32, ST.lat(SC.append(U32, ps, zs), x), ST.lat(ps, x), lat_app(ps, zs, x, IT.lt_head(x, t, SC.length(U32, ps), hp))) : {Bool.and(U32.is_eq(_, pv), Bool.and(U32.is_eq(ST.lat(SC.append(U32, ns, ws), x), ST.hd_or(t, e)), ST.lk(t, ST.ln(x), e, SC.append(U32, ps, zs), SC.append(U32, ns, ws)))) == ST.lk(Con{x, t}, pv, e, ps, ns) : Bool}
      %Equal.sym(U32, ST.lat(SC.append(U32, ns, ws), x), ST.lat(ns, x), lat_app(ns, ws, x, IT.lt_head(x, t, SC.length(U32, ns), hn))) : {Bool.and(U32.is_eq(ST.lat(ps, x), pv), Bool.and(U32.is_eq(_, ST.hd_or(t, e)), ST.lk(t, ST.ln(x), e, SC.append(U32, ps, zs), SC.append(U32, ns, ws)))) == ST.lk(Con{x, t}, pv, e, ps, ns) : Bool}
      %Equal.sym(Bool, ST.lk(t, ST.ln(x), e, SC.append(U32, ps, zs), SC.append(U32, ns, ws)), ST.lk(t, ST.ln(x), e, ps, ns), ih) : {Bool.and(U32.is_eq(ST.lat(ps, x), pv), Bool.and(U32.is_eq(ST.lat(ns, x), ST.hd_or(t, e)), _)) == ST.lk(Con{x, t}, pv, e, ps, ns) : Bool}
      {==}

def items_grow(-T: Data, +xs: List<&2, Maybe<&2, T>>, +zs: List<&2, Maybe<&2, T>>, +ord: List<&2, Nat>, +h: {ST.alllt(ord, SC.length(Maybe<&2, T>, xs)) == True{} : Bool}) -> {ST.items(T, SC.append(Maybe<&2, T>, xs, zs), ord) == ST.items(T, xs, ord) : List<&2, E.Item<T>>}:
  match ord:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      +ih = items_grow(T, xs, zs, t, IT.lt_tail(p, t, SC.length(Maybe<&2, T>, xs), h))
      %Equal.sym(Maybe<&2, T>, ST.vat(T, SC.append(Maybe<&2, T>, xs, zs), p), ST.vat(T, xs, p), vat_app(T, xs, zs, p, IT.lt_head(p, t, SC.length(Maybe<&2, T>, xs), h))) : {ST.itm(T, _, p, ST.items(T, SC.append(Maybe<&2, T>, xs, zs), t)) == ST.items(T, xs, Con{p, t}) : List<&2, E.Item<T>>}
      %Equal.sym(List<&2, E.Item<T>>, ST.items(T, SC.append(Maybe<&2, T>, xs, zs), t), ST.items(T, xs, t), ih) : {ST.itm(T, ST.vat(T, xs, p), p, _) == ST.items(T, xs, Con{p, t}) : List<&2, E.Item<T>>}
      {==}

def g_good(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hdl: {Nat.is_lt(depth, 31n) == True{} : Bool}) -> {ST.good(~T, gsh(~T, tag, fresh, depth, tv, tp, tn, ord)) == True{} : Bool}:
  +xs = AR.slots(Maybe<&2, T>, tv)
  +ps = AR.slots(U32, tp)
  +ns = AR.slots(U32, tn)
  +rv = AR.trep(Maybe<&2, T>, depth, None{})
  +rp = AR.trep(U32, depth, D.nil())
  +rn = AR.trep(U32, depth, D.nil())
  +pfv = F.g_tv(~T, tag, fresh, depth, tv, tp, tn, ord, h)
  +pfp = F.g_tp(~T, tag, fresh, depth, tv, tp, tn, ord, h)
  +pfn = F.g_tn(~T, tag, fresh, depth, tv, tp, tn, ord, h)
  +hf = F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, ord, h)
  +hlt = F.g_lt(~T, tag, fresh, depth, tv, tp, tn, ord, h)
  +lenv = AR.slots_length(Maybe<&2, T>, depth, tv, pfv)
  +lenp = AR.slots_length(U32, depth, tp, pfp)
  +lenn = AR.slots_length(U32, depth, tn, pfn)
  +hfv = L.subst(Nat, z => {Nat.is_le(Nat.add(fresh, 0n), z) == True{} : Bool}, SC.pow2(depth), SC.length(Maybe<&2, T>, xs), Equal.sym(Nat, SC.length(Maybe<&2, T>, xs), SC.pow2(depth), lenv), L.subst(Nat, z => {Nat.is_le(z, SC.pow2(depth)) == True{} : Bool}, fresh, Nat.add(fresh, 0n), Equal.sym(Nat, Nat.add(fresh, 0n), fresh, N.add_zero(fresh)), hf))
  +hop = K.alllt_mono(ord, fresh, SC.length(U32, ps), L.subst(Nat, z => {Nat.is_le(fresh, z) == True{} : Bool}, SC.pow2(depth), SC.length(U32, ps), Equal.sym(Nat, SC.length(U32, ps), SC.pow2(depth), lenp), hf), hlt)
  +hon = K.alllt_mono(ord, fresh, SC.length(U32, ns), L.subst(Nat, z => {Nat.is_le(fresh, z) == True{} : Bool}, SC.pow2(depth), SC.length(U32, ns), Equal.sym(Nat, SC.length(U32, ns), SC.pow2(depth), lenn), hf), hlt)
  +hlv = Equal.trans(Bool, ST.lv(T, fresh, SC.append(Maybe<&2, T>, xs, AR.slots(Maybe<&2, T>, rv)), 0n, ord), ST.lv(T, fresh, xs, 0n, ord), True{}, lv_grow(T, fresh, xs, AR.slots(Maybe<&2, T>, rv), 0n, ord, hfv), F.g_lv(~T, tag, fresh, depth, tv, tp, tn, ord, h))
  +hlk = Equal.trans(Bool, ST.lk(ord, D.nil(), D.nil(), SC.append(U32, ps, AR.slots(U32, rp)), SC.append(U32, ns, AR.slots(U32, rn))), ST.lk(ord, D.nil(), D.nil(), ps, ns), True{}, lk_grow(ord, D.nil(), D.nil(), ps, AR.slots(U32, rp), ns, AR.slots(U32, rn), hop, hon), F.g_lk(~T, tag, fresh, depth, tv, tp, tn, ord, h))
  F.good_mk(~T, tag, fresh, 1n+depth, AR.TNode{tv, rv}, AR.TNode{tp, rp}, AR.TNode{tn, rn}, ord, N.lt_succ_le_succ(depth, 31n, hdl),
    L.and_intro(AR.perfect(Maybe<&2, T>, depth, tv), AR.perfect(Maybe<&2, T>, depth, rv), pfv, AR.trep_perfect(Maybe<&2, T>, depth, None{})),
    L.and_intro(AR.perfect(U32, depth, tp), AR.perfect(U32, depth, rp), pfp, AR.trep_perfect(U32, depth, D.nil())),
    L.and_intro(AR.perfect(U32, depth, tn), AR.perfect(U32, depth, rn), pfn, AR.trep_perfect(U32, depth, D.nil())),
    N.le_trans(fresh, SC.pow2(depth), SC.pow2(1n+depth), hf, N.lt_le(SC.pow2(depth), SC.pow2(1n+depth), N.pow2_lt_succ(depth))),
    hlt, F.g_nd(~T, tag, fresh, depth, tv, tp, tn, ord, h), hlv, hlk)

# the items along a stretch of the order are those of the lower half
def g_items(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +zs: List<&2, Nat>, +hz: {ST.alllt(zs, fresh) == True{} : Bool}) -> {ST.items(T, AR.slots(Maybe<&2, T>, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}), zs) == ST.items(T, AR.slots(Maybe<&2, T>, tv), zs) : List<&2, E.Item<T>>}:
  +pfv = F.g_tv(~T, tag, fresh, depth, tv, tp, tn, ord, h)
  +lenv = AR.slots_length(Maybe<&2, T>, depth, tv, pfv)
  items_grow(T, AR.slots(Maybe<&2, T>, tv), AR.slots(Maybe<&2, T>, AR.trep(Maybe<&2, T>, depth, None{})), zs,
    K.alllt_mono(zs, fresh, SC.length(Maybe<&2, T>, AR.slots(Maybe<&2, T>, tv)), L.subst(Nat, z => {Nat.is_le(fresh, z) == True{} : Bool}, SC.pow2(depth), SC.length(Maybe<&2, T>, AR.slots(Maybe<&2, T>, tv)), Equal.sym(Nat, SC.length(Maybe<&2, T>, AR.slots(Maybe<&2, T>, tv)), SC.pow2(depth), lenv), F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, ord, h)), hz))

def g_vals(~T: Data, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>) -> {D.grown_vals(~T, depth, AR.thaw(Maybe<&2, T>, tv)) == AR.thaw(Maybe<&2, T>, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}) : Array<Maybe<&2, T>>}:
  %Equal.sym(Array<Maybe<&2, T>>, Array.new(Maybe<&2, T>, depth, None{}), AR.thaw(Maybe<&2, T>, AR.trep(Maybe<&2, T>, depth, None{})), AR.new(Maybe<&2, T>, depth, None{})) : {ANode{AR.thaw(Maybe<&2, T>, tv), _} == AR.thaw(Maybe<&2, T>, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}) : Array<Maybe<&2, T>>}
  {==}

def g_links(+depth: Nat, +t: AR.Tree<U32>) -> {D.grown_links(depth, AR.thaw(U32, t)) == AR.thaw(U32, AR.TNode{t, AR.trep(U32, depth, D.nil())}) : Array<U32>}:
  %Equal.sym(Array<U32>, Array.new(U32, depth, D.nil()), AR.thaw(U32, AR.trep(U32, depth, D.nil())), AR.new(U32, depth, D.nil())) : {ANode{AR.thaw(U32, t), _} == AR.thaw(U32, AR.TNode{t, AR.trep(U32, depth, D.nil())}) : Array<U32>}
  {==}
