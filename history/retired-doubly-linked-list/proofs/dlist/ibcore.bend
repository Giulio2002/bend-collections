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
import ./insert.bend as IN
import ./grow.bend as GR
import ../graph/addedge.bend as AE

# insert_between on a good shadow whose order is x ++ y, with a = the last
# id of x and b = the first id of y: the list after the splice (growing the
# blocks first when they are full), under the room premise fresh < 2^q, q <= 31.

def ICore(~T: Data, rt: D.DList<T> & E.Handle, +hh: E.Handle, m: DS.Model<T>, +fresh: Nat) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh2 => {rt == (ST.real(~T, sh2), hh) : D.DList<T> & E.Handle} & ({ST.good(~T, sh2) == True{} : Bool} & ({ST.model(~T, sh2) == m : DS.Model<T>} & {K.sfresh(~T, sh2) == 1n+fresh : Nat}))>

def imk(~T: Data, -rt: D.DList<T> & E.Handle, -hh: E.Handle, -m: DS.Model<T>, -fresh: Nat, sh2: ST.Shadow<T>, e1: {rt == (ST.real(~T, sh2), hh) : D.DList<T> & E.Handle}, e2: {ST.good(~T, sh2) == True{} : Bool}, e3: {ST.model(~T, sh2) == m : DS.Model<T>}, e4: {K.sfresh(~T, sh2) == 1n+fresh : Nat}) -> ICore(~T, rt, hh, m, fresh):
  (sh2, (e1, (e2, (e3, e4))))

def IM(~T: Data, +tag: U32, +fresh: Nat, +xs: List<&2, Maybe<&2, T>>, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: T) -> DS.Model<T>:
  DS.DM{tag, 1n+fresh, SC.append(E.Item<T>, ST.items(T, xs, x), Con{E.Item{U32.from_nat(fresh), v}, ST.items(T, xs, y)})}

def IB(~T: Data, +tag: U32, +fresh: Nat, +ord: List<&2, Nat>, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +a: U32, +b: U32, v: T) -> D.DList<T> & E.Handle:
  D.insert_between(~T, tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn), a, b, v)

# the fresh id as a U32 has the value fresh
def fresh_nat(+fresh: Nat, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hf: {Nat.is_le(fresh, SC.pow2(depth)) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(fresh)) == fresh : Nat}:
  U.to_nat_from_nat(fresh, 1n+depth, N.lt_succ_le_succ(depth, 32n, N.le_lt_trans(depth, 31n, 32n, hd, N.lt_succ(31n))), N.le_lt_trans(fresh, SC.pow2(depth), SC.pow2(1n+depth), hf, N.pow2_lt_succ(depth)))

def g_rt(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +a: U32, +b: U32, +v: T) -> {D.insert_room(~T, tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn), a, b, v, False{}) == D.link_in(~T, tag, U32.from_nat(fresh), U32.inc(U32.from_nat(fresh)), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), 1n+depth, U.pow2u(1n+depth), AR.thaw(Maybe<&2, T>, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}), AR.thaw(U32, AR.TNode{tp, AR.trep(U32, depth, D.nil())}), AR.thaw(U32, AR.TNode{tn, AR.trep(U32, depth, D.nil())}), a, b, v) : D.DList<T> & E.Handle}:
  %Equal.sym(Array<Maybe<&2, T>>, D.grown_vals(~T, depth, AR.thaw(Maybe<&2, T>, tv)), AR.thaw(Maybe<&2, T>, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}), GR.g_vals(~T, depth, tv)) : {D.link_in(~T, tag, U32.from_nat(fresh), U32.inc(U32.from_nat(fresh)), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), 1n+depth, U32.shl(U.pow2u(depth)), _, D.grown_links(depth, AR.thaw(U32, tp)), D.grown_links(depth, AR.thaw(U32, tn)), a, b, v) == D.link_in(~T, tag, U32.from_nat(fresh), U32.inc(U32.from_nat(fresh)), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), 1n+depth, U.pow2u(1n+depth), AR.thaw(Maybe<&2, T>, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}), AR.thaw(U32, AR.TNode{tp, AR.trep(U32, depth, D.nil())}), AR.thaw(U32, AR.TNode{tn, AR.trep(U32, depth, D.nil())}), a, b, v) : D.DList<T> & E.Handle}
  %Equal.sym(Array<U32>, D.grown_links(depth, AR.thaw(U32, tp)), AR.thaw(U32, AR.TNode{tp, AR.trep(U32, depth, D.nil())}), GR.g_links(depth, tp)) : {D.link_in(~T, tag, U32.from_nat(fresh), U32.inc(U32.from_nat(fresh)), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), 1n+depth, U32.shl(U.pow2u(depth)), AR.thaw(Maybe<&2, T>, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}), _, D.grown_links(depth, AR.thaw(U32, tn)), a, b, v) == D.link_in(~T, tag, U32.from_nat(fresh), U32.inc(U32.from_nat(fresh)), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), 1n+depth, U.pow2u(1n+depth), AR.thaw(Maybe<&2, T>, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}), AR.thaw(U32, AR.TNode{tp, AR.trep(U32, depth, D.nil())}), AR.thaw(U32, AR.TNode{tn, AR.trep(U32, depth, D.nil())}), a, b, v) : D.DList<T> & E.Handle}
  %Equal.sym(Array<U32>, D.grown_links(depth, AR.thaw(U32, tn)), AR.thaw(U32, AR.TNode{tn, AR.trep(U32, depth, D.nil())}), GR.g_links(depth, tn)) : {D.link_in(~T, tag, U32.from_nat(fresh), U32.inc(U32.from_nat(fresh)), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), 1n+depth, U32.shl(U.pow2u(depth)), AR.thaw(Maybe<&2, T>, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}), AR.thaw(U32, AR.TNode{tp, AR.trep(U32, depth, D.nil())}), _, a, b, v) == D.link_in(~T, tag, U32.from_nat(fresh), U32.inc(U32.from_nat(fresh)), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), 1n+depth, U.pow2u(1n+depth), AR.thaw(Maybe<&2, T>, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}), AR.thaw(U32, AR.TNode{tp, AR.trep(U32, depth, D.nil())}), AR.thaw(U32, AR.TNode{tn, AR.trep(U32, depth, D.nil())}), a, b, v) : D.DList<T> & E.Handle}
  {==}

def ib_room(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: T, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, x, y)}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hroom: {Nat.is_lt(fresh, SC.pow2(q)) == True{} : Bool}, rb: Bool, +erb: {U32.is_lt(U32.from_nat(fresh), U.pow2u(depth)) == rb : Bool}) -> ICore(~T, D.insert_room(~T, tag, U32.from_nat(fresh), 0, SC.length(Nat, SC.append(Nat, x, y)), ST.hd(SC.append(Nat, x, y)), ST.lst(SC.append(Nat, x, y)), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn), LK.lastl(x, D.nil()), ST.hd_or(y, D.nil()), v, rb), E.H{tag, U32.from_nat(fresh)}, IM(~T, tag, fresh, AR.slots(Maybe<&2, T>, tv), x, y, v), fresh):
  match rb:
    case True{}:
      +o = SC.append(Nat, x, y)
      +hd = F.g_depth(~T, tag, fresh, depth, tv, tp, tn, o, h)
      +hf = F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, o, h)
      +hd32 = N.le_lt_trans(depth, 31n, 32n, hd, N.lt_succ(31n))
      +efn = fresh_nat(fresh, depth, hd, hf)
      +hb = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(depth)) == True{} : Bool}, U32.to_nat(U32.from_nat(fresh)), fresh, efn, AR.lt_bridge(U32.from_nat(fresh), depth, hd32, True{}, erb))
      imk(~T, D.insert_room(~T, tag, U32.from_nat(fresh), 0, SC.length(Nat, o), ST.hd(o), ST.lst(o), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn), LK.lastl(x, D.nil()), ST.hd_or(y, D.nil()), v, True{}), E.H{tag, U32.from_nat(fresh)}, IM(~T, tag, fresh, AR.slots(Maybe<&2, T>, tv), x, y, v), fresh,
        IN.lsh(~T, tag, fresh, depth, tv, tp, tn, x, y, v),
        IN.li_rt(~T, tag, fresh, depth, tv, tp, tn, x, y, v, h, hb),
        IN.li_good(~T, tag, fresh, depth, tv, tp, tn, x, y, v, h, hb),
        IN.li_model(~T, tag, fresh, depth, tv, tp, tn, x, y, v, h, hb),
        {==})
    case False{}:
      +o = SC.append(Nat, x, y)
      +hd = F.g_depth(~T, tag, fresh, depth, tv, tp, tn, o, h)
      +hf = F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, o, h)
      +hd32 = N.le_lt_trans(depth, 31n, 32n, hd, N.lt_succ(31n))
      +efn = fresh_nat(fresh, depth, hd, hf)
      +hb = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(depth)) == False{} : Bool}, U32.to_nat(U32.from_nat(fresh)), fresh, efn, AR.lt_bridge(U32.from_nat(fresh), depth, hd32, False{}, erb))
      +hge = N.not_lt_le(fresh, SC.pow2(depth), hb)
      +hdq = AE.pow2_inv(depth, q, N.le_lt_trans(SC.pow2(depth), fresh, SC.pow2(q), hge, hroom))
      +hdl = N.lt_le_trans(depth, q, 31n, hdq, hq)
      +hr2 = N.le_lt_trans(fresh, SC.pow2(depth), SC.pow2(1n+depth), hf, N.pow2_lt_succ(depth))
      +gg = GR.g_good(~T, tag, fresh, depth, tv, tp, tn, o, h, hdl)
      +hlt = F.g_lt(~T, tag, fresh, depth, tv, tp, tn, o, h)
      +hxs = GR.g_items(~T, tag, fresh, depth, tv, tp, tn, o, h, x, TL.alllt_l(x, y, fresh, hlt))
      +hys = GR.g_items(~T, tag, fresh, depth, tv, tp, tn, o, h, y, TL.alllt_r(x, y, fresh, hlt))
      +em0 = IN.li_model(~T, tag, fresh, 1n+depth, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}, AR.TNode{tp, AR.trep(U32, depth, D.nil())}, AR.TNode{tn, AR.trep(U32, depth, D.nil())}, x, y, v, gg, hr2)
      +em1 = L.subst(List<&2, E.Item<T>>, z => {ST.model(~T, IN.lsh(~T, tag, fresh, 1n+depth, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}, AR.TNode{tp, AR.trep(U32, depth, D.nil())}, AR.TNode{tn, AR.trep(U32, depth, D.nil())}, x, y, v)) == DS.DM{tag, 1n+fresh, SC.append(E.Item<T>, z, Con{E.Item{U32.from_nat(fresh), v}, ST.items(T, AR.slots(Maybe<&2, T>, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}), y)})} : DS.Model<T>}, ST.items(T, AR.slots(Maybe<&2, T>, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}), x), ST.items(T, AR.slots(Maybe<&2, T>, tv), x), hxs, em0)
      +em2 = L.subst(List<&2, E.Item<T>>, z => {ST.model(~T, IN.lsh(~T, tag, fresh, 1n+depth, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}, AR.TNode{tp, AR.trep(U32, depth, D.nil())}, AR.TNode{tn, AR.trep(U32, depth, D.nil())}, x, y, v)) == DS.DM{tag, 1n+fresh, SC.append(E.Item<T>, ST.items(T, AR.slots(Maybe<&2, T>, tv), x), Con{E.Item{U32.from_nat(fresh), v}, z})} : DS.Model<T>}, ST.items(T, AR.slots(Maybe<&2, T>, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}), y), ST.items(T, AR.slots(Maybe<&2, T>, tv), y), hys, em1)
      imk(~T, D.insert_room(~T, tag, U32.from_nat(fresh), 0, SC.length(Nat, o), ST.hd(o), ST.lst(o), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn), LK.lastl(x, D.nil()), ST.hd_or(y, D.nil()), v, False{}), E.H{tag, U32.from_nat(fresh)}, IM(~T, tag, fresh, AR.slots(Maybe<&2, T>, tv), x, y, v), fresh,
        IN.lsh(~T, tag, fresh, 1n+depth, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}, AR.TNode{tp, AR.trep(U32, depth, D.nil())}, AR.TNode{tn, AR.trep(U32, depth, D.nil())}, x, y, v),
        Equal.trans(D.DList<T> & E.Handle, D.insert_room(~T, tag, U32.from_nat(fresh), 0, SC.length(Nat, o), ST.hd(o), ST.lst(o), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn), LK.lastl(x, D.nil()), ST.hd_or(y, D.nil()), v, False{}), D.link_in(~T, tag, U32.from_nat(fresh), U32.inc(U32.from_nat(fresh)), 0, SC.length(Nat, o), ST.hd(o), ST.lst(o), 1n+depth, U.pow2u(1n+depth), AR.thaw(Maybe<&2, T>, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}), AR.thaw(U32, AR.TNode{tp, AR.trep(U32, depth, D.nil())}), AR.thaw(U32, AR.TNode{tn, AR.trep(U32, depth, D.nil())}), LK.lastl(x, D.nil()), ST.hd_or(y, D.nil()), v), (ST.real(~T, IN.lsh(~T, tag, fresh, 1n+depth, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}, AR.TNode{tp, AR.trep(U32, depth, D.nil())}, AR.TNode{tn, AR.trep(U32, depth, D.nil())}, x, y, v)), E.H{tag, U32.from_nat(fresh)}),
          g_rt(~T, tag, fresh, depth, tv, tp, tn, o, LK.lastl(x, D.nil()), ST.hd_or(y, D.nil()), v),
          IN.li_rt(~T, tag, fresh, 1n+depth, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}, AR.TNode{tp, AR.trep(U32, depth, D.nil())}, AR.TNode{tn, AR.trep(U32, depth, D.nil())}, x, y, v, gg, hr2)),
        IN.li_good(~T, tag, fresh, 1n+depth, AR.TNode{tv, AR.trep(Maybe<&2, T>, depth, None{})}, AR.TNode{tp, AR.trep(U32, depth, D.nil())}, AR.TNode{tn, AR.trep(U32, depth, D.nil())}, x, y, v, gg, hr2),
        em2,
        {==})

def ib_core(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: T, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +eo: {ord == SC.append(Nat, x, y) : List<&2, Nat>}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hroom: {Nat.is_lt(fresh, SC.pow2(q)) == True{} : Bool}) -> ICore(~T, IB(~T, tag, fresh, ord, depth, tv, tp, tn, LK.lastl(x, D.nil()), ST.hd_or(y, D.nil()), v), E.H{tag, U32.from_nat(fresh)}, IM(~T, tag, fresh, AR.slots(Maybe<&2, T>, tv), x, y, v), fresh):
  +h2 = L.subst(List<&2, Nat>, z => {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, z}) == True{} : Bool}, ord, SC.append(Nat, x, y), eo, h)
  L.subst(List<&2, Nat>, z => ICore(~T, IB(~T, tag, fresh, z, depth, tv, tp, tn, LK.lastl(x, D.nil()), ST.hd_or(y, D.nil()), v), E.H{tag, U32.from_nat(fresh)}, IM(~T, tag, fresh, AR.slots(Maybe<&2, T>, tv), x, y, v), fresh), SC.append(Nat, x, y), ord, Equal.sym(List<&2, Nat>, ord, SC.append(Nat, x, y), eo),
    ib_room(~T, tag, fresh, depth, tv, tp, tn, x, y, v, h2, q, hq, hroom, U32.is_lt(U32.from_nat(fresh), U.pow2u(depth)), {==}))
