import Base
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../spec/doubly_linked_list.bend as DS
import ../../src/doubly_linked_list.bend as D
import ../../types/doubly_linked_list.bend as E
import ./state.bend as ST
import ./links.bend as LK
import ./alive.bend as AL
import ./core.bend as K
import ./reads.bend as RD
import ./nbrs.bend as NB
import ./tolist.bend as TL
import ./mut.bend as MU
import ./rm.bend as RMV
import ./insert.bend as INS
import ./grow.bend as GRW
import ./ibcore.bend as ICR
import ./insops.bend as IOP
import ./trace.bend as DTR
import ../lib/u32.bend as U

# Checked instantiations of the (template) DLL proofs at T = U32.

def i_length(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> K.StepOK(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.Length{}):
  RD.length_ok(~U32, tag, fresh, depth, tv, tp, tn, ord, h)

def i_get(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +l: U32, +i: U32, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> K.StepOK(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.Get{E.H{l, i}}):
  RD.get_ok(~U32, tag, fresh, depth, tv, tp, tn, ord, l, i, h)

def i_next(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +l: U32, +i: U32, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> K.StepOK(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.Next{E.H{l, i}}):
  NB.next_ok(~U32, tag, fresh, depth, tv, tp, tn, ord, l, i, h)

def i_prev(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +l: U32, +i: U32, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> K.StepOK(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.Prev{E.H{l, i}}):
  NB.prev_ok(~U32, tag, fresh, depth, tv, tp, tn, ord, l, i, h)

def i_walk(+depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +ns: List<&2, U32>, +r: List<&2, Nat>, +acc: List<&2, U32>, +e: U32, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfv: {AR.perfect(Maybe<&2, U32>, depth, tv) == True{} : Bool}, +pfp: {AR.perfect(U32, depth, tp) == True{} : Bool}, +hl: {ST.alllt(SC.reverse(Nat, r), SC.pow2(depth)) == True{} : Bool}, +ha: {AL.alive(U32, AR.slots(Maybe<&2, U32>, tv), SC.reverse(Nat, r)) == True{} : Bool}, +hk: {ST.lk(SC.reverse(Nat, r), D.nil(), e, AR.slots(U32, tp), ns) == True{} : Bool}) -> {D.walk(~U32, SC.length(Nat, r), TL.wcur(~U32, tv, tp, acc, LK.lastl(SC.reverse(Nat, r), D.nil()))) == TL.wcur(~U32, tv, tp, SC.append(U32, DS.vals(U32, ST.items(U32, AR.slots(Maybe<&2, U32>, tv), SC.reverse(Nat, r))), acc), D.nil()) : D.Cur<U32>}:
  TL.walk_ok(~U32, depth, tv, tp, ns, r, acc, e, hd, pfv, pfp, hl, ha, hk)

def i_tolist(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> K.StepOK(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.ToList{}):
  TL.tolist_ok(~U32, tag, fresh, depth, tv, tp, tn, ord, h)

def i_set(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +l: U32, +i: U32, +x: U32, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> K.StepOK(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.Set{E.H{l, i}, x}):
  MU.set_ok(~U32, tag, fresh, depth, tv, tp, tn, ord, l, i, x, h)

def i_remove(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +l: U32, +i: U32, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> K.StepOK(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.Remove{E.H{l, i}}):
  RMV.remove_ok(~U32, tag, fresh, depth, tv, tp, tn, ord, l, i, h)

def i_li_rt(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: U32, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, x, y)}) == True{} : Bool}, +hr: {Nat.is_lt(fresh, SC.pow2(depth)) == True{} : Bool}) -> {D.link_in(~U32, tag, U32.from_nat(fresh), U32.inc(U32.from_nat(fresh)), 0, SC.length(Nat, SC.append(Nat, x, y)), ST.hd(SC.append(Nat, x, y)), ST.lst(SC.append(Nat, x, y)), depth, U.pow2u(depth), AR.thaw(Maybe<&2, U32>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn), LK.lastl(x, D.nil()), ST.hd_or(y, D.nil()), v) == (ST.real(~U32, INS.lsh(~U32, tag, fresh, depth, tv, tp, tn, x, y, v)), E.H{tag, U32.from_nat(fresh)}) : D.DList<U32> & E.Handle}:
  INS.li_rt(~U32, tag, fresh, depth, tv, tp, tn, x, y, v, h, hr)

def i_li_good(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: U32, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, x, y)}) == True{} : Bool}, +hr: {Nat.is_lt(fresh, SC.pow2(depth)) == True{} : Bool}) -> {ST.good(~U32, INS.lsh(~U32, tag, fresh, depth, tv, tp, tn, x, y, v)) == True{} : Bool}:
  INS.li_good(~U32, tag, fresh, depth, tv, tp, tn, x, y, v, h, hr)

def i_li_model(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: U32, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, x, y)}) == True{} : Bool}, +hr: {Nat.is_lt(fresh, SC.pow2(depth)) == True{} : Bool}) -> Unit:
  +e = INS.li_model(~U32, tag, fresh, depth, tv, tp, tn, x, y, v, h, hr)
  Unit{}

def i_g_good(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hdl: {Nat.is_lt(depth, 31n) == True{} : Bool}) -> {ST.good(~U32, GRW.gsh(~U32, tag, fresh, depth, tv, tp, tn, ord)) == True{} : Bool}:
  GRW.g_good(~U32, tag, fresh, depth, tv, tp, tn, ord, h, hdl)

def i_g_items(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +zs: List<&2, Nat>, +hz: {ST.alllt(zs, fresh) == True{} : Bool}) -> Unit:
  +e = GRW.g_items(~U32, tag, fresh, depth, tv, tp, tn, ord, h, zs, hz)
  +e2 = GRW.g_vals(~U32, depth, tv)
  Unit{}

def i_ib_core(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: U32, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +eo: {ord == SC.append(Nat, x, y) : List<&2, Nat>}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hroom: {Nat.is_lt(fresh, SC.pow2(q)) == True{} : Bool}) -> ICR.ICore(~U32, ICR.IB(~U32, tag, fresh, ord, depth, tv, tp, tn, LK.lastl(x, D.nil()), ST.hd_or(y, D.nil()), v), E.H{tag, U32.from_nat(fresh)}, ICR.IM(~U32, tag, fresh, AR.slots(Maybe<&2, U32>, tv), x, y, v), fresh):
  ICR.ib_core(~U32, tag, fresh, depth, tv, tp, tn, ord, x, y, v, h, eo, q, hq, hroom)

def i_pf(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +x: U32, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hroom: {Nat.is_lt(fresh, SC.pow2(q)) == True{} : Bool}) -> K.StepOK(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.PushFront{x}):
  IOP.push_front_ok(~U32, tag, fresh, depth, tv, tp, tn, ord, x, h, q, hq, hroom)

def i_pb(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +x: U32, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hroom: {Nat.is_lt(fresh, SC.pow2(q)) == True{} : Bool}) -> K.StepOK(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.PushBack{x}):
  IOP.push_back_ok(~U32, tag, fresh, depth, tv, tp, tn, ord, x, h, q, hq, hroom)

def i_ib(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +l: U32, +i: U32, +x: U32, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hroom: {Nat.is_lt(fresh, SC.pow2(q)) == True{} : Bool}) -> K.StepOK(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.InsertBefore{E.H{l, i}, x}):
  IOP.insert_before_ok(~U32, tag, fresh, depth, tv, tp, tn, ord, l, i, x, h, q, hq, hroom)

def i_ia(+tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, U32>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +l: U32, +i: U32, +x: U32, +h: {ST.good(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hroom: {Nat.is_lt(fresh, SC.pow2(q)) == True{} : Bool}) -> K.StepOK(~U32, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.InsertAfter{E.H{l, i}, x}):
  IOP.insert_after_ok(~U32, tag, fresh, depth, tv, tp, tn, ord, l, i, x, h, q, hq, hroom)

def i_trace(+tag: U32, +ops: List<&2, E.Op<U32>>, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(DTR.inserts(U32, ops), SC.pow2(q)) == True{} : Bool}) -> DTR.TraceNew(~U32, tag, ops):
  DTR.trace_new(~U32, tag, ops, q, hq, room)
