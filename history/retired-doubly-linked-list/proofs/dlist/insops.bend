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
import ./ibcore.bend as IC
import ./rm.bend as RM

# The four insertions as steps, under the room premise fresh < 2^q, q <= 31.

def mo(~T: Data, m: DS.Model<T>, o: E.Obs<T>) -> DS.Model<T> & E.Obs<T>:
  (m, o)

def ic_fresh(+fresh: Nat) -> {Nat.is_le(1n+fresh, Nat.add(fresh, 1n)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(1n+fresh, z) == True{} : Bool}, 1n+fresh, Nat.add(fresh, 1n),
    Equal.sym(Nat, Nat.add(fresh, 1n), 1n+fresh, Equal.trans(Nat, Nat.add(fresh, 1n), 1n+Nat.add(fresh, 0n), 1n+fresh, N.add_succ(fresh, 0n), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(fresh, 0n), fresh, N.add_zero(fresh)))),
    N.le_refl(1n+fresh))

def ic_le(~T: Data, -sh: ST.Shadow<T>, -sh2: ST.Shadow<T>, +fresh: Nat, +ef: {K.sfresh(~T, sh) == fresh : Nat}, +e4: {K.sfresh(~T, sh2) == 1n+fresh : Nat}) -> {Nat.is_le(K.sfresh(~T, sh2), Nat.add(K.sfresh(~T, sh), 1n)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(K.sfresh(~T, sh2), Nat.add(z, 1n)) == True{} : Bool}, fresh, K.sfresh(~T, sh), Equal.sym(Nat, K.sfresh(~T, sh), fresh, ef),
    L.subst(Nat, z => {Nat.is_le(z, Nat.add(fresh, 1n)) == True{} : Bool}, 1n+fresh, K.sfresh(~T, sh2), Equal.sym(Nat, K.sfresh(~T, sh2), 1n+fresh, e4), ic_fresh(fresh)))

def ic_h(~T: Data, -sh: ST.Shadow<T>, -rt: D.DList<T> & E.Handle, +hh: E.Handle, -m: DS.Model<T>, +fresh: Nat, +ef: {K.sfresh(~T, sh) == fresh : Nat}, c: IC.ICore(~T, rt, hh, m, fresh)) -> K.GCore(~T, sh, D.obs_handle(~T, rt), mo(~T, m, E.OHandle{hh}), 1n):
  match c:
    case Tuple{sh2, Tuple{e1, Tuple{e2, Tuple{e3, e4}}}}:
      K.gmk(~T, sh, D.obs_handle(~T, rt), mo(~T, m, E.OHandle{hh}), 1n, sh2, E.OHandle{hh},
        Equal.cong(D.DList<T> & E.Handle, D.DList<T> & E.Obs<T>, z => D.obs_handle(~T, z), rt, (ST.real(~T, sh2), hh), e1),
        e2,
        Equal.cong(DS.Model<T>, DS.Model<T> & E.Obs<T>, z => mo(~T, z, E.OHandle{hh}), ST.model(~T, sh2), m, e3),
        ic_le(~T, sh, sh2, fresh, ef, e4))

def ic_i(~T: Data, -sh: ST.Shadow<T>, -rt: D.DList<T> & E.Handle, +hh: E.Handle, -m: DS.Model<T>, +fresh: Nat, +ef: {K.sfresh(~T, sh) == fresh : Nat}, c: IC.ICore(~T, rt, hh, m, fresh)) -> K.GCore(~T, sh, D.obs_insert(~T, D.done_handle(~T, rt)), mo(~T, m, E.OInsert{Done{hh}}), 1n):
  match c:
    case Tuple{sh2, Tuple{e1, Tuple{e2, Tuple{e3, e4}}}}:
      K.gmk(~T, sh, D.obs_insert(~T, D.done_handle(~T, rt)), mo(~T, m, E.OInsert{Done{hh}}), 1n, sh2, E.OInsert{Done{hh}},
        Equal.cong(D.DList<T> & E.Handle, D.DList<T> & E.Obs<T>, z => D.obs_insert(~T, D.done_handle(~T, z)), rt, (ST.real(~T, sh2), hh), e1),
        e2,
        Equal.cong(DS.Model<T>, DS.Model<T> & E.Obs<T>, z => mo(~T, z, E.OInsert{Done{hh}}), ST.model(~T, sh2), m, e3),
        ic_le(~T, sh, sh2, fresh, ef, e4))

# ---- push_front / push_back ----

def push_front_ok(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +x: T, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hroom: {Nat.is_lt(fresh, SC.pow2(q)) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.PushFront{x}):
  ic_h(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, IC.IB(~T, tag, fresh, ord, depth, tv, tp, tn, D.nil(), ST.hd(ord), x), E.H{tag, U32.from_nat(fresh)}, IC.IM(~T, tag, fresh, AR.slots(Maybe<&2, T>, tv), Nil{}, ord, x), fresh, {==}, L.subst(U32, z => IC.ICore(~T, IC.IB(~T, tag, fresh, ord, depth, tv, tp, tn, D.nil(), z, x), E.H{tag, U32.from_nat(fresh)}, IC.IM(~T, tag, fresh, AR.slots(Maybe<&2, T>, tv), Nil{}, ord, x), fresh), ST.hd_or(ord, D.nil()), ST.hd(ord), RF.hd_or_nil(ord), IC.ib_core(~T, tag, fresh, depth, tv, tp, tn, ord, Nil{}, ord, x, h, {==}, q, hq, hroom)))

def push_back_ok(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +x: T, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hroom: {Nat.is_lt(fresh, SC.pow2(q)) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.PushBack{x}):
  ic_h(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, IC.IB(~T, tag, fresh, ord, depth, tv, tp, tn, ST.lst(ord), D.nil(), x), E.H{tag, U32.from_nat(fresh)}, IC.IM(~T, tag, fresh, AR.slots(Maybe<&2, T>, tv), ord, Nil{}, x), fresh, {==}, L.subst(U32, z => IC.ICore(~T, IC.IB(~T, tag, fresh, ord, depth, tv, tp, tn, z, D.nil(), x), E.H{tag, U32.from_nat(fresh)}, IC.IM(~T, tag, fresh, AR.slots(Maybe<&2, T>, tv), ord, Nil{}, x), fresh), LK.lastl(ord, D.nil()), ST.lst(ord), Equal.sym(U32, ST.lst(ord), LK.lastl(ord, D.nil()), TL.lst_lastl(ord)), IC.ib_core(~T, tag, fresh, depth, tv, tp, tn, ord, ord, Nil{}, x, h, Equal.sym(List<&2, Nat>, SC.append(Nat, ord, Nil{}), ord, LL.append_nil(Nat, ord)), q, hq, hroom)))

# ---- insert_before / insert_after ----

def INS(-T: Data, after: Bool, its: List<&2, E.Item<T>>, +i: U32, +it: E.Item<T>) -> List<&2, E.Item<T>>:
  match after:
    case False{}:
      DS.ins_before(T, its, i, it)
    case True{}:
      DS.ins_after(T, its, i, it)

def IRT(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +x: T, after: Bool, ok: Bool, same: Bool) -> D.DList<T> & E.Obs<T>:
  D.obs_insert(~T, D.insert_checked(~T, after, ok, tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn), i, x, same))

def ISP(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +x: T, after: Bool, c: Maybe<&2, E.Error>) -> DS.Model<T> & E.Obs<T>:
  DS.insert_at(T, c, tag, fresh, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), INS(T, after, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i, E.Item{U32.from_nat(fresh), x}))

def ifound(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +x: T, after: Bool, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> D.DList<T> & E.Obs<T>:
  D.obs_insert(~T, D.ins_found(~T, after, tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(U32, tp), AR.thaw(U32, tn), i, x, r))

def ILV(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +x: T, after: Bool, pr: Array<U32> & U32, nx: Array<U32> & U32) -> D.DList<T> & E.Obs<T>:
  D.obs_insert(~T, D.ins_live2(~T, after, tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), i, x, pr, nx))

def ILB(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +x: T, +pa: U32, +pb: U32) -> D.DList<T> & E.Obs<T>:
  D.obs_insert(~T, D.done_handle(~T, IC.IB(~T, tag, fresh, ord, depth, tv, tp, tn, pa, pb, x)))

def ins_cut(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +b: List<&2, Nat>, +i: U32, +x: T, after: Bool, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b})}) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hroom: {Nat.is_lt(fresh, SC.pow2(q)) == True{} : Bool}) -> K.GCore(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b})}, ILV(~T, tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b}), i, x, after, D.link_at(AR.thaw(U32, tp), i), D.link_at(AR.thaw(U32, tn), i)), ISP(~T, tag, fresh, depth, tv, tp, tn, SC.append(Nat, a, Con{U32.to_nat(i), b}), i, x, after, None{}), 1n):
  match after:
    case False{}:
      +n = U32.to_nat(i)
      +o = SC.append(Nat, a, Con{n, b})
      +xs = AR.slots(Maybe<&2, T>, tv)
      +ps = AR.slots(U32, tp)
      +ns = AR.slots(U32, tn)
      +p = LK.lastl(a, D.nil())
      +qq = ST.hd_or(b, D.nil())
      +hd = F.g_depth(~T, tag, fresh, depth, tv, tp, tn, o, h)
      +pfp = F.g_tp(~T, tag, fresh, depth, tv, tp, tn, o, h)
      +pfn = F.g_tn(~T, tag, fresh, depth, tv, tp, tn, o, h)
      +hn = RD.hi_of(~T, tag, fresh, depth, tv, tp, tn, o, i, h, hi)
      +hk = F.g_lk(~T, tag, fresh, depth, tv, tp, tn, o, h)
      +hlo = K.alllt_mono(o, fresh, SC.pow2(depth), F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, o, h), F.g_lt(~T, tag, fresh, depth, tv, tp, tn, o, h))
      +epr = Equal.trans(Array<U32> & U32, D.link_at(AR.thaw(U32, tp), i), (AR.thaw(U32, tp), ST.lat(ps, n)), (AR.thaw(U32, tp), p), NB.read_l(~T, tag, fresh, depth, tv, tp, tn, o, tp, i, h, pfp, hi), Equal.cong(U32, Array<U32> & U32, z => RM.lpair(tp, z), ST.lat(ps, n), p, RF.plink(a, n, b, ps, ns, hk)))
      +enx = Equal.trans(Array<U32> & U32, D.link_at(AR.thaw(U32, tn), i), (AR.thaw(U32, tn), ST.lat(ns, n)), (AR.thaw(U32, tn), qq), NB.read_l(~T, tag, fresh, depth, tv, tp, tn, o, tn, i, h, pfn, hi), Equal.cong(U32, Array<U32> & U32, z => RM.lpair(tn, z), ST.lat(ns, n), qq, RF.nlink(a, n, b, ps, ns, hk)))
      +eli = F.link_ln(i, n, F.u32_id(i, depth, hd, hn))
      +ert = Equal.trans(D.DList<T> & E.Obs<T>, ILV(~T, tag, fresh, depth, tv, tp, tn, o, i, x, False{}, D.link_at(AR.thaw(U32, tp), i), D.link_at(AR.thaw(U32, tn), i)), ILV(~T, tag, fresh, depth, tv, tp, tn, o, i, x, False{}, (AR.thaw(U32, tp), p), D.link_at(AR.thaw(U32, tn), i)), ILB(~T, tag, fresh, depth, tv, tp, tn, o, x, p, ST.ln(n)),
        Equal.cong(Array<U32> & U32, D.DList<T> & E.Obs<T>, z => ILV(~T, tag, fresh, depth, tv, tp, tn, o, i, x, False{}, z, D.link_at(AR.thaw(U32, tn), i)), D.link_at(AR.thaw(U32, tp), i), (AR.thaw(U32, tp), p), epr),
        Equal.trans(D.DList<T> & E.Obs<T>, ILV(~T, tag, fresh, depth, tv, tp, tn, o, i, x, False{}, (AR.thaw(U32, tp), p), D.link_at(AR.thaw(U32, tn), i)), ILV(~T, tag, fresh, depth, tv, tp, tn, o, i, x, False{}, (AR.thaw(U32, tp), p), (AR.thaw(U32, tn), qq)), ILB(~T, tag, fresh, depth, tv, tp, tn, o, x, p, ST.ln(n)),
          Equal.cong(Array<U32> & U32, D.DList<T> & E.Obs<T>, z => ILV(~T, tag, fresh, depth, tv, tp, tn, o, i, x, False{}, (AR.thaw(U32, tp), p), z), D.link_at(AR.thaw(U32, tn), i), (AR.thaw(U32, tn), qq), enx),
          Equal.cong(U32, D.DList<T> & E.Obs<T>, z => ILB(~T, tag, fresh, depth, tv, tp, tn, o, x, p, z), D.link(i), ST.ln(n), eli)))
      +esp = Equal.cong(List<&2, E.Item<T>>, DS.Model<T> & E.Obs<T>, z => mo(~T, DS.DM{tag, 1n+fresh, z}, E.OInsert{Done{E.H{tag, U32.from_nat(fresh)}}}), SC.append(E.Item<T>, ST.items(T, xs, a), Con{E.Item{U32.from_nat(fresh), x}, ST.items(T, xs, Con{n, b})}), DS.ins_before(T, ST.items(T, xs, o), i, E.Item{U32.from_nat(fresh), x}),
        Equal.sym(List<&2, E.Item<T>>, DS.ins_before(T, ST.items(T, xs, o), i, E.Item{U32.from_nat(fresh), x}), SC.append(E.Item<T>, ST.items(T, xs, a), Con{E.Item{U32.from_nat(fresh), x}, ST.items(T, xs, Con{n, b})}), II.ib_eq(T, xs, a, b, i, E.Item{U32.from_nat(fresh), x}, depth, hd, hlo, AL.g_alive(~T, tag, fresh, depth, tv, tp, tn, o, h), F.g_nd(~T, tag, fresh, depth, tv, tp, tn, o, h))))
      K.gconv(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, o}, ILV(~T, tag, fresh, depth, tv, tp, tn, o, i, x, False{}, D.link_at(AR.thaw(U32, tp), i), D.link_at(AR.thaw(U32, tn), i)), ILB(~T, tag, fresh, depth, tv, tp, tn, o, x, p, ST.ln(n)), ISP(~T, tag, fresh, depth, tv, tp, tn, o, i, x, False{}, None{}), mo(~T, IC.IM(~T, tag, fresh, xs, a, Con{n, b}, x), E.OInsert{Done{E.H{tag, U32.from_nat(fresh)}}}), 1n,
        Equal.sym(D.DList<T> & E.Obs<T>, ILV(~T, tag, fresh, depth, tv, tp, tn, o, i, x, False{}, D.link_at(AR.thaw(U32, tp), i), D.link_at(AR.thaw(U32, tn), i)), ILB(~T, tag, fresh, depth, tv, tp, tn, o, x, p, ST.ln(n)), ert),
        esp,
        ic_i(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, o}, IC.IB(~T, tag, fresh, o, depth, tv, tp, tn, p, ST.ln(n), x), E.H{tag, U32.from_nat(fresh)}, IC.IM(~T, tag, fresh, xs, a, Con{n, b}, x), fresh, {==},
          IC.ib_core(~T, tag, fresh, depth, tv, tp, tn, o, a, Con{n, b}, x, h, {==}, q, hq, hroom)))
    case True{}:
      +n = U32.to_nat(i)
      +o = SC.append(Nat, a, Con{n, b})
      +an = SC.append(Nat, a, Con{n, Nil{}})
      +xs = AR.slots(Maybe<&2, T>, tv)
      +ps = AR.slots(U32, tp)
      +ns = AR.slots(U32, tn)
      +p = LK.lastl(a, D.nil())
      +qq = ST.hd_or(b, D.nil())
      +hd = F.g_depth(~T, tag, fresh, depth, tv, tp, tn, o, h)
      +pfp = F.g_tp(~T, tag, fresh, depth, tv, tp, tn, o, h)
      +pfn = F.g_tn(~T, tag, fresh, depth, tv, tp, tn, o, h)
      +hn = RD.hi_of(~T, tag, fresh, depth, tv, tp, tn, o, i, h, hi)
      +hk = F.g_lk(~T, tag, fresh, depth, tv, tp, tn, o, h)
      +hlo = K.alllt_mono(o, fresh, SC.pow2(depth), F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, o, h), F.g_lt(~T, tag, fresh, depth, tv, tp, tn, o, h))
      +epr = Equal.trans(Array<U32> & U32, D.link_at(AR.thaw(U32, tp), i), (AR.thaw(U32, tp), ST.lat(ps, n)), (AR.thaw(U32, tp), p), NB.read_l(~T, tag, fresh, depth, tv, tp, tn, o, tp, i, h, pfp, hi), Equal.cong(U32, Array<U32> & U32, z => RM.lpair(tp, z), ST.lat(ps, n), p, RF.plink(a, n, b, ps, ns, hk)))
      +enx = Equal.trans(Array<U32> & U32, D.link_at(AR.thaw(U32, tn), i), (AR.thaw(U32, tn), ST.lat(ns, n)), (AR.thaw(U32, tn), qq), NB.read_l(~T, tag, fresh, depth, tv, tp, tn, o, tn, i, h, pfn, hi), Equal.cong(U32, Array<U32> & U32, z => RM.lpair(tn, z), ST.lat(ns, n), qq, RF.nlink(a, n, b, ps, ns, hk)))
      +eli = Equal.trans(U32, D.link(i), ST.ln(n), LK.lastl(an, D.nil()), F.link_ln(i, n, F.u32_id(i, depth, hd, hn)), Equal.sym(U32, LK.lastl(an, D.nil()), ST.ln(n), TL.lastl_snoc(a, n, D.nil())))
      +ert = Equal.trans(D.DList<T> & E.Obs<T>, ILV(~T, tag, fresh, depth, tv, tp, tn, o, i, x, True{}, D.link_at(AR.thaw(U32, tp), i), D.link_at(AR.thaw(U32, tn), i)), ILV(~T, tag, fresh, depth, tv, tp, tn, o, i, x, True{}, (AR.thaw(U32, tp), p), D.link_at(AR.thaw(U32, tn), i)), ILB(~T, tag, fresh, depth, tv, tp, tn, o, x, LK.lastl(an, D.nil()), qq),
        Equal.cong(Array<U32> & U32, D.DList<T> & E.Obs<T>, z => ILV(~T, tag, fresh, depth, tv, tp, tn, o, i, x, True{}, z, D.link_at(AR.thaw(U32, tn), i)), D.link_at(AR.thaw(U32, tp), i), (AR.thaw(U32, tp), p), epr),
        Equal.trans(D.DList<T> & E.Obs<T>, ILV(~T, tag, fresh, depth, tv, tp, tn, o, i, x, True{}, (AR.thaw(U32, tp), p), D.link_at(AR.thaw(U32, tn), i)), ILV(~T, tag, fresh, depth, tv, tp, tn, o, i, x, True{}, (AR.thaw(U32, tp), p), (AR.thaw(U32, tn), qq)), ILB(~T, tag, fresh, depth, tv, tp, tn, o, x, LK.lastl(an, D.nil()), qq),
          Equal.cong(Array<U32> & U32, D.DList<T> & E.Obs<T>, z => ILV(~T, tag, fresh, depth, tv, tp, tn, o, i, x, True{}, (AR.thaw(U32, tp), p), z), D.link_at(AR.thaw(U32, tn), i), (AR.thaw(U32, tn), qq), enx),
          Equal.cong(U32, D.DList<T> & E.Obs<T>, z => ILB(~T, tag, fresh, depth, tv, tp, tn, o, x, z, qq), D.link(i), LK.lastl(an, D.nil()), eli)))
      +esp = Equal.cong(List<&2, E.Item<T>>, DS.Model<T> & E.Obs<T>, z => mo(~T, DS.DM{tag, 1n+fresh, z}, E.OInsert{Done{E.H{tag, U32.from_nat(fresh)}}}), SC.append(E.Item<T>, ST.items(T, xs, an), Con{E.Item{U32.from_nat(fresh), x}, ST.items(T, xs, b)}), DS.ins_after(T, ST.items(T, xs, o), i, E.Item{U32.from_nat(fresh), x}),
        Equal.sym(List<&2, E.Item<T>>, DS.ins_after(T, ST.items(T, xs, o), i, E.Item{U32.from_nat(fresh), x}), SC.append(E.Item<T>, ST.items(T, xs, an), Con{E.Item{U32.from_nat(fresh), x}, ST.items(T, xs, b)}), II.ia_eq(T, xs, a, b, i, E.Item{U32.from_nat(fresh), x}, depth, hd, hlo, AL.g_alive(~T, tag, fresh, depth, tv, tp, tn, o, h), F.g_nd(~T, tag, fresh, depth, tv, tp, tn, o, h))))
      K.gconv(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, o}, ILV(~T, tag, fresh, depth, tv, tp, tn, o, i, x, True{}, D.link_at(AR.thaw(U32, tp), i), D.link_at(AR.thaw(U32, tn), i)), ILB(~T, tag, fresh, depth, tv, tp, tn, o, x, LK.lastl(an, D.nil()), qq), ISP(~T, tag, fresh, depth, tv, tp, tn, o, i, x, True{}, None{}), mo(~T, IC.IM(~T, tag, fresh, xs, an, b, x), E.OInsert{Done{E.H{tag, U32.from_nat(fresh)}}}), 1n,
        Equal.sym(D.DList<T> & E.Obs<T>, ILV(~T, tag, fresh, depth, tv, tp, tn, o, i, x, True{}, D.link_at(AR.thaw(U32, tp), i), D.link_at(AR.thaw(U32, tn), i)), ILB(~T, tag, fresh, depth, tv, tp, tn, o, x, LK.lastl(an, D.nil()), qq), ert),
        esp,
        ic_i(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, o}, IC.IB(~T, tag, fresh, o, depth, tv, tp, tn, LK.lastl(an, D.nil()), qq, x), E.H{tag, U32.from_nat(fresh)}, IC.IM(~T, tag, fresh, xs, an, b, x), fresh, {==},
          IC.ib_core(~T, tag, fresh, depth, tv, tp, tn, o, an, b, x, h, Equal.sym(List<&2, Nat>, SC.append(Nat, an, b), o, LL.append_assoc(Nat, a, Con{n, Nil{}}, b)), q, hq, hroom)))

def ins_some(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +x: T, after: Bool, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}, +v: T, +em: {RD.xv(~T, tv, i) == Some{v} : Maybe<&2, T>}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hroom: {Nat.is_lt(fresh, SC.pow2(q)) == True{} : Bool}) -> K.GCore(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, ILV(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, D.link_at(AR.thaw(U32, tp), i), D.link_at(AR.thaw(U32, tn), i)), ISP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, None{}), 1n):
  +n = U32.to_nat(i)
  +es = SP.split_eq(ord, n, NB.live_of(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi, v, em))
  +a = SP.spre(ord, n)
  +b = SP.spost(ord, n)
  +h2 = L.subst(List<&2, Nat>, z => {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, z}) == True{} : Bool}, ord, SC.append(Nat, a, Con{n, b}), es, h)
  L.subst(List<&2, Nat>, z => K.GCore(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, z}, ILV(~T, tag, fresh, depth, tv, tp, tn, z, i, x, after, D.link_at(AR.thaw(U32, tp), i), D.link_at(AR.thaw(U32, tn), i)), ISP(~T, tag, fresh, depth, tv, tp, tn, z, i, x, after, None{}), 1n),
    SC.append(Nat, a, Con{n, b}), ord, Equal.sym(List<&2, Nat>, ord, SC.append(Nat, a, Con{n, b}), es),
    ins_cut(~T, tag, fresh, depth, tv, tp, tn, a, b, i, x, after, h2, hi, q, hq, hroom))

def ins_m(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +x: T, after: Bool, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}, m: Maybe<&2, T>, +em: {RD.xv(~T, tv, i) == m : Maybe<&2, T>}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hroom: {Nat.is_lt(fresh, SC.pow2(q)) == True{} : Bool}) -> K.GCore(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, ifound(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, (AR.thaw(Maybe<&2, T>, tv), m)), ISP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, DS.check(T, True{}, m)), 1n):
  match m:
    case None{}:
      K.gsame(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, ifound(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, (AR.thaw(Maybe<&2, T>, tv), None{})), ISP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, DS.check(T, True{}, None{})), 1n, h, E.OInsert{Fail{E.StaleHandle{}}}, {==}, {==})
    case Some{v}:
      ins_some(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, h, hi, v, em, q, hq, hroom)

def ins_core(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +x: T, after: Bool, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hroom: {Nat.is_lt(fresh, SC.pow2(q)) == True{} : Bool}, ok: Bool, +eok: {U32.is_lt(i, U32.from_nat(fresh)) == ok : Bool}, same: Bool) -> K.GCore(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, IRT(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, ok, same), ISP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, DS.check(T, same, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i))), 1n):
  match ok same:
    case True{} False{}:
      K.gsame(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, IRT(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, True{}, False{}), ISP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, DS.check(T, False{}, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i))), 1n, h, E.OInsert{Fail{E.ForeignHandle{}}}, {==}, {==})
    case False{} False{}:
      K.gsame(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, IRT(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, False{}, False{}), ISP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, DS.check(T, False{}, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i))), 1n, h, E.OInsert{Fail{E.ForeignHandle{}}}, {==}, {==})
    case False{} True{}:
      K.gsame(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, IRT(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, False{}, True{}), ISP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, DS.check(T, True{}, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i))), 1n, h, E.OInsert{Fail{E.StaleHandle{}}}, {==},
        Equal.cong(Maybe<&2, T>, DS.Model<T> & E.Obs<T>, mm => ISP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, DS.check(T, True{}, mm)), None{}, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), Equal.sym(Maybe<&2, T>, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), None{}, RD.getv_ok_false(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, eok))))
    case True{} True{}:
      +hi = RD.hi_ok(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, eok)
      K.gconv(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, IRT(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, True{}, True{}), ifound(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, (AR.thaw(Maybe<&2, T>, tv), RD.xv(~T, tv, i))), ISP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, DS.check(T, True{}, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i))), ISP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, DS.check(T, True{}, RD.xv(~T, tv, i))), 1n,
        Equal.cong(Array<Maybe<&2, T>> & Maybe<&2, T>, D.DList<T> & E.Obs<T>, r => ifound(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, r), (AR.thaw(Maybe<&2, T>, tv), RD.xv(~T, tv, i)), Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), i), Equal.sym(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), i), (AR.thaw(Maybe<&2, T>, tv), RD.xv(~T, tv, i)), RD.read_v(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi))),
        Equal.cong(Maybe<&2, T>, DS.Model<T> & E.Obs<T>, mm => ISP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, DS.check(T, True{}, mm)), RD.xv(~T, tv, i), DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), Equal.sym(Maybe<&2, T>, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), RD.xv(~T, tv, i), RD.getv_xv(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi))),
        ins_m(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, after, h, hi, RD.xv(~T, tv, i), {==}, q, hq, hroom))

def insert_before_ok(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +l: U32, +i: U32, +x: T, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hroom: {Nat.is_lt(fresh, SC.pow2(q)) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.InsertBefore{E.H{l, i}, x}):
  ins_core(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, False{}, h, q, hq, hroom, U32.is_lt(i, U32.from_nat(fresh)), {==}, U32.is_eq(l, tag))

def insert_after_ok(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +l: U32, +i: U32, +x: T, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hroom: {Nat.is_lt(fresh, SC.pow2(q)) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.InsertAfter{E.H{l, i}, x}):
  ins_core(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, True{}, h, q, hq, hroom, U32.is_lt(i, U32.from_nat(fresh)), {==}, U32.is_eq(l, tag))
