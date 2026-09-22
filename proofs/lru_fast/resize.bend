import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/array.bend as AR
import ../lib/u32.bend as U
import ../../spec/common.bend as SC
import ../../spec/lru_fast.bend as S
import ../../src/lru/fast.bend as F
import support/link_primitives.bend as D
import ../../types/lru_model.bend as T
import support/links_state.bend as DST
import support/links_split.bend as SP
import support/links_tolist.bend as TL
import support/links_core.bend as K
import support/links_alive.bend as AL
import support/links_facts.bend as DF
import support/links_links.bend as LK
import support/links_tset.bend as TS
import ../../reference/lru/proofs/lookup_refinement.bend as LR
import ./state.bend as ST
import ./table.bend as TB
import ./ents.bend as EN
import ./rs.bend as RS
import ./remove.bend as RM
import ./addop.bend as AO
import support/links_items.bend as IT

# resize(cap): the capacity is set, then the oldest entry is evicted while the
# cache holds more than cap entries (at most len(order) rounds). During the loop
# the invariant is carried at the OLD capacity c0: the new one may be below the
# length until the loop ends. The removal core never reads the capacity.

# ---- the invariant at another capacity ----

def recap(~V: Data, +c0: U32, +capn: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +hc: {Bool.not(U32.is_eq(capn, 0)) == True{} : Bool}, +hn: {Nat.is_le(SC.length(Nat, ord), U32.to_nat(capn)) == True{} : Bool}) -> {ST.inv(~V, capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}:
  ST.inv_mk(~V, capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, ST.g_depth(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_tk(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_te(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_tp(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_tn(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_tc(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_fresh(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_ordlt(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_fllt(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_nodup(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_count(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_lk(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_fk(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_occ(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_mapped(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_incl(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_crit(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_pop(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), hc, hn)

# ---- removing the head with the invariant held at c0 ----

def rmc_real(~V: Data, +c0: U32, +capn: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, +metric: Nat, +hm: {DST.lmem(s, ord) == True{} : Bool}, +h: {ST.inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {F.remove_slot(~V, ST.real(~V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), U32.from_nat(s), metric) == (ST.real(~V, RM.rs_sh_at(V, capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, s, fl, metric)), F.slot_val(~V, ST.sat(V, AR.slots(F.Slot<V>, te), s))) : F.Fast<V> & Maybe<&2, V>}:
  +a = SP.spre(ord, s)
  +b = SP.spost(ord, s)
  +o = SC.append(Nat, a, Con{s, b})
  +hs2 = RM.split_inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, hm, h)
  +P = SC.pow2(depth)
  +hfr = ST.g_fresh(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)
  +hol = ST.g_ordlt(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)
  +hsf = L.and_left(Nat.is_lt(s, fresh), DST.alllt(b, fresh), TL.alllt_r(a, Con{s, b}, fresh, hol))
  +hle = N.le_trans(SC.length(Nat, o), fresh, P, RS.ord_le(o, fl, fresh, ST.g_count(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)), hfr)
  +r = RS.rs_real(~V, capn, fresh, depth, life, tc, table, tk, te, tp, tn, a, s, b, fl, metric, ST.g_depth(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), ST.g_tc(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), ST.g_tk(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), ST.g_te(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), ST.g_tp(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), ST.g_tn(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), N.lt_le_trans(s, fresh, P, hsf, hfr), K.alllt_mono(o, fresh, P, hfr, hol), ST.g_lk(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), hle)
  L.subst(List<&2, Nat>, z => {F.remove_slot(~V, ST.real(~V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, z, fl}), U32.from_nat(s), metric) == (ST.real(~V, RM.rs_sh_at(V, capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, s, fl, metric)), F.slot_val(~V, ST.sat(V, AR.slots(F.Slot<V>, te), s))) : F.Fast<V> & Maybe<&2, V>}, o, ord, Equal.sym(List<&2, Nat>, ord, o, SP.split_eq(ord, s, hm)), r)

def evc_real(~V: Data, +c0: U32, +capn: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +s0: Nat, +rest: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl) == True{} : Bool}) -> {F.evict_oldest(~V, ST.real(~V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl})) == ST.real(~V, RM.rs_sh_at(V, capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, s0, fl, 1n)) : F.Fast<V>}:
  +hm = TB.or_true_l(Nat.is_eq(s0, s0), DST.lmem(s0, rest), AL.lmem_self(s0))
  +hs0 = N.lt_le_trans(s0, fresh, SC.pow2(depth), L.and_left(Nat.is_lt(s0, fresh), DST.alllt(rest, fresh), ST.g_ordlt(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h)), ST.g_fresh(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h))
  +r = Equal.cong(F.Fast<V> & Maybe<&2, V>, F.Fast<V>, p => F.drop_val(~V, p), F.remove_slot(~V, ST.real(~V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), U32.from_nat(s0), 1n), (ST.real(~V, RM.rs_sh_at(V, capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, s0, fl, 1n)), F.slot_val(~V, ST.sat(V, AR.slots(F.Slot<V>, te), s0))), rmc_real(~V, c0, capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, s0, 1n, hm, h))
  L.subst(U32, z => {F.drop_val(~V, F.remove_slot(~V, ST.real(~V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), z, 1n)) == ST.real(~V, RM.rs_sh_at(V, capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, s0, fl, 1n)) : F.Fast<V>}, U32.from_nat(s0), F.slot(DST.ln(s0)), Equal.sym(U32, F.slot(DST.ln(s0)), U32.from_nat(s0), DF.slot_ln(s0, depth, ST.g_depth(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h), hs0)), r)

# ---- the ghost loop ----

def ev1(-V: Data, sh: ST.Shadow<V>) -> ST.Shadow<V>:
  match sh:
    case ST.Sh{+cap, +fresh, +depth, +life, +tc, +table, +tk, +te, +tp, +tn, +ord, +fl}:
      RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, AO.hd_nat(ord), fl, 1n)

def inc_snd(-V: Data, r: ST.Shadow<V> & Nat) -> ST.Shadow<V> & Nat:
  (s, k) = r
  (s, 1n+k)

def sr_pick(-V: Data, sh: ST.Shadow<V>, r: ST.Shadow<V> & Nat, over: Bool) -> ST.Shadow<V> & Nat:
  match over:
    case True{}:
      inc_snd(V, r)
    case False{}:
      (sh, 0n)

def sr_dec(-V: Data, sh: ST.Shadow<V>, r: ST.Shadow<V> & Nat) -> ST.Shadow<V> & Nat:
  match sh:
    case ST.Sh{+cap, +fresh, +depth, +life, +tc, +table, +tk, +te, +tp, +tn, +ord, +fl}:
      sr_pick(V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, r, Nat.is_lt(U32.to_nat(cap), SC.length(Nat, ord)))

def sr_g(-V: Data, fuel: Nat, +sh: ST.Shadow<V>) -> ST.Shadow<V> & Nat:
  match fuel:
    case 0n:
      (sh, 0n)
    case 1n+p:
      sr_dec(V, sh, sr_g(V, p, ev1(V, sh)))

def srp(~V: Data, r: ST.Shadow<V> & Nat, +j: Nat) -> F.Shr<V>:
  (s, k) = r
  F.SR{ST.real(~V, s), U32.from_nat(Nat.add(k, j))}

def srp_inc(~V: Data, r: ST.Shadow<V> & Nat, +j: Nat) -> {srp(~V, inc_snd(V, r), j) == srp(~V, r, 1n+j) : F.Shr<V>}:
  (s, k) = r
  Equal.cong(Nat, F.Shr<V>, z => F.SR{ST.real(~V, s), U32.from_nat(z)}, 1n+Nat.add(k, j), Nat.add(k, 1n+j), Equal.sym(Nat, Nat.add(k, 1n+j), 1n+Nat.add(k, j), N.add_succ(k, j)))

# the test of the loop: capacity below the length
def over_eq(~V: Data, +c0: U32, +capn: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {U32.is_lt(capn, U32.from_nat(SC.length(Nat, ord))) == Nat.is_lt(U32.to_nat(capn), SC.length(Nat, ord)) : Bool}:
  Equal.trans(Bool, U32.is_lt(capn, U32.from_nat(SC.length(Nat, ord))), Nat.is_lt(U32.to_nat(capn), U32.to_nat(U32.from_nat(SC.length(Nat, ord)))), Nat.is_lt(U32.to_nat(capn), SC.length(Nat, ord)),
    U.is_lt_nat(capn, U32.from_nat(SC.length(Nat, ord))),
    Equal.cong(Nat, Bool, z => Nat.is_lt(U32.to_nat(capn), z), U32.to_nat(U32.from_nat(SC.length(Nat, ord))), SC.length(Nat, ord), AO.len_nat(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)))

# while the capacity is not below the length the loop does nothing
def idle(~V: Data, p: Nat, +c0: U32, +capn: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +ev: U32, +eo: {Nat.is_lt(U32.to_nat(capn), SC.length(Nat, ord)) == False{} : Bool}, +h: {ST.inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {F.shrink(~V, p, capn, F.SR{ST.real(~V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), ev}) == F.SR{ST.real(~V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), ev} : F.Shr<V>}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      +eo2 = Equal.trans(Bool, U32.is_lt(capn, U32.from_nat(SC.length(Nat, ord))), Nat.is_lt(U32.to_nat(capn), SC.length(Nat, ord)), False{}, over_eq(~V, c0, capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), eo)
      L.subst(Bool, z => {F.shrink(~V, q, capn, F.shrink_one(~V, capn, ST.real(~V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), ev, z)) == F.SR{ST.real(~V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), ev} : F.Shr<V>}, False{}, U32.is_lt(capn, U32.from_nat(SC.length(Nat, ord))), Equal.sym(Bool, U32.is_lt(capn, U32.from_nat(SC.length(Nat, ord))), False{}, eo2), idle(~V, q, c0, capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, ev, eo, h))

# ---- the runtime loop ----

def SrIH(~V: Data, +p: Nat, +c0: U32, +capn: U32) -> Type:
  @fresh: Nat -> @depth: Nat -> @life: T.Int64 -> @tc: AR.Tree<U32> -> @table: Map<&2, Maybe<&2, U32>> -> @tk: AR.Tree<String> -> @te: AR.Tree<F.Slot<V>> -> @tp: AR.Tree<U32> -> @tn: AR.Tree<U32> -> @ord: List<&2, Nat> -> @fl: List<&2, Nat> -> @j: Nat -> @h: {ST.inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool} -> {F.shrink(~V, p, capn, F.SR{ST.real(~V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), U32.from_nat(j)}) == srp(~V, sr_g(V, p, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), j) : F.Shr<V>}

def sr_over(~V: Data, +p: Nat, +c0: U32, +capn: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, ord: List<&2, Nat>, +fl: List<&2, Nat>, +j: Nat, +eo: {Nat.is_lt(U32.to_nat(capn), SC.length(Nat, ord)) == True{} : Bool}, +h: {ST.inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, ih: SrIH(~V, p, c0, capn)) -> {F.shrink(~V, p, capn, F.SR{F.evict_oldest(~V, ST.real(~V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl})), U32.inc(U32.from_nat(j))}) == srp(~V, inc_snd(V, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}))), j) : F.Shr<V>}:
  match ord:
    case Nil{}:
      Empty.absurd({F.shrink(~V, p, capn, F.SR{F.evict_oldest(~V, ST.real(~V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Nil{}, fl})), U32.inc(U32.from_nat(j))}) == srp(~V, inc_snd(V, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Nil{}, fl}))), j) : F.Shr<V>}, N.lt_zero_absurd(U32.to_nat(capn), eo))
    case Con{+s0, +rest}:
      +hm = TB.or_true_l(Nat.is_eq(s0, s0), DST.lmem(s0, rest), AL.lmem_self(s0))
      +h2 = RM.rm_at_inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, s0, 1n, hm, h)
      +e1 = Equal.cong(F.Fast<V>, F.Shr<V>, f => F.shrink(~V, p, capn, F.SR{f, U32.from_nat(1n+j)}), F.evict_oldest(~V, ST.real(~V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl})), ST.real(~V, RM.rs_sh_at(V, capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, s0, fl, 1n)), evc_real(~V, c0, capn, fresh, depth, life, tc, table, tk, te, tp, tn, s0, rest, fl, h))
      +e2 = ih(fresh, depth, life, RS.sbd(tc, 1n), Map.del(&2, Maybe<&2, U32>, table, ST.kat(AR.slots(String, tk), s0)), tk, AR.upd(F.Slot<V>, depth, te, s0, F.Vacant{}), TS.tpup(depth, tp, SP.spost(Con{s0, rest}, s0), LK.lastl(SP.spre(Con{s0, rest}, s0), D.nil())), AR.upd(U32, depth, TS.tnup(depth, tn, SP.spre(Con{s0, rest}, s0), DST.hd_or(SP.spost(Con{s0, rest}, s0), D.nil())), s0, DST.hd(fl)), SC.append(Nat, SP.spre(Con{s0, rest}, s0), SP.spost(Con{s0, rest}, s0)), Con{s0, fl}, 1n+j, h2)
      Equal.trans(F.Shr<V>, F.shrink(~V, p, capn, F.SR{F.evict_oldest(~V, ST.real(~V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl})), U32.from_nat(1n+j)}), srp(~V, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl})), 1n+j), srp(~V, inc_snd(V, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}))), j),
        Equal.trans(F.Shr<V>, F.shrink(~V, p, capn, F.SR{F.evict_oldest(~V, ST.real(~V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl})), U32.from_nat(1n+j)}), F.shrink(~V, p, capn, F.SR{ST.real(~V, RM.rs_sh_at(V, capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, s0, fl, 1n)), U32.from_nat(1n+j)}), srp(~V, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl})), 1n+j), e1, e2),
        Equal.sym(F.Shr<V>, srp(~V, inc_snd(V, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}))), j), srp(~V, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl})), 1n+j), srp_inc(~V, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl})), j)))

def sr_c(~V: Data, +p: Nat, +c0: U32, +capn: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +j: Nat, over: Bool, +eo: {Nat.is_lt(U32.to_nat(capn), SC.length(Nat, ord)) == over : Bool}, +h: {ST.inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, ih: SrIH(~V, p, c0, capn)) -> {F.shrink(~V, p, capn, F.shrink_one(~V, capn, ST.real(~V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), U32.from_nat(j), over)) == srp(~V, sr_pick(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl})), over), j) : F.Shr<V>}:
  match over:
    case False{}:
      idle(~V, p, c0, capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, U32.from_nat(j), eo, h)
    case True{}:
      sr_over(~V, p, c0, capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, j, eo, h, ih)

def sr_real(~V: Data, fuel: Nat, +c0: U32, +capn: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +j: Nat, +h: {ST.inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {F.shrink(~V, fuel, capn, F.SR{ST.real(~V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), U32.from_nat(j)}) == srp(~V, sr_g(V, fuel, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), j) : F.Shr<V>}:
  match fuel:
    case 0n:
      {==}
    case 1n+ +p:
      L.subst(Bool, z => {F.shrink(~V, p, capn, F.shrink_one(~V, capn, ST.real(~V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), U32.from_nat(j), z)) == srp(~V, sr_pick(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl})), Nat.is_lt(U32.to_nat(capn), SC.length(Nat, ord))), j) : F.Shr<V>}, Nat.is_lt(U32.to_nat(capn), SC.length(Nat, ord)), U32.is_lt(capn, U32.from_nat(SC.length(Nat, ord))), Equal.sym(Bool, U32.is_lt(capn, U32.from_nat(SC.length(Nat, ord))), Nat.is_lt(U32.to_nat(capn), SC.length(Nat, ord)), over_eq(~V, c0, capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)),
        sr_c(~V, p, c0, capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, j, Nat.is_lt(U32.to_nat(capn), SC.length(Nat, ord)), {==}, h, a1 => a2 => a3 => a4 => a5 => a6 => a7 => a8 => a9 => a10 => a11 => a12 => a13 => sr_real(~V, p, c0, capn, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13)))

# ---- Nat subtraction facts ----

def sub_le_zero(a: Nat, b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.sub(a, b) == 0n : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.sub(1n+ap, 0n) == 0n : Nat}, L.false_true(h))
    case 1n+ap 1n+bp:
      sub_le_zero(ap, bp, h)

def sub_zero_le(a: Nat, b: Nat, +h: {Nat.sub(a, b) == 0n : Nat}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, N.succ_zero(ap, h))
    case 1n+ap 1n+bp:
      sub_zero_le(ap, bp, h)

def pred_eq(+a: Nat, +b: Nat, +h: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, z => N.pred(z), 1n+a, 1n+b, h)

# ---- removing the head: entries lose their first element, the order one slot ----

def hrm_ents(~V: Data, +c0: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +s0: Nat, +rest: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl) == True{} : Bool}) -> {ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s0, F.Vacant{})), SC.append(Nat, SP.spre(Con{s0, rest}, s0), SP.spost(Con{s0, rest}, s0))) == S.tail(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), Con{s0, rest})) : List<&2, S.Ent<V>>}:
  +ks = AR.slots(String, tk)
  +es = AR.slots(F.Slot<V>, te)
  +k0 = ST.kat(ks, s0)
  +hm = TB.or_true_l(Nat.is_eq(s0, s0), DST.lmem(s0, rest), AL.lmem_self(s0))
  +a = SP.spre(Con{s0, rest}, s0)
  +b = SP.spost(Con{s0, rest}, s0)
  +esp = SP.split_eq(Con{s0, rest}, s0, hm)
  +hs2 = RM.split_inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, s0, hm, h)
  +P0 = SC.pow2(depth)
  +hfr = ST.g_fresh(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h)
  +hol = ST.g_ordlt(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h)
  +hs0 = N.lt_le_trans(s0, fresh, P0, L.and_left(Nat.is_lt(s0, fresh), DST.alllt(rest, fresh), hol), hfr)
  +hlo2 = K.alllt_mono(SC.append(Nat, a, Con{s0, b}), fresh, P0, ST.g_fresh(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s0, b}), fl, hs2), ST.g_ordlt(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s0, b}), fl, hs2))
  +hocc = ST.g_occ(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h)
  +hmp = ST.g_mapped(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h)
  +ho = L.and_left(ST.is_occ(V, ST.sat(V, es, s0)), ST.all_occ(V, es, rest), hocc)
  +hnd0 = SP.nodup_app_l(Con{s0, rest}, fl, ST.g_nodup(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h))
  +hn0 = TB.not_false(DST.lmem(s0, rest), L.and_left(Bool.not(DST.lmem(s0, rest)), DST.nodup(rest), hnd0))
  +hlr = K.alllt_mono(rest, fresh, P0, hfr, L.and_right(Nat.is_lt(s0, fresh), DST.alllt(rest, fresh), hol))
  +hnk = RS.nk_part(table, ks, rest, s0, depth, ST.g_depth(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h), hs0, hlr, hn0, RS.lk_slot(table, ks, Nil{}, s0, rest, hmp), L.and_right(ST.mapped(table, k0, s0), ST.all_mapped(table, ks, rest), hmp))
  +xs = ST.ents(V, ks, es, Con{s0, rest})
  +er = ST.ents(V, ks, es, rest)
  Equal.trans(List<&2, S.Ent<V>>, ST.ents(V, ks, AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s0, F.Vacant{})), SC.append(Nat, a, b)), S.drop(V, ST.ents(V, ks, es, SC.append(Nat, a, Con{s0, b})), k0), S.tail(V, xs),
    RS.rs_ents(V, depth, table, tk, te, a, s0, b, ST.g_depth(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h), ST.g_te(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h), hs0, hlo2, SP.nodup_app_l(SC.append(Nat, a, Con{s0, b}), fl, ST.g_nodup(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s0, b}), fl, hs2)), ST.g_occ(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s0, b}), fl, hs2), ST.g_mapped(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s0, b}), fl, hs2)),
    Equal.trans(List<&2, S.Ent<V>>, S.drop(V, ST.ents(V, ks, es, SC.append(Nat, a, Con{s0, b})), k0), S.drop(V, xs, k0), S.tail(V, xs),
      Equal.cong(List<&2, Nat>, List<&2, S.Ent<V>>, z => S.drop(V, ST.ents(V, ks, es, z), k0), SC.append(Nat, a, Con{s0, b}), Con{s0, rest}, Equal.sym(List<&2, Nat>, Con{s0, rest}, SC.append(Nat, a, Con{s0, b}), esp)),
      Equal.trans(List<&2, S.Ent<V>>, S.drop(V, xs, k0), S.drop(V, er, k0), S.tail(V, xs),
        EN.drop_here(V, k0, ST.sat(V, es, s0), er, k0, LR.string_reflexive(k0), ho),
        Equal.trans(List<&2, S.Ent<V>>, S.drop(V, er, k0), er, S.tail(V, xs), EN.drop_none(V, ks, es, rest, k0, hnk), Equal.sym(List<&2, S.Ent<V>>, S.tail(V, xs), er, EN.ent_tail(V, k0, ST.sat(V, es, s0), er, ho))))))

def hrm_len(+s0: Nat, +rest: List<&2, Nat>, +hm: {DST.lmem(s0, Con{s0, rest}) == True{} : Bool}) -> {SC.length(Nat, SC.append(Nat, SP.spre(Con{s0, rest}, s0), SP.spost(Con{s0, rest}, s0))) == SC.length(Nat, rest) : Nat}:
  +a = SP.spre(Con{s0, rest}, s0)
  +b = SP.spost(Con{s0, rest}, s0)
  +e = Equal.trans(Nat, 1n+SC.length(Nat, SC.append(Nat, a, b)), SC.length(Nat, SC.append(Nat, a, Con{s0, b})), SC.length(Nat, Con{s0, rest}), Equal.sym(Nat, SC.length(Nat, SC.append(Nat, a, Con{s0, b})), 1n+SC.length(Nat, SC.append(Nat, a, b)), RS.len_cut(a, s0, b)), Equal.cong(List<&2, Nat>, Nat, z => SC.length(Nat, z), SC.append(Nat, a, Con{s0, b}), Con{s0, rest}, Equal.sym(List<&2, Nat>, Con{s0, rest}, SC.append(Nat, a, Con{s0, b}), SP.split_eq(Con{s0, rest}, s0, hm))))
  pred_eq(SC.length(Nat, SC.append(Nat, a, b)), SC.length(Nat, rest), e)


# ---- the model of the loop ----

def sr_mp(~V: Data, r: ST.Shadow<V> & Nat) -> S.Model<V> & Nat:
  (s, k) = r
  (ST.model(~V, s), k)

def inc2(~V: Data, r: S.Model<V> & Nat) -> S.Model<V> & Nat:
  (m, k) = r
  (m, 1n+k)

def mp_inc(~V: Data, r: ST.Shadow<V> & Nat) -> {sr_mp(~V, inc_snd(V, r)) == inc2(~V, sr_mp(~V, r)) : S.Model<V> & Nat}:
  (s, k) = r
  {==}

def SrmIH(~V: Data, +p: Nat, +c0: U32, +capn: U32) -> Type:
  @fresh: Nat -> @depth: Nat -> @life: T.Int64 -> @tc: AR.Tree<U32> -> @table: Map<&2, Maybe<&2, U32>> -> @tk: AR.Tree<String> -> @te: AR.Tree<F.Slot<V>> -> @tp: AR.Tree<U32> -> @tn: AR.Tree<U32> -> @ord: List<&2, Nat> -> @fl: List<&2, Nat> -> @k: Nat -> @ek: {Nat.sub(SC.length(Nat, ord), U32.to_nat(capn)) == k : Nat} -> @hk: {Nat.is_le(k, p) == True{} : Bool} -> @h: {ST.inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool} -> {sr_mp(~V, sr_g(V, p, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl})) == (S.LM{capn, life, S.dropn(V, k, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord)), S.bumpn(k, 1n, ST.mets(AR.slots(U32, tc)))}, k) : S.Model<V> & Nat}

def zero_res(~V: Data, +capn: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +k: Nat, +ek: {0n == k : Nat}) -> {(ST.model(~V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), 0n) == (S.LM{capn, life, S.dropn(V, k, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord)), S.bumpn(k, 1n, ST.mets(AR.slots(U32, tc)))}, k) : S.Model<V> & Nat}:
  L.subst(Nat, z => {(ST.model(~V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), 0n) == (S.LM{capn, life, S.dropn(V, z, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord)), S.bumpn(z, 1n, ST.mets(AR.slots(U32, tc)))}, z) : S.Model<V> & Nat}, 0n, k, ek, {==})

def srm_over(~V: Data, +p: Nat, +c0: U32, +capn: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, ord: List<&2, Nat>, +fl: List<&2, Nat>, +k: Nat, +ek: {Nat.sub(SC.length(Nat, ord), U32.to_nat(capn)) == k : Nat}, +hk: {Nat.is_le(k, 1n+p) == True{} : Bool}, +eo: {Nat.is_lt(U32.to_nat(capn), SC.length(Nat, ord)) == True{} : Bool}, +h: {ST.inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, ih: SrmIH(~V, p, c0, capn)) -> {sr_mp(~V, inc_snd(V, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl})))) == (S.LM{capn, life, S.dropn(V, k, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord)), S.bumpn(k, 1n, ST.mets(AR.slots(U32, tc)))}, k) : S.Model<V> & Nat}:
  match ord:
    case Nil{}:
      Empty.absurd({sr_mp(~V, inc_snd(V, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Nil{}, fl})))) == (S.LM{capn, life, S.dropn(V, k, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), Nil{})), S.bumpn(k, 1n, ST.mets(AR.slots(U32, tc)))}, k) : S.Model<V> & Nat}, N.lt_zero_absurd(U32.to_nat(capn), eo))
    case Con{+s0, +rest}:
      +hm = TB.or_true_l(Nat.is_eq(s0, s0), DST.lmem(s0, rest), AL.lmem_self(s0))
      +h2 = RM.rm_at_inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, s0, 1n, hm, h)
      +ab = SC.append(Nat, SP.spre(Con{s0, rest}, s0), SP.spost(Con{s0, rest}, s0))
      +k1 = Nat.sub(SC.length(Nat, ab), U32.to_nat(capn))
      +cr = N.lt_succ_le_succ(U32.to_nat(capn), 1n+SC.length(Nat, rest), eo)
      +ek2 = Equal.trans(Nat, k, Nat.sub(1n+SC.length(Nat, rest), U32.to_nat(capn)), 1n+k1, Equal.sym(Nat, Nat.sub(1n+SC.length(Nat, rest), U32.to_nat(capn)), k, ek),
        Equal.trans(Nat, Nat.sub(1n+SC.length(Nat, rest), U32.to_nat(capn)), 1n+Nat.sub(SC.length(Nat, rest), U32.to_nat(capn)), 1n+k1, N.sub_succ_left(SC.length(Nat, rest), U32.to_nat(capn), cr),
          Equal.cong(Nat, Nat, z => 1n+Nat.sub(z, U32.to_nat(capn)), SC.length(Nat, rest), SC.length(Nat, ab), Equal.sym(Nat, SC.length(Nat, ab), SC.length(Nat, rest), hrm_len(s0, rest, hm)))))
      +hk1 = L.subst(Nat, z => {Nat.is_le(z, 1n+p) == True{} : Bool}, k, 1n+k1, ek2, hk)
      +r1 = ih(fresh, depth, life, RS.sbd(tc, 1n), Map.del(&2, Maybe<&2, U32>, table, ST.kat(AR.slots(String, tk), s0)), tk, AR.upd(F.Slot<V>, depth, te, s0, F.Vacant{}), TS.tpup(depth, tp, SP.spost(Con{s0, rest}, s0), LK.lastl(SP.spre(Con{s0, rest}, s0), D.nil())), AR.upd(U32, depth, TS.tnup(depth, tn, SP.spre(Con{s0, rest}, s0), DST.hd_or(SP.spost(Con{s0, rest}, s0), D.nil())), s0, DST.hd(fl)), SC.append(Nat, SP.spre(Con{s0, rest}, s0), SP.spost(Con{s0, rest}, s0)), Con{s0, fl}, k1, {==}, hk1, h2)
      +xs = ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), Con{s0, rest})
      +xs1 = ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s0, F.Vacant{})), ab)
      +mt1 = ST.mets(AR.slots(U32, RS.sbd(tc, 1n)))
      +e3 = Equal.trans(S.Model<V> & Nat, inc2(~V, (S.LM{capn, life, S.dropn(V, k1, xs1), S.bumpn(k1, 1n, mt1)}, k1)), (S.LM{capn, life, S.dropn(V, k1, S.tail(V, xs)), S.bumpn(k1, 1n, mt1)}, 1n+k1), (S.LM{capn, life, S.dropn(V, k1, S.tail(V, xs)), S.bumpn(k1, 1n, T.bump(1n, ST.mets(AR.slots(U32, tc))))}, 1n+k1),
        Equal.cong(List<&2, S.Ent<V>>, S.Model<V> & Nat, z => (S.LM{capn, life, S.dropn(V, k1, z), S.bumpn(k1, 1n, mt1)}, 1n+k1), xs1, S.tail(V, xs), hrm_ents(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, s0, rest, fl, h)),
        Equal.cong(T.Metrics, S.Model<V> & Nat, z => (S.LM{capn, life, S.dropn(V, k1, S.tail(V, xs)), S.bumpn(k1, 1n, z)}, 1n+k1), mt1, T.bump(1n, ST.mets(AR.slots(U32, tc))), RS.mets_drop(tc, 1n, ST.g_tc(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h))))
      +e4 = Equal.trans(S.Model<V> & Nat, sr_mp(~V, inc_snd(V, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl})))), inc2(~V, sr_mp(~V, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl})))), (S.LM{capn, life, S.dropn(V, k1, S.tail(V, xs)), S.bumpn(k1, 1n, T.bump(1n, ST.mets(AR.slots(U32, tc))))}, 1n+k1),
        mp_inc(~V, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}))),
        Equal.trans(S.Model<V> & Nat, inc2(~V, sr_mp(~V, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl})))), inc2(~V, (S.LM{capn, life, S.dropn(V, k1, xs1), S.bumpn(k1, 1n, mt1)}, k1)), (S.LM{capn, life, S.dropn(V, k1, S.tail(V, xs)), S.bumpn(k1, 1n, T.bump(1n, ST.mets(AR.slots(U32, tc))))}, 1n+k1),
          Equal.cong(S.Model<V> & Nat, S.Model<V> & Nat, z => inc2(~V, z), sr_mp(~V, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}))), (S.LM{capn, life, S.dropn(V, k1, xs1), S.bumpn(k1, 1n, mt1)}, k1), r1),
          e3))
      L.subst(Nat, z => {sr_mp(~V, inc_snd(V, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl})))) == (S.LM{capn, life, S.dropn(V, z, xs), S.bumpn(z, 1n, ST.mets(AR.slots(U32, tc)))}, z) : S.Model<V> & Nat}, 1n+k1, k, Equal.sym(Nat, k, 1n+k1, ek2), e4)

def srm_c(~V: Data, +p: Nat, +c0: U32, +capn: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +k: Nat, +ek: {Nat.sub(SC.length(Nat, ord), U32.to_nat(capn)) == k : Nat}, +hk: {Nat.is_le(k, 1n+p) == True{} : Bool}, over: Bool, +eo: {Nat.is_lt(U32.to_nat(capn), SC.length(Nat, ord)) == over : Bool}, +h: {ST.inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, ih: SrmIH(~V, p, c0, capn)) -> {sr_mp(~V, sr_pick(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl})), over)) == (S.LM{capn, life, S.dropn(V, k, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord)), S.bumpn(k, 1n, ST.mets(AR.slots(U32, tc)))}, k) : S.Model<V> & Nat}:
  match over:
    case False{}:
      zero_res(~V, capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, k, Equal.trans(Nat, 0n, Nat.sub(SC.length(Nat, ord), U32.to_nat(capn)), k, Equal.sym(Nat, Nat.sub(SC.length(Nat, ord), U32.to_nat(capn)), 0n, sub_le_zero(SC.length(Nat, ord), U32.to_nat(capn), N.not_lt_le(U32.to_nat(capn), SC.length(Nat, ord), eo))), ek))
    case True{}:
      srm_over(~V, p, c0, capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, k, ek, hk, eo, h, ih)

def sr_model(~V: Data, fuel: Nat, +c0: U32, +capn: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +k: Nat, +ek: {Nat.sub(SC.length(Nat, ord), U32.to_nat(capn)) == k : Nat}, +hk: {Nat.is_le(k, fuel) == True{} : Bool}, +h: {ST.inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {sr_mp(~V, sr_g(V, fuel, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl})) == (S.LM{capn, life, S.dropn(V, k, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord)), S.bumpn(k, 1n, ST.mets(AR.slots(U32, tc)))}, k) : S.Model<V> & Nat}:
  match fuel:
    case 0n:
      zero_res(~V, capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, k, Equal.sym(Nat, k, 0n, IT.eq_nat_true(k, 0n, AO.le0_eq(k, hk))))
    case 1n+ +p:
      srm_c(~V, p, c0, capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, k, ek, hk, Nat.is_lt(U32.to_nat(capn), SC.length(Nat, ord)), {==}, h, a1 => a2 => a3 => a4 => a5 => a6 => a7 => a8 => a9 => a10 => a11 => a12 => a13 => a14 => a15 => sr_model(~V, p, c0, capn, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15))

# ---- the invariant after the loop ----

def sr_gd(~V: Data, r: ST.Shadow<V> & Nat) -> Bool:
  (s, k) = r
  ST.good(~V, s)

def gd_inc(~V: Data, r: ST.Shadow<V> & Nat) -> {sr_gd(~V, inc_snd(V, r)) == sr_gd(~V, r) : Bool}:
  (s, k) = r
  {==}

def SriIH(~V: Data, +p: Nat, +c0: U32, +capn: U32) -> Type:
  @fresh: Nat -> @depth: Nat -> @life: T.Int64 -> @tc: AR.Tree<U32> -> @table: Map<&2, Maybe<&2, U32>> -> @tk: AR.Tree<String> -> @te: AR.Tree<F.Slot<V>> -> @tp: AR.Tree<U32> -> @tn: AR.Tree<U32> -> @ord: List<&2, Nat> -> @fl: List<&2, Nat> -> @k: Nat -> @ek: {Nat.sub(SC.length(Nat, ord), U32.to_nat(capn)) == k : Nat} -> @hk: {Nat.is_le(k, p) == True{} : Bool} -> @hc: {Bool.not(U32.is_eq(capn, 0)) == True{} : Bool} -> @h: {ST.inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool} -> {sr_gd(~V, sr_g(V, p, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl})) == True{} : Bool}

def sri_over(~V: Data, +p: Nat, +c0: U32, +capn: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, ord: List<&2, Nat>, +fl: List<&2, Nat>, +k: Nat, +ek: {Nat.sub(SC.length(Nat, ord), U32.to_nat(capn)) == k : Nat}, +hk: {Nat.is_le(k, 1n+p) == True{} : Bool}, +eo: {Nat.is_lt(U32.to_nat(capn), SC.length(Nat, ord)) == True{} : Bool}, +hc: {Bool.not(U32.is_eq(capn, 0)) == True{} : Bool}, +h: {ST.inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, ih: SriIH(~V, p, c0, capn)) -> {sr_gd(~V, inc_snd(V, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl})))) == True{} : Bool}:
  match ord:
    case Nil{}:
      Empty.absurd({sr_gd(~V, inc_snd(V, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Nil{}, fl})))) == True{} : Bool}, N.lt_zero_absurd(U32.to_nat(capn), eo))
    case Con{+s0, +rest}:
      +hm = TB.or_true_l(Nat.is_eq(s0, s0), DST.lmem(s0, rest), AL.lmem_self(s0))
      +h2 = RM.rm_at_inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, s0, 1n, hm, h)
      +ab = SC.append(Nat, SP.spre(Con{s0, rest}, s0), SP.spost(Con{s0, rest}, s0))
      +k1 = Nat.sub(SC.length(Nat, ab), U32.to_nat(capn))
      +cr = N.lt_succ_le_succ(U32.to_nat(capn), 1n+SC.length(Nat, rest), eo)
      +ek2 = Equal.trans(Nat, k, Nat.sub(1n+SC.length(Nat, rest), U32.to_nat(capn)), 1n+k1, Equal.sym(Nat, Nat.sub(1n+SC.length(Nat, rest), U32.to_nat(capn)), k, ek),
        Equal.trans(Nat, Nat.sub(1n+SC.length(Nat, rest), U32.to_nat(capn)), 1n+Nat.sub(SC.length(Nat, rest), U32.to_nat(capn)), 1n+k1, N.sub_succ_left(SC.length(Nat, rest), U32.to_nat(capn), cr),
          Equal.cong(Nat, Nat, z => 1n+Nat.sub(z, U32.to_nat(capn)), SC.length(Nat, rest), SC.length(Nat, ab), Equal.sym(Nat, SC.length(Nat, ab), SC.length(Nat, rest), hrm_len(s0, rest, hm)))))
      +hk1 = L.subst(Nat, z => {Nat.is_le(z, 1n+p) == True{} : Bool}, k, 1n+k1, ek2, hk)
      Equal.trans(Bool, sr_gd(~V, inc_snd(V, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl})))), sr_gd(~V, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}))), True{},
        gd_inc(~V, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}))),
        ih(fresh, depth, life, RS.sbd(tc, 1n), Map.del(&2, Maybe<&2, U32>, table, ST.kat(AR.slots(String, tk), s0)), tk, AR.upd(F.Slot<V>, depth, te, s0, F.Vacant{}), TS.tpup(depth, tp, SP.spost(Con{s0, rest}, s0), LK.lastl(SP.spre(Con{s0, rest}, s0), D.nil())), AR.upd(U32, depth, TS.tnup(depth, tn, SP.spre(Con{s0, rest}, s0), DST.hd_or(SP.spost(Con{s0, rest}, s0), D.nil())), s0, DST.hd(fl)), SC.append(Nat, SP.spre(Con{s0, rest}, s0), SP.spost(Con{s0, rest}, s0)), Con{s0, fl}, k1, {==}, hk1, hc, h2))

def sri_c(~V: Data, +p: Nat, +c0: U32, +capn: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +k: Nat, +ek: {Nat.sub(SC.length(Nat, ord), U32.to_nat(capn)) == k : Nat}, +hk: {Nat.is_le(k, 1n+p) == True{} : Bool}, over: Bool, +eo: {Nat.is_lt(U32.to_nat(capn), SC.length(Nat, ord)) == over : Bool}, +hc: {Bool.not(U32.is_eq(capn, 0)) == True{} : Bool}, +h: {ST.inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, ih: SriIH(~V, p, c0, capn)) -> {sr_gd(~V, sr_pick(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, sr_g(V, p, ev1(V, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl})), over)) == True{} : Bool}:
  match over:
    case False{}:
      recap(~V, c0, capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h, hc, N.not_lt_le(U32.to_nat(capn), SC.length(Nat, ord), eo))
    case True{}:
      sri_over(~V, p, c0, capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, k, ek, hk, eo, hc, h, ih)

def sr_inv(~V: Data, fuel: Nat, +c0: U32, +capn: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +k: Nat, +ek: {Nat.sub(SC.length(Nat, ord), U32.to_nat(capn)) == k : Nat}, +hk: {Nat.is_le(k, fuel) == True{} : Bool}, +hc: {Bool.not(U32.is_eq(capn, 0)) == True{} : Bool}, +h: {ST.inv(~V, c0, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {sr_gd(~V, sr_g(V, fuel, ST.Sh{capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl})) == True{} : Bool}:
  match fuel:
    case 0n:
      +ek0 = Equal.trans(Nat, Nat.sub(SC.length(Nat, ord), U32.to_nat(capn)), k, 0n, ek, IT.eq_nat_true(k, 0n, AO.le0_eq(k, hk)))
      recap(~V, c0, capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h, hc, sub_zero_le(SC.length(Nat, ord), U32.to_nat(capn), ek0))
    case 1n+ +p:
      sri_c(~V, p, c0, capn, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, k, ek, hk, Nat.is_lt(U32.to_nat(capn), SC.length(Nat, ord)), {==}, hc, h, a1 => a2 => a3 => a4 => a5 => a6 => a7 => a8 => a9 => a10 => a11 => a12 => a13 => a14 => a15 => a16 => sr_inv(~V, p, c0, capn, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16))
