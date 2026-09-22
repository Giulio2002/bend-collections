import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../spec/lru_fast.bend as S
import ../../src/lru/fast.bend as F
import ../../types/lru_model.bend as T
import support/links_state.bend as DST
import support/links_split.bend as SP
import support/links_tolist.bend as TL
import support/links_core.bend as K
import ../../reference/lru/proofs/map_key_presence.bend as Presence
import ../../reference/lru/proofs/map_key_membership.bend as KeyMem
import ../../reference/lru/proofs/recency_unique.bend as RU
import ../../reference/lru/proofs/invariants.bend as Inv
import ./state.bend as ST
import ./table.bend as TB
import ./ents.bend as EN
import ./rs.bend as RS
import ./lists.bend as LS
import ../lib/u32.bend as U
import ../../src/lru/time.bend as Time
import ../../reference/lru/proofs/map_populated.bend as Pop

# remove(key): the key's slot (the first slot of the order holding the key,
# TB.firstk) is cut out by the removal core; an absent key changes nothing.

# ---- the removal core at a slot of an unsplit order ----

def rs_sh_at(-V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +s: Nat, +fl: List<&2, Nat>, +metric: Nat) -> ST.Shadow<V>:
  RS.rs_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SP.spre(ord, s), s, SP.spost(ord, s), fl, metric)

def split_inv(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, +hm: {DST.lmem(s, ord) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl) == True{} : Bool}:
  L.subst(List<&2, Nat>, z => {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, z, fl) == True{} : Bool}, ord, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), SP.split_eq(ord, s, hm), h)

def rm_at_real(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, +metric: Nat, +hm: {DST.lmem(s, ord) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {F.remove_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), U32.from_nat(s), metric) == (ST.real(~V, rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, s, fl, metric)), F.slot_val(~V, ST.sat(V, AR.slots(F.Slot<V>, te), s))) : F.Fast<V> & Maybe<&2, V>}:
  +a = SP.spre(ord, s)
  +b = SP.spost(ord, s)
  +o = SC.append(Nat, a, Con{s, b})
  +hs2 = split_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, hm, h)
  +P = SC.pow2(depth)
  +hfr = ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2)
  +hol = ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2)
  +hsf = L.and_left(Nat.is_lt(s, fresh), DST.alllt(b, fresh), TL.alllt_r(a, Con{s, b}, fresh, hol))
  +hle = N.le_trans(SC.length(Nat, o), fresh, P, RS.ord_le(o, fl, fresh, ST.g_count(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2)), hfr)
  +r = RS.rs_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, a, s, b, fl, metric, ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2), ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2), ST.g_tk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2), ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2), ST.g_tp(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2), ST.g_tn(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2), N.lt_le_trans(s, fresh, P, hsf, hfr), K.alllt_mono(o, fresh, P, hfr, hol), ST.g_lk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2), hle)
  L.subst(List<&2, Nat>, z => {F.remove_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, z, fl}), U32.from_nat(s), metric) == (ST.real(~V, rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, s, fl, metric)), F.slot_val(~V, ST.sat(V, AR.slots(F.Slot<V>, te), s))) : F.Fast<V> & Maybe<&2, V>}, o, ord, Equal.sym(List<&2, Nat>, ord, o, SP.split_eq(ord, s, hm)), r)

def rm_at_inv(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, +metric: Nat, +hm: {DST.lmem(s, ord) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {ST.good(~V, rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, s, fl, metric)) == True{} : Bool}:
  RS.rs_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SP.spre(ord, s), s, SP.spost(ord, s), fl, metric, split_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, hm, h))

def rm_at_model(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, +metric: Nat, +hm: {DST.lmem(s, ord) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {ST.model(~V, rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, s, fl, metric)) == S.LM{cap, life, S.drop(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), ST.kat(AR.slots(String, tk), s)), T.bump(RS.mi(metric), ST.mets(AR.slots(U32, tc)))} : S.Model<V>}:
  +a = SP.spre(ord, s)
  +b = SP.spost(ord, s)
  +o = SC.append(Nat, a, Con{s, b})
  +hs2 = split_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, hm, h)
  +P = SC.pow2(depth)
  +hfr = ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2)
  +hol = ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2)
  +hsf = L.and_left(Nat.is_lt(s, fresh), DST.alllt(b, fresh), TL.alllt_r(a, Con{s, b}, fresh, hol))
  +r = RS.rs_model(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, a, s, b, fl, metric, ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2), ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2), ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2), N.lt_le_trans(s, fresh, P, hsf, hfr), K.alllt_mono(o, fresh, P, hfr, hol), SP.nodup_app_l(o, fl, ST.g_nodup(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2)), ST.g_occ(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2), ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2))
  L.subst(List<&2, Nat>, z => {ST.model(~V, rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, s, fl, metric)) == S.LM{cap, life, S.drop(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), z), ST.kat(AR.slots(String, tk), s)), T.bump(RS.mi(metric), ST.mets(AR.slots(U32, tc)))} : S.Model<V>}, o, ord, Equal.sym(List<&2, Nat>, ord, o, SP.split_eq(ord, s, hm)), r)

# ---- a present key ----

def found_k(+t: Map<&2, Maybe<&2, U32>>, +ks: List<&2, String>, +ord: List<&2, Nat>, +q: String, +x: U32, +hx: {TB.lk(t, q) == Some{x} : Maybe<&2, U32>}, +crit: {Inv.critbit(Maybe<&2, U32>, t) == True{} : Bool}, +pop: {Pop.populated(U32, t) == True{} : Bool}, +incl: {Inv.included(Map.keys(&2, Maybe<&2, U32>, t), ST.keys_at(ks, ord)) == True{} : Bool}) -> {Bool.and(DST.lmem(TB.firstk(ks, ord, q), ord), String.eq(ST.kat(ks, TB.firstk(ks, ord, q)), q)) == True{} : Bool}:
  +hmem = Equal.trans(Bool, Inv.member(Map.keys(&2, Maybe<&2, U32>, t), q), Maybe.is_some(&2, U32, TB.lk(t, q)), True{}, Equal.sym(Bool, Maybe.is_some(&2, U32, TB.lk(t, q)), Inv.member(Map.keys(&2, Maybe<&2, U32>, t), q), Presence.lookup_presence(U32, t, q, crit, pop)), Equal.cong(Maybe<&2, U32>, Bool, m => Maybe.is_some(&2, U32, m), TB.lk(t, q), Some{x}, hx))
  TB.fk_ok(ks, ord, q, KeyMem.included_member(Map.keys(&2, Maybe<&2, U32>, t), ST.keys_at(ks, ord), q, incl, hmem))

# the spec's remove on the found entry of an occupied slot
def rm_found_spec(~V: Data, +cap: U32, +life: T.Int64, +xs: List<&2, S.Ent<V>>, +m: T.Metrics, +key: String, +k: String, e: F.Slot<V>, +ho: {ST.is_occ(V, e) == True{} : Bool}) -> {S.remove_found(V, cap, life, xs, m, key, EN.ent1(V, k, e)) == (S.LM{cap, life, S.drop(V, xs, key), T.bump(2n, m)}, F.slot_val(~V, e)) : S.Model<V> & Maybe<&2, V>}:
  match e:
    case F.Vacant{}:
      Empty.absurd({(S.LM{cap, life, xs, m}, None{}) == (S.LM{cap, life, S.drop(V, xs, key), T.bump(2n, m)}, None{}) : S.Model<V> & Maybe<&2, V>}, L.false_true(ho))
    case F.Live{v}:
      {==}
    case F.Timed{v, d}:
      {==}

# ---- the operation ----

def rm_ghost(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, m: Maybe<&2, U32>) -> ST.Shadow<V> & Maybe<&2, V>:
  match m:
    case None{}:
      (ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, None{})
    case Some{+x}:
      (rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, TB.firstk(AR.slots(String, tk), ord, key), fl, 2n), F.slot_val(~V, ST.sat(V, AR.slots(F.Slot<V>, te), TB.firstk(AR.slots(String, tk), ord, key))))

def rp(~V: Data, g: ST.Shadow<V> & Maybe<&2, V>) -> F.Fast<V> & Maybe<&2, V>:
  (sh, v) = g
  (ST.real(~V, sh), v)

def mp(~V: Data, g: ST.Shadow<V> & Maybe<&2, V>) -> S.Model<V> & Maybe<&2, V>:
  (sh, v) = g
  (ST.model(~V, sh), v)

def gp(~V: Data, g: ST.Shadow<V> & Maybe<&2, V>) -> Bool:
  (sh, v) = g
  ST.good(~V, sh)

def rm_real_m(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, m: Maybe<&2, U32>, +em: {TB.lk(table, key) == m : Maybe<&2, U32>}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {F.rm_pick(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), m) == rp(~V, rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, m)) : F.Fast<V> & Maybe<&2, V>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      +ks = AR.slots(String, tk)
      +s = TB.firstk(ks, ord, key)
      +ex = TB.locate(table, ks, ord, key, x, em, ST.g_crit(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_pop(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_incl(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
      +hk = found_k(table, ks, ord, key, x, em, ST.g_crit(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_pop(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_incl(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
      L.subst(U32, z => {F.remove_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), z, 2n) == (ST.real(~V, rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, s, fl, 2n)), F.slot_val(~V, ST.sat(V, AR.slots(F.Slot<V>, te), s))) : F.Fast<V> & Maybe<&2, V>}, U32.from_nat(s), x, Equal.sym(U32, x, U32.from_nat(s), ex),
        rm_at_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, 2n, L.and_left(DST.lmem(s, ord), String.eq(ST.kat(ks, s), key), hk), h))

def remove_real(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {F.remove(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key) == rp(~V, rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key))) : F.Fast<V> & Maybe<&2, V>}:
  L.subst(Map<&2, Maybe<&2, U32>> & Maybe<&2, U32>, z => {F.rm_found(~V, cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), AR.thaw(String, tk), AR.thaw(F.Slot<V>, te), F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, z) == rp(~V, rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key))) : F.Fast<V> & Maybe<&2, V>}, TB.mpair(table, TB.lk(table, key)), Map.get(Maybe<&2, U32>, None{}, table, key), Equal.sym(Map<&2, Maybe<&2, U32>> & Maybe<&2, U32>, Map.get(Maybe<&2, U32>, None{}, table, key), TB.mpair(table, TB.lk(table, key)), TB.get_pair(table, key)),
    rm_real_m(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key), {==}, h))

def remove_inv_m(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, m: Maybe<&2, U32>, +em: {TB.lk(table, key) == m : Maybe<&2, U32>}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {gp(~V, rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, m)) == True{} : Bool}:
  match m:
    case None{}:
      h
    case Some{+x}:
      +ks = AR.slots(String, tk)
      +s = TB.firstk(ks, ord, key)
      +hk = found_k(table, ks, ord, key, x, em, ST.g_crit(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_pop(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_incl(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
      rm_at_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, 2n, L.and_left(DST.lmem(s, ord), String.eq(ST.kat(ks, s), key), hk), h)

def remove_inv(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {gp(~V, rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key))) == True{} : Bool}:
  remove_inv_m(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key), {==}, h)

def remove_model_m(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, m: Maybe<&2, U32>, +em: {TB.lk(table, key) == m : Maybe<&2, U32>}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {S.remove_found(V, cap, life, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), ST.mets(AR.slots(U32, tc)), key, S.find(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), key)) == mp(~V, rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, m)) : S.Model<V> & Maybe<&2, V>}:
  match m:
    case None{}:
      +ks = AR.slots(String, tk)
      +es = AR.slots(F.Slot<V>, te)
      +xs = ST.ents(V, ks, es, ord)
      +mt = ST.mets(AR.slots(U32, tc))
      +hnk = TB.nk_all(table, ks, ord, key, None{}, em, ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), TB.nomap_none(ord))
      L.subst(Maybe<&2, S.Ent<V>>, z => {S.remove_found(V, cap, life, xs, mt, key, z) == (S.LM{cap, life, xs, mt}, None{}) : S.Model<V> & Maybe<&2, V>}, None{}, S.find(V, xs, key), Equal.sym(Maybe<&2, S.Ent<V>>, S.find(V, xs, key), None{}, EN.find_none(V, ks, es, ord, key, hnk)), {==})
    case Some{+x}:
      +ks = AR.slots(String, tk)
      +es = AR.slots(F.Slot<V>, te)
      +xs = ST.ents(V, ks, es, ord)
      +mt = ST.mets(AR.slots(U32, tc))
      +s = TB.firstk(ks, ord, key)
      +ex = TB.locate(table, ks, ord, key, x, em, ST.g_crit(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_pop(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_incl(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
      +hk = found_k(table, ks, ord, key, x, em, ST.g_crit(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_pop(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_incl(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
      +hm = L.and_left(DST.lmem(s, ord), String.eq(ST.kat(ks, s), key), hk)
      +heq = L.and_right(DST.lmem(s, ord), String.eq(ST.kat(ks, s), key), hk)
      +a = SP.spre(ord, s)
      +b = SP.spost(ord, s)
      +o = SC.append(Nat, a, Con{s, b})
      +esp = SP.split_eq(ord, s, hm)
      +hs2 = split_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, hm, h)
      +P = SC.pow2(depth)
      +hfr = ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2)
      +hol = ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2)
      +hsf = L.and_left(Nat.is_lt(s, fresh), DST.alllt(b, fresh), TL.alllt_r(a, Con{s, b}, fresh, hol))
      +hlo = K.alllt_mono(o, fresh, P, hfr, hol)
      +hn = LS.notin_rm(a, s, b, SP.nodup_app_l(o, fl, ST.g_nodup(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2)))
      +elk = Equal.trans(Maybe<&2, U32>, TB.lk(table, key), Some{x}, Some{U32.from_nat(s)}, em, Equal.cong(U32, Maybe<&2, U32>, z => Some{z}, x, U32.from_nat(s), ex))
      +hna = RS.nk_part_q(table, ks, a, s, key, depth, ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2), N.lt_le_trans(s, fresh, P, hsf, hfr), TL.alllt_l(a, Con{s, b}, P, hlo), RS.notin_l(s, a, b, hn), elk, RS.am_l(table, ks, a, Con{s, b}, ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2)))
      +ho = RS.occ_mid(V, es, a, s, b, ST.g_occ(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, hs2))
      +efind = Equal.trans(Maybe<&2, S.Ent<V>>, S.find(V, xs, key), S.find(V, ST.ents(V, ks, es, o), key), EN.ent1(V, ST.kat(ks, s), ST.sat(V, es, s)),
        Equal.cong(List<&2, Nat>, Maybe<&2, S.Ent<V>>, z => S.find(V, ST.ents(V, ks, es, z), key), ord, o, esp),
        EN.find_at_slot(V, ks, es, a, s, b, key, hna, heq, ho))
      +ek = RU.equal_boolean(ST.kat(ks, s), key, heq)
      +emod = Equal.trans(S.Model<V>, ST.model(~V, rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, s, fl, 2n)), S.LM{cap, life, S.drop(V, xs, ST.kat(ks, s)), T.bump(2n, mt)}, S.LM{cap, life, S.drop(V, xs, key), T.bump(2n, mt)},
        rm_at_model(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, 2n, hm, h),
        Equal.cong(String, S.Model<V>, z => S.LM{cap, life, S.drop(V, xs, z), T.bump(2n, mt)}, ST.kat(ks, s), key, ek))
      L.subst(Maybe<&2, S.Ent<V>>, z => {S.remove_found(V, cap, life, xs, mt, key, z) == (ST.model(~V, rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, s, fl, 2n)), F.slot_val(~V, ST.sat(V, es, s))) : S.Model<V> & Maybe<&2, V>}, EN.ent1(V, ST.kat(ks, s), ST.sat(V, es, s)), S.find(V, xs, key), Equal.sym(Maybe<&2, S.Ent<V>>, S.find(V, xs, key), EN.ent1(V, ST.kat(ks, s), ST.sat(V, es, s)), efind),
        Equal.trans(S.Model<V> & Maybe<&2, V>, S.remove_found(V, cap, life, xs, mt, key, EN.ent1(V, ST.kat(ks, s), ST.sat(V, es, s))), (S.LM{cap, life, S.drop(V, xs, key), T.bump(2n, mt)}, F.slot_val(~V, ST.sat(V, es, s))), (ST.model(~V, rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, s, fl, 2n)), F.slot_val(~V, ST.sat(V, es, s))),
          rm_found_spec(~V, cap, life, xs, mt, key, ST.kat(ks, s), ST.sat(V, es, s), ho),
          Equal.cong(S.Model<V>, S.Model<V> & Maybe<&2, V>, z => (z, F.slot_val(~V, ST.sat(V, es, s))), S.LM{cap, life, S.drop(V, xs, key), T.bump(2n, mt)}, ST.model(~V, rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, s, fl, 2n)), Equal.sym(S.Model<V>, ST.model(~V, rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, s, fl, 2n)), S.LM{cap, life, S.drop(V, xs, key), T.bump(2n, mt)}, emod))))

def remove_model(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {S.remove(V, ST.model(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key) == mp(~V, rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key))) : S.Model<V> & Maybe<&2, V>}:
  remove_model_m(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key), {==}, h)
