import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/array.bend as AR
import ../lib/u32.bend as U
import ../../spec/common.bend as SC
import ../../spec/lru_fast.bend as S
import ../../spec/lru_numeric.bend as NS
import ../../src/lru/fast.bend as F
import ../../src/lru/time.bend as Time
import ../../src/doubly_linked_list.bend as D
import ../../types/lru_model.bend as T
import ../dlist/state.bend as DST
import ../dlist/split.bend as SP
import ../dlist/tolist.bend as TL
import ../dlist/core.bend as K
import ../dlist/links.bend as LK
import ../dlist/tset.bend as TS
import ../../reference/lru/proofs/recency_unique.bend as RU
import ./num/numeric.bend as NUM
import ./state.bend as ST
import ./table.bend as TB
import ./ents.bend as EN
import ./lists.bend as LS
import ./rs.bend as RS
import ./remove.bend as RM
import ./touch.bend as TO
import ./touch2.bend as T2
import ./readfacts.bend as RF

# get / peek / contains: F.read(key, now, tracked). A missing key reads as a
# miss; a found slot is live (a hit, touched when tracked), or timed and then
# either still live or expired (removed, counted as a removal, read as a miss).

# ---- the ghost results ----

def hcs(-V: Data, sh: ST.Shadow<V>, tracked: Bool) -> ST.Shadow<V>:
  match sh:
    case ST.Sh{+cap, +fresh, +depth, +life, +tc, +table, +tk, +te, +tp, +tn, +ord, +fl}:
      ST.Sh{cap, fresh, depth, life, RF.hc(tc, tracked, False{}), table, tk, te, tp, tn, ord, fl}

def rd_live(-V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, tracked: Bool, v: V) -> ST.Shadow<V> & Maybe<&2, V>:
  match tracked:
    case False{}:
      (ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, Some{v})
    case True{}:
      (ST.Sh{cap, fresh, depth, life, RF.hc(tc, True{}, True{}), table, tk, te, TO.t_tp(depth, tp, SP.spre(ord, s), s, SP.spost(ord, s)), TO.t_tn(depth, tn, SP.spre(ord, s), s, SP.spost(ord, s)), TO.t_ord(SP.spre(ord, s), s, SP.spost(ord, s)), fl}, Some{v})

def rd_exp(-V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, +tracked: Bool, v: V, expired: Bool) -> ST.Shadow<V> & Maybe<&2, V>:
  match expired:
    case False{}:
      rd_live(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, tracked, v)
    case True{}:
      (hcs(V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, s, fl, 2n), tracked), None{})

def rd_slot(-V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, +now: T.Int64, +tracked: Bool, e: F.Slot<V>) -> ST.Shadow<V> & Maybe<&2, V>:
  match e:
    case F.Vacant{}:
      (ST.Sh{cap, fresh, depth, life, RF.hc(tc, tracked, False{}), table, tk, te, tp, tn, ord, fl}, None{})
    case F.Live{v}:
      rd_live(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, tracked, v)
    case F.Timed{v, dl}:
      rd_exp(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, tracked, v, NS.expired(F.stamp_int(dl), now))

def rd_ghost(-V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +now: T.Int64, +tracked: Bool, m: Maybe<&2, U32>) -> ST.Shadow<V> & Maybe<&2, V>:
  match m:
    case None{}:
      (ST.Sh{cap, fresh, depth, life, RF.hc(tc, tracked, False{}), table, tk, te, tp, tn, ord, fl}, None{})
    case Some{+x}:
      rd_slot(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, TB.firstk(AR.slots(String, tk), ord, key), now, tracked, ST.sat(V, AR.slots(F.Slot<V>, te), TB.firstk(AR.slots(String, tk), ord, key)))

# ---- the runtime ----

def miss_real(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, tracked: Bool, +pfc: {AR.perfect(U32, 4n, tc) == True{} : Bool}) -> {(F.F{cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), F.hit_counts(AR.thaw(U32, tc), tracked, False{}), table, AR.thaw(String, tk), AR.thaw(F.Slot<V>, te), F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}}, None{}) == RM.rp(~V, (ST.Sh{cap, fresh, depth, life, RF.hc(tc, tracked, False{}), table, tk, te, tp, tn, ord, fl}, None{})) : F.Fast<V> & Maybe<&2, V>}:
  Equal.cong(Array<U32>, F.Fast<V> & Maybe<&2, V>, z => (F.F{cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), z, table, AR.thaw(String, tk), AR.thaw(F.Slot<V>, te), F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}}, None{}), F.hit_counts(AR.thaw(U32, tc), tracked, False{}), AR.thaw(U32, RF.hc(tc, tracked, False{})), RF.hc_ok(tc, tracked, False{}, pfc))

def rl_real(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, tracked: Bool, v: V, +hm: {DST.lmem(s, ord) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {F.read_live(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), U32.from_nat(s), tracked, v) == RM.rp(~V, rd_live(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, tracked, v)) : F.Fast<V> & Maybe<&2, V>}:
  match tracked:
    case False{}:
      {==}
    case True{}:
      +a = SP.spre(ord, s)
      +b = SP.spost(ord, s)
      +o = SC.append(Nat, a, Con{s, b})
      +esp = SP.split_eq(ord, s, hm)
      +hs2 = RM.split_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, hm, h)
      +P = SC.pow2(depth)
      +hfr = ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)
      +hlo = K.alllt_mono(o, fresh, P, hfr, ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2))
      +to = TO.t_ord(a, s, b)
      +tp2 = TO.t_tp(depth, tp, a, s, b)
      +tn2 = TO.t_tn(depth, tn, a, s, b)
      +tch = TO.touch_chain(depth, tp, tn, a, s, b, DST.hd(fl), ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), ST.g_tp(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), ST.g_tn(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), hlo, SP.nodup_app_l(o, fl, ST.g_nodup(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)), ST.g_lk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2))
      +tch2 = L.subst(List<&2, Nat>, z => {F.touch(F.CH{DST.hd(z), DST.lst(z), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)) == F.CH{DST.hd(to), DST.lst(to), DST.hd(fl), AR.thaw(U32, tp2), AR.thaw(U32, tn2)} : F.Chain}, o, ord, Equal.sym(List<&2, Nat>, ord, o, esp), tch)
      +elen = Equal.trans(Nat, SC.length(Nat, ord), SC.length(Nat, o), SC.length(Nat, to), Equal.cong(List<&2, Nat>, Nat, z => SC.length(Nat, z), ord, o, esp), Equal.sym(Nat, SC.length(Nat, to), SC.length(Nat, o), Equal.trans(Nat, SC.length(Nat, to), SC.length(Nat, TO.mv(a, s, b)), SC.length(Nat, o), Equal.cong(List<&2, Nat>, Nat, z => SC.length(Nat, z), to, TO.mv(a, s, b), TO.t_ord_eq(a, s, b)), TO.len_mv(a, s, b))))
      Equal.trans(F.Fast<V> & Maybe<&2, V>, RS.k3(~V, cap, fresh, depth, life, table, tk, te, U32.from_nat(SC.length(Nat, ord)), F.hit_counts(AR.thaw(U32, tc), True{}, True{}), F.touch(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)), Some{v}), RS.k3(~V, cap, fresh, depth, life, table, tk, te, U32.from_nat(SC.length(Nat, to)), F.hit_counts(AR.thaw(U32, tc), True{}, True{}), F.touch(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)), Some{v}), RS.k3(~V, cap, fresh, depth, life, table, tk, te, U32.from_nat(SC.length(Nat, to)), AR.thaw(U32, RF.hc(tc, True{}, True{})), F.CH{DST.hd(to), DST.lst(to), DST.hd(fl), AR.thaw(U32, tp2), AR.thaw(U32, tn2)}, Some{v}),
        Equal.cong(Nat, F.Fast<V> & Maybe<&2, V>, z => RS.k3(~V, cap, fresh, depth, life, table, tk, te, U32.from_nat(z), F.hit_counts(AR.thaw(U32, tc), True{}, True{}), F.touch(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)), Some{v}), SC.length(Nat, ord), SC.length(Nat, to), elen),
        Equal.trans(F.Fast<V> & Maybe<&2, V>, RS.k3(~V, cap, fresh, depth, life, table, tk, te, U32.from_nat(SC.length(Nat, to)), F.hit_counts(AR.thaw(U32, tc), True{}, True{}), F.touch(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)), Some{v}), RS.k3(~V, cap, fresh, depth, life, table, tk, te, U32.from_nat(SC.length(Nat, to)), AR.thaw(U32, RF.hc(tc, True{}, True{})), F.touch(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)), Some{v}), RS.k3(~V, cap, fresh, depth, life, table, tk, te, U32.from_nat(SC.length(Nat, to)), AR.thaw(U32, RF.hc(tc, True{}, True{})), F.CH{DST.hd(to), DST.lst(to), DST.hd(fl), AR.thaw(U32, tp2), AR.thaw(U32, tn2)}, Some{v}),
          Equal.cong(Array<U32>, F.Fast<V> & Maybe<&2, V>, z => RS.k3(~V, cap, fresh, depth, life, table, tk, te, U32.from_nat(SC.length(Nat, to)), z, F.touch(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)), Some{v}), F.hit_counts(AR.thaw(U32, tc), True{}, True{}), AR.thaw(U32, RF.hc(tc, True{}, True{})), RF.hc_ok(tc, True{}, True{}, ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))),
          Equal.cong(F.Chain, F.Fast<V> & Maybe<&2, V>, z => RS.k3(~V, cap, fresh, depth, life, table, tk, te, U32.from_nat(SC.length(Nat, to)), AR.thaw(U32, RF.hc(tc, True{}, True{})), z, Some{v}), F.touch(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)), F.CH{DST.hd(to), DST.lst(to), DST.hd(fl), AR.thaw(U32, tp2), AR.thaw(U32, tn2)}, tch2)))

def rx_real(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, +tracked: Bool, +hm: {DST.lmem(s, ord) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {F.miss_expired(~V, tracked, F.remove_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), U32.from_nat(s), 2n)) == RM.rp(~V, (hcs(V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, s, fl, 2n), tracked), None{})) : F.Fast<V> & Maybe<&2, V>}:
  +a = SP.spre(ord, s)
  +b = SP.spost(ord, s)
  +ab = SC.append(Nat, a, b)
  +ks = AR.slots(String, tk)
  +table2 = Map.del(&2, Maybe<&2, U32>, table, ST.kat(ks, s))
  +te2 = AR.upd(F.Slot<V>, depth, te, s, F.Vacant{})
  +tp2 = TS.tpup(depth, tp, b, LK.lastl(a, D.nil()))
  +tn2 = AR.upd(U32, depth, TS.tnup(depth, tn, a, DST.hd_or(b, D.nil())), s, DST.hd(fl))
  +tc2 = RS.sbd(tc, 2n)
  +n2 = U32.from_nat(SC.length(Nat, ab))
  Equal.trans(F.Fast<V> & Maybe<&2, V>, F.miss_expired(~V, tracked, F.remove_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), U32.from_nat(s), 2n)), F.miss_expired(~V, tracked, (ST.real(~V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, s, fl, 2n)), F.slot_val(~V, ST.sat(V, AR.slots(F.Slot<V>, te), s)))), RM.rp(~V, (hcs(V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, s, fl, 2n), tracked), None{})),
    Equal.cong(F.Fast<V> & Maybe<&2, V>, F.Fast<V> & Maybe<&2, V>, r => F.miss_expired(~V, tracked, r), F.remove_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), U32.from_nat(s), 2n), (ST.real(~V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, s, fl, 2n)), F.slot_val(~V, ST.sat(V, AR.slots(F.Slot<V>, te), s))), RM.rm_at_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, 2n, hm, h)),
    Equal.cong(Array<U32>, F.Fast<V> & Maybe<&2, V>, z => RS.k3(~V, cap, fresh, depth, life, table2, tk, te2, n2, z, F.CH{DST.hd(ab), DST.lst(ab), DST.hd(Con{s, fl}), AR.thaw(U32, tp2), AR.thaw(U32, tn2)}, None{}), F.hit_counts(AR.thaw(U32, tc2), tracked, False{}), AR.thaw(U32, RF.hc(tc2, tracked, False{})), RF.hc_ok(tc2, tracked, False{}, RS.sbd_pf(tc, 2n, ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)))))

def re_real(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, +tracked: Bool, v: V, expired: Bool, +hm: {DST.lmem(s, ord) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {F.read_expiry(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), U32.from_nat(s), tracked, v, expired) == RM.rp(~V, rd_exp(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, tracked, v, expired)) : F.Fast<V> & Maybe<&2, V>}:
  match expired:
    case False{}:
      rl_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, tracked, v, hm, h)
    case True{}:
      rx_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, tracked, hm, h)

def exp_eq(dl: F.Stamp, +now: T.Int64) -> {Time.expired(F.stamp_int(dl), F.stamp_int(F.int_stamp(now))) == NS.expired(F.stamp_int(dl), now) : Bool}:
  Equal.trans(Bool, Time.expired(F.stamp_int(dl), F.stamp_int(F.int_stamp(now))), Time.expired(F.stamp_int(dl), now), NS.expired(F.stamp_int(dl), now),
    Equal.cong(T.Int64, Bool, z => Time.expired(F.stamp_int(dl), z), F.stamp_int(F.int_stamp(now)), now, RF.stamp_iso(now)),
    NUM.expiration_refines(F.stamp_int(dl), now))

def rs_real_slot(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, +now: T.Int64, +tracked: Bool, e: F.Slot<V>, +hm: {DST.lmem(s, ord) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {F.read_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), U32.from_nat(s), F.int_stamp(now), tracked, e) == RM.rp(~V, rd_slot(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, now, tracked, e)) : F.Fast<V> & Maybe<&2, V>}:
  match e:
    case F.Vacant{}:
      miss_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, tracked, ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
    case F.Live{v}:
      rl_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, tracked, v, hm, h)
    case F.Timed{v, +dl}:
      L.subst(Bool, z => {F.read_expiry(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), U32.from_nat(s), tracked, v, z) == RM.rp(~V, rd_exp(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, tracked, v, NS.expired(F.stamp_int(dl), now))) : F.Fast<V> & Maybe<&2, V>}, NS.expired(F.stamp_int(dl), now), Time.expired(F.stamp_int(dl), F.stamp_int(F.int_stamp(now))), Equal.sym(Bool, Time.expired(F.stamp_int(dl), F.stamp_int(F.int_stamp(now))), NS.expired(F.stamp_int(dl), now), exp_eq(dl, now)),
        re_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, tracked, v, NS.expired(F.stamp_int(dl), now), hm, h))

def rd_real_m(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +now: T.Int64, +tracked: Bool, m: Maybe<&2, U32>, +em: {TB.lk(table, key) == m : Maybe<&2, U32>}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {F.read_pick(~V, cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(String, tk), AR.thaw(F.Slot<V>, te), F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, F.int_stamp(now), tracked, m) == RM.rp(~V, rd_ghost(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked, m)) : F.Fast<V> & Maybe<&2, V>}:
  match m:
    case None{}:
      miss_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, tracked, ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
    case Some{+x}:
      +ks = AR.slots(String, tk)
      +es = AR.slots(F.Slot<V>, te)
      +s = TB.firstk(ks, ord, key)
      +ex = TB.locate(table, ks, ord, key, x, em, ST.g_crit(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_pop(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_incl(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
      +hk = RM.found_k(table, ks, ord, key, x, em, ST.g_crit(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_pop(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_incl(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
      +hm = L.and_left(DST.lmem(s, ord), String.eq(ST.kat(ks, s), key), hk)
      +hs2 = RM.split_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, hm, h)
      +P = SC.pow2(depth)
      +hsf = L.and_left(Nat.is_lt(s, fresh), DST.alllt(SP.spost(ord, s), fresh), TL.alllt_r(SP.spre(ord, s), Con{s, SP.spost(ord, s)}, fresh, ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)))
      +hs = N.lt_le_trans(s, fresh, P, hsf, ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2))
      +sv = L.some_value(F.Slot<V>, SC.nth(F.Slot<V>, es, s), F.Vacant{})
      +r1 = Equal.trans(F.Fast<V> & Maybe<&2, V>, F.read_got(~V, cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(String, tk), F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s), F.int_stamp(now), tracked, Array.get(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s))), F.read_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), U32.from_nat(s), F.int_stamp(now), tracked, sv), RM.rp(~V, rd_slot(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, now, tracked, ST.sat(V, es, s))),
        Equal.cong(Array<F.Slot<V>> & F.Slot<V>, F.Fast<V> & Maybe<&2, V>, r => F.read_got(~V, cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(String, tk), F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s), F.int_stamp(now), tracked, r), Array.get(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s)), (AR.thaw(F.Slot<V>, te), sv), TL.get_at(F.Slot<V>, depth, te, s, F.Vacant{}, ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), hs)),
        Equal.trans(F.Fast<V> & Maybe<&2, V>, F.read_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), U32.from_nat(s), F.int_stamp(now), tracked, sv), F.read_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), U32.from_nat(s), F.int_stamp(now), tracked, ST.sat(V, es, s)), RM.rp(~V, rd_slot(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, now, tracked, ST.sat(V, es, s))),
          Equal.cong(F.Slot<V>, F.Fast<V> & Maybe<&2, V>, e => F.read_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), U32.from_nat(s), F.int_stamp(now), tracked, e), sv, ST.sat(V, es, s), RS.sat_sv(V, SC.nth(F.Slot<V>, es, s))),
          rs_real_slot(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, now, tracked, ST.sat(V, es, s), hm, h)))
      L.subst(U32, z => {F.read_got(~V, cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(String, tk), F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, z, F.int_stamp(now), tracked, Array.get(F.Slot<V>, AR.thaw(F.Slot<V>, te), z)) == RM.rp(~V, rd_slot(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, now, tracked, ST.sat(V, es, s))) : F.Fast<V> & Maybe<&2, V>}, U32.from_nat(s), x, Equal.sym(U32, x, U32.from_nat(s), ex), r1)

def read_real(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +now: T.Int64, +tracked: Bool, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {F.read(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, F.int_stamp(now), tracked) == RM.rp(~V, rd_ghost(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked, TB.lk(table, key))) : F.Fast<V> & Maybe<&2, V>}:
  L.subst(Map<&2, Maybe<&2, U32>> & Maybe<&2, U32>, z => {F.read_found(~V, cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), AR.thaw(String, tk), AR.thaw(F.Slot<V>, te), F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, F.int_stamp(now), tracked, z) == RM.rp(~V, rd_ghost(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked, TB.lk(table, key))) : F.Fast<V> & Maybe<&2, V>}, TB.mpair(table, TB.lk(table, key)), Map.get(Maybe<&2, U32>, None{}, table, key), Equal.sym(Map<&2, Maybe<&2, U32>> & Maybe<&2, U32>, Map.get(Maybe<&2, U32>, None{}, table, key), TB.mpair(table, TB.lk(table, key)), TB.get_pair(table, key)),
    rd_real_m(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked, TB.lk(table, key), {==}, h))

# ---- the invariant ----

# replacing the counter tree by another perfect one keeps the invariant
def inv_tc(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +tc2: AR.Tree<U32>, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +pf2: {AR.perfect(U32, 4n, tc2) == True{} : Bool}) -> {ST.inv(~V, cap, fresh, depth, life, tc2, table, tk, te, tp, tn, ord, fl) == True{} : Bool}:
  ST.inv_mk(~V, cap, fresh, depth, life, tc2, table, tk, te, tp, tn, ord, fl, ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_tk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_tp(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_tn(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), pf2, ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_fllt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_nodup(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_count(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_lk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_fk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_occ(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_incl(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_crit(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_pop(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_cap(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_n(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))

def rl_inv(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, tracked: Bool, v: V, +hm: {DST.lmem(s, ord) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {RM.gp(~V, rd_live(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, tracked, v)) == True{} : Bool}:
  match tracked:
    case False{}:
      h
    case True{}:
      +a = SP.spre(ord, s)
      +b = SP.spost(ord, s)
      +hs2 = RM.split_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, hm, h)
      T2.touch_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, a, s, b, fl, RF.hc(tc, True{}, True{}), te, hs2, RF.hc_pf(tc, True{}, True{}, ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)), ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), TO.occ_mv(V, AR.slots(F.Slot<V>, te), a, s, b, ST.g_occ(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)))

def re_inv(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, +tracked: Bool, v: V, expired: Bool, +hm: {DST.lmem(s, ord) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {RM.gp(~V, rd_exp(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, tracked, v, expired)) == True{} : Bool}:
  match expired:
    case False{}:
      rl_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, tracked, v, hm, h)
    case True{}:
      inv_tc(~V, cap, fresh, depth, life, RS.sbd(tc, 2n), Map.del(&2, Maybe<&2, U32>, table, ST.kat(AR.slots(String, tk), s)), tk, AR.upd(F.Slot<V>, depth, te, s, F.Vacant{}), TS.tpup(depth, tp, SP.spost(ord, s), LK.lastl(SP.spre(ord, s), D.nil())), AR.upd(U32, depth, TS.tnup(depth, tn, SP.spre(ord, s), DST.hd_or(SP.spost(ord, s), D.nil())), s, DST.hd(fl)), SC.append(Nat, SP.spre(ord, s), SP.spost(ord, s)), Con{s, fl}, RF.hc(RS.sbd(tc, 2n), tracked, False{}), RM.rm_at_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, 2n, hm, h), RF.hc_pf(RS.sbd(tc, 2n), tracked, False{}, RS.sbd_pf(tc, 2n, ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))))

def rsl_inv(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, +now: T.Int64, +tracked: Bool, e: F.Slot<V>, +hm: {DST.lmem(s, ord) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {RM.gp(~V, rd_slot(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, now, tracked, e)) == True{} : Bool}:
  match e:
    case F.Vacant{}:
      inv_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, RF.hc(tc, tracked, False{}), h, RF.hc_pf(tc, tracked, False{}, ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)))
    case F.Live{v}:
      rl_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, tracked, v, hm, h)
    case F.Timed{v, +dl}:
      re_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, tracked, v, NS.expired(F.stamp_int(dl), now), hm, h)

def rd_inv_m(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +now: T.Int64, +tracked: Bool, m: Maybe<&2, U32>, +em: {TB.lk(table, key) == m : Maybe<&2, U32>}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {RM.gp(~V, rd_ghost(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked, m)) == True{} : Bool}:
  match m:
    case None{}:
      inv_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, RF.hc(tc, tracked, False{}), h, RF.hc_pf(tc, tracked, False{}, ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)))
    case Some{+x}:
      +ks = AR.slots(String, tk)
      +s = TB.firstk(ks, ord, key)
      +hk = RM.found_k(table, ks, ord, key, x, em, ST.g_crit(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_pop(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_incl(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
      rsl_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, now, tracked, ST.sat(V, AR.slots(F.Slot<V>, te), s), L.and_left(DST.lmem(s, ord), String.eq(ST.kat(ks, s), key), hk), h)

def read_inv(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +now: T.Int64, +tracked: Bool, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {RM.gp(~V, rd_ghost(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked, TB.lk(table, key))) == True{} : Bool}:
  rd_inv_m(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked, TB.lk(table, key), {==}, h)

# ---- the model ----

def rl_model(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, +key: String, tracked: Bool, v: V, +x: S.Ent<V>, +hx: {ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), Con{s, Nil{}}) == Con{x, Nil{}} : List<&2, S.Ent<V>>}, +hvx: {S.val_of(V, x) == v : V}, +elk: {TB.lk(table, key) == Some{U32.from_nat(s)} : Maybe<&2, U32>}, +heq: {String.eq(ST.kat(AR.slots(String, tk), s), key) == True{} : Bool}, +hm: {DST.lmem(s, ord) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {S.read_live(V, cap, life, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), ST.mets(AR.slots(U32, tc)), key, x, tracked) == RM.mp(~V, rd_live(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, tracked, v)) : S.Model<V> & Maybe<&2, V>}:
  match tracked:
    case False{}:
      Equal.cong(V, S.Model<V> & Maybe<&2, V>, z => (S.LM{cap, life, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), ST.mets(AR.slots(U32, tc))}, Some{z}), S.val_of(V, x), v, hvx)
    case True{}:
      +ks = AR.slots(String, tk)
      +es = AR.slots(F.Slot<V>, te)
      +a = SP.spre(ord, s)
      +b = SP.spost(ord, s)
      +o = SC.append(Nat, a, Con{s, b})
      +esp = SP.split_eq(ord, s, hm)
      +hs2 = RM.split_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, hm, h)
      +P = SC.pow2(depth)
      +hfr = ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)
      +hol = ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)
      +hsf = L.and_left(Nat.is_lt(s, fresh), DST.alllt(b, fresh), TL.alllt_r(a, Con{s, b}, fresh, hol))
      +hs = N.lt_le_trans(s, fresh, P, hsf, hfr)
      +hlo = K.alllt_mono(o, fresh, P, hfr, hol)
      +hnd = SP.nodup_app_l(o, fl, ST.g_nodup(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2))
      +hn = LS.notin_rm(a, s, b, hnd)
      +hmp = ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)
      +hna = RS.nk_part_q(table, ks, a, s, key, depth, ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), hs, TL.alllt_l(a, Con{s, b}, P, hlo), RS.notin_l(s, a, b, hn), elk, RS.am_l(table, ks, a, Con{s, b}, hmp))
      +hnb = RS.nk_part_q(table, ks, b, s, key, depth, ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), hs, L.and_right(Nat.is_lt(s, P), DST.alllt(b, P), TL.alllt_r(a, Con{s, b}, P, hlo)), RS.notin_r(s, a, b, hn), elk, L.and_right(ST.mapped(table, ST.kat(ks, s), s), ST.all_mapped(table, ks, b), RS.am_r(table, ks, a, Con{s, b}, hmp)))
      +ho = RS.occ_mid(V, es, a, s, b, ST.g_occ(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2))
      +to = TO.t_ord(a, s, b)
      +xs = ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord)
      +eents = Equal.trans(List<&2, S.Ent<V>>, ST.ents(V, ks, es, to), SC.append(S.Ent<V>, S.drop(V, ST.ents(V, ks, es, o), key), ST.ents(V, ks, es, Con{s, Nil{}})), S.snoc(V, S.drop(V, xs, key), x),
        T2.touch_ents(V, ks, es, a, s, b, key, hna, hnb, heq, ho),
        Equal.trans(List<&2, S.Ent<V>>, SC.append(S.Ent<V>, S.drop(V, ST.ents(V, ks, es, o), key), ST.ents(V, ks, es, Con{s, Nil{}})), SC.append(S.Ent<V>, S.drop(V, xs, key), Con{x, Nil{}}), S.snoc(V, S.drop(V, xs, key), x),
          Equal.trans(List<&2, S.Ent<V>>, SC.append(S.Ent<V>, S.drop(V, ST.ents(V, ks, es, o), key), ST.ents(V, ks, es, Con{s, Nil{}})), SC.append(S.Ent<V>, S.drop(V, xs, key), ST.ents(V, ks, es, Con{s, Nil{}})), SC.append(S.Ent<V>, S.drop(V, xs, key), Con{x, Nil{}}),
            Equal.cong(List<&2, Nat>, List<&2, S.Ent<V>>, z => SC.append(S.Ent<V>, S.drop(V, ST.ents(V, ks, es, z), key), ST.ents(V, ks, es, Con{s, Nil{}})), o, ord, Equal.sym(List<&2, Nat>, ord, o, esp)),
            Equal.cong(List<&2, S.Ent<V>>, List<&2, S.Ent<V>>, z => SC.append(S.Ent<V>, S.drop(V, xs, key), z), ST.ents(V, ks, es, Con{s, Nil{}}), Con{x, Nil{}}, hx)),
          Equal.sym(List<&2, S.Ent<V>>, S.snoc(V, S.drop(V, xs, key), x), SC.append(S.Ent<V>, S.drop(V, xs, key), Con{x, Nil{}}), EN.snoc_app(V, S.drop(V, xs, key), x))))
      Equal.sym(S.Model<V> & Maybe<&2, V>, (S.LM{cap, life, ST.ents(V, ks, es, to), ST.mets(AR.slots(U32, RF.hc(tc, True{}, True{})))}, Some{v}), (S.LM{cap, life, S.snoc(V, S.drop(V, xs, key), x), T.bump(3n, ST.mets(AR.slots(U32, tc)))}, Some{S.val_of(V, x)}),
        Equal.trans(S.Model<V> & Maybe<&2, V>, (S.LM{cap, life, ST.ents(V, ks, es, to), ST.mets(AR.slots(U32, RF.hc(tc, True{}, True{})))}, Some{v}), (S.LM{cap, life, S.snoc(V, S.drop(V, xs, key), x), ST.mets(AR.slots(U32, RF.hc(tc, True{}, True{})))}, Some{v}), (S.LM{cap, life, S.snoc(V, S.drop(V, xs, key), x), T.bump(3n, ST.mets(AR.slots(U32, tc)))}, Some{S.val_of(V, x)}),
          Equal.cong(List<&2, S.Ent<V>>, S.Model<V> & Maybe<&2, V>, z => (S.LM{cap, life, z, ST.mets(AR.slots(U32, RF.hc(tc, True{}, True{})))}, Some{v}), ST.ents(V, ks, es, to), S.snoc(V, S.drop(V, xs, key), x), eents),
          Equal.trans(S.Model<V> & Maybe<&2, V>, (S.LM{cap, life, S.snoc(V, S.drop(V, xs, key), x), ST.mets(AR.slots(U32, RF.hc(tc, True{}, True{})))}, Some{v}), (S.LM{cap, life, S.snoc(V, S.drop(V, xs, key), x), T.bump(3n, ST.mets(AR.slots(U32, tc)))}, Some{v}), (S.LM{cap, life, S.snoc(V, S.drop(V, xs, key), x), T.bump(3n, ST.mets(AR.slots(U32, tc)))}, Some{S.val_of(V, x)}),
            Equal.cong(T.Metrics, S.Model<V> & Maybe<&2, V>, z => (S.LM{cap, life, S.snoc(V, S.drop(V, xs, key), x), z}, Some{v}), ST.mets(AR.slots(U32, RF.hc(tc, True{}, True{}))), T.bump(3n, ST.mets(AR.slots(U32, tc))), RF.hc_mets_hit(tc, True{}, ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))),
            Equal.cong(V, S.Model<V> & Maybe<&2, V>, z => (S.LM{cap, life, S.snoc(V, S.drop(V, xs, key), x), T.bump(3n, ST.mets(AR.slots(U32, tc)))}, Some{z}), v, S.val_of(V, x), Equal.sym(V, S.val_of(V, x), v, hvx)))))

def rx_model(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, +key: String, +tracked: Bool, +elk: {TB.lk(table, key) == Some{U32.from_nat(s)} : Maybe<&2, U32>}, +heq: {String.eq(ST.kat(AR.slots(String, tk), s), key) == True{} : Bool}, +hm: {DST.lmem(s, ord) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {(S.LM{cap, life, S.drop(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), key), S.count_if(tracked, 4n, T.bump(2n, ST.mets(AR.slots(U32, tc))))}, None{}) == RM.mp(~V, (hcs(V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, s, fl, 2n), tracked), None{})) : S.Model<V> & Maybe<&2, V>}:
      +ks = AR.slots(String, tk)
      +es = AR.slots(F.Slot<V>, te)
      +a = SP.spre(ord, s)
      +b = SP.spost(ord, s)
      +o = SC.append(Nat, a, Con{s, b})
      +esp = SP.split_eq(ord, s, hm)
      +hs2 = RM.split_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, hm, h)
      +P = SC.pow2(depth)
      +hfr = ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)
      +hol = ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)
      +hsf = L.and_left(Nat.is_lt(s, fresh), DST.alllt(b, fresh), TL.alllt_r(a, Con{s, b}, fresh, hol))
      +hs = N.lt_le_trans(s, fresh, P, hsf, hfr)
      +hlo = K.alllt_mono(o, fresh, P, hfr, hol)
      +hnd = SP.nodup_app_l(o, fl, ST.g_nodup(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2))
      +hn = LS.notin_rm(a, s, b, hnd)
      +hmp = ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)
      +hna = RS.nk_part_q(table, ks, a, s, key, depth, ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), hs, TL.alllt_l(a, Con{s, b}, P, hlo), RS.notin_l(s, a, b, hn), elk, RS.am_l(table, ks, a, Con{s, b}, hmp))
      +hnb = RS.nk_part_q(table, ks, b, s, key, depth, ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), hs, L.and_right(Nat.is_lt(s, P), DST.alllt(b, P), TL.alllt_r(a, Con{s, b}, P, hlo)), RS.notin_r(s, a, b, hn), elk, L.and_right(ST.mapped(table, ST.kat(ks, s), s), ST.all_mapped(table, ks, b), RS.am_r(table, ks, a, Con{s, b}, hmp)))
      +ho = RS.occ_mid(V, es, a, s, b, ST.g_occ(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2))
      +xs = ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord)
      +ab = SC.append(Nat, a, b)
      +E2 = ST.ents(V, ks, AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, F.Vacant{})), ab)
      +ek = RU.equal_boolean(ST.kat(ks, s), key, heq)
      +eents = Equal.trans(List<&2, S.Ent<V>>, E2, S.drop(V, ST.ents(V, ks, es, o), ST.kat(ks, s)), S.drop(V, xs, key),
        RS.rs_ents(V, depth, table, tk, te, a, s, b, ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), hs, hlo, hnd, ST.g_occ(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), hmp),
        Equal.trans(List<&2, S.Ent<V>>, S.drop(V, ST.ents(V, ks, es, o), ST.kat(ks, s)), S.drop(V, xs, ST.kat(ks, s)), S.drop(V, xs, key),
          Equal.cong(List<&2, Nat>, List<&2, S.Ent<V>>, z => S.drop(V, ST.ents(V, ks, es, z), ST.kat(ks, s)), o, ord, Equal.sym(List<&2, Nat>, ord, o, esp)),
          Equal.cong(String, List<&2, S.Ent<V>>, z => S.drop(V, xs, z), ST.kat(ks, s), key, ek)))
      +tc2 = RS.sbd(tc, 2n)
      +emets = Equal.trans(T.Metrics, ST.mets(AR.slots(U32, RF.hc(tc2, tracked, False{}))), S.count_if(tracked, 4n, ST.mets(AR.slots(U32, tc2))), S.count_if(tracked, 4n, T.bump(2n, ST.mets(AR.slots(U32, tc)))),
        RF.hc_mets_miss(tc2, tracked, RS.sbd_pf(tc, 2n, ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))),
        Equal.cong(T.Metrics, T.Metrics, z => S.count_if(tracked, 4n, z), ST.mets(AR.slots(U32, tc2)), T.bump(2n, ST.mets(AR.slots(U32, tc))), RS.mets_drop(tc, 2n, ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))))
      Equal.sym(S.Model<V> & Maybe<&2, V>, (S.LM{cap, life, E2, ST.mets(AR.slots(U32, RF.hc(tc2, tracked, False{})))}, None{}), (S.LM{cap, life, S.drop(V, xs, key), S.count_if(tracked, 4n, T.bump(2n, ST.mets(AR.slots(U32, tc))))}, None{}),
        Equal.trans(S.Model<V> & Maybe<&2, V>, (S.LM{cap, life, E2, ST.mets(AR.slots(U32, RF.hc(tc2, tracked, False{})))}, None{}), (S.LM{cap, life, S.drop(V, xs, key), ST.mets(AR.slots(U32, RF.hc(tc2, tracked, False{})))}, None{}), (S.LM{cap, life, S.drop(V, xs, key), S.count_if(tracked, 4n, T.bump(2n, ST.mets(AR.slots(U32, tc))))}, None{}),
          Equal.cong(List<&2, S.Ent<V>>, S.Model<V> & Maybe<&2, V>, z => (S.LM{cap, life, z, ST.mets(AR.slots(U32, RF.hc(tc2, tracked, False{})))}, None{}), E2, S.drop(V, xs, key), eents),
          Equal.cong(T.Metrics, S.Model<V> & Maybe<&2, V>, z => (S.LM{cap, life, S.drop(V, xs, key), z}, None{}), ST.mets(AR.slots(U32, RF.hc(tc2, tracked, False{}))), S.count_if(tracked, 4n, T.bump(2n, ST.mets(AR.slots(U32, tc)))), emets)))

def re_model(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, +key: String, +tracked: Bool, v: V, +x: S.Ent<V>, +hx: {ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), Con{s, Nil{}}) == Con{x, Nil{}} : List<&2, S.Ent<V>>}, +hvx: {S.val_of(V, x) == v : V}, expired: Bool, +elk: {TB.lk(table, key) == Some{U32.from_nat(s)} : Maybe<&2, U32>}, +heq: {String.eq(ST.kat(AR.slots(String, tk), s), key) == True{} : Bool}, +hm: {DST.lmem(s, ord) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {S.read_expiry(V, cap, life, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), ST.mets(AR.slots(U32, tc)), key, x, tracked, expired) == RM.mp(~V, rd_exp(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, tracked, v, expired)) : S.Model<V> & Maybe<&2, V>}:
  match expired:
    case False{}:
      rl_model(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, key, tracked, v, x, hx, hvx, elk, heq, hm, h)
    case True{}:
      rx_model(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, key, tracked, elk, heq, hm, h)

def rsl_model(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, +key: String, +now: T.Int64, +tracked: Bool, e: F.Slot<V>, +ee: {ST.sat(V, AR.slots(F.Slot<V>, te), s) == e : F.Slot<V>}, +elk: {TB.lk(table, key) == Some{U32.from_nat(s)} : Maybe<&2, U32>}, +heq: {String.eq(ST.kat(AR.slots(String, tk), s), key) == True{} : Bool}, +hm: {DST.lmem(s, ord) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {S.read_found(V, cap, life, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), ST.mets(AR.slots(U32, tc)), key, now, tracked, EN.ent1(V, ST.kat(AR.slots(String, tk), s), e)) == RM.mp(~V, rd_slot(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, now, tracked, e)) : S.Model<V> & Maybe<&2, V>}:
  match e:
    case F.Vacant{}:
      +a = SP.spre(ord, s)
      +b = SP.spost(ord, s)
      +hs2 = RM.split_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, hm, h)
      +ho = RS.occ_mid(V, AR.slots(F.Slot<V>, te), a, s, b, ST.g_occ(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2))
      Empty.absurd({(S.LM{cap, life, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), S.count_if(tracked, 4n, ST.mets(AR.slots(U32, tc)))}, None{}) == RM.mp(~V, (ST.Sh{cap, fresh, depth, life, RF.hc(tc, tracked, False{}), table, tk, te, tp, tn, ord, fl}, None{})) : S.Model<V> & Maybe<&2, V>}, L.false_true(L.subst(F.Slot<V>, z => {ST.is_occ(V, z) == True{} : Bool}, ST.sat(V, AR.slots(F.Slot<V>, te), s), F.Vacant{}, ee, ho)))
    case F.Live{+v}:
      +k = ST.kat(AR.slots(String, tk), s)
      L.subst(Bool, z => {S.read_expiry(V, cap, life, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), ST.mets(AR.slots(U32, tc)), key, S.En{k, v, S.zero_time()}, tracked, z) == RM.mp(~V, rd_live(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, tracked, v)) : S.Model<V> & Maybe<&2, V>}, False{}, NS.expired(S.zero_time(), now), Equal.sym(Bool, NS.expired(S.zero_time(), now), False{}, RF.zero_live(now)),
        rl_model(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, key, tracked, v, S.En{k, v, S.zero_time()}, Equal.cong(F.Slot<V>, List<&2, S.Ent<V>>, z => ST.ent_at(V, k, z, Nil{}), ST.sat(V, AR.slots(F.Slot<V>, te), s), F.Live{v}, ee), {==}, elk, heq, hm, h))
    case F.Timed{+v, +dl}:
      +k = ST.kat(AR.slots(String, tk), s)
      re_model(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, key, tracked, v, S.En{k, v, F.stamp_int(dl)}, Equal.cong(F.Slot<V>, List<&2, S.Ent<V>>, z => ST.ent_at(V, k, z, Nil{}), ST.sat(V, AR.slots(F.Slot<V>, te), s), F.Timed{v, dl}, ee), {==}, NS.expired(F.stamp_int(dl), now), elk, heq, hm, h)

def rd_model_m(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +now: T.Int64, +tracked: Bool, m: Maybe<&2, U32>, +em: {TB.lk(table, key) == m : Maybe<&2, U32>}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {S.read_found(V, cap, life, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), ST.mets(AR.slots(U32, tc)), key, now, tracked, S.find(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), key)) == RM.mp(~V, rd_ghost(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked, m)) : S.Model<V> & Maybe<&2, V>}:
  match m:
    case None{}:
      +ks = AR.slots(String, tk)
      +es = AR.slots(F.Slot<V>, te)
      +xs = ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord)
      +hnk = TB.nk_all(table, ks, ord, key, None{}, em, ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), TB.nomap_none(ord))
      L.subst(Maybe<&2, S.Ent<V>>, z => {S.read_found(V, cap, life, xs, ST.mets(AR.slots(U32, tc)), key, now, tracked, z) == RM.mp(~V, (ST.Sh{cap, fresh, depth, life, RF.hc(tc, tracked, False{}), table, tk, te, tp, tn, ord, fl}, None{})) : S.Model<V> & Maybe<&2, V>}, None{}, S.find(V, xs, key), Equal.sym(Maybe<&2, S.Ent<V>>, S.find(V, xs, key), None{}, EN.find_none(V, ks, es, ord, key, hnk)),
        Equal.cong(T.Metrics, S.Model<V> & Maybe<&2, V>, z => (S.LM{cap, life, xs, z}, None{}), S.count_if(tracked, 4n, ST.mets(AR.slots(U32, tc))), ST.mets(AR.slots(U32, RF.hc(tc, tracked, False{}))), Equal.sym(T.Metrics, ST.mets(AR.slots(U32, RF.hc(tc, tracked, False{}))), S.count_if(tracked, 4n, ST.mets(AR.slots(U32, tc))), RF.hc_mets_miss(tc, tracked, ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)))))
    case Some{+x}:
      +ks = AR.slots(String, tk)
      +es = AR.slots(F.Slot<V>, te)
      +xs = ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord)
      +s = TB.firstk(ks, ord, key)
      +ex = TB.locate(table, ks, ord, key, x, em, ST.g_crit(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_pop(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_incl(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
      +hk = RM.found_k(table, ks, ord, key, x, em, ST.g_crit(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_pop(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_incl(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
      +hm = L.and_left(DST.lmem(s, ord), String.eq(ST.kat(ks, s), key), hk)
      +heq = L.and_right(DST.lmem(s, ord), String.eq(ST.kat(ks, s), key), hk)
      +elk = Equal.trans(Maybe<&2, U32>, TB.lk(table, key), Some{x}, Some{U32.from_nat(s)}, em, Equal.cong(U32, Maybe<&2, U32>, z => Some{z}, x, U32.from_nat(s), ex))
      +a = SP.spre(ord, s)
      +b = SP.spost(ord, s)
      +o = SC.append(Nat, a, Con{s, b})
      +esp = SP.split_eq(ord, s, hm)
      +hs2 = RM.split_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, hm, h)
      +P = SC.pow2(depth)
      +hfr = ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)
      +hol = ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)
      +hsf = L.and_left(Nat.is_lt(s, fresh), DST.alllt(b, fresh), TL.alllt_r(a, Con{s, b}, fresh, hol))
      +hlo = K.alllt_mono(o, fresh, P, hfr, hol)
      +hn = LS.notin_rm(a, s, b, SP.nodup_app_l(o, fl, ST.g_nodup(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)))
      +hna = RS.nk_part_q(table, ks, a, s, key, depth, ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), N.lt_le_trans(s, fresh, P, hsf, hfr), TL.alllt_l(a, Con{s, b}, P, hlo), RS.notin_l(s, a, b, hn), elk, RS.am_l(table, ks, a, Con{s, b}, ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)))
      +efind = Equal.trans(Maybe<&2, S.Ent<V>>, S.find(V, xs, key), S.find(V, ST.ents(V, ks, es, o), key), EN.ent1(V, ST.kat(ks, s), ST.sat(V, es, s)),
        Equal.cong(List<&2, Nat>, Maybe<&2, S.Ent<V>>, z => S.find(V, ST.ents(V, ks, es, z), key), ord, o, esp),
        EN.find_at_slot(V, ks, es, a, s, b, key, hna, heq, RS.occ_mid(V, es, a, s, b, ST.g_occ(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2))))
      L.subst(Maybe<&2, S.Ent<V>>, z => {S.read_found(V, cap, life, xs, ST.mets(AR.slots(U32, tc)), key, now, tracked, z) == RM.mp(~V, rd_slot(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, now, tracked, ST.sat(V, es, s))) : S.Model<V> & Maybe<&2, V>}, EN.ent1(V, ST.kat(ks, s), ST.sat(V, es, s)), S.find(V, xs, key), Equal.sym(Maybe<&2, S.Ent<V>>, S.find(V, xs, key), EN.ent1(V, ST.kat(ks, s), ST.sat(V, es, s)), efind),
        rsl_model(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, key, now, tracked, ST.sat(V, es, s), {==}, elk, heq, hm, h))

def read_model(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +now: T.Int64, +tracked: Bool, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {S.read(V, ST.model(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, now, tracked) == RM.mp(~V, rd_ghost(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked, TB.lk(table, key))) : S.Model<V> & Maybe<&2, V>}:
  rd_model_m(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked, TB.lk(table, key), {==}, h)
