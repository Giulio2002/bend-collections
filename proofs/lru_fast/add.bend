import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../lib/u32.bend as U
import ../../spec/common.bend as SC
import ../../spec/lru_fast.bend as S
import ../../spec/lru_numeric.bend as NS
import ../../src/lru/fast.bend as F
import ../../src/lru/time.bend as Time
import ../../types/lru_model.bend as T
import ../../types/lru_fast.bend as E
import support/links_state.bend as DST
import support/links_split.bend as SP
import support/links_tolist.bend as TL
import support/links_core.bend as K
import support/links_insert.bend as IN
import ../../reference/lru/proofs/recency_unique.bend as RU
import ./state.bend as ST
import ./table.bend as TB
import ./ents.bend as EN
import ./lists.bend as LS
import ./counts.bend as CT
import ./rs.bend as RS
import ./remove.bend as RM
import ./touch.bend as TO
import ./touch2.bend as T2
import ./addfacts.bend as AF

# add(key, v, now) of a PRESENT key: the slot keeps its key, takes the new
# entry, becomes the newest, and one insert is counted.

def rep_sh(-V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, +e: F.Slot<V>) -> ST.Shadow<V>:
  ST.Sh{cap, fresh, depth, life, CT.bt(tc, 0n), table, tk, AR.upd(F.Slot<V>, depth, te, s, e), TO.t_tp(depth, tp, SP.spre(ord, s), s, SP.spost(ord, s)), TO.t_tn(depth, tn, SP.spre(ord, s), s, SP.spost(ord, s)), TO.t_ord(SP.spre(ord, s), s, SP.spost(ord, s)), fl}

def k4(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +n: U32, c: Array<U32>, es: Array<F.Slot<V>>, ch: F.Chain) -> F.Fast<V>:
  F.F{cap, n, U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), c, table, AR.thaw(String, tk), es, ch}

def rep_real(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, e: F.Slot<V>, +hm: {DST.lmem(s, ord) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {F.replace(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), U32.from_nat(s), e) == ST.real(~V, rep_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, e)) : F.Fast<V>}:
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
  +to = TO.t_ord(a, s, b)
  +tp2 = TO.t_tp(depth, tp, a, s, b)
  +tn2 = TO.t_tn(depth, tn, a, s, b)
  +tch = TO.touch_chain(depth, tp, tn, a, s, b, DST.hd(fl), ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), ST.g_tp(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), ST.g_tn(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), hlo, hnd, ST.g_lk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2))
  +tch2 = L.subst(List<&2, Nat>, z => {F.touch(F.CH{DST.hd(z), DST.lst(z), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)) == F.CH{DST.hd(to), DST.lst(to), DST.hd(fl), AR.thaw(U32, tp2), AR.thaw(U32, tn2)} : F.Chain}, o, ord, Equal.sym(List<&2, Nat>, ord, o, esp), tch)
  +elen = Equal.trans(Nat, SC.length(Nat, ord), SC.length(Nat, o), SC.length(Nat, to), Equal.cong(List<&2, Nat>, Nat, z => SC.length(Nat, z), ord, o, esp), Equal.sym(Nat, SC.length(Nat, to), SC.length(Nat, o), Equal.trans(Nat, SC.length(Nat, to), SC.length(Nat, TO.mv(a, s, b)), SC.length(Nat, o), Equal.cong(List<&2, Nat>, Nat, z => SC.length(Nat, z), to, TO.mv(a, s, b), TO.t_ord_eq(a, s, b)), TO.len_mv(a, s, b))))
  Equal.trans(F.Fast<V>, k4(~V, cap, fresh, depth, life, table, tk, U32.from_nat(SC.length(Nat, ord)), F.bump_ins(AR.thaw(U32, tc)), Array.set(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s), e), F.touch(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s))), k4(~V, cap, fresh, depth, life, table, tk, U32.from_nat(SC.length(Nat, to)), F.bump_ins(AR.thaw(U32, tc)), Array.set(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s), e), F.touch(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s))), k4(~V, cap, fresh, depth, life, table, tk, U32.from_nat(SC.length(Nat, to)), AR.thaw(U32, CT.bt(tc, 0n)), AR.thaw(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), F.CH{DST.hd(to), DST.lst(to), DST.hd(fl), AR.thaw(U32, tp2), AR.thaw(U32, tn2)}),
    Equal.cong(Nat, F.Fast<V>, z => k4(~V, cap, fresh, depth, life, table, tk, U32.from_nat(z), F.bump_ins(AR.thaw(U32, tc)), Array.set(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s), e), F.touch(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s))), SC.length(Nat, ord), SC.length(Nat, to), elen),
    Equal.trans(F.Fast<V>, k4(~V, cap, fresh, depth, life, table, tk, U32.from_nat(SC.length(Nat, to)), F.bump_ins(AR.thaw(U32, tc)), Array.set(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s), e), F.touch(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s))), k4(~V, cap, fresh, depth, life, table, tk, U32.from_nat(SC.length(Nat, to)), AR.thaw(U32, CT.bt(tc, 0n)), Array.set(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s), e), F.touch(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s))), k4(~V, cap, fresh, depth, life, table, tk, U32.from_nat(SC.length(Nat, to)), AR.thaw(U32, CT.bt(tc, 0n)), AR.thaw(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), F.CH{DST.hd(to), DST.lst(to), DST.hd(fl), AR.thaw(U32, tp2), AR.thaw(U32, tn2)}),
      Equal.cong(Array<U32>, F.Fast<V>, z => k4(~V, cap, fresh, depth, life, table, tk, U32.from_nat(SC.length(Nat, to)), z, Array.set(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s), e), F.touch(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s))), F.bump_ins(AR.thaw(U32, tc)), AR.thaw(U32, CT.bt(tc, 0n)), CT.bump_ok(tc, 0, 0n, {==}, {==}, ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), {==})),
      Equal.trans(F.Fast<V>, k4(~V, cap, fresh, depth, life, table, tk, U32.from_nat(SC.length(Nat, to)), AR.thaw(U32, CT.bt(tc, 0n)), Array.set(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s), e), F.touch(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s))), k4(~V, cap, fresh, depth, life, table, tk, U32.from_nat(SC.length(Nat, to)), AR.thaw(U32, CT.bt(tc, 0n)), AR.thaw(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), F.touch(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s))), k4(~V, cap, fresh, depth, life, table, tk, U32.from_nat(SC.length(Nat, to)), AR.thaw(U32, CT.bt(tc, 0n)), AR.thaw(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), F.CH{DST.hd(to), DST.lst(to), DST.hd(fl), AR.thaw(U32, tp2), AR.thaw(U32, tn2)}),
        Equal.cong(Array<F.Slot<V>>, F.Fast<V>, z => k4(~V, cap, fresh, depth, life, table, tk, U32.from_nat(SC.length(Nat, to)), AR.thaw(U32, CT.bt(tc, 0n)), z, F.touch(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s))), Array.set(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s), e), AR.thaw(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), IN.set_f(F.Slot<V>, depth, te, s, e, ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), hs, ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))),
        Equal.cong(F.Chain, F.Fast<V>, z => k4(~V, cap, fresh, depth, life, table, tk, U32.from_nat(SC.length(Nat, to)), AR.thaw(U32, CT.bt(tc, 0n)), AR.thaw(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), z), F.touch(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)), F.CH{DST.hd(to), DST.lst(to), DST.hd(fl), AR.thaw(U32, tp2), AR.thaw(U32, tn2)}, tch2))))

# the entries on the moved order are occupied after writing an occupied entry at s
def occ_set(-V: Data, +es: List<&2, F.Slot<V>>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +e: F.Slot<V>, +hn: {DST.lmem(s, SC.append(Nat, a, b)) == False{} : Bool}, +hocc: {ST.all_occ(V, es, SC.append(Nat, a, Con{s, b})) == True{} : Bool}, +hlen: {Nat.is_lt(s, SC.length(F.Slot<V>, es)) == True{} : Bool}, +ho: {ST.is_occ(V, e) == True{} : Bool}) -> {ST.all_occ(V, SC.update(F.Slot<V>, es, s, e), TO.mv(a, s, b)) == True{} : Bool}:
  +es2 = SC.update(F.Slot<V>, es, s, e)
  +ab = SC.append(Nat, a, b)
  +hab = Equal.trans(Bool, ST.all_occ(V, es2, ab), ST.all_occ(V, es, ab), True{}, LS.occ_frame(V, es, s, e, ab, hn), LS.occ_cut(V, es, a, s, b, hocc))
  +es_s = Equal.cong(Maybe<&2, F.Slot<V>>, F.Slot<V>, m => ST.sat_m(V, m), SC.nth(F.Slot<V>, es2, s), Some{e}, LL.nth_update_same(F.Slot<V>, es, s, e, hlen))
  +hs1 = L.subst(F.Slot<V>, z => {ST.is_occ(V, z) == True{} : Bool}, e, ST.sat(V, es2, s), Equal.sym(F.Slot<V>, ST.sat(V, es2, s), e, es_s), ho)
  L.subst(Bool, z => {z == True{} : Bool}, Bool.and(ST.all_occ(V, es2, ab), ST.all_occ(V, es2, Con{s, Nil{}})), ST.all_occ(V, es2, TO.mv(a, s, b)), Equal.sym(Bool, ST.all_occ(V, es2, TO.mv(a, s, b)), Bool.and(ST.all_occ(V, es2, ab), ST.all_occ(V, es2, Con{s, Nil{}})), LS.occ_app(V, es2, ab, Con{s, Nil{}})),
    L.and_intro(ST.all_occ(V, es2, ab), ST.all_occ(V, es2, Con{s, Nil{}}), hab, L.and_intro(ST.is_occ(V, ST.sat(V, es2, s)), True{}, hs1, {==})))

def rep_inv(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, +e: F.Slot<V>, +ho: {ST.is_occ(V, e) == True{} : Bool}, +hm: {DST.lmem(s, ord) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {ST.good(~V, rep_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, e)) == True{} : Bool}:
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
  +es = AR.slots(F.Slot<V>, te)
  +pfe = ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)
  +hlen = L.subst(Nat, z => {Nat.is_lt(s, z) == True{} : Bool}, P, SC.length(F.Slot<V>, es), Equal.sym(Nat, SC.length(F.Slot<V>, es), P, AR.slots_length(F.Slot<V>, depth, te, pfe)), hs)
  +hocc2 = L.subst(List<&2, F.Slot<V>>, z => {ST.all_occ(V, z, TO.mv(a, s, b)) == True{} : Bool}, SC.update(F.Slot<V>, es, s, e), AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), Equal.sym(List<&2, F.Slot<V>>, AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), SC.update(F.Slot<V>, es, s, e), AR.upd_slots(F.Slot<V>, depth, te, s, e, hs, pfe)), occ_set(V, es, a, s, b, e, hn, ST.g_occ(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), hlen, ho))
  T2.touch_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, a, s, b, fl, CT.bt(tc, 0n), AR.upd(F.Slot<V>, depth, te, s, e), hs2, RS.bt_pf(tc, 0n, ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)), AR.upd_perfect(F.Slot<V>, depth, te, s, e, pfe), hocc2)

# the spec's add of a present key
def af_some(-V: Data, +cap: U32, +life: T.Int64, +xs: List<&2, S.Ent<V>>, +m: T.Metrics, +key: String, +en: S.Ent<V>, +k: String, e0: F.Slot<V>, +ho: {ST.is_occ(V, e0) == True{} : Bool}) -> {S.add_found(V, cap, life, xs, m, key, en, EN.ent1(V, k, e0)) == (S.LM{cap, life, S.snoc(V, S.drop(V, xs, key), en), T.bump(0n, m)}, E.OFlag{False{}}) : S.Model<V> & E.Obs<V>}:
  match e0:
    case F.Vacant{}:
      Empty.absurd({S.add_found(V, cap, life, xs, m, key, en, None{}) == (S.LM{cap, life, S.snoc(V, S.drop(V, xs, key), en), T.bump(0n, m)}, E.OFlag{False{}}) : S.Model<V> & E.Obs<V>}, L.false_true(ho))
    case F.Live{v}:
      {==}
    case F.Timed{v, d}:
      {==}

def rep_model(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, +key: String, +v: V, +now: T.Int64, +elk: {TB.lk(table, key) == Some{U32.from_nat(s)} : Maybe<&2, U32>}, +heq: {String.eq(ST.kat(AR.slots(String, tk), s), key) == True{} : Bool}, +hm: {DST.lmem(s, ord) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {S.add_found(V, cap, life, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), ST.mets(AR.slots(U32, tc)), key, S.En{key, v, NS.deadline(now, life)}, S.find(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), key)) == (ST.model(~V, rep_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, AF.entry(~V, life, v, now))), E.OFlag{False{}}) : S.Model<V> & E.Obs<V>}:
  +ks = AR.slots(String, tk)
  +es = AR.slots(F.Slot<V>, te)
  +xs = ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord)
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
  +pfe = ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)
  +hmp = ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2)
  +hna = RS.nk_part_q(table, ks, a, s, key, depth, ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), hs, TL.alllt_l(a, Con{s, b}, P, hlo), RS.notin_l(s, a, b, hn), elk, RS.am_l(table, ks, a, Con{s, b}, hmp))
  +hnb = RS.nk_part_q(table, ks, b, s, key, depth, ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2), hs, L.and_right(Nat.is_lt(s, P), DST.alllt(b, P), TL.alllt_r(a, Con{s, b}, P, hlo)), RS.notin_r(s, a, b, hn), elk, L.and_right(ST.mapped(table, ST.kat(ks, s), s), ST.all_mapped(table, ks, b), RS.am_r(table, ks, a, Con{s, b}, hmp)))
  +ho = RS.occ_mid(V, es, a, s, b, ST.g_occ(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, SP.spre(ord, s), Con{s, SP.spost(ord, s)}), fl, hs2))
  +efind = Equal.trans(Maybe<&2, S.Ent<V>>, S.find(V, xs, key), S.find(V, ST.ents(V, ks, es, o), key), EN.ent1(V, ST.kat(ks, s), ST.sat(V, es, s)),
    Equal.cong(List<&2, Nat>, Maybe<&2, S.Ent<V>>, z => S.find(V, ST.ents(V, ks, es, z), key), ord, o, esp),
    EN.find_at_slot(V, ks, es, a, s, b, key, hna, heq, ho))
  +e = AF.entry(~V, life, v, now)
  +es2 = SC.update(F.Slot<V>, es, s, e)
  +hlen = L.subst(Nat, z => {Nat.is_lt(s, z) == True{} : Bool}, P, SC.length(F.Slot<V>, es), Equal.sym(Nat, SC.length(F.Slot<V>, es), P, AR.slots_length(F.Slot<V>, depth, te, pfe)), hs)
  +es_s = Equal.cong(Maybe<&2, F.Slot<V>>, F.Slot<V>, m => ST.sat_m(V, m), SC.nth(F.Slot<V>, es2, s), Some{e}, LL.nth_update_same(F.Slot<V>, es, s, e, hlen))
  +ho2 = L.subst(F.Slot<V>, z => {ST.is_occ(V, z) == True{} : Bool}, e, ST.sat(V, es2, s), Equal.sym(F.Slot<V>, ST.sat(V, es2, s), e, es_s), AF.entry_occ(~V, life, v, now))
  +ab = SC.append(Nat, a, b)
  +to = TO.t_ord(a, s, b)
  +ek = RU.equal_boolean(ST.kat(ks, s), key, heq)
  +edrop = Equal.trans(List<&2, S.Ent<V>>, S.drop(V, ST.ents(V, ks, es2, o), key), ST.ents(V, ks, es2, ab), S.drop(V, xs, key),
    EN.drop_at_slot(V, ks, es2, a, s, b, key, hna, hnb, heq, ho2),
    Equal.trans(List<&2, S.Ent<V>>, ST.ents(V, ks, es2, ab), ST.ents(V, ks, es, ab), S.drop(V, xs, key),
      LS.ents_frame_e(V, ks, es, s, e, ab, hn),
      Equal.trans(List<&2, S.Ent<V>>, ST.ents(V, ks, es, ab), S.drop(V, ST.ents(V, ks, es, o), key), S.drop(V, xs, key),
        Equal.sym(List<&2, S.Ent<V>>, S.drop(V, ST.ents(V, ks, es, o), key), ST.ents(V, ks, es, ab), EN.drop_at_slot(V, ks, es, a, s, b, key, hna, hnb, heq, ho)),
        Equal.cong(List<&2, Nat>, List<&2, S.Ent<V>>, z => S.drop(V, ST.ents(V, ks, es, z), key), o, ord, Equal.sym(List<&2, Nat>, ord, o, esp)))))
  +eone = Equal.trans(List<&2, S.Ent<V>>, ST.ents(V, ks, es2, Con{s, Nil{}}), ST.ent_at(V, ST.kat(ks, s), e, Nil{}), Con{S.En{key, v, NS.deadline(now, life)}, Nil{}},
    Equal.cong(F.Slot<V>, List<&2, S.Ent<V>>, z => ST.ent_at(V, ST.kat(ks, s), z, Nil{}), ST.sat(V, es2, s), e, es_s),
    Equal.trans(List<&2, S.Ent<V>>, ST.ent_at(V, ST.kat(ks, s), e, Nil{}), Con{S.En{ST.kat(ks, s), v, NS.deadline(now, life)}, Nil{}}, Con{S.En{key, v, NS.deadline(now, life)}, Nil{}},
      AF.entry_ent(~V, ST.kat(ks, s), v, life, now),
      Equal.cong(String, List<&2, S.Ent<V>>, z => Con{S.En{z, v, NS.deadline(now, life)}, Nil{}}, ST.kat(ks, s), key, ek)))
  +eents = Equal.trans(List<&2, S.Ent<V>>, ST.ents(V, ks, AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), to), ST.ents(V, ks, es2, to), S.snoc(V, S.drop(V, xs, key), S.En{key, v, NS.deadline(now, life)}),
    Equal.cong(List<&2, F.Slot<V>>, List<&2, S.Ent<V>>, z => ST.ents(V, ks, z, to), AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), es2, AR.upd_slots(F.Slot<V>, depth, te, s, e, hs, pfe)),
    Equal.trans(List<&2, S.Ent<V>>, ST.ents(V, ks, es2, to), SC.append(S.Ent<V>, S.drop(V, ST.ents(V, ks, es2, o), key), ST.ents(V, ks, es2, Con{s, Nil{}})), S.snoc(V, S.drop(V, xs, key), S.En{key, v, NS.deadline(now, life)}),
      T2.touch_ents(V, ks, es2, a, s, b, key, hna, hnb, heq, ho2),
      Equal.trans(List<&2, S.Ent<V>>, SC.append(S.Ent<V>, S.drop(V, ST.ents(V, ks, es2, o), key), ST.ents(V, ks, es2, Con{s, Nil{}})), SC.append(S.Ent<V>, S.drop(V, xs, key), Con{S.En{key, v, NS.deadline(now, life)}, Nil{}}), S.snoc(V, S.drop(V, xs, key), S.En{key, v, NS.deadline(now, life)}),
        Equal.trans(List<&2, S.Ent<V>>, SC.append(S.Ent<V>, S.drop(V, ST.ents(V, ks, es2, o), key), ST.ents(V, ks, es2, Con{s, Nil{}})), SC.append(S.Ent<V>, S.drop(V, xs, key), ST.ents(V, ks, es2, Con{s, Nil{}})), SC.append(S.Ent<V>, S.drop(V, xs, key), Con{S.En{key, v, NS.deadline(now, life)}, Nil{}}),
          Equal.cong(List<&2, S.Ent<V>>, List<&2, S.Ent<V>>, z => SC.append(S.Ent<V>, z, ST.ents(V, ks, es2, Con{s, Nil{}})), S.drop(V, ST.ents(V, ks, es2, o), key), S.drop(V, xs, key), edrop),
          Equal.cong(List<&2, S.Ent<V>>, List<&2, S.Ent<V>>, z => SC.append(S.Ent<V>, S.drop(V, xs, key), z), ST.ents(V, ks, es2, Con{s, Nil{}}), Con{S.En{key, v, NS.deadline(now, life)}, Nil{}}, eone)),
        Equal.sym(List<&2, S.Ent<V>>, S.snoc(V, S.drop(V, xs, key), S.En{key, v, NS.deadline(now, life)}), SC.append(S.Ent<V>, S.drop(V, xs, key), Con{S.En{key, v, NS.deadline(now, life)}, Nil{}}), EN.snoc_app(V, S.drop(V, xs, key), S.En{key, v, NS.deadline(now, life)})))))
  +cs = AR.slots(U32, tc)
  +pfc = ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)
  +emets = Equal.trans(T.Metrics, ST.mets(AR.slots(U32, CT.bt(tc, 0n))), ST.mets(CT.sbt(cs, 0n, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0), DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n)))), T.bump(0n, ST.mets(cs)),
    Equal.cong(List<&2, U32>, T.Metrics, z => ST.mets(z), AR.slots(U32, CT.bt(tc, 0n)), CT.sbt(cs, 0n, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0), DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n))), CT.slots_bt(tc, 0n, pfc, {==})),
    CT.mets_bump_0(cs, RS.len16(tc, 1n, {==}, pfc)))
  +emod = Equal.trans(S.Model<V>, S.LM{cap, life, S.snoc(V, S.drop(V, xs, key), S.En{key, v, NS.deadline(now, life)}), T.bump(0n, ST.mets(AR.slots(U32, tc)))}, S.LM{cap, life, ST.ents(V, ks, AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), to), T.bump(0n, ST.mets(AR.slots(U32, tc)))}, S.LM{cap, life, ST.ents(V, ks, AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), to), ST.mets(AR.slots(U32, CT.bt(tc, 0n)))},
    Equal.cong(List<&2, S.Ent<V>>, S.Model<V>, z => S.LM{cap, life, z, T.bump(0n, ST.mets(AR.slots(U32, tc)))}, S.snoc(V, S.drop(V, xs, key), S.En{key, v, NS.deadline(now, life)}), ST.ents(V, ks, AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), to), Equal.sym(List<&2, S.Ent<V>>, ST.ents(V, ks, AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), to), S.snoc(V, S.drop(V, xs, key), S.En{key, v, NS.deadline(now, life)}), eents)),
    Equal.cong(T.Metrics, S.Model<V>, z => S.LM{cap, life, ST.ents(V, ks, AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), to), z}, T.bump(0n, ST.mets(AR.slots(U32, tc))), ST.mets(AR.slots(U32, CT.bt(tc, 0n))), Equal.sym(T.Metrics, ST.mets(AR.slots(U32, CT.bt(tc, 0n))), T.bump(0n, ST.mets(AR.slots(U32, tc))), emets)))
  L.subst(Maybe<&2, S.Ent<V>>, z => {S.add_found(V, cap, life, xs, ST.mets(AR.slots(U32, tc)), key, S.En{key, v, NS.deadline(now, life)}, z) == (ST.model(~V, rep_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, e)), E.OFlag{False{}}) : S.Model<V> & E.Obs<V>}, EN.ent1(V, ST.kat(ks, s), ST.sat(V, es, s)), S.find(V, xs, key), Equal.sym(Maybe<&2, S.Ent<V>>, S.find(V, xs, key), EN.ent1(V, ST.kat(ks, s), ST.sat(V, es, s)), efind),
    Equal.trans(S.Model<V> & E.Obs<V>, S.add_found(V, cap, life, xs, ST.mets(AR.slots(U32, tc)), key, S.En{key, v, NS.deadline(now, life)}, EN.ent1(V, ST.kat(ks, s), ST.sat(V, es, s))), (S.LM{cap, life, S.snoc(V, S.drop(V, xs, key), S.En{key, v, NS.deadline(now, life)}), T.bump(0n, ST.mets(AR.slots(U32, tc)))}, E.OFlag{False{}}), (ST.model(~V, rep_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, e)), E.OFlag{False{}}),
      af_some(V, cap, life, xs, ST.mets(AR.slots(U32, tc)), key, S.En{key, v, NS.deadline(now, life)}, ST.kat(ks, s), ST.sat(V, es, s), ho),
      Equal.cong(S.Model<V>, S.Model<V> & E.Obs<V>, z => (z, E.OFlag{False{}}), S.LM{cap, life, S.snoc(V, S.drop(V, xs, key), S.En{key, v, NS.deadline(now, life)}), T.bump(0n, ST.mets(AR.slots(U32, tc)))}, ST.model(~V, rep_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, e)), emod)))
