import Base
import ../lib/logic.bend as L
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../spec/lru_fast.bend as S
import ../../src/lru/fast.bend as F
import ../../types/lru_model.bend as T
import support/links_state.bend as DST
import support/links_split.bend as SP
import support/links_core.bend as K
import ../../reference/lru/proofs/invariants.bend as Inv
import ./state.bend as ST
import ./ents.bend as EN
import ./table.bend as TB
import ./touch.bend as TO

# Touching slot s keeps the invariant (for any perfect counter tree and any
# perfect entry tree whose entries on the new order are occupied), and the
# entries become the old ones without s's key, followed by s's entry.

def to_t(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>) -> {TO.mv(a, s, b) == TO.t_ord(a, s, b) : List<&2, Nat>}:
  Equal.sym(List<&2, Nat>, TO.t_ord(a, s, b), TO.mv(a, s, b), TO.t_ord_eq(a, s, b))

def touch_inv(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +fl: List<&2, Nat>, +tc2: AR.Tree<U32>, +te2: AR.Tree<F.Slot<V>>, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl) == True{} : Bool}, +pfc2: {AR.perfect(U32, 4n, tc2) == True{} : Bool}, +pfe2: {AR.perfect(F.Slot<V>, depth, te2) == True{} : Bool}, +hocc2: {ST.all_occ(V, AR.slots(F.Slot<V>, te2), TO.mv(a, s, b)) == True{} : Bool}) -> {ST.inv(~V, cap, fresh, depth, life, tc2, table, tk, te2, TO.t_tp(depth, tp, a, s, b), TO.t_tn(depth, tn, a, s, b), TO.t_ord(a, s, b), fl) == True{} : Bool}:
  +o = SC.append(Nat, a, Con{s, b})
  +to = TO.t_ord(a, s, b)
  +m = TO.mv(a, s, b)
  +ks = AR.slots(String, tk)
  +P = SC.pow2(depth)
  +hd = ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, h)
  +pfp = ST.g_tp(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, h)
  +pfn = ST.g_tn(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, h)
  +hfr = ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, h)
  +hol = ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, h)
  +hnd2 = ST.g_nodup(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, h)
  +hlo = K.alllt_mono(o, fresh, P, hfr, hol)
  +hnd = SP.nodup_app_l(o, fl, hnd2)
  +elen = Equal.trans(Nat, SC.length(Nat, to), SC.length(Nat, m), SC.length(Nat, o), Equal.cong(List<&2, Nat>, Nat, z => SC.length(Nat, z), to, m, TO.t_ord_eq(a, s, b)), TO.len_mv(a, s, b))
  +h7 = L.subst(List<&2, Nat>, z => {DST.alllt(z, fresh) == True{} : Bool}, m, to, to_t(a, s, b), TO.alllt_mv(a, s, b, fresh, hol))
  +h9 = L.subst(List<&2, Nat>, z => {DST.nodup(SC.append(Nat, z, fl)) == True{} : Bool}, m, to, to_t(a, s, b), TO.nodup_mv(a, s, b, fl, hnd2))
  +h10 = L.subst(Nat, z => {Nat.is_eq(Nat.add(z, SC.length(Nat, fl)), fresh) == True{} : Bool}, SC.length(Nat, o), SC.length(Nat, to), Equal.sym(Nat, SC.length(Nat, to), SC.length(Nat, o), elen), ST.g_count(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, h))
  +h13 = L.subst(List<&2, Nat>, z => {ST.all_occ(V, AR.slots(F.Slot<V>, te2), z) == True{} : Bool}, m, to, to_t(a, s, b), hocc2)
  +h14 = L.subst(List<&2, Nat>, z => {ST.all_mapped(table, ks, z) == True{} : Bool}, m, to, to_t(a, s, b), TO.am_mv(table, ks, a, s, b, ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, h)))
  +h15 = L.subst(List<&2, Nat>, z => {Inv.included(Map.keys(&2, Maybe<&2, U32>, table), ST.keys_at(ks, z)) == True{} : Bool}, m, to, to_t(a, s, b), TO.incl_mv(Map.keys(&2, Maybe<&2, U32>, table), ks, a, s, b, ST.g_incl(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, h)))
  +h19 = L.subst(Nat, z => {Nat.is_le(z, U32.to_nat(cap)) == True{} : Bool}, SC.length(Nat, o), SC.length(Nat, to), Equal.sym(Nat, SC.length(Nat, to), SC.length(Nat, o), elen), ST.g_n(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, h))
  ST.inv_mk(~V, cap, fresh, depth, life, tc2, table, tk, te2, TO.t_tp(depth, tp, a, s, b), TO.t_tn(depth, tn, a, s, b), to, fl,
    hd, ST.g_tk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, h), pfe2, TO.t_pf_p(depth, tp, a, s, b, pfp), TO.t_pf_n(depth, tn, a, s, b, pfn), pfc2, hfr, h7, ST.g_fllt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, h), h9, h10,
    TO.t_lk(depth, tp, tn, a, s, b, hd, pfp, pfn, hlo, hnd, ST.g_lk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, h)), TO.t_fk(depth, tn, a, s, b, fl, hd, pfn, hlo, hnd2, ST.g_fk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, h)),
    h13, h14, h15, ST.g_crit(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, h), ST.g_pop(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, h), ST.g_cap(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl, h), h19)

# the entries along the touched order
def touch_ents(-V: Data, +ks: List<&2, String>, +es: List<&2, F.Slot<V>>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +q: String, +hna: {TB.none_key(ks, a, q) == True{} : Bool}, +hnb: {TB.none_key(ks, b, q) == True{} : Bool}, +heq: {String.eq(ST.kat(ks, s), q) == True{} : Bool}, +ho: {ST.is_occ(V, ST.sat(V, es, s)) == True{} : Bool}) -> {ST.ents(V, ks, es, TO.t_ord(a, s, b)) == SC.append(S.Ent<V>, S.drop(V, ST.ents(V, ks, es, SC.append(Nat, a, Con{s, b})), q), ST.ents(V, ks, es, Con{s, Nil{}})) : List<&2, S.Ent<V>>}:
  +ab = SC.append(Nat, a, b)
  Equal.trans(List<&2, S.Ent<V>>, ST.ents(V, ks, es, TO.t_ord(a, s, b)), ST.ents(V, ks, es, TO.mv(a, s, b)), SC.append(S.Ent<V>, S.drop(V, ST.ents(V, ks, es, SC.append(Nat, a, Con{s, b})), q), ST.ents(V, ks, es, Con{s, Nil{}})),
    Equal.cong(List<&2, Nat>, List<&2, S.Ent<V>>, z => ST.ents(V, ks, es, z), TO.t_ord(a, s, b), TO.mv(a, s, b), TO.t_ord_eq(a, s, b)),
    Equal.trans(List<&2, S.Ent<V>>, ST.ents(V, ks, es, TO.mv(a, s, b)), SC.append(S.Ent<V>, ST.ents(V, ks, es, ab), ST.ents(V, ks, es, Con{s, Nil{}})), SC.append(S.Ent<V>, S.drop(V, ST.ents(V, ks, es, SC.append(Nat, a, Con{s, b})), q), ST.ents(V, ks, es, Con{s, Nil{}})),
      EN.ents_app(V, ks, es, ab, Con{s, Nil{}}),
      Equal.cong(List<&2, S.Ent<V>>, List<&2, S.Ent<V>>, z => SC.append(S.Ent<V>, z, ST.ents(V, ks, es, Con{s, Nil{}})), ST.ents(V, ks, es, ab), S.drop(V, ST.ents(V, ks, es, SC.append(Nat, a, Con{s, b})), q), Equal.sym(List<&2, S.Ent<V>>, S.drop(V, ST.ents(V, ks, es, SC.append(Nat, a, Con{s, b})), q), ST.ents(V, ks, es, ab), EN.drop_at_slot(V, ks, es, a, s, b, q, hna, hnb, heq, ho)))))
