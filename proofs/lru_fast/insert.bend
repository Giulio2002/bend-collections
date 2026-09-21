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
import ../../src/doubly_linked_list.bend as D
import ../../types/lru_model.bend as T
import ../dlist/state.bend as DST
import ../dlist/links.bend as LK
import ../dlist/split.bend as SP
import ../dlist/retarget.bend as RT
import ../dlist/rmfacts.bend as RM
import ../dlist/tolist.bend as TL
import ../dlist/core.bend as K
import ../dlist/insert.bend as IN
import ../dlist/inslk.bend as IL
import ../dlist/tset.bend as TS
import ../dlist/facts.bend as DF
import ../../reference/lru/proofs/invariants.bend as Inv
import ../../reference/lru/proofs/map_insert.bend as MI
import ../../reference/lru/proofs/map_populated.bend as Pop
import ../../reference/lru/proofs/map_set_critbit.bend as SetCrit
import ./state.bend as ST
import ../dlist/nbrs.bend as NB
import ../dlist/grow.bend as GR
import ../dlist/items.bend as IT
import ./table.bend as TB
import ./ents.bend as EN
import ./lists.bend as LS
import ./counts.bend as CT
import ./chain.bend as CHN
import ./rs.bend as RS
import ./touch.bend as TO
import ./addfacts.bend as AF

# Inserting a new key at slot s (outside the order): the key and entry are
# written at s, the table maps the key to s, s is linked as the newest, and one
# insert is counted. put_new is the shared tail of the three allocation paths.

def ins_sh(-V: Data, +cap: U32, +fresh2: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl2: List<&2, Nat>, +s: Nat, +key: String, +e: F.Slot<V>) -> ST.Shadow<V>:
  ST.Sh{cap, fresh2, depth, life, CT.bt(tc, 0n), Map.set(&2, Maybe<&2, U32>, table, key, Some{U32.from_nat(s)}), AR.upd(String, depth, tk, s, key), AR.upd(F.Slot<V>, depth, te, s, e), AR.upd(U32, depth, tp, s, LK.lastl(ord, D.nil())), TS.tnup(depth, AR.upd(U32, depth, tn, s, D.nil()), ord, DST.ln(s)), SC.append(Nat, ord, Con{s, Nil{}}), fl2}

def k5(~V: Data, +cap: U32, +fresh2: Nat, +depth: Nat, +life: T.Int64, +table: Map<&2, Maybe<&2, U32>>, +n: U32, c: Array<U32>, ks: Array<String>, es: Array<F.Slot<V>>, ch: F.Chain) -> F.Fast<V>:
  F.F{cap, n, U32.from_nat(fresh2), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), c, table, ks, es, ch}

def len_snoc(+ord: List<&2, Nat>, +s: Nat) -> {SC.length(Nat, SC.append(Nat, ord, Con{s, Nil{}})) == 1n+SC.length(Nat, ord) : Nat}:
  Equal.trans(Nat, SC.length(Nat, SC.append(Nat, ord, Con{s, Nil{}})), Nat.add(SC.length(Nat, ord), 1n), 1n+SC.length(Nat, ord),
    LL.length_append(Nat, ord, Con{s, Nil{}}),
    Equal.trans(Nat, Nat.add(SC.length(Nat, ord), 1n), 1n+Nat.add(SC.length(Nat, ord), 0n), 1n+SC.length(Nat, ord),
      N.add_succ(SC.length(Nat, ord), 0n),
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(SC.length(Nat, ord), 0n), SC.length(Nat, ord), N.add_zero(SC.length(Nat, ord)))))

def n_inc(+ord: List<&2, Nat>, +s: Nat) -> {U32.inc(U32.from_nat(SC.length(Nat, ord))) == U32.from_nat(SC.length(Nat, SC.append(Nat, ord, Con{s, Nil{}}))) : U32}:
  Equal.cong(Nat, U32, z => U32.from_nat(z), 1n+SC.length(Nat, ord), SC.length(Nat, SC.append(Nat, ord, Con{s, Nil{}})), Equal.sym(Nat, SC.length(Nat, SC.append(Nat, ord, Con{s, Nil{}})), 1n+SC.length(Nat, ord), len_snoc(ord, s)))

def put_ok(~V: Data, +cap: U32, +fresh2: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl2: List<&2, Nat>, +s: Nat, +key: String, e: F.Slot<V>, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfc: {AR.perfect(U32, 4n, tc) == True{} : Bool}, +pfk: {AR.perfect(String, depth, tk) == True{} : Bool}, +pfe: {AR.perfect(F.Slot<V>, depth, te) == True{} : Bool}, +pfp: {AR.perfect(U32, depth, tp) == True{} : Bool}, +pfn: {AR.perfect(U32, depth, tn) == True{} : Bool}, +hs: {Nat.is_lt(s, SC.pow2(depth)) == True{} : Bool}, +hl: {DST.alllt(ord, SC.pow2(depth)) == True{} : Bool}) -> {F.put_new(~V, cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh2), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(String, tk), AR.thaw(F.Slot<V>, te), F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl2), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s), key, e) == ST.real(~V, ins_sh(V, cap, fresh2, depth, life, tc, table, tk, te, tp, tn, ord, fl2, s, key, e)) : F.Fast<V>}:
  +o2 = SC.append(Nat, ord, Con{s, Nil{}})
  +t2 = Map.set(&2, Maybe<&2, U32>, table, key, Some{U32.from_nat(s)})
  +tp2 = AR.upd(U32, depth, tp, s, LK.lastl(ord, D.nil()))
  +tn2 = TS.tnup(depth, AR.upd(U32, depth, tn, s, D.nil()), ord, DST.ln(s))
  Equal.trans(F.Fast<V>, k5(~V, cap, fresh2, depth, life, t2, U32.inc(U32.from_nat(SC.length(Nat, ord))), F.bump_ins(AR.thaw(U32, tc)), Array.set(String, AR.thaw(String, tk), U32.from_nat(s), key), Array.set(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s), e), F.link_tail(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl2), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s))), k5(~V, cap, fresh2, depth, life, t2, U32.from_nat(SC.length(Nat, o2)), F.bump_ins(AR.thaw(U32, tc)), Array.set(String, AR.thaw(String, tk), U32.from_nat(s), key), Array.set(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s), e), F.link_tail(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl2), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s))), k5(~V, cap, fresh2, depth, life, t2, U32.from_nat(SC.length(Nat, o2)), AR.thaw(U32, CT.bt(tc, 0n)), AR.thaw(String, AR.upd(String, depth, tk, s, key)), AR.thaw(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), F.CH{DST.hd(o2), DST.lst(o2), DST.hd(fl2), AR.thaw(U32, tp2), AR.thaw(U32, tn2)}),
    Equal.cong(U32, F.Fast<V>, z => k5(~V, cap, fresh2, depth, life, t2, z, F.bump_ins(AR.thaw(U32, tc)), Array.set(String, AR.thaw(String, tk), U32.from_nat(s), key), Array.set(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s), e), F.link_tail(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl2), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s))), U32.inc(U32.from_nat(SC.length(Nat, ord))), U32.from_nat(SC.length(Nat, o2)), n_inc(ord, s)),
    Equal.trans(F.Fast<V>, k5(~V, cap, fresh2, depth, life, t2, U32.from_nat(SC.length(Nat, o2)), F.bump_ins(AR.thaw(U32, tc)), Array.set(String, AR.thaw(String, tk), U32.from_nat(s), key), Array.set(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s), e), F.link_tail(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl2), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s))), k5(~V, cap, fresh2, depth, life, t2, U32.from_nat(SC.length(Nat, o2)), AR.thaw(U32, CT.bt(tc, 0n)), Array.set(String, AR.thaw(String, tk), U32.from_nat(s), key), Array.set(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s), e), F.link_tail(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl2), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s))), k5(~V, cap, fresh2, depth, life, t2, U32.from_nat(SC.length(Nat, o2)), AR.thaw(U32, CT.bt(tc, 0n)), AR.thaw(String, AR.upd(String, depth, tk, s, key)), AR.thaw(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), F.CH{DST.hd(o2), DST.lst(o2), DST.hd(fl2), AR.thaw(U32, tp2), AR.thaw(U32, tn2)}),
      Equal.cong(Array<U32>, F.Fast<V>, z => k5(~V, cap, fresh2, depth, life, t2, U32.from_nat(SC.length(Nat, o2)), z, Array.set(String, AR.thaw(String, tk), U32.from_nat(s), key), Array.set(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s), e), F.link_tail(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl2), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s))), F.bump_ins(AR.thaw(U32, tc)), AR.thaw(U32, CT.bt(tc, 0n)), CT.bump_ok(tc, 0, 0n, {==}, {==}, pfc, {==})),
      Equal.trans(F.Fast<V>, k5(~V, cap, fresh2, depth, life, t2, U32.from_nat(SC.length(Nat, o2)), AR.thaw(U32, CT.bt(tc, 0n)), Array.set(String, AR.thaw(String, tk), U32.from_nat(s), key), Array.set(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s), e), F.link_tail(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl2), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s))), k5(~V, cap, fresh2, depth, life, t2, U32.from_nat(SC.length(Nat, o2)), AR.thaw(U32, CT.bt(tc, 0n)), AR.thaw(String, AR.upd(String, depth, tk, s, key)), Array.set(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s), e), F.link_tail(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl2), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s))), k5(~V, cap, fresh2, depth, life, t2, U32.from_nat(SC.length(Nat, o2)), AR.thaw(U32, CT.bt(tc, 0n)), AR.thaw(String, AR.upd(String, depth, tk, s, key)), AR.thaw(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), F.CH{DST.hd(o2), DST.lst(o2), DST.hd(fl2), AR.thaw(U32, tp2), AR.thaw(U32, tn2)}),
        Equal.cong(Array<String>, F.Fast<V>, z => k5(~V, cap, fresh2, depth, life, t2, U32.from_nat(SC.length(Nat, o2)), AR.thaw(U32, CT.bt(tc, 0n)), z, Array.set(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s), e), F.link_tail(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl2), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s))), Array.set(String, AR.thaw(String, tk), U32.from_nat(s), key), AR.thaw(String, AR.upd(String, depth, tk, s, key)), IN.set_f(String, depth, tk, s, key, hd, hs, pfk)),
        Equal.trans(F.Fast<V>, k5(~V, cap, fresh2, depth, life, t2, U32.from_nat(SC.length(Nat, o2)), AR.thaw(U32, CT.bt(tc, 0n)), AR.thaw(String, AR.upd(String, depth, tk, s, key)), Array.set(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s), e), F.link_tail(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl2), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s))), k5(~V, cap, fresh2, depth, life, t2, U32.from_nat(SC.length(Nat, o2)), AR.thaw(U32, CT.bt(tc, 0n)), AR.thaw(String, AR.upd(String, depth, tk, s, key)), AR.thaw(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), F.link_tail(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl2), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s))), k5(~V, cap, fresh2, depth, life, t2, U32.from_nat(SC.length(Nat, o2)), AR.thaw(U32, CT.bt(tc, 0n)), AR.thaw(String, AR.upd(String, depth, tk, s, key)), AR.thaw(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), F.CH{DST.hd(o2), DST.lst(o2), DST.hd(fl2), AR.thaw(U32, tp2), AR.thaw(U32, tn2)}),
          Equal.cong(Array<F.Slot<V>>, F.Fast<V>, z => k5(~V, cap, fresh2, depth, life, t2, U32.from_nat(SC.length(Nat, o2)), AR.thaw(U32, CT.bt(tc, 0n)), AR.thaw(String, AR.upd(String, depth, tk, s, key)), z, F.link_tail(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl2), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s))), Array.set(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s), e), AR.thaw(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), IN.set_f(F.Slot<V>, depth, te, s, e, hd, hs, pfe)),
          Equal.cong(F.Chain, F.Fast<V>, z => k5(~V, cap, fresh2, depth, life, t2, U32.from_nat(SC.length(Nat, o2)), AR.thaw(U32, CT.bt(tc, 0n)), AR.thaw(String, AR.upd(String, depth, tk, s, key)), AR.thaw(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), z), F.link_tail(F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl2), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)), F.CH{DST.hd(o2), DST.lst(o2), DST.hd(fl2), AR.thaw(U32, tp2), AR.thaw(U32, tn2)}, CHN.link_tail_ok(depth, tp, tn, ord, s, DST.hd(fl2), hd, pfp, pfn, hs, hl))))))

# ---- the invariant after inserting ----

def disj_app_r(+a: List<&2, Nat>, +b: List<&2, Nat>, +ys: List<&2, Nat>, +h: {SP.disj(SC.append(Nat, a, b), ys) == True{} : Bool}) -> {SP.disj(b, ys) == True{} : Bool}:
  match a:
    case Nil{}:
      h
    case Con{+x, +r}:
      disj_app_r(r, b, ys, L.and_right(Bool.not(DST.lmem(x, ys)), SP.disj(SC.append(Nat, r, b), ys), h))

def occ_snoc(-V: Data, +es: List<&2, F.Slot<V>>, +ord: List<&2, Nat>, +s: Nat, +e: F.Slot<V>, +hn: {DST.lmem(s, ord) == False{} : Bool}, +hocc: {ST.all_occ(V, es, ord) == True{} : Bool}, +hlen: {Nat.is_lt(s, SC.length(F.Slot<V>, es)) == True{} : Bool}, +ho: {ST.is_occ(V, e) == True{} : Bool}) -> {ST.all_occ(V, SC.update(F.Slot<V>, es, s, e), SC.append(Nat, ord, Con{s, Nil{}})) == True{} : Bool}:
  +es2 = SC.update(F.Slot<V>, es, s, e)
  +es_s = Equal.cong(Maybe<&2, F.Slot<V>>, F.Slot<V>, m => ST.sat_m(V, m), SC.nth(F.Slot<V>, es2, s), Some{e}, LL.nth_update_same(F.Slot<V>, es, s, e, hlen))
  +hs1 = L.subst(F.Slot<V>, z => {ST.is_occ(V, z) == True{} : Bool}, e, ST.sat(V, es2, s), Equal.sym(F.Slot<V>, ST.sat(V, es2, s), e, es_s), ho)
  L.subst(Bool, z => {z == True{} : Bool}, Bool.and(ST.all_occ(V, es2, ord), ST.all_occ(V, es2, Con{s, Nil{}})), ST.all_occ(V, es2, SC.append(Nat, ord, Con{s, Nil{}})), Equal.sym(Bool, ST.all_occ(V, es2, SC.append(Nat, ord, Con{s, Nil{}})), Bool.and(ST.all_occ(V, es2, ord), ST.all_occ(V, es2, Con{s, Nil{}})), LS.occ_app(V, es2, ord, Con{s, Nil{}})),
    L.and_intro(ST.all_occ(V, es2, ord), ST.all_occ(V, es2, Con{s, Nil{}}), Equal.trans(Bool, ST.all_occ(V, es2, ord), ST.all_occ(V, es, ord), True{}, LS.occ_frame(V, es, s, e, ord, hn), hocc), L.and_intro(ST.is_occ(V, ST.sat(V, es2, s)), True{}, hs1, {==})))

def kat_same(+ks: List<&2, String>, +s: Nat, +key: String, +hlen: {Nat.is_lt(s, SC.length(String, ks)) == True{} : Bool}) -> {ST.kat(SC.update(String, ks, s, key), s) == key : String}:
  Equal.cong(Maybe<&2, String>, String, m => L.some_value(String, m, ""), SC.nth(String, SC.update(String, ks, s, key), s), Some{key}, LL.nth_update_same(String, ks, s, key, hlen))

def am_snoc(+t: Map<&2, Maybe<&2, U32>>, +ks: List<&2, String>, +ord: List<&2, Nat>, +s: Nat, +key: String, +hn: {DST.lmem(s, ord) == False{} : Bool}, +hmap: {ST.all_mapped(t, ks, ord) == True{} : Bool}, +hlen: {Nat.is_lt(s, SC.length(String, ks)) == True{} : Bool}, +hno: {TB.lk(t, key) == None{} : Maybe<&2, U32>}, +crit: {Inv.critbit(Maybe<&2, U32>, t) == True{} : Bool}) -> {ST.all_mapped(Map.set(&2, Maybe<&2, U32>, t, key, Some{U32.from_nat(s)}), SC.update(String, ks, s, key), SC.append(Nat, ord, Con{s, Nil{}})) == True{} : Bool}:
  +t2 = Map.set(&2, Maybe<&2, U32>, t, key, Some{U32.from_nat(s)})
  +ks2 = SC.update(String, ks, s, key)
  +hnk = TB.nk_all(t, ks, ord, key, None{}, hno, hmap, TB.nomap_none(ord))
  +h1 = Equal.trans(Bool, ST.all_mapped(t2, ks2, ord), ST.all_mapped(t2, ks, ord), True{}, LS.am_frame_k(t2, ks, s, key, ord, hn), TB.am_set(t, key, Some{U32.from_nat(s)}, ks, ord, crit, hnk, hmap))
  +elk = MI.set_same(Maybe<&2, U32>, None{}, t, key, Some{U32.from_nat(s)})
  +h2 = L.subst(String, z => {ST.mapped(t2, z, s) == True{} : Bool}, key, ST.kat(ks2, s), Equal.sym(String, ST.kat(ks2, s), key, kat_same(ks, s, key, hlen)),
    L.subst(Maybe<&2, U32>, z => {ST.mapped_m(z, s) == True{} : Bool}, Some{U32.from_nat(s)}, TB.lk(t2, key), Equal.sym(Maybe<&2, U32>, TB.lk(t2, key), Some{U32.from_nat(s)}, elk), RT.eq_self(U32.from_nat(s), U32.from_nat(s), {==})))
  L.subst(Bool, z => {z == True{} : Bool}, Bool.and(ST.all_mapped(t2, ks2, ord), ST.all_mapped(t2, ks2, Con{s, Nil{}})), ST.all_mapped(t2, ks2, SC.append(Nat, ord, Con{s, Nil{}})), Equal.sym(Bool, ST.all_mapped(t2, ks2, SC.append(Nat, ord, Con{s, Nil{}})), Bool.and(ST.all_mapped(t2, ks2, ord), ST.all_mapped(t2, ks2, Con{s, Nil{}})), LS.am_app(t2, ks2, ord, Con{s, Nil{}})),
    L.and_intro(ST.all_mapped(t2, ks2, ord), ST.all_mapped(t2, ks2, Con{s, Nil{}}), h1, L.and_intro(ST.mapped(t2, ST.kat(ks2, s), s), True{}, h2, {==})))

def incl_snoc(+t: Map<&2, Maybe<&2, U32>>, +ks: List<&2, String>, +ord: List<&2, Nat>, +s: Nat, +key: String, +hn: {DST.lmem(s, ord) == False{} : Bool}, +hlen: {Nat.is_lt(s, SC.length(String, ks)) == True{} : Bool}, +crit: {Inv.critbit(Maybe<&2, U32>, t) == True{} : Bool}, +pop: {Pop.populated(U32, t) == True{} : Bool}, +hincl: {Inv.included(Map.keys(&2, Maybe<&2, U32>, t), ST.keys_at(ks, ord)) == True{} : Bool}) -> {Inv.included(Map.keys(&2, Maybe<&2, U32>, Map.set(&2, Maybe<&2, U32>, t, key, Some{U32.from_nat(s)})), ST.keys_at(SC.update(String, ks, s, key), SC.append(Nat, ord, Con{s, Nil{}}))) == True{} : Bool}:
  +ks2 = SC.update(String, ks, s, key)
  TB.incl_set(t, key, U32.from_nat(s), ks2, ord, s, kat_same(ks, s, key, hlen), crit, pop,
    L.subst(List<&2, String>, z => {Inv.included(Map.keys(&2, Maybe<&2, U32>, t), z) == True{} : Bool}, ST.keys_at(ks, ord), ST.keys_at(ks2, ord), Equal.sym(List<&2, String>, ST.keys_at(ks2, ord), ST.keys_at(ks, ord), LS.keys_frame(ks, s, key, ord, hn)), hincl))

def lk_snoc(+ord: List<&2, Nat>, +s: Nat, +ps: List<&2, U32>, +ns: List<&2, U32>, +hnd: {DST.nodup(ord) == True{} : Bool}, +hn: {DST.lmem(s, ord) == False{} : Bool}, +hx: {DST.alllt(ord, SC.length(U32, ns)) == True{} : Bool}, +hfp: {Nat.is_lt(s, SC.length(U32, ps)) == True{} : Bool}, +hfn: {Nat.is_lt(s, SC.length(U32, ns)) == True{} : Bool}, +hk: {DST.lk(ord, D.nil(), D.nil(), ps, ns) == True{} : Bool}) -> {DST.lk(SC.append(Nat, ord, Con{s, Nil{}}), D.nil(), D.nil(), SC.update(U32, ps, s, LK.lastl(ord, D.nil())), RT.nupd(SC.update(U32, ns, s, D.nil()), ord, DST.ln(s))) == True{} : Bool}:
  +on = SC.append(Nat, ord, Nil{})
  +enil = Equal.sym(List<&2, Nat>, on, ord, LL.append_nil(Nat, ord))
  +r = IL.lk_ins(on, Nil{}, s, ps, ns,
    L.subst(List<&2, Nat>, z => {DST.nodup(SC.append(Nat, z, Nil{})) == True{} : Bool}, ord, on, enil, L.subst(List<&2, Nat>, z => {DST.nodup(z) == True{} : Bool}, ord, on, enil, hnd)),
    L.subst(List<&2, Nat>, z => {DST.lmem(s, SC.append(Nat, z, Nil{})) == False{} : Bool}, ord, on, enil, L.subst(List<&2, Nat>, z => {DST.lmem(s, z) == False{} : Bool}, ord, on, enil, hn)),
    L.subst(List<&2, Nat>, z => {DST.alllt(z, SC.length(U32, ns)) == True{} : Bool}, ord, on, enil, hx),
    {==}, hfp, hfn,
    L.subst(List<&2, Nat>, z => {DST.lk(SC.append(Nat, z, Nil{}), D.nil(), D.nil(), ps, ns) == True{} : Bool}, ord, on, enil, L.subst(List<&2, Nat>, z => {DST.lk(z, D.nil(), D.nil(), ps, ns) == True{} : Bool}, ord, on, enil, hk)))
  L.subst(List<&2, Nat>, z => {DST.lk(SC.append(Nat, z, Con{s, Nil{}}), D.nil(), D.nil(), SC.update(U32, ps, s, LK.lastl(z, D.nil())), RT.nupd(SC.update(U32, ns, s, D.nil()), z, DST.ln(s))) == True{} : Bool}, on, ord, LL.append_nil(Nat, ord), r)

def ins_inv(~V: Data, +cap: U32, +fresh: Nat, +fresh2: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +fl2: List<&2, Nat>, +s: Nat, +key: String, +e: F.Slot<V>, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +hno: {TB.lk(table, key) == None{} : Maybe<&2, U32>}, +ho: {ST.is_occ(V, e) == True{} : Bool}, +hs: {Nat.is_lt(s, SC.pow2(depth)) == True{} : Bool}, +hfr2: {Nat.is_le(fresh2, SC.pow2(depth)) == True{} : Bool}, +hol2: {DST.alllt(SC.append(Nat, ord, Con{s, Nil{}}), fresh2) == True{} : Bool}, +hfl2: {DST.alllt(fl2, fresh2) == True{} : Bool}, +hnd2: {DST.nodup(SC.append(Nat, SC.append(Nat, ord, Con{s, Nil{}}), fl2)) == True{} : Bool}, +hcnt2: {Nat.is_eq(Nat.add(SC.length(Nat, SC.append(Nat, ord, Con{s, Nil{}})), SC.length(Nat, fl2)), fresh2) == True{} : Bool}, +hfk2: {ST.fk(fl2, AR.slots(U32, tn)) == True{} : Bool}, +hn2: {Nat.is_le(SC.length(Nat, SC.append(Nat, ord, Con{s, Nil{}})), U32.to_nat(cap)) == True{} : Bool}) -> {ST.good(~V, ins_sh(V, cap, fresh2, depth, life, tc, table, tk, te, tp, tn, ord, fl2, s, key, e)) == True{} : Bool}:
  +o2 = SC.append(Nat, ord, Con{s, Nil{}})
  +P = SC.pow2(depth)
  +ks = AR.slots(String, tk)
  +es = AR.slots(F.Slot<V>, te)
  +ps = AR.slots(U32, tp)
  +ns = AR.slots(U32, tn)
  +hd = ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)
  +pfk = ST.g_tk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)
  +pfe = ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)
  +pfp = ST.g_tp(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)
  +pfn = ST.g_tn(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)
  +crit = ST.g_crit(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)
  +pop = ST.g_pop(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)
  +hlo = K.alllt_mono(ord, fresh, P, ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
  +hnd = SP.nodup_app_l(ord, fl, ST.g_nodup(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
  +hdo2 = SP.nodup_disj(o2, fl2, hnd2)
  +hdo = RS.disj_app_l(ord, Con{s, Nil{}}, fl2, hdo2)
  +hsfl2 = TB.not_false(DST.lmem(s, fl2), L.and_left(Bool.not(DST.lmem(s, fl2)), True{}, disj_app_r(ord, Con{s, Nil{}}, fl2, hdo2)))
  +hn0 = LS.notin_rm(ord, s, Nil{}, SP.nodup_app_l(o2, fl2, hnd2))
  +hn = L.subst(List<&2, Nat>, z => {DST.lmem(s, z) == False{} : Bool}, SC.append(Nat, ord, Nil{}), ord, LL.append_nil(Nat, ord), hn0)
  +lp = AR.slots_length(U32, depth, tp, pfp)
  +lnn = AR.slots_length(U32, depth, tn, pfn)
  +hlk = lk_snoc(ord, s, ps, ns, hnd, hn, TO.alllt_len(ord, ns, P, lnn, hlo), TO.lt_len(s, ps, P, lp, hs), TO.lt_len(s, ns, P, lnn, hs), ST.g_lk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
  +tn1 = AR.upd(U32, depth, tn, s, D.nil())
  +pf1 = AR.upd_perfect(U32, depth, tn, s, D.nil(), pfn)
  +ens = Equal.trans(List<&2, U32>, AR.slots(U32, TS.tnup(depth, tn1, ord, DST.ln(s))), RT.nupd(AR.slots(U32, tn1), ord, DST.ln(s)), RT.nupd(SC.update(U32, ns, s, D.nil()), ord, DST.ln(s)),
    TS.tnup_slots(depth, tn1, ord, DST.ln(s), pf1, hlo),
    Equal.cong(List<&2, U32>, List<&2, U32>, z => RT.nupd(z, ord, DST.ln(s)), AR.slots(U32, tn1), SC.update(U32, ns, s, D.nil()), AR.upd_slots(U32, depth, tn, s, D.nil(), hs, pfn)))
  +eps = AR.upd_slots(U32, depth, tp, s, LK.lastl(ord, D.nil()), hs, pfp)
  +h11 = L.subst(List<&2, U32>, z => {DST.lk(o2, D.nil(), D.nil(), AR.slots(U32, AR.upd(U32, depth, tp, s, LK.lastl(ord, D.nil()))), z) == True{} : Bool}, RT.nupd(SC.update(U32, ns, s, D.nil()), ord, DST.ln(s)), AR.slots(U32, TS.tnup(depth, tn1, ord, DST.ln(s))), Equal.sym(List<&2, U32>, AR.slots(U32, TS.tnup(depth, tn1, ord, DST.ln(s))), RT.nupd(SC.update(U32, ns, s, D.nil()), ord, DST.ln(s)), ens),
    L.subst(List<&2, U32>, z => {DST.lk(o2, D.nil(), D.nil(), z, RT.nupd(SC.update(U32, ns, s, D.nil()), ord, DST.ln(s))) == True{} : Bool}, SC.update(U32, ps, s, LK.lastl(ord, D.nil())), AR.slots(U32, AR.upd(U32, depth, tp, s, LK.lastl(ord, D.nil()))), Equal.sym(List<&2, U32>, AR.slots(U32, AR.upd(U32, depth, tp, s, LK.lastl(ord, D.nil()))), SC.update(U32, ps, s, LK.lastl(ord, D.nil())), eps), hlk))
  +h12 = Equal.trans(Bool, ST.fk(fl2, AR.slots(U32, TS.tnup(depth, tn1, ord, DST.ln(s)))), ST.fk(fl2, RT.nupd(SC.update(U32, ns, s, D.nil()), ord, DST.ln(s))), True{},
    Equal.cong(List<&2, U32>, Bool, z => ST.fk(fl2, z), AR.slots(U32, TS.tnup(depth, tn1, ord, DST.ln(s))), RT.nupd(SC.update(U32, ns, s, D.nil()), ord, DST.ln(s)), ens),
    Equal.trans(Bool, ST.fk(fl2, RT.nupd(SC.update(U32, ns, s, D.nil()), ord, DST.ln(s))), ST.fk(fl2, SC.update(U32, ns, s, D.nil())), True{},
      LS.fk_frame_nupd(fl2, SC.update(U32, ns, s, D.nil()), ord, DST.ln(s), hdo),
      Equal.trans(Bool, ST.fk(fl2, SC.update(U32, ns, s, D.nil())), ST.fk(fl2, ns), True{}, LS.fk_frame(fl2, ns, s, D.nil(), hsfl2), hfk2)))
  +lke = AR.slots_length(F.Slot<V>, depth, te, pfe)
  +hle = L.subst(Nat, z => {Nat.is_lt(s, z) == True{} : Bool}, P, SC.length(F.Slot<V>, es), Equal.sym(Nat, SC.length(F.Slot<V>, es), P, lke), hs)
  +h13 = L.subst(List<&2, F.Slot<V>>, z => {ST.all_occ(V, z, o2) == True{} : Bool}, SC.update(F.Slot<V>, es, s, e), AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), Equal.sym(List<&2, F.Slot<V>>, AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), SC.update(F.Slot<V>, es, s, e), AR.upd_slots(F.Slot<V>, depth, te, s, e, hs, pfe)), occ_snoc(V, es, ord, s, e, hn, ST.g_occ(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), hle, ho))
  +lkk = AR.slots_length(String, depth, tk, pfk)
  +hlk2 = L.subst(Nat, z => {Nat.is_lt(s, z) == True{} : Bool}, P, SC.length(String, ks), Equal.sym(Nat, SC.length(String, ks), P, lkk), hs)
  +eks = AR.upd_slots(String, depth, tk, s, key, hs, pfk)
  +t2 = Map.set(&2, Maybe<&2, U32>, table, key, Some{U32.from_nat(s)})
  +h14 = L.subst(List<&2, String>, z => {ST.all_mapped(t2, z, o2) == True{} : Bool}, SC.update(String, ks, s, key), AR.slots(String, AR.upd(String, depth, tk, s, key)), Equal.sym(List<&2, String>, AR.slots(String, AR.upd(String, depth, tk, s, key)), SC.update(String, ks, s, key), eks), am_snoc(table, ks, ord, s, key, hn, ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), hlk2, hno, crit))
  +h15 = L.subst(List<&2, String>, z => {Inv.included(Map.keys(&2, Maybe<&2, U32>, t2), ST.keys_at(z, o2)) == True{} : Bool}, SC.update(String, ks, s, key), AR.slots(String, AR.upd(String, depth, tk, s, key)), Equal.sym(List<&2, String>, AR.slots(String, AR.upd(String, depth, tk, s, key)), SC.update(String, ks, s, key), eks), incl_snoc(table, ks, ord, s, key, hn, hlk2, crit, pop, ST.g_incl(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)))
  ST.inv_mk(~V, cap, fresh2, depth, life, CT.bt(tc, 0n), t2, AR.upd(String, depth, tk, s, key), AR.upd(F.Slot<V>, depth, te, s, e), AR.upd(U32, depth, tp, s, LK.lastl(ord, D.nil())), TS.tnup(depth, tn1, ord, DST.ln(s)), o2, fl2,
    hd, AR.upd_perfect(String, depth, tk, s, key, pfk), AR.upd_perfect(F.Slot<V>, depth, te, s, e, pfe), AR.upd_perfect(U32, depth, tp, s, LK.lastl(ord, D.nil()), pfp), TS.tnup_pf(depth, tn1, ord, DST.ln(s), pf1), RS.bt_pf(tc, 0n, ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)),
    hfr2, hol2, hfl2, hnd2, hcnt2, h11, h12, h13, h14, h15,
    SetCrit.preserves_critbit(Maybe<&2, U32>, table, key, Some{U32.from_nat(s)}, crit), Pop.set_preserves_populated(U32, table, key, Some{U32.from_nat(s)}, {==}, pop), ST.g_cap(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), hn2)

# ---- the model after inserting ----

def mets_ins(+tc: AR.Tree<U32>, +pfc: {AR.perfect(U32, 4n, tc) == True{} : Bool}) -> {ST.mets(AR.slots(U32, CT.bt(tc, 0n))) == T.bump(0n, ST.mets(AR.slots(U32, tc))) : T.Metrics}:
  +cs = AR.slots(U32, tc)
  Equal.trans(T.Metrics, ST.mets(AR.slots(U32, CT.bt(tc, 0n))), ST.mets(CT.sbt(cs, 0n, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0), DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n)))), T.bump(0n, ST.mets(cs)),
    Equal.cong(List<&2, U32>, T.Metrics, z => ST.mets(z), AR.slots(U32, CT.bt(tc, 0n)), CT.sbt(cs, 0n, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0), DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n))), CT.slots_bt(tc, 0n, pfc, {==})),
    CT.mets_bump_0(cs, RS.len16(tc, 1n, {==}, pfc)))

def ins_model(~V: Data, +cap: U32, +fresh2: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl2: List<&2, Nat>, +s: Nat, +key: String, +v: V, +now: T.Int64, +hs: {Nat.is_lt(s, SC.pow2(depth)) == True{} : Bool}, +hn: {DST.lmem(s, ord) == False{} : Bool}, +pfc: {AR.perfect(U32, 4n, tc) == True{} : Bool}, +pfk: {AR.perfect(String, depth, tk) == True{} : Bool}, +pfe: {AR.perfect(F.Slot<V>, depth, te) == True{} : Bool}) -> {ST.model(~V, ins_sh(V, cap, fresh2, depth, life, tc, table, tk, te, tp, tn, ord, fl2, s, key, AF.entry(~V, life, v, now))) == S.LM{cap, life, S.snoc(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), S.En{key, v, NS.deadline(now, life)}), T.bump(0n, ST.mets(AR.slots(U32, tc)))} : S.Model<V>}:
  +P = SC.pow2(depth)
  +ks = AR.slots(String, tk)
  +es = AR.slots(F.Slot<V>, te)
  +e = AF.entry(~V, life, v, now)
  +ks2 = SC.update(String, ks, s, key)
  +es2 = SC.update(F.Slot<V>, es, s, e)
  +o2 = SC.append(Nat, ord, Con{s, Nil{}})
  +xs = ST.ents(V, ks, es, ord)
  +hle = L.subst(Nat, z => {Nat.is_lt(s, z) == True{} : Bool}, P, SC.length(F.Slot<V>, es), Equal.sym(Nat, SC.length(F.Slot<V>, es), P, AR.slots_length(F.Slot<V>, depth, te, pfe)), hs)
  +hlk = L.subst(Nat, z => {Nat.is_lt(s, z) == True{} : Bool}, P, SC.length(String, ks), Equal.sym(Nat, SC.length(String, ks), P, AR.slots_length(String, depth, tk, pfk)), hs)
  +es_s = Equal.cong(Maybe<&2, F.Slot<V>>, F.Slot<V>, m => ST.sat_m(V, m), SC.nth(F.Slot<V>, es2, s), Some{e}, LL.nth_update_same(F.Slot<V>, es, s, e, hle))
  +eold = Equal.trans(List<&2, S.Ent<V>>, ST.ents(V, ks2, es2, ord), ST.ents(V, ks, es2, ord), xs, LS.ents_frame_k(V, ks, es2, s, key, ord, hn), LS.ents_frame_e(V, ks, es, s, e, ord, hn))
  +enew = Equal.trans(List<&2, S.Ent<V>>, ST.ents(V, ks2, es2, Con{s, Nil{}}), ST.ent_at(V, key, e, Nil{}), Con{S.En{key, v, NS.deadline(now, life)}, Nil{}},
    Equal.trans(List<&2, S.Ent<V>>, ST.ents(V, ks2, es2, Con{s, Nil{}}), ST.ent_at(V, key, ST.sat(V, es2, s), Nil{}), ST.ent_at(V, key, e, Nil{}),
      Equal.cong(String, List<&2, S.Ent<V>>, z => ST.ent_at(V, z, ST.sat(V, es2, s), Nil{}), ST.kat(ks2, s), key, kat_same(ks, s, key, hlk)),
      Equal.cong(F.Slot<V>, List<&2, S.Ent<V>>, z => ST.ent_at(V, key, z, Nil{}), ST.sat(V, es2, s), e, es_s)),
    AF.entry_ent(~V, key, v, life, now))
  +eents = Equal.trans(List<&2, S.Ent<V>>, ST.ents(V, AR.slots(String, AR.upd(String, depth, tk, s, key)), AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), o2), ST.ents(V, ks2, es2, o2), S.snoc(V, xs, S.En{key, v, NS.deadline(now, life)}),
    Equal.trans(List<&2, S.Ent<V>>, ST.ents(V, AR.slots(String, AR.upd(String, depth, tk, s, key)), AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), o2), ST.ents(V, ks2, AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), o2), ST.ents(V, ks2, es2, o2),
      Equal.cong(List<&2, String>, List<&2, S.Ent<V>>, z => ST.ents(V, z, AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), o2), AR.slots(String, AR.upd(String, depth, tk, s, key)), ks2, AR.upd_slots(String, depth, tk, s, key, hs, pfk)),
      Equal.cong(List<&2, F.Slot<V>>, List<&2, S.Ent<V>>, z => ST.ents(V, ks2, z, o2), AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), es2, AR.upd_slots(F.Slot<V>, depth, te, s, e, hs, pfe))),
    Equal.trans(List<&2, S.Ent<V>>, ST.ents(V, ks2, es2, o2), SC.append(S.Ent<V>, ST.ents(V, ks2, es2, ord), ST.ents(V, ks2, es2, Con{s, Nil{}})), S.snoc(V, xs, S.En{key, v, NS.deadline(now, life)}),
      EN.ents_app(V, ks2, es2, ord, Con{s, Nil{}}),
      Equal.trans(List<&2, S.Ent<V>>, SC.append(S.Ent<V>, ST.ents(V, ks2, es2, ord), ST.ents(V, ks2, es2, Con{s, Nil{}})), SC.append(S.Ent<V>, xs, Con{S.En{key, v, NS.deadline(now, life)}, Nil{}}), S.snoc(V, xs, S.En{key, v, NS.deadline(now, life)}),
        Equal.trans(List<&2, S.Ent<V>>, SC.append(S.Ent<V>, ST.ents(V, ks2, es2, ord), ST.ents(V, ks2, es2, Con{s, Nil{}})), SC.append(S.Ent<V>, xs, ST.ents(V, ks2, es2, Con{s, Nil{}})), SC.append(S.Ent<V>, xs, Con{S.En{key, v, NS.deadline(now, life)}, Nil{}}),
          Equal.cong(List<&2, S.Ent<V>>, List<&2, S.Ent<V>>, z => SC.append(S.Ent<V>, z, ST.ents(V, ks2, es2, Con{s, Nil{}})), ST.ents(V, ks2, es2, ord), xs, eold),
          Equal.cong(List<&2, S.Ent<V>>, List<&2, S.Ent<V>>, z => SC.append(S.Ent<V>, xs, z), ST.ents(V, ks2, es2, Con{s, Nil{}}), Con{S.En{key, v, NS.deadline(now, life)}, Nil{}}, enew)),
        Equal.sym(List<&2, S.Ent<V>>, S.snoc(V, xs, S.En{key, v, NS.deadline(now, life)}), SC.append(S.Ent<V>, xs, Con{S.En{key, v, NS.deadline(now, life)}, Nil{}}), EN.snoc_app(V, xs, S.En{key, v, NS.deadline(now, life)})))))
  Equal.trans(S.Model<V>, S.LM{cap, life, ST.ents(V, AR.slots(String, AR.upd(String, depth, tk, s, key)), AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), o2), ST.mets(AR.slots(U32, CT.bt(tc, 0n)))}, S.LM{cap, life, S.snoc(V, xs, S.En{key, v, NS.deadline(now, life)}), ST.mets(AR.slots(U32, CT.bt(tc, 0n)))}, S.LM{cap, life, S.snoc(V, xs, S.En{key, v, NS.deadline(now, life)}), T.bump(0n, ST.mets(AR.slots(U32, tc)))},
    Equal.cong(List<&2, S.Ent<V>>, S.Model<V>, z => S.LM{cap, life, z, ST.mets(AR.slots(U32, CT.bt(tc, 0n)))}, ST.ents(V, AR.slots(String, AR.upd(String, depth, tk, s, key)), AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, e)), o2), S.snoc(V, xs, S.En{key, v, NS.deadline(now, life)}), eents),
    Equal.cong(T.Metrics, S.Model<V>, z => S.LM{cap, life, S.snoc(V, xs, S.En{key, v, NS.deadline(now, life)}), z}, ST.mets(AR.slots(U32, CT.bt(tc, 0n))), T.bump(0n, ST.mets(AR.slots(U32, tc))), mets_ins(tc, pfc)))

# ---- the three allocation paths ----

# a free slot f0 (the head of the free list) is reused
def ins_free_real(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +f0: Nat, +rest: List<&2, Nat>, +key: String, e: F.Slot<V>, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfc: {AR.perfect(U32, 4n, tc) == True{} : Bool}, +pfk: {AR.perfect(String, depth, tk) == True{} : Bool}, +pfe: {AR.perfect(F.Slot<V>, depth, te) == True{} : Bool}, +pfp: {AR.perfect(U32, depth, tp) == True{} : Bool}, +pfn: {AR.perfect(U32, depth, tn) == True{} : Bool}, +hl: {DST.alllt(ord, SC.pow2(depth)) == True{} : Bool}, +hf0: {Nat.is_lt(f0, SC.pow2(depth)) == True{} : Bool}, +hfk: {ST.fk(Con{f0, rest}, AR.slots(U32, tn)) == True{} : Bool}) -> {F.insert_new(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}}), key, e) == ST.real(~V, ins_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, rest, f0, key, e)) : F.Fast<V>}:
  +ns = AR.slots(U32, tn)
  +enf = Equal.trans(U32, DST.lat(ns, f0), DST.hd_or(rest, D.nil()), DST.hd(rest), NB.ueq_true(DST.lat(ns, f0), DST.hd_or(rest, D.nil()), L.and_left(U32.is_eq(DST.lat(ns, f0), DST.hd_or(rest, D.nil())), ST.fk(rest, ns), hfk)), RM.hd_or_nil(rest))
  +r3 = Equal.trans(F.Fast<V>, F.alloc_free(~V, cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(String, tk), AR.thaw(F.Slot<V>, te), DST.hd(ord), DST.lst(ord), U32.from_nat(f0), AR.thaw(U32, tp), key, e, Array.get(U32, AR.thaw(U32, tn), U32.from_nat(f0))), F.put_new(~V, cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(String, tk), AR.thaw(F.Slot<V>, te), F.CH{DST.hd(ord), DST.lst(ord), DST.lat(ns, f0), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(f0), key, e), ST.real(~V, ins_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, rest, f0, key, e)),
    Equal.cong(Array<U32> & U32, F.Fast<V>, r => F.alloc_free(~V, cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(String, tk), AR.thaw(F.Slot<V>, te), DST.hd(ord), DST.lst(ord), U32.from_nat(f0), AR.thaw(U32, tp), key, e, r), Array.get(U32, AR.thaw(U32, tn), U32.from_nat(f0)), (AR.thaw(U32, tn), DST.lat(ns, f0)), TL.get_at(U32, depth, tn, f0, 0, hd, pfn, hf0)),
    Equal.trans(F.Fast<V>, F.put_new(~V, cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(String, tk), AR.thaw(F.Slot<V>, te), F.CH{DST.hd(ord), DST.lst(ord), DST.lat(ns, f0), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(f0), key, e), F.put_new(~V, cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(String, tk), AR.thaw(F.Slot<V>, te), F.CH{DST.hd(ord), DST.lst(ord), DST.hd(rest), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(f0), key, e), ST.real(~V, ins_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, rest, f0, key, e)),
      Equal.cong(U32, F.Fast<V>, z => F.put_new(~V, cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(String, tk), AR.thaw(F.Slot<V>, te), F.CH{DST.hd(ord), DST.lst(ord), z, AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(f0), key, e), DST.lat(ns, f0), DST.hd(rest), enf),
      put_ok(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, rest, f0, key, e, hd, pfc, pfk, pfe, pfp, pfn, hf0, hl)))
  +r2 = L.subst(U32, z => {F.alloc_free(~V, cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(String, tk), AR.thaw(F.Slot<V>, te), DST.hd(ord), DST.lst(ord), z, AR.thaw(U32, tp), key, e, Array.get(U32, AR.thaw(U32, tn), z)) == ST.real(~V, ins_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, rest, f0, key, e)) : F.Fast<V>}, U32.from_nat(f0), F.slot(DST.ln(f0)), Equal.sym(U32, F.slot(DST.ln(f0)), U32.from_nat(f0), DF.slot_ln(f0, depth, hd, hf0)), r3)
  L.subst(Bool, z => {F.alloc_pick(~V, cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(String, tk), AR.thaw(F.Slot<V>, te), DST.hd(ord), DST.lst(ord), DST.ln(f0), AR.thaw(U32, tp), AR.thaw(U32, tn), key, e, z) == ST.real(~V, ins_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, rest, f0, key, e)) : F.Fast<V>}, False{}, U32.is_eq(DST.ln(f0), F.nil()), Equal.sym(Bool, U32.is_eq(DST.ln(f0), F.nil()), False{}, DF.ln_ne_nil(f0, depth, hd, hf0)), r2)

def room_true(+fresh: Nat, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hroom: {Nat.is_lt(fresh, SC.pow2(depth)) == True{} : Bool}, c: Bool, +ec: {U32.is_lt(U32.from_nat(fresh), U.pow2u(depth)) == c : Bool}) -> {U32.is_lt(U32.from_nat(fresh), U.pow2u(depth)) == True{} : Bool}:
  +e1 = AR.lt_bridge(U32.from_nat(fresh), depth, N.le_lt_trans(depth, 31n, 32n, hd, N.lt_succ(31n)), c, ec)
  +e2 = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(depth)) == c : Bool}, U32.to_nat(U32.from_nat(fresh)), fresh, DF.id_nat(fresh, depth, hd, hroom), e1)
  Equal.trans(Bool, U32.is_lt(U32.from_nat(fresh), U.pow2u(depth)), c, True{}, ec, Equal.trans(Bool, c, Nat.is_lt(fresh, SC.pow2(depth)), True{}, Equal.sym(Bool, Nat.is_lt(fresh, SC.pow2(depth)), c, e2), hroom))

# no free slot, room below 2^depth: the next fresh slot is used
def ins_fresh_real(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +key: String, e: F.Slot<V>, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfc: {AR.perfect(U32, 4n, tc) == True{} : Bool}, +pfk: {AR.perfect(String, depth, tk) == True{} : Bool}, +pfe: {AR.perfect(F.Slot<V>, depth, te) == True{} : Bool}, +pfp: {AR.perfect(U32, depth, tp) == True{} : Bool}, +pfn: {AR.perfect(U32, depth, tn) == True{} : Bool}, +hl: {DST.alllt(ord, SC.pow2(depth)) == True{} : Bool}, +hroom: {Nat.is_lt(fresh, SC.pow2(depth)) == True{} : Bool}) -> {F.insert_new(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}}), key, e) == ST.real(~V, ins_sh(V, cap, 1n+fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, fresh, key, e)) : F.Fast<V>}:
  L.subst(Bool, z => {F.alloc_fresh(~V, cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(String, tk), AR.thaw(F.Slot<V>, te), F.CH{DST.hd(ord), DST.lst(ord), F.nil(), AR.thaw(U32, tp), AR.thaw(U32, tn)}, key, e, z) == ST.real(~V, ins_sh(V, cap, 1n+fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, fresh, key, e)) : F.Fast<V>}, True{}, U32.is_lt(U32.from_nat(fresh), U.pow2u(depth)), Equal.sym(Bool, U32.is_lt(U32.from_nat(fresh), U.pow2u(depth)), True{}, room_true(fresh, depth, hd, hroom, U32.is_lt(U32.from_nat(fresh), U.pow2u(depth)), {==})),
    put_ok(~V, cap, 1n+fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, fresh, key, e, hd, pfc, pfk, pfe, pfp, pfn, hroom, hl))

# no free slot and no room: every array doubles (the new half vacant), then
# the next fresh slot is used
def room_false(+fresh: Nat, +depth: Nat, +hdl: {Nat.is_lt(depth, 31n) == True{} : Bool}, +hfr: {Nat.is_le(fresh, SC.pow2(depth)) == True{} : Bool}, +hfull: {Nat.is_lt(fresh, SC.pow2(depth)) == False{} : Bool}, c: Bool, +ec: {U32.is_lt(U32.from_nat(fresh), U.pow2u(depth)) == c : Bool}) -> {U32.is_lt(U32.from_nat(fresh), U.pow2u(depth)) == False{} : Bool}:
  +hd1 = N.lt_succ_le_succ(depth, 31n, hdl)
  +e1 = AR.lt_bridge(U32.from_nat(fresh), depth, N.lt_trans(depth, 31n, 32n, hdl, N.lt_succ(31n)), c, ec)
  +e2 = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(depth)) == c : Bool}, U32.to_nat(U32.from_nat(fresh)), fresh, DF.id_nat(fresh, 1n+depth, hd1, N.le_lt_trans(fresh, SC.pow2(depth), SC.pow2(1n+depth), hfr, N.pow2_lt_succ(depth))), e1)
  Equal.trans(Bool, U32.is_lt(U32.from_nat(fresh), U.pow2u(depth)), c, False{}, ec, Equal.trans(Bool, c, Nat.is_lt(fresh, SC.pow2(depth)), False{}, Equal.sym(Bool, Nat.is_lt(fresh, SC.pow2(depth)), c, e2), hfull))

def k6(~V: Data, +cap: U32, +n: U32, +fresh2: U32, +size: U32, +depth: Nat, +life: T.Int64, c: Array<U32>, +table: Map<&2, Maybe<&2, U32>>, ks: Array<String>, es: Array<F.Slot<V>>, +h: U32, +t: U32, +f: U32, ps: Array<U32>, ns: Array<U32>, +s: U32, +key: String, e: F.Slot<V>) -> F.Fast<V>:
  F.put_new(~V, cap, n, fresh2, size, depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), c, table, ks, es, F.CH{h, t, f, ps, ns}, s, key, e)

def gk_ok(+tk: AR.Tree<String>, +depth: Nat) -> {F.grow_str(depth, AR.thaw(String, tk)) == AR.thaw(String, AR.TNode{tk, AR.trep(String, depth, "")}) : Array<String>}:
  Equal.cong(Array<String>, Array<String>, z => ANode{AR.thaw(String, tk), z}, Array.new(String, depth, ""), AR.thaw(String, AR.trep(String, depth, "")), AR.new(String, depth, ""))

def ge_ok(~V: Data, +te: AR.Tree<F.Slot<V>>, +depth: Nat) -> {F.grow_ents(~V, depth, AR.thaw(F.Slot<V>, te)) == AR.thaw(F.Slot<V>, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}) : Array<F.Slot<V>>}:
  Equal.cong(Array<F.Slot<V>>, Array<F.Slot<V>>, z => ANode{AR.thaw(F.Slot<V>, te), z}, Array.new(F.Slot<V>, depth, F.Vacant{}), AR.thaw(F.Slot<V>, AR.trep(F.Slot<V>, depth, F.Vacant{})), AR.new(F.Slot<V>, depth, F.Vacant{}))

def gu_ok(+t: AR.Tree<U32>, +depth: Nat) -> {F.grow_u32(depth, AR.thaw(U32, t)) == AR.thaw(U32, AR.TNode{t, AR.trep(U32, depth, 0)}) : Array<U32>}:
  Equal.cong(Array<U32>, Array<U32>, z => ANode{AR.thaw(U32, t), z}, Array.new(U32, depth, 0), AR.thaw(U32, AR.trep(U32, depth, 0)), AR.new(U32, depth, 0))

def ins_grow_real(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +key: String, e: F.Slot<V>, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfc: {AR.perfect(U32, 4n, tc) == True{} : Bool}, +pfk: {AR.perfect(String, depth, tk) == True{} : Bool}, +pfe: {AR.perfect(F.Slot<V>, depth, te) == True{} : Bool}, +pfp: {AR.perfect(U32, depth, tp) == True{} : Bool}, +pfn: {AR.perfect(U32, depth, tn) == True{} : Bool}, +hl: {DST.alllt(ord, SC.pow2(depth)) == True{} : Bool}, +hdl: {Nat.is_lt(depth, 31n) == True{} : Bool}, +hfr: {Nat.is_le(fresh, SC.pow2(depth)) == True{} : Bool}, +hfull: {Nat.is_lt(fresh, SC.pow2(depth)) == False{} : Bool}) -> {F.insert_new(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}}), key, e) == ST.real(~V, ins_sh(V, cap, 1n+fresh, 1n+depth, life, tc, table, AR.TNode{tk, AR.trep(String, depth, "")}, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}, AR.TNode{tp, AR.trep(U32, depth, 0)}, AR.TNode{tn, AR.trep(U32, depth, 0)}, ord, Nil{}, fresh, key, e)) : F.Fast<V>}:
  +n = U32.from_nat(SC.length(Nat, ord))
  +fr2 = U32.from_nat(1n+fresh)
  +sz = U.pow2u(1n+depth)
  +P1 = SC.pow2(1n+depth)
  +hlt = N.pow2_lt_succ(depth)
  +pk2 = L.and_intro(AR.perfect(String, depth, tk), AR.perfect(String, depth, AR.trep(String, depth, "")), pfk, AR.trep_perfect(String, depth, ""))
  +pe2 = L.and_intro(AR.perfect(F.Slot<V>, depth, te), AR.perfect(F.Slot<V>, depth, AR.trep(F.Slot<V>, depth, F.Vacant{})), pfe, AR.trep_perfect(F.Slot<V>, depth, F.Vacant{}))
  +pp2 = L.and_intro(AR.perfect(U32, depth, tp), AR.perfect(U32, depth, AR.trep(U32, depth, 0)), pfp, AR.trep_perfect(U32, depth, 0))
  +pn2 = L.and_intro(AR.perfect(U32, depth, tn), AR.perfect(U32, depth, AR.trep(U32, depth, 0)), pfn, AR.trep_perfect(U32, depth, 0))
  +hs1 = N.le_lt_trans(fresh, SC.pow2(depth), P1, hfr, hlt)
  +hl1 = K.alllt_mono(ord, SC.pow2(depth), P1, N.lt_le(SC.pow2(depth), P1, hlt), hl)
  +r = Equal.trans(F.Fast<V>, k6(~V, cap, n, fr2, sz, 1n+depth, life, AR.thaw(U32, tc), table, F.grow_str(depth, AR.thaw(String, tk)), F.grow_ents(~V, depth, AR.thaw(F.Slot<V>, te)), DST.hd(ord), DST.lst(ord), F.nil(), F.grow_u32(depth, AR.thaw(U32, tp)), F.grow_u32(depth, AR.thaw(U32, tn)), U32.from_nat(fresh), key, e), k6(~V, cap, n, fr2, sz, 1n+depth, life, AR.thaw(U32, tc), table, AR.thaw(String, AR.TNode{tk, AR.trep(String, depth, "")}), F.grow_ents(~V, depth, AR.thaw(F.Slot<V>, te)), DST.hd(ord), DST.lst(ord), F.nil(), F.grow_u32(depth, AR.thaw(U32, tp)), F.grow_u32(depth, AR.thaw(U32, tn)), U32.from_nat(fresh), key, e), ST.real(~V, ins_sh(V, cap, 1n+fresh, 1n+depth, life, tc, table, AR.TNode{tk, AR.trep(String, depth, "")}, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}, AR.TNode{tp, AR.trep(U32, depth, 0)}, AR.TNode{tn, AR.trep(U32, depth, 0)}, ord, Nil{}, fresh, key, e)),
    Equal.cong(Array<String>, F.Fast<V>, z => k6(~V, cap, n, fr2, sz, 1n+depth, life, AR.thaw(U32, tc), table, z, F.grow_ents(~V, depth, AR.thaw(F.Slot<V>, te)), DST.hd(ord), DST.lst(ord), F.nil(), F.grow_u32(depth, AR.thaw(U32, tp)), F.grow_u32(depth, AR.thaw(U32, tn)), U32.from_nat(fresh), key, e), F.grow_str(depth, AR.thaw(String, tk)), AR.thaw(String, AR.TNode{tk, AR.trep(String, depth, "")}), gk_ok(tk, depth)),
    Equal.trans(F.Fast<V>, k6(~V, cap, n, fr2, sz, 1n+depth, life, AR.thaw(U32, tc), table, AR.thaw(String, AR.TNode{tk, AR.trep(String, depth, "")}), F.grow_ents(~V, depth, AR.thaw(F.Slot<V>, te)), DST.hd(ord), DST.lst(ord), F.nil(), F.grow_u32(depth, AR.thaw(U32, tp)), F.grow_u32(depth, AR.thaw(U32, tn)), U32.from_nat(fresh), key, e), k6(~V, cap, n, fr2, sz, 1n+depth, life, AR.thaw(U32, tc), table, AR.thaw(String, AR.TNode{tk, AR.trep(String, depth, "")}), AR.thaw(F.Slot<V>, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}), DST.hd(ord), DST.lst(ord), F.nil(), F.grow_u32(depth, AR.thaw(U32, tp)), F.grow_u32(depth, AR.thaw(U32, tn)), U32.from_nat(fresh), key, e), ST.real(~V, ins_sh(V, cap, 1n+fresh, 1n+depth, life, tc, table, AR.TNode{tk, AR.trep(String, depth, "")}, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}, AR.TNode{tp, AR.trep(U32, depth, 0)}, AR.TNode{tn, AR.trep(U32, depth, 0)}, ord, Nil{}, fresh, key, e)),
      Equal.cong(Array<F.Slot<V>>, F.Fast<V>, z => k6(~V, cap, n, fr2, sz, 1n+depth, life, AR.thaw(U32, tc), table, AR.thaw(String, AR.TNode{tk, AR.trep(String, depth, "")}), z, DST.hd(ord), DST.lst(ord), F.nil(), F.grow_u32(depth, AR.thaw(U32, tp)), F.grow_u32(depth, AR.thaw(U32, tn)), U32.from_nat(fresh), key, e), F.grow_ents(~V, depth, AR.thaw(F.Slot<V>, te)), AR.thaw(F.Slot<V>, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}), ge_ok(~V, te, depth)),
      Equal.trans(F.Fast<V>, k6(~V, cap, n, fr2, sz, 1n+depth, life, AR.thaw(U32, tc), table, AR.thaw(String, AR.TNode{tk, AR.trep(String, depth, "")}), AR.thaw(F.Slot<V>, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}), DST.hd(ord), DST.lst(ord), F.nil(), F.grow_u32(depth, AR.thaw(U32, tp)), F.grow_u32(depth, AR.thaw(U32, tn)), U32.from_nat(fresh), key, e), k6(~V, cap, n, fr2, sz, 1n+depth, life, AR.thaw(U32, tc), table, AR.thaw(String, AR.TNode{tk, AR.trep(String, depth, "")}), AR.thaw(F.Slot<V>, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}), DST.hd(ord), DST.lst(ord), F.nil(), AR.thaw(U32, AR.TNode{tp, AR.trep(U32, depth, 0)}), F.grow_u32(depth, AR.thaw(U32, tn)), U32.from_nat(fresh), key, e), ST.real(~V, ins_sh(V, cap, 1n+fresh, 1n+depth, life, tc, table, AR.TNode{tk, AR.trep(String, depth, "")}, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}, AR.TNode{tp, AR.trep(U32, depth, 0)}, AR.TNode{tn, AR.trep(U32, depth, 0)}, ord, Nil{}, fresh, key, e)),
        Equal.cong(Array<U32>, F.Fast<V>, z => k6(~V, cap, n, fr2, sz, 1n+depth, life, AR.thaw(U32, tc), table, AR.thaw(String, AR.TNode{tk, AR.trep(String, depth, "")}), AR.thaw(F.Slot<V>, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}), DST.hd(ord), DST.lst(ord), F.nil(), z, F.grow_u32(depth, AR.thaw(U32, tn)), U32.from_nat(fresh), key, e), F.grow_u32(depth, AR.thaw(U32, tp)), AR.thaw(U32, AR.TNode{tp, AR.trep(U32, depth, 0)}), gu_ok(tp, depth)),
        Equal.trans(F.Fast<V>, k6(~V, cap, n, fr2, sz, 1n+depth, life, AR.thaw(U32, tc), table, AR.thaw(String, AR.TNode{tk, AR.trep(String, depth, "")}), AR.thaw(F.Slot<V>, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}), DST.hd(ord), DST.lst(ord), F.nil(), AR.thaw(U32, AR.TNode{tp, AR.trep(U32, depth, 0)}), F.grow_u32(depth, AR.thaw(U32, tn)), U32.from_nat(fresh), key, e), k6(~V, cap, n, fr2, sz, 1n+depth, life, AR.thaw(U32, tc), table, AR.thaw(String, AR.TNode{tk, AR.trep(String, depth, "")}), AR.thaw(F.Slot<V>, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}), DST.hd(ord), DST.lst(ord), F.nil(), AR.thaw(U32, AR.TNode{tp, AR.trep(U32, depth, 0)}), AR.thaw(U32, AR.TNode{tn, AR.trep(U32, depth, 0)}), U32.from_nat(fresh), key, e), ST.real(~V, ins_sh(V, cap, 1n+fresh, 1n+depth, life, tc, table, AR.TNode{tk, AR.trep(String, depth, "")}, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}, AR.TNode{tp, AR.trep(U32, depth, 0)}, AR.TNode{tn, AR.trep(U32, depth, 0)}, ord, Nil{}, fresh, key, e)),
          Equal.cong(Array<U32>, F.Fast<V>, z => k6(~V, cap, n, fr2, sz, 1n+depth, life, AR.thaw(U32, tc), table, AR.thaw(String, AR.TNode{tk, AR.trep(String, depth, "")}), AR.thaw(F.Slot<V>, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}), DST.hd(ord), DST.lst(ord), F.nil(), AR.thaw(U32, AR.TNode{tp, AR.trep(U32, depth, 0)}), z, U32.from_nat(fresh), key, e), F.grow_u32(depth, AR.thaw(U32, tn)), AR.thaw(U32, AR.TNode{tn, AR.trep(U32, depth, 0)}), gu_ok(tn, depth)),
          put_ok(~V, cap, 1n+fresh, 1n+depth, life, tc, table, AR.TNode{tk, AR.trep(String, depth, "")}, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}, AR.TNode{tp, AR.trep(U32, depth, 0)}, AR.TNode{tn, AR.trep(U32, depth, 0)}, ord, Nil{}, fresh, key, e, N.lt_succ_le_succ(depth, 31n, hdl), pfc, pk2, pe2, pp2, pn2, hs1, hl1)))))
  L.subst(Bool, z => {F.alloc_fresh(~V, cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(String, tk), AR.thaw(F.Slot<V>, te), F.CH{DST.hd(ord), DST.lst(ord), F.nil(), AR.thaw(U32, tp), AR.thaw(U32, tn)}, key, e, z) == ST.real(~V, ins_sh(V, cap, 1n+fresh, 1n+depth, life, tc, table, AR.TNode{tk, AR.trep(String, depth, "")}, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}, AR.TNode{tp, AR.trep(U32, depth, 0)}, AR.TNode{tn, AR.trep(U32, depth, 0)}, ord, Nil{}, fresh, key, e)) : F.Fast<V>}, False{}, U32.is_lt(U32.from_nat(fresh), U.pow2u(depth)), Equal.sym(Bool, U32.is_lt(U32.from_nat(fresh), U.pow2u(depth)), False{}, room_false(fresh, depth, hdl, hfr, hfull, U32.is_lt(U32.from_nat(fresh), U.pow2u(depth)), {==})), r)

# ---- growing keeps everything the order reads ----

def sat_app(-V: Data, +es: List<&2, F.Slot<V>>, +zs: List<&2, F.Slot<V>>, +x: Nat, +h: {Nat.is_lt(x, SC.length(F.Slot<V>, es)) == True{} : Bool}) -> {ST.sat(V, SC.append(F.Slot<V>, es, zs), x) == ST.sat(V, es, x) : F.Slot<V>}:
  Equal.cong(Maybe<&2, F.Slot<V>>, F.Slot<V>, m => ST.sat_m(V, m), SC.nth(F.Slot<V>, SC.append(F.Slot<V>, es, zs), x), SC.nth(F.Slot<V>, es, x), LL.nth_append_left(F.Slot<V>, es, zs, x, h))

def kat_app(+ks: List<&2, String>, +zs: List<&2, String>, +x: Nat, +h: {Nat.is_lt(x, SC.length(String, ks)) == True{} : Bool}) -> {ST.kat(SC.append(String, ks, zs), x) == ST.kat(ks, x) : String}:
  Equal.cong(Maybe<&2, String>, String, m => L.some_value(String, m, ""), SC.nth(String, SC.append(String, ks, zs), x), SC.nth(String, ks, x), LL.nth_append_left(String, ks, zs, x, h))

def occ_grow(-V: Data, +es: List<&2, F.Slot<V>>, +zs: List<&2, F.Slot<V>>, +ord: List<&2, Nat>, +hl: {DST.alllt(ord, SC.length(F.Slot<V>, es)) == True{} : Bool}) -> {ST.all_occ(V, SC.append(F.Slot<V>, es, zs), ord) == ST.all_occ(V, es, ord) : Bool}:
  match ord:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.trans(Bool, Bool.and(ST.is_occ(V, ST.sat(V, SC.append(F.Slot<V>, es, zs), x)), ST.all_occ(V, SC.append(F.Slot<V>, es, zs), t)), Bool.and(ST.is_occ(V, ST.sat(V, es, x)), ST.all_occ(V, SC.append(F.Slot<V>, es, zs), t)), Bool.and(ST.is_occ(V, ST.sat(V, es, x)), ST.all_occ(V, es, t)),
        Equal.cong(F.Slot<V>, Bool, z => Bool.and(ST.is_occ(V, z), ST.all_occ(V, SC.append(F.Slot<V>, es, zs), t)), ST.sat(V, SC.append(F.Slot<V>, es, zs), x), ST.sat(V, es, x), sat_app(V, es, zs, x, IT.lt_head(x, t, SC.length(F.Slot<V>, es), hl))),
        Equal.cong(Bool, Bool, z => Bool.and(ST.is_occ(V, ST.sat(V, es, x)), z), ST.all_occ(V, SC.append(F.Slot<V>, es, zs), t), ST.all_occ(V, es, t), occ_grow(V, es, zs, t, IT.lt_tail(x, t, SC.length(F.Slot<V>, es), hl))))

def am_grow(+tb: Map<&2, Maybe<&2, U32>>, +ks: List<&2, String>, +zs: List<&2, String>, +ord: List<&2, Nat>, +hl: {DST.alllt(ord, SC.length(String, ks)) == True{} : Bool}) -> {ST.all_mapped(tb, SC.append(String, ks, zs), ord) == ST.all_mapped(tb, ks, ord) : Bool}:
  match ord:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.trans(Bool, Bool.and(ST.mapped(tb, ST.kat(SC.append(String, ks, zs), x), x), ST.all_mapped(tb, SC.append(String, ks, zs), t)), Bool.and(ST.mapped(tb, ST.kat(ks, x), x), ST.all_mapped(tb, SC.append(String, ks, zs), t)), Bool.and(ST.mapped(tb, ST.kat(ks, x), x), ST.all_mapped(tb, ks, t)),
        Equal.cong(String, Bool, z => Bool.and(ST.mapped(tb, z, x), ST.all_mapped(tb, SC.append(String, ks, zs), t)), ST.kat(SC.append(String, ks, zs), x), ST.kat(ks, x), kat_app(ks, zs, x, IT.lt_head(x, t, SC.length(String, ks), hl))),
        Equal.cong(Bool, Bool, z => Bool.and(ST.mapped(tb, ST.kat(ks, x), x), z), ST.all_mapped(tb, SC.append(String, ks, zs), t), ST.all_mapped(tb, ks, t), am_grow(tb, ks, zs, t, IT.lt_tail(x, t, SC.length(String, ks), hl))))

def keys_grow(+ks: List<&2, String>, +zs: List<&2, String>, +ord: List<&2, Nat>, +hl: {DST.alllt(ord, SC.length(String, ks)) == True{} : Bool}) -> {ST.keys_at(SC.append(String, ks, zs), ord) == ST.keys_at(ks, ord) : List<&2, String>}:
  match ord:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.trans(List<&2, String>, Con{ST.kat(SC.append(String, ks, zs), x), ST.keys_at(SC.append(String, ks, zs), t)}, Con{ST.kat(ks, x), ST.keys_at(SC.append(String, ks, zs), t)}, Con{ST.kat(ks, x), ST.keys_at(ks, t)},
        Equal.cong(String, List<&2, String>, z => Con{z, ST.keys_at(SC.append(String, ks, zs), t)}, ST.kat(SC.append(String, ks, zs), x), ST.kat(ks, x), kat_app(ks, zs, x, IT.lt_head(x, t, SC.length(String, ks), hl))),
        Equal.cong(List<&2, String>, List<&2, String>, z => Con{ST.kat(ks, x), z}, ST.keys_at(SC.append(String, ks, zs), t), ST.keys_at(ks, t), keys_grow(ks, zs, t, IT.lt_tail(x, t, SC.length(String, ks), hl))))

def ents_grow(-V: Data, +ks: List<&2, String>, +zk: List<&2, String>, +es: List<&2, F.Slot<V>>, +ze: List<&2, F.Slot<V>>, +ord: List<&2, Nat>, +hlk: {DST.alllt(ord, SC.length(String, ks)) == True{} : Bool}, +hle: {DST.alllt(ord, SC.length(F.Slot<V>, es)) == True{} : Bool}) -> {ST.ents(V, SC.append(String, ks, zk), SC.append(F.Slot<V>, es, ze), ord) == ST.ents(V, ks, es, ord) : List<&2, S.Ent<V>>}:
  match ord:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +ks2 = SC.append(String, ks, zk)
      +es2 = SC.append(F.Slot<V>, es, ze)
      Equal.trans(List<&2, S.Ent<V>>, ST.ent_at(V, ST.kat(ks2, x), ST.sat(V, es2, x), ST.ents(V, ks2, es2, t)), ST.ent_at(V, ST.kat(ks, x), ST.sat(V, es2, x), ST.ents(V, ks2, es2, t)), ST.ents(V, ks, es, Con{x, t}),
        Equal.cong(String, List<&2, S.Ent<V>>, z => ST.ent_at(V, z, ST.sat(V, es2, x), ST.ents(V, ks2, es2, t)), ST.kat(ks2, x), ST.kat(ks, x), kat_app(ks, zk, x, IT.lt_head(x, t, SC.length(String, ks), hlk))),
        Equal.trans(List<&2, S.Ent<V>>, ST.ent_at(V, ST.kat(ks, x), ST.sat(V, es2, x), ST.ents(V, ks2, es2, t)), ST.ent_at(V, ST.kat(ks, x), ST.sat(V, es, x), ST.ents(V, ks2, es2, t)), ST.ents(V, ks, es, Con{x, t}),
          Equal.cong(F.Slot<V>, List<&2, S.Ent<V>>, z => ST.ent_at(V, ST.kat(ks, x), z, ST.ents(V, ks2, es2, t)), ST.sat(V, es2, x), ST.sat(V, es, x), sat_app(V, es, ze, x, IT.lt_head(x, t, SC.length(F.Slot<V>, es), hle))),
          Equal.cong(List<&2, S.Ent<V>>, List<&2, S.Ent<V>>, z => ST.ent_at(V, ST.kat(ks, x), ST.sat(V, es, x), z), ST.ents(V, ks2, es2, t), ST.ents(V, ks, es, t), ents_grow(V, ks, zk, es, ze, t, IT.lt_tail(x, t, SC.length(String, ks), hlk), IT.lt_tail(x, t, SC.length(F.Slot<V>, es), hle)))))

def fk_grow(+xs: List<&2, Nat>, +ns: List<&2, U32>, +ws: List<&2, U32>, +hl: {DST.alllt(xs, SC.length(U32, ns)) == True{} : Bool}) -> {ST.fk(xs, SC.append(U32, ns, ws)) == ST.fk(xs, ns) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.trans(Bool, Bool.and(U32.is_eq(DST.lat(SC.append(U32, ns, ws), x), DST.hd_or(t, D.nil())), ST.fk(t, SC.append(U32, ns, ws))), Bool.and(U32.is_eq(DST.lat(ns, x), DST.hd_or(t, D.nil())), ST.fk(t, SC.append(U32, ns, ws))), Bool.and(U32.is_eq(DST.lat(ns, x), DST.hd_or(t, D.nil())), ST.fk(t, ns)),
        Equal.cong(U32, Bool, z => Bool.and(U32.is_eq(z, DST.hd_or(t, D.nil())), ST.fk(t, SC.append(U32, ns, ws))), DST.lat(SC.append(U32, ns, ws), x), DST.lat(ns, x), GR.lat_app(ns, ws, x, IT.lt_head(x, t, SC.length(U32, ns), hl))),
        Equal.cong(Bool, Bool, z => Bool.and(U32.is_eq(DST.lat(ns, x), DST.hd_or(t, D.nil())), z), ST.fk(t, SC.append(U32, ns, ws)), ST.fk(t, ns), fk_grow(t, ns, ws, IT.lt_tail(x, t, SC.length(U32, ns), hl))))

def eq_true(+b: Bool, +c: Bool, +e: {b == c : Bool}, +h: {c == True{} : Bool}) -> {b == True{} : Bool}:
  Equal.trans(Bool, b, c, True{}, e, h)

def grow_inv(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +hdl: {Nat.is_lt(depth, 31n) == True{} : Bool}) -> {ST.inv(~V, cap, fresh, 1n+depth, life, tc, table, AR.TNode{tk, AR.trep(String, depth, "")}, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}, AR.TNode{tp, AR.trep(U32, depth, 0)}, AR.TNode{tn, AR.trep(U32, depth, 0)}, ord, fl) == True{} : Bool}:
  +P = SC.pow2(depth)
  +hlt = N.pow2_lt_succ(depth)
  +hlo = K.alllt_mono(ord, fresh, P, ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
  +hfo = K.alllt_mono(fl, fresh, P, ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_fllt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
  +pfk = ST.g_tk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)
  +pfe = ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)
  +pfp = ST.g_tp(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)
  +pfn = ST.g_tn(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)
  +ks = AR.slots(String, tk)
  +es = AR.slots(F.Slot<V>, te)
  +ps = AR.slots(U32, tp)
  +ns = AR.slots(U32, tn)
  +zk = AR.slots(String, AR.trep(String, depth, ""))
  +ze = AR.slots(F.Slot<V>, AR.trep(F.Slot<V>, depth, F.Vacant{}))
  +zp = AR.slots(U32, AR.trep(U32, depth, 0))
  +zn = AR.slots(U32, AR.trep(U32, depth, 0))
  +lk_ = AR.slots_length(String, depth, tk, pfk)
  +le_ = AR.slots_length(F.Slot<V>, depth, te, pfe)
  +hlk = L.subst(Nat, z => {DST.alllt(ord, z) == True{} : Bool}, P, SC.length(String, ks), Equal.sym(Nat, SC.length(String, ks), P, lk_), hlo)
  +hle = L.subst(Nat, z => {DST.alllt(ord, z) == True{} : Bool}, P, SC.length(F.Slot<V>, es), Equal.sym(Nat, SC.length(F.Slot<V>, es), P, le_), hlo)
  +hlp = TO.alllt_len(ord, ps, P, AR.slots_length(U32, depth, tp, pfp), hlo)
  +hln = TO.alllt_len(ord, ns, P, AR.slots_length(U32, depth, tn, pfn), hlo)
  +hfn = TO.alllt_len(fl, ns, P, AR.slots_length(U32, depth, tn, pfn), hfo)
  ST.inv_mk(~V, cap, fresh, 1n+depth, life, tc, table, AR.TNode{tk, AR.trep(String, depth, "")}, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}, AR.TNode{tp, AR.trep(U32, depth, 0)}, AR.TNode{tn, AR.trep(U32, depth, 0)}, ord, fl,
    N.lt_succ_le_succ(depth, 31n, hdl),
    L.and_intro(AR.perfect(String, depth, tk), AR.perfect(String, depth, AR.trep(String, depth, "")), pfk, AR.trep_perfect(String, depth, "")),
    L.and_intro(AR.perfect(F.Slot<V>, depth, te), AR.perfect(F.Slot<V>, depth, AR.trep(F.Slot<V>, depth, F.Vacant{})), pfe, AR.trep_perfect(F.Slot<V>, depth, F.Vacant{})),
    L.and_intro(AR.perfect(U32, depth, tp), AR.perfect(U32, depth, AR.trep(U32, depth, 0)), pfp, AR.trep_perfect(U32, depth, 0)),
    L.and_intro(AR.perfect(U32, depth, tn), AR.perfect(U32, depth, AR.trep(U32, depth, 0)), pfn, AR.trep_perfect(U32, depth, 0)),
    ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h),
    N.le_trans(fresh, P, SC.pow2(1n+depth), ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), N.lt_le(P, SC.pow2(1n+depth), hlt)),
    ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_fllt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_nodup(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_count(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h),
    eq_true(DST.lk(ord, D.nil(), D.nil(), SC.append(U32, ps, zp), SC.append(U32, ns, zn)), DST.lk(ord, D.nil(), D.nil(), ps, ns), GR.lk_grow(ord, D.nil(), D.nil(), ps, zp, ns, zn, hlp, hln), ST.g_lk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)),
    eq_true(ST.fk(fl, SC.append(U32, ns, zn)), ST.fk(fl, ns), fk_grow(fl, ns, zn, hfn), ST.g_fk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)),
    eq_true(ST.all_occ(V, SC.append(F.Slot<V>, es, ze), ord), ST.all_occ(V, es, ord), occ_grow(V, es, ze, ord, hle), ST.g_occ(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)),
    eq_true(ST.all_mapped(table, SC.append(String, ks, zk), ord), ST.all_mapped(table, ks, ord), am_grow(table, ks, zk, ord, hlk), ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)),
    L.subst(List<&2, String>, z => {Inv.included(Map.keys(&2, Maybe<&2, U32>, table), z) == True{} : Bool}, ST.keys_at(ks, ord), ST.keys_at(SC.append(String, ks, zk), ord), Equal.sym(List<&2, String>, ST.keys_at(SC.append(String, ks, zk), ord), ST.keys_at(ks, ord), keys_grow(ks, zk, ord, hlk)), ST.g_incl(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)),
    ST.g_crit(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_pop(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_cap(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_n(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))

def grow_model(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {ST.model(~V, ST.Sh{cap, fresh, 1n+depth, life, tc, table, AR.TNode{tk, AR.trep(String, depth, "")}, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}, AR.TNode{tp, AR.trep(U32, depth, 0)}, AR.TNode{tn, AR.trep(U32, depth, 0)}, ord, fl}) == ST.model(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}) : S.Model<V>}:
  +P = SC.pow2(depth)
  +hlo = K.alllt_mono(ord, fresh, P, ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
  +ks = AR.slots(String, tk)
  +es = AR.slots(F.Slot<V>, te)
  +hlk = L.subst(Nat, z => {DST.alllt(ord, z) == True{} : Bool}, P, SC.length(String, ks), Equal.sym(Nat, SC.length(String, ks), P, AR.slots_length(String, depth, tk, ST.g_tk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))), hlo)
  +hle = L.subst(Nat, z => {DST.alllt(ord, z) == True{} : Bool}, P, SC.length(F.Slot<V>, es), Equal.sym(Nat, SC.length(F.Slot<V>, es), P, AR.slots_length(F.Slot<V>, depth, te, ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))), hlo)
  Equal.cong(List<&2, S.Ent<V>>, S.Model<V>, z => S.LM{cap, life, z, ST.mets(AR.slots(U32, tc))}, ST.ents(V, SC.append(String, ks, AR.slots(String, AR.trep(String, depth, ""))), SC.append(F.Slot<V>, es, AR.slots(F.Slot<V>, AR.trep(F.Slot<V>, depth, F.Vacant{}))), ord), ST.ents(V, ks, es, ord), ents_grow(V, ks, AR.slots(String, AR.trep(String, depth, "")), es, AR.slots(F.Slot<V>, AR.trep(F.Slot<V>, depth, F.Vacant{})), ord, hlk, hle))
