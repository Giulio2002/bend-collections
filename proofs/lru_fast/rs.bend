import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../lib/u32.bend as U
import ../../spec/common.bend as SC
import ../../spec/lru_fast.bend as S
import ../../src/lru/fast.bend as F
import support/link_primitives.bend as D
import ../../types/lru_model.bend as T
import ../../src/lru/time.bend as Time
import support/links_state.bend as DST
import support/links_links.bend as LK
import support/links_split.bend as SP
import support/links_retarget.bend as RT
import support/links_rmfacts.bend as RM
import support/links_facts.bend as DF
import support/links_items.bend as IT
import support/links_alive.bend as AL
import support/links_core.bend as K
import support/links_tolist.bend as TL
import support/links_tset.bend as TS
import support/array_ashift.bend as AS2
import ../binary_heap/u32idx.bend as BI
import ../../reference/lru/proofs/map_delete_critbit.bend as DelCrit
import ../../reference/lru/proofs/map_delete_populated.bend as DelPop
import ../../reference/lru/proofs/lookup_refinement.bend as LR
import ./state.bend as ST
import ./table.bend as TB
import ./counts.bend as CT
import ./ents.bend as EN
import ./chain.bend as CHN
import ./lists.bend as LS

# Removing a live slot (F.remove_slot: shared by remove, expiry and eviction):
# the runtime result is the abstraction of the shadow with the slot cut out of
# the order and pushed on the free list; the invariant is preserved; and the
# model loses exactly the slot's entry and counts one eviction or removal.

# ---- array access at a slot below 2^depth ----

def swap_at(-A: Data, +depth: Nat, +t: AR.Tree<A>, +x: Nat, +v: A, +d: A, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pf: {AR.perfect(A, depth, t) == True{} : Bool}, +hx: {Nat.is_lt(x, SC.pow2(depth)) == True{} : Bool}) -> {Array.swap(A, AR.thaw(A, t), U32.from_nat(x), v) == (AR.thaw(A, AR.upd(A, depth, t, x, v)), L.some_value(A, SC.nth(A, AR.slots(A, t), x), d)) : Array<A> & A}:
  +rx = DF.id_nat(x, depth, hd, hx)
  Equal.trans(Array<A> & A, Array.swap(A, AR.thaw(A, t), U32.from_nat(x), v), (AR.thaw(A, AR.upd(A, depth, t, U32.to_nat(U32.from_nat(x)), v)), L.some_value(A, SC.nth(A, AR.slots(A, t), x), d)), (AR.thaw(A, AR.upd(A, depth, t, x, v)), L.some_value(A, SC.nth(A, AR.slots(A, t), x), d)),
    AR.swap(A, depth, t, U32.from_nat(x), v, L.some_value(A, SC.nth(A, AR.slots(A, t), x), d), N.le_lt_trans(depth, 31n, 32n, hd, N.lt_succ(31n)),
      L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(depth)) == True{} : Bool}, x, U32.to_nat(U32.from_nat(x)), Equal.sym(Nat, U32.to_nat(U32.from_nat(x)), x, rx), hx),
      L.subst(Nat, z => {SC.nth(A, AR.slots(A, t), z) == Some{L.some_value(A, SC.nth(A, AR.slots(A, t), x), d)} : Maybe<&2, A>}, x, U32.to_nat(U32.from_nat(x)), Equal.sym(Nat, U32.to_nat(U32.from_nat(x)), x, rx), AS2.tsat(A, depth, t, x, d, pf, hx)),
      pf),
    Equal.cong(Nat, Array<A> & A, z => (AR.thaw(A, AR.upd(A, depth, t, z, v)), L.some_value(A, SC.nth(A, AR.slots(A, t), x), d)), U32.to_nat(U32.from_nat(x)), x, rx))

def sat_sv(-V: Data, m: Maybe<&2, F.Slot<V>>) -> {L.some_value(F.Slot<V>, m, F.Vacant{}) == ST.sat_m(V, m) : F.Slot<V>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# ---- the eviction / removal counter ----

def sbd(+tc: AR.Tree<U32>, +metric: Nat) -> AR.Tree<U32>:
  match metric:
    case 1n:
      CT.bt(tc, 2n)
    case _:
      CT.bt(tc, 4n)

def mi(+metric: Nat) -> Nat:
  match metric:
    case 1n:
      1n
    case _:
      2n

def drop_ok1(+tc: AR.Tree<U32>, p: Nat, +pf: {AR.perfect(U32, 4n, tc) == True{} : Bool}) -> {F.bump_drop(1n+p, AR.thaw(U32, tc)) == AR.thaw(U32, sbd(tc, 1n+p)) : Array<U32>}:
  match p:
    case 0n:
      CT.bump_ok(tc, 1, 2n, {==}, {==}, pf, {==})
    case 1n+q:
      CT.bump_ok(tc, 2, 4n, {==}, {==}, pf, {==})

def drop_ok(+tc: AR.Tree<U32>, metric: Nat, +pf: {AR.perfect(U32, 4n, tc) == True{} : Bool}) -> {F.bump_drop(metric, AR.thaw(U32, tc)) == AR.thaw(U32, sbd(tc, metric)) : Array<U32>}:
  match metric:
    case 0n:
      CT.bump_ok(tc, 2, 4n, {==}, {==}, pf, {==})
    case 1n+p:
      drop_ok1(tc, p, pf)

def bt_hi_pf(+t1: AR.Tree<U32>, +i: Nat, +h: U32, zero: Bool, +pf: {AR.perfect(U32, 4n, t1) == True{} : Bool}) -> {AR.perfect(U32, 4n, CT.bt_hi(t1, i, h, zero)) == True{} : Bool}:
  match zero:
    case True{}:
      AR.upd_perfect(U32, 4n, t1, 1n+i, U32.inc(h), pf)
    case False{}:
      pf

def bt_pf(+tc: AR.Tree<U32>, +i: Nat, +pf: {AR.perfect(U32, 4n, tc) == True{} : Bool}) -> {AR.perfect(U32, 4n, CT.bt(tc, i)) == True{} : Bool}:
  bt_hi_pf(AR.upd(U32, 4n, tc, i, U32.inc(DST.lat(AR.slots(U32, tc), i))), i, DST.lat(AR.slots(U32, tc), 1n+i), U32.is_eq(U32.inc(DST.lat(AR.slots(U32, tc), i)), 0), AR.upd_perfect(U32, 4n, tc, i, U32.inc(DST.lat(AR.slots(U32, tc), i)), pf))

def sbd_pf1(+tc: AR.Tree<U32>, p: Nat, +pf: {AR.perfect(U32, 4n, tc) == True{} : Bool}) -> {AR.perfect(U32, 4n, sbd(tc, 1n+p)) == True{} : Bool}:
  match p:
    case 0n:
      bt_pf(tc, 2n, pf)
    case 1n+q:
      bt_pf(tc, 4n, pf)

def sbd_pf(+tc: AR.Tree<U32>, metric: Nat, +pf: {AR.perfect(U32, 4n, tc) == True{} : Bool}) -> {AR.perfect(U32, 4n, sbd(tc, metric)) == True{} : Bool}:
  match metric:
    case 0n:
      bt_pf(tc, 4n, pf)
    case 1n+p:
      sbd_pf1(tc, p, pf)

def len16(+tc: AR.Tree<U32>, +i: Nat, +hi: {Nat.is_lt(i, 16n) == True{} : Bool}, +pf: {AR.perfect(U32, 4n, tc) == True{} : Bool}) -> {Nat.is_lt(i, SC.length(U32, AR.slots(U32, tc))) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, 16n, SC.length(U32, AR.slots(U32, tc)), Equal.sym(Nat, SC.length(U32, AR.slots(U32, tc)), 16n, AR.slots_length(U32, 4n, tc, pf)), hi)

def mets_drop1(+tc: AR.Tree<U32>, p: Nat, +pf: {AR.perfect(U32, 4n, tc) == True{} : Bool}) -> {ST.mets(AR.slots(U32, sbd(tc, 1n+p))) == T.bump(mi(1n+p), ST.mets(AR.slots(U32, tc))) : T.Metrics}:
  match p:
    case 0n:
      +cs = AR.slots(U32, tc)
      Equal.trans(T.Metrics, ST.mets(AR.slots(U32, CT.bt(tc, 2n))), ST.mets(CT.sbt(cs, 2n, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0), DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n)))), T.bump(1n, ST.mets(cs)),
        Equal.cong(List<&2, U32>, T.Metrics, z => ST.mets(z), AR.slots(U32, CT.bt(tc, 2n)), CT.sbt(cs, 2n, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0), DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n))), CT.slots_bt(tc, 2n, pf, {==})),
        CT.mets_bump_1(cs, len16(tc, 3n, {==}, pf)))
    case 1n+q:
      +cs = AR.slots(U32, tc)
      Equal.trans(T.Metrics, ST.mets(AR.slots(U32, CT.bt(tc, 4n))), ST.mets(CT.sbt(cs, 4n, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0), DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n)))), T.bump(2n, ST.mets(cs)),
        Equal.cong(List<&2, U32>, T.Metrics, z => ST.mets(z), AR.slots(U32, CT.bt(tc, 4n)), CT.sbt(cs, 4n, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0), DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n))), CT.slots_bt(tc, 4n, pf, {==})),
        CT.mets_bump_2(cs, len16(tc, 5n, {==}, pf)))

def mets_drop(+tc: AR.Tree<U32>, metric: Nat, +pf: {AR.perfect(U32, 4n, tc) == True{} : Bool}) -> {ST.mets(AR.slots(U32, sbd(tc, metric))) == T.bump(mi(metric), ST.mets(AR.slots(U32, tc))) : T.Metrics}:
  match metric:
    case 0n:
      +cs = AR.slots(U32, tc)
      Equal.trans(T.Metrics, ST.mets(AR.slots(U32, CT.bt(tc, 4n))), ST.mets(CT.sbt(cs, 4n, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0), DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n)))), T.bump(2n, ST.mets(cs)),
        Equal.cong(List<&2, U32>, T.Metrics, z => ST.mets(z), AR.slots(U32, CT.bt(tc, 4n)), CT.sbt(cs, 4n, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0), DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n))), CT.slots_bt(tc, 4n, pf, {==})),
        CT.mets_bump_2(cs, len16(tc, 5n, {==}, pf)))
    case 1n+p:
      mets_drop1(tc, p, pf)

# ---- counting ----

def len_cut(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>) -> {SC.length(Nat, SC.append(Nat, a, Con{s, b})) == 1n+SC.length(Nat, SC.append(Nat, a, b)) : Nat}:
  +la = SC.length(Nat, a)
  +lb = SC.length(Nat, b)
  Equal.trans(Nat, SC.length(Nat, SC.append(Nat, a, Con{s, b})), Nat.add(la, 1n+lb), 1n+SC.length(Nat, SC.append(Nat, a, b)),
    LL.length_append(Nat, a, Con{s, b}),
    Equal.trans(Nat, Nat.add(la, 1n+lb), 1n+Nat.add(la, lb), 1n+SC.length(Nat, SC.append(Nat, a, b)),
      N.add_succ(la, lb),
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(la, lb), SC.length(Nat, SC.append(Nat, a, b)), Equal.sym(Nat, SC.length(Nat, SC.append(Nat, a, b)), Nat.add(la, lb), LL.length_append(Nat, a, b)))))

# the order is no longer than fresh, which is at most 2^depth <= 2^31
def ord_le(+o: List<&2, Nat>, +fl: List<&2, Nat>, +fresh: Nat, +h: {Nat.is_eq(Nat.add(SC.length(Nat, o), SC.length(Nat, fl)), fresh) == True{} : Bool}) -> {Nat.is_le(SC.length(Nat, o), fresh) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(SC.length(Nat, o), z) == True{} : Bool}, Nat.add(SC.length(Nat, o), SC.length(Nat, fl)), fresh, IT.eq_nat_true(Nat.add(SC.length(Nat, o), SC.length(Nat, fl)), fresh, h), N.le_add_right(SC.length(Nat, o), SC.length(Nat, fl)))

def n_dec(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hle: {Nat.is_le(SC.length(Nat, SC.append(Nat, a, Con{s, b})), SC.pow2(depth)) == True{} : Bool}) -> {U32.sub(U32.from_nat(SC.length(Nat, SC.append(Nat, a, Con{s, b}))), 1) == U32.from_nat(SC.length(Nat, SC.append(Nat, a, b))) : U32}:
  +j = SC.length(Nat, SC.append(Nat, a, Con{s, b}))
  +hpos = L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, 1n+SC.length(Nat, SC.append(Nat, a, b)), j, Equal.sym(Nat, j, 1n+SC.length(Nat, SC.append(Nat, a, b)), len_cut(a, s, b)), N.zero_le(SC.length(Nat, SC.append(Nat, a, b))))
  Equal.trans(U32, U32.sub(U32.from_nat(j), 1), U32.from_nat(Nat.sub(j, 1n)), U32.from_nat(SC.length(Nat, SC.append(Nat, a, b))),
    BI.sub_one(j, 1n+depth, hd, N.le_lt_trans(j, SC.pow2(depth), SC.pow2(1n+depth), hle, N.pow2_lt_succ(depth)), hpos),
    Equal.cong(Nat, U32, z => U32.from_nat(z), Nat.sub(j, 1n), SC.length(Nat, SC.append(Nat, a, b)), RM.cnt_cut(a, s, b)))

# ---- the shadow after removing slot s ----

def rs_sh(-V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +fl: List<&2, Nat>, +metric: Nat) -> ST.Shadow<V>:
  ST.Sh{cap, fresh, depth, life, sbd(tc, metric), Map.del(&2, Maybe<&2, U32>, table, ST.kat(AR.slots(String, tk), s)), tk, AR.upd(F.Slot<V>, depth, te, s, F.Vacant{}), TS.tpup(depth, tp, b, LK.lastl(a, D.nil())), AR.upd(U32, depth, TS.tnup(depth, tn, a, DST.hd_or(b, D.nil())), s, DST.hd(fl)), SC.append(Nat, a, b), Con{s, fl}}

# ---- the runtime ----

def k1(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +o: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, +metric: Nat, r: Array<String> & String) -> F.Fast<V> & Maybe<&2, V>:
  F.rm_key(~V, cap, U32.from_nat(SC.length(Nat, o)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(F.Slot<V>, te), F.CH{DST.hd(o), DST.lst(o), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s), metric, r)

def k2(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +o: List<&2, Nat>, +fl: List<&2, Nat>, +s: Nat, +metric: Nat, r: Array<F.Slot<V>> & F.Slot<V>) -> F.Fast<V> & Maybe<&2, V>:
  F.rm_val(~V, cap, U32.from_nat(SC.length(Nat, o)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), Map.del(&2, Maybe<&2, U32>, table, ST.kat(AR.slots(String, tk), s)), AR.thaw(String, tk), F.CH{DST.hd(o), DST.lst(o), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s), metric, r)

def k3(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +n: U32, c: Array<U32>, ch: F.Chain, v: Maybe<&2, V>) -> F.Fast<V> & Maybe<&2, V>:
  (F.F{cap, n, U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), c, table, AR.thaw(String, tk), AR.thaw(F.Slot<V>, te), ch}, v)

def rs_real(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +fl: List<&2, Nat>, +metric: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfc: {AR.perfect(U32, 4n, tc) == True{} : Bool}, +pfk: {AR.perfect(String, depth, tk) == True{} : Bool}, +pfe: {AR.perfect(F.Slot<V>, depth, te) == True{} : Bool}, +pfp: {AR.perfect(U32, depth, tp) == True{} : Bool}, +pfn: {AR.perfect(U32, depth, tn) == True{} : Bool}, +hs: {Nat.is_lt(s, SC.pow2(depth)) == True{} : Bool}, +hl: {DST.alllt(SC.append(Nat, a, Con{s, b}), SC.pow2(depth)) == True{} : Bool}, +hk: {DST.lk(SC.append(Nat, a, Con{s, b}), D.nil(), D.nil(), AR.slots(U32, tp), AR.slots(U32, tn)) == True{} : Bool}, +hle: {Nat.is_le(SC.length(Nat, SC.append(Nat, a, Con{s, b})), SC.pow2(depth)) == True{} : Bool}) -> {F.remove_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl}), U32.from_nat(s), metric) == (ST.real(~V, rs_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, a, s, b, fl, metric)), F.slot_val(~V, ST.sat(V, AR.slots(F.Slot<V>, te), s))) : F.Fast<V> & Maybe<&2, V>}:
  +o = SC.append(Nat, a, Con{s, b})
  +ab = SC.append(Nat, a, b)
  +k = ST.kat(AR.slots(String, tk), s)
  +sv = L.some_value(F.Slot<V>, SC.nth(F.Slot<V>, AR.slots(F.Slot<V>, te), s), F.Vacant{})
  +te2 = AR.upd(F.Slot<V>, depth, te, s, F.Vacant{})
  +tp2 = TS.tpup(depth, tp, b, LK.lastl(a, D.nil()))
  +tn1 = TS.tnup(depth, tn, a, DST.hd_or(b, D.nil()))
  +table2 = Map.del(&2, Maybe<&2, U32>, table, k)
  +n1 = U32.sub(U32.from_nat(SC.length(Nat, o)), 1)
  +n2 = U32.from_nat(SC.length(Nat, ab))
  +v2 = F.slot_val(~V, ST.sat(V, AR.slots(F.Slot<V>, te), s))
  +ul = CHN.unlink_ok(depth, tp, tn, a, s, b, DST.hd(fl), hd, pfp, pfn, hl, hk)
  +pfr = CHN.push_free_ok(depth, tn1, fl, s, DST.hd(ab), DST.lst(ab), AR.thaw(U32, tp2), hd, TS.tnup_pf(depth, tn, a, DST.hd_or(b, D.nil()), pfn), hs)
  +ech = Equal.trans(F.Chain, F.push_free(F.unlink(F.CH{DST.hd(o), DST.lst(o), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)), U32.from_nat(s)), F.push_free(F.CH{DST.hd(ab), DST.lst(ab), DST.hd(fl), AR.thaw(U32, tp2), AR.thaw(U32, tn1)}, U32.from_nat(s)), F.CH{DST.hd(ab), DST.lst(ab), DST.hd(Con{s, fl}), AR.thaw(U32, tp2), AR.thaw(U32, AR.upd(U32, depth, tn1, s, DST.hd(fl)))},
    Equal.cong(F.Chain, F.Chain, c => F.push_free(c, U32.from_nat(s)), F.unlink(F.CH{DST.hd(o), DST.lst(o), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)), F.CH{DST.hd(ab), DST.lst(ab), DST.hd(fl), AR.thaw(U32, tp2), AR.thaw(U32, tn1)}, ul),
    pfr)
  +e3 = Equal.trans(F.Fast<V> & Maybe<&2, V>, k3(~V, cap, fresh, depth, life, table2, tk, te2, n1, F.bump_drop(metric, AR.thaw(U32, tc)), F.push_free(F.unlink(F.CH{DST.hd(o), DST.lst(o), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)), U32.from_nat(s)), F.slot_val(~V, sv)), k3(~V, cap, fresh, depth, life, table2, tk, te2, n2, F.bump_drop(metric, AR.thaw(U32, tc)), F.push_free(F.unlink(F.CH{DST.hd(o), DST.lst(o), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)), U32.from_nat(s)), F.slot_val(~V, sv)), k3(~V, cap, fresh, depth, life, table2, tk, te2, n2, AR.thaw(U32, sbd(tc, metric)), F.CH{DST.hd(ab), DST.lst(ab), DST.hd(Con{s, fl}), AR.thaw(U32, tp2), AR.thaw(U32, AR.upd(U32, depth, tn1, s, DST.hd(fl)))}, v2),
    Equal.cong(U32, F.Fast<V> & Maybe<&2, V>, z => k3(~V, cap, fresh, depth, life, table2, tk, te2, z, F.bump_drop(metric, AR.thaw(U32, tc)), F.push_free(F.unlink(F.CH{DST.hd(o), DST.lst(o), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)), U32.from_nat(s)), F.slot_val(~V, sv)), n1, n2, n_dec(a, s, b, depth, hd, hle)),
    Equal.trans(F.Fast<V> & Maybe<&2, V>, k3(~V, cap, fresh, depth, life, table2, tk, te2, n2, F.bump_drop(metric, AR.thaw(U32, tc)), F.push_free(F.unlink(F.CH{DST.hd(o), DST.lst(o), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)), U32.from_nat(s)), F.slot_val(~V, sv)), k3(~V, cap, fresh, depth, life, table2, tk, te2, n2, AR.thaw(U32, sbd(tc, metric)), F.push_free(F.unlink(F.CH{DST.hd(o), DST.lst(o), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)), U32.from_nat(s)), F.slot_val(~V, sv)), k3(~V, cap, fresh, depth, life, table2, tk, te2, n2, AR.thaw(U32, sbd(tc, metric)), F.CH{DST.hd(ab), DST.lst(ab), DST.hd(Con{s, fl}), AR.thaw(U32, tp2), AR.thaw(U32, AR.upd(U32, depth, tn1, s, DST.hd(fl)))}, v2),
      Equal.cong(Array<U32>, F.Fast<V> & Maybe<&2, V>, z => k3(~V, cap, fresh, depth, life, table2, tk, te2, n2, z, F.push_free(F.unlink(F.CH{DST.hd(o), DST.lst(o), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)), U32.from_nat(s)), F.slot_val(~V, sv)), F.bump_drop(metric, AR.thaw(U32, tc)), AR.thaw(U32, sbd(tc, metric)), drop_ok(tc, metric, pfc)),
      Equal.trans(F.Fast<V> & Maybe<&2, V>, k3(~V, cap, fresh, depth, life, table2, tk, te2, n2, AR.thaw(U32, sbd(tc, metric)), F.push_free(F.unlink(F.CH{DST.hd(o), DST.lst(o), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)), U32.from_nat(s)), F.slot_val(~V, sv)), k3(~V, cap, fresh, depth, life, table2, tk, te2, n2, AR.thaw(U32, sbd(tc, metric)), F.CH{DST.hd(ab), DST.lst(ab), DST.hd(Con{s, fl}), AR.thaw(U32, tp2), AR.thaw(U32, AR.upd(U32, depth, tn1, s, DST.hd(fl)))}, F.slot_val(~V, sv)), k3(~V, cap, fresh, depth, life, table2, tk, te2, n2, AR.thaw(U32, sbd(tc, metric)), F.CH{DST.hd(ab), DST.lst(ab), DST.hd(Con{s, fl}), AR.thaw(U32, tp2), AR.thaw(U32, AR.upd(U32, depth, tn1, s, DST.hd(fl)))}, v2),
        Equal.cong(F.Chain, F.Fast<V> & Maybe<&2, V>, z => k3(~V, cap, fresh, depth, life, table2, tk, te2, n2, AR.thaw(U32, sbd(tc, metric)), z, F.slot_val(~V, sv)), F.push_free(F.unlink(F.CH{DST.hd(o), DST.lst(o), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)), U32.from_nat(s)), F.CH{DST.hd(ab), DST.lst(ab), DST.hd(Con{s, fl}), AR.thaw(U32, tp2), AR.thaw(U32, AR.upd(U32, depth, tn1, s, DST.hd(fl)))}, ech),
        Equal.cong(F.Slot<V>, F.Fast<V> & Maybe<&2, V>, z => k3(~V, cap, fresh, depth, life, table2, tk, te2, n2, AR.thaw(U32, sbd(tc, metric)), F.CH{DST.hd(ab), DST.lst(ab), DST.hd(Con{s, fl}), AR.thaw(U32, tp2), AR.thaw(U32, AR.upd(U32, depth, tn1, s, DST.hd(fl)))}, F.slot_val(~V, z)), sv, ST.sat(V, AR.slots(F.Slot<V>, te), s), sat_sv(V, SC.nth(F.Slot<V>, AR.slots(F.Slot<V>, te), s))))))
  +e2 = L.subst(Array<F.Slot<V>> & F.Slot<V>, z => {k2(~V, cap, fresh, depth, life, tc, table, tk, tp, tn, o, fl, s, metric, z) == k3(~V, cap, fresh, depth, life, table2, tk, te2, n2, AR.thaw(U32, sbd(tc, metric)), F.CH{DST.hd(ab), DST.lst(ab), DST.hd(Con{s, fl}), AR.thaw(U32, tp2), AR.thaw(U32, AR.upd(U32, depth, tn1, s, DST.hd(fl)))}, v2) : F.Fast<V> & Maybe<&2, V>}, (AR.thaw(F.Slot<V>, te2), sv), Array.swap(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s), F.Vacant{}), Equal.sym(Array<F.Slot<V>> & F.Slot<V>, Array.swap(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s), F.Vacant{}), (AR.thaw(F.Slot<V>, te2), sv), swap_at(F.Slot<V>, depth, te, s, F.Vacant{}, F.Vacant{}, hd, pfe, hs)), e3)
  L.subst(Array<String> & String, z => {k1(~V, cap, fresh, depth, life, tc, table, te, tp, tn, o, fl, s, metric, z) == k3(~V, cap, fresh, depth, life, table2, tk, te2, n2, AR.thaw(U32, sbd(tc, metric)), F.CH{DST.hd(ab), DST.lst(ab), DST.hd(Con{s, fl}), AR.thaw(U32, tp2), AR.thaw(U32, AR.upd(U32, depth, tn1, s, DST.hd(fl)))}, v2) : F.Fast<V> & Maybe<&2, V>}, (AR.thaw(String, tk), k), Array.get(String, AR.thaw(String, tk), U32.from_nat(s)), Equal.sym(Array<String> & String, Array.get(String, AR.thaw(String, tk), U32.from_nat(s)), (AR.thaw(String, tk), k), TL.get_at(String, depth, tk, s, "", hd, pfk, hs)), e2)

# ---- facts about the removed slot ----

def mapped_some(m: Maybe<&2, U32>, +s: Nat, +h: {ST.mapped_m(m, s) == True{} : Bool}) -> {m == Some{U32.from_nat(s)} : Maybe<&2, U32>}:
  match m:
    case None{}:
      Empty.absurd({None{} == Some{U32.from_nat(s)} : Maybe<&2, U32>}, L.false_true(h))
    case Some{x}:
      Equal.cong(U32, Maybe<&2, U32>, z => Some{z}, x, U32.from_nat(s), TB.some_mapped(x, s, h))

def lmem_mid(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>) -> {DST.lmem(s, SC.append(Nat, a, Con{s, b})) == True{} : Bool}:
  L.subst(Bool, z => {z == True{} : Bool}, Bool.or(DST.lmem(s, a), DST.lmem(s, Con{s, b})), DST.lmem(s, SC.append(Nat, a, Con{s, b})), Equal.sym(Bool, DST.lmem(s, SC.append(Nat, a, Con{s, b})), Bool.or(DST.lmem(s, a), DST.lmem(s, Con{s, b})), SP.lmem_app(s, a, Con{s, b})),
    TB.or_true_r(DST.lmem(s, a), DST.lmem(s, Con{s, b}), TB.or_true_l(Nat.is_eq(s, s), DST.lmem(s, b), AL.lmem_self(s))))

def notin_l(+i: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, +h: {DST.lmem(i, SC.append(Nat, a, b)) == False{} : Bool}) -> {DST.lmem(i, a) == False{} : Bool}:
  LK.or_false_l(DST.lmem(i, a), DST.lmem(i, b), L.subst(Bool, z => {z == False{} : Bool}, DST.lmem(i, SC.append(Nat, a, b)), Bool.or(DST.lmem(i, a), DST.lmem(i, b)), SP.lmem_app(i, a, b), h))

def notin_r(+i: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, +h: {DST.lmem(i, SC.append(Nat, a, b)) == False{} : Bool}) -> {DST.lmem(i, b) == False{} : Bool}:
  LK.or_false_r(DST.lmem(i, a), DST.lmem(i, b), L.subst(Bool, z => {z == False{} : Bool}, DST.lmem(i, SC.append(Nat, a, b)), Bool.or(DST.lmem(i, a), DST.lmem(i, b)), SP.lmem_app(i, a, b), h))

def am_l(+t: Map<&2, Maybe<&2, U32>>, +ks: List<&2, String>, +a: List<&2, Nat>, +c: List<&2, Nat>, +h: {ST.all_mapped(t, ks, SC.append(Nat, a, c)) == True{} : Bool}) -> {ST.all_mapped(t, ks, a) == True{} : Bool}:
  L.and_left(ST.all_mapped(t, ks, a), ST.all_mapped(t, ks, c), L.subst(Bool, z => {z == True{} : Bool}, ST.all_mapped(t, ks, SC.append(Nat, a, c)), Bool.and(ST.all_mapped(t, ks, a), ST.all_mapped(t, ks, c)), LS.am_app(t, ks, a, c), h))

def am_r(+t: Map<&2, Maybe<&2, U32>>, +ks: List<&2, String>, +a: List<&2, Nat>, +c: List<&2, Nat>, +h: {ST.all_mapped(t, ks, SC.append(Nat, a, c)) == True{} : Bool}) -> {ST.all_mapped(t, ks, c) == True{} : Bool}:
  L.and_right(ST.all_mapped(t, ks, a), ST.all_mapped(t, ks, c), L.subst(Bool, z => {z == True{} : Bool}, ST.all_mapped(t, ks, SC.append(Nat, a, c)), Bool.and(ST.all_mapped(t, ks, a), ST.all_mapped(t, ks, c)), LS.am_app(t, ks, a, c), h))

def occ_mid(-V: Data, +es: List<&2, F.Slot<V>>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +h: {ST.all_occ(V, es, SC.append(Nat, a, Con{s, b})) == True{} : Bool}) -> {ST.is_occ(V, ST.sat(V, es, s)) == True{} : Bool}:
  L.and_left(ST.is_occ(V, ST.sat(V, es, s)), ST.all_occ(V, es, b), L.and_right(ST.all_occ(V, es, a), ST.all_occ(V, es, Con{s, b}), L.subst(Bool, z => {z == True{} : Bool}, ST.all_occ(V, es, SC.append(Nat, a, Con{s, b})), Bool.and(ST.all_occ(V, es, a), ST.all_occ(V, es, Con{s, b})), LS.occ_app(V, es, a, Con{s, b}), h)))

# the table sends the removed slot's key to the slot
def lk_slot(+t: Map<&2, Maybe<&2, U32>>, +ks: List<&2, String>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +hmap: {ST.all_mapped(t, ks, SC.append(Nat, a, Con{s, b})) == True{} : Bool}) -> {TB.lk(t, ST.kat(ks, s)) == Some{U32.from_nat(s)} : Maybe<&2, U32>}:
  mapped_some(TB.lk(t, ST.kat(ks, s)), s, TB.am_at(t, ks, SC.append(Nat, a, Con{s, b}), s, hmap, lmem_mid(a, s, b)))

# no other slot of the order holds the removed slot's key
def nk_part(+t: Map<&2, Maybe<&2, U32>>, +ks: List<&2, String>, +xs: List<&2, Nat>, +s: Nat, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hs: {Nat.is_lt(s, SC.pow2(depth)) == True{} : Bool}, +hl: {DST.alllt(xs, SC.pow2(depth)) == True{} : Bool}, +hn: {DST.lmem(s, xs) == False{} : Bool}, +hlk: {TB.lk(t, ST.kat(ks, s)) == Some{U32.from_nat(s)} : Maybe<&2, U32>}, +hm: {ST.all_mapped(t, ks, xs) == True{} : Bool}) -> {TB.none_key(ks, xs, ST.kat(ks, s)) == True{} : Bool}:
  TB.nk_all(t, ks, xs, ST.kat(ks, s), Some{U32.from_nat(s)}, hlk, hm, TB.nomap_some(s, xs, depth, hd, hs, hl, hn))

# ---- the model ----

def rs_ents(-V: Data, +depth: Nat, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfe: {AR.perfect(F.Slot<V>, depth, te) == True{} : Bool}, +hs: {Nat.is_lt(s, SC.pow2(depth)) == True{} : Bool}, +hl: {DST.alllt(SC.append(Nat, a, Con{s, b}), SC.pow2(depth)) == True{} : Bool}, +hnd: {DST.nodup(SC.append(Nat, a, Con{s, b})) == True{} : Bool}, +hocc: {ST.all_occ(V, AR.slots(F.Slot<V>, te), SC.append(Nat, a, Con{s, b})) == True{} : Bool}, +hmap: {ST.all_mapped(table, AR.slots(String, tk), SC.append(Nat, a, Con{s, b})) == True{} : Bool}) -> {ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, F.Vacant{})), SC.append(Nat, a, b)) == S.drop(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), SC.append(Nat, a, Con{s, b})), ST.kat(AR.slots(String, tk), s)) : List<&2, S.Ent<V>>}:
  +ks = AR.slots(String, tk)
  +es = AR.slots(F.Slot<V>, te)
  +k = ST.kat(ks, s)
  +ab = SC.append(Nat, a, b)
  +o = SC.append(Nat, a, Con{s, b})
  +P = SC.pow2(depth)
  +hn = LS.notin_rm(a, s, b, hnd)
  +hlk = lk_slot(table, ks, a, s, b, hmap)
  +hla = TL.alllt_l(a, Con{s, b}, P, hl)
  +hlb = L.and_right(Nat.is_lt(s, P), DST.alllt(b, P), TL.alllt_r(a, Con{s, b}, P, hl))
  +hna = nk_part(table, ks, a, s, depth, hd, hs, hla, notin_l(s, a, b, hn), hlk, am_l(table, ks, a, Con{s, b}, hmap))
  +hnb = nk_part(table, ks, b, s, depth, hd, hs, hlb, notin_r(s, a, b, hn), hlk, L.and_right(ST.mapped(table, k, s), ST.all_mapped(table, ks, b), am_r(table, ks, a, Con{s, b}, hmap)))
  Equal.trans(List<&2, S.Ent<V>>, ST.ents(V, ks, AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, F.Vacant{})), ab), ST.ents(V, ks, SC.update(F.Slot<V>, es, s, F.Vacant{}), ab), S.drop(V, ST.ents(V, ks, es, o), k),
    Equal.cong(List<&2, F.Slot<V>>, List<&2, S.Ent<V>>, z => ST.ents(V, ks, z, ab), AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, F.Vacant{})), SC.update(F.Slot<V>, es, s, F.Vacant{}), AR.upd_slots(F.Slot<V>, depth, te, s, F.Vacant{}, hs, pfe)),
    Equal.trans(List<&2, S.Ent<V>>, ST.ents(V, ks, SC.update(F.Slot<V>, es, s, F.Vacant{}), ab), ST.ents(V, ks, es, ab), S.drop(V, ST.ents(V, ks, es, o), k),
      LS.ents_frame_e(V, ks, es, s, F.Vacant{}, ab, hn),
      Equal.sym(List<&2, S.Ent<V>>, S.drop(V, ST.ents(V, ks, es, o), k), ST.ents(V, ks, es, ab), EN.drop_at_slot(V, ks, es, a, s, b, k, hna, hnb, LR.string_reflexive(k), occ_mid(V, es, a, s, b, hocc)))))

def rs_model(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +fl: List<&2, Nat>, +metric: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfc: {AR.perfect(U32, 4n, tc) == True{} : Bool}, +pfe: {AR.perfect(F.Slot<V>, depth, te) == True{} : Bool}, +hs: {Nat.is_lt(s, SC.pow2(depth)) == True{} : Bool}, +hl: {DST.alllt(SC.append(Nat, a, Con{s, b}), SC.pow2(depth)) == True{} : Bool}, +hnd: {DST.nodup(SC.append(Nat, a, Con{s, b})) == True{} : Bool}, +hocc: {ST.all_occ(V, AR.slots(F.Slot<V>, te), SC.append(Nat, a, Con{s, b})) == True{} : Bool}, +hmap: {ST.all_mapped(table, AR.slots(String, tk), SC.append(Nat, a, Con{s, b})) == True{} : Bool}) -> {ST.model(~V, rs_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, a, s, b, fl, metric)) == S.LM{cap, life, S.drop(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), SC.append(Nat, a, Con{s, b})), ST.kat(AR.slots(String, tk), s)), T.bump(mi(metric), ST.mets(AR.slots(U32, tc)))} : S.Model<V>}:
  +ks = AR.slots(String, tk)
  +es = AR.slots(F.Slot<V>, te)
  +k = ST.kat(ks, s)
  +ab = SC.append(Nat, a, b)
  +o = SC.append(Nat, a, Con{s, b})
  +P = SC.pow2(depth)
  +hn = LS.notin_rm(a, s, b, hnd)
  +hlk = lk_slot(table, ks, a, s, b, hmap)
  +hla = TL.alllt_l(a, Con{s, b}, P, hl)
  +hlb = L.and_right(Nat.is_lt(s, P), DST.alllt(b, P), TL.alllt_r(a, Con{s, b}, P, hl))
  +hna = nk_part(table, ks, a, s, depth, hd, hs, hla, notin_l(s, a, b, hn), hlk, am_l(table, ks, a, Con{s, b}, hmap))
  +hnb = nk_part(table, ks, b, s, depth, hd, hs, hlb, notin_r(s, a, b, hn), hlk, L.and_right(ST.mapped(table, k, s), ST.all_mapped(table, ks, b), am_r(table, ks, a, Con{s, b}, hmap)))
  +ee = Equal.trans(List<&2, S.Ent<V>>, ST.ents(V, ks, AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, F.Vacant{})), ab), ST.ents(V, ks, SC.update(F.Slot<V>, es, s, F.Vacant{}), ab), S.drop(V, ST.ents(V, ks, es, o), k),
    Equal.cong(List<&2, F.Slot<V>>, List<&2, S.Ent<V>>, z => ST.ents(V, ks, z, ab), AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, F.Vacant{})), SC.update(F.Slot<V>, es, s, F.Vacant{}), AR.upd_slots(F.Slot<V>, depth, te, s, F.Vacant{}, hs, pfe)),
    Equal.trans(List<&2, S.Ent<V>>, ST.ents(V, ks, SC.update(F.Slot<V>, es, s, F.Vacant{}), ab), ST.ents(V, ks, es, ab), S.drop(V, ST.ents(V, ks, es, o), k),
      LS.ents_frame_e(V, ks, es, s, F.Vacant{}, ab, hn),
      Equal.sym(List<&2, S.Ent<V>>, S.drop(V, ST.ents(V, ks, es, o), k), ST.ents(V, ks, es, ab), EN.drop_at_slot(V, ks, es, a, s, b, k, hna, hnb, LR.string_reflexive(k), occ_mid(V, es, a, s, b, hocc)))))
  Equal.trans(S.Model<V>, S.LM{cap, life, ST.ents(V, ks, AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, F.Vacant{})), ab), ST.mets(AR.slots(U32, sbd(tc, metric)))}, S.LM{cap, life, S.drop(V, ST.ents(V, ks, es, o), k), ST.mets(AR.slots(U32, sbd(tc, metric)))}, S.LM{cap, life, S.drop(V, ST.ents(V, ks, es, o), k), T.bump(mi(metric), ST.mets(AR.slots(U32, tc)))},
    Equal.cong(List<&2, S.Ent<V>>, S.Model<V>, z => S.LM{cap, life, z, ST.mets(AR.slots(U32, sbd(tc, metric)))}, ST.ents(V, ks, AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, F.Vacant{})), ab), S.drop(V, ST.ents(V, ks, es, o), k), ee),
    Equal.cong(T.Metrics, S.Model<V>, z => S.LM{cap, life, S.drop(V, ST.ents(V, ks, es, o), k), z}, ST.mets(AR.slots(U32, sbd(tc, metric))), T.bump(mi(metric), ST.mets(AR.slots(U32, tc))), mets_drop(tc, metric, pfc)))

# ---- the invariant ----

def disj_app_l(+a: List<&2, Nat>, +b: List<&2, Nat>, +ys: List<&2, Nat>, +h: {SP.disj(SC.append(Nat, a, b), ys) == True{} : Bool}) -> {SP.disj(a, ys) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      L.and_intro(Bool.not(DST.lmem(x, ys)), SP.disj(r, ys), L.and_left(Bool.not(DST.lmem(x, ys)), SP.disj(SC.append(Nat, r, b), ys), h), disj_app_l(r, b, ys, L.and_right(Bool.not(DST.lmem(x, ys)), SP.disj(SC.append(Nat, r, b), ys), h)))

def rs_inv(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +fl: List<&2, Nat>, +metric: Nat, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s, b}), fl) == True{} : Bool}) -> {ST.good(~V, rs_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, a, s, b, fl, metric)) == True{} : Bool}:
  +o = SC.append(Nat, a, Con{s, b})
  +ab = SC.append(Nat, a, b)
  +ks = AR.slots(String, tk)
  +es = AR.slots(F.Slot<V>, te)
  +k = ST.kat(ks, s)
  +P = SC.pow2(depth)
  +v = DST.hd(fl)
  +lastv = LK.lastl(a, D.nil())
  +hdb = DST.hd_or(b, D.nil())
  +tn1 = TS.tnup(depth, tn, a, hdb)
  +hd = ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, o, fl, h)
  +pfe = ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, o, fl, h)
  +pfp = ST.g_tp(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, o, fl, h)
  +pfn = ST.g_tn(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, o, fl, h)
  +pfc = ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, o, fl, h)
  +hfr = ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, o, fl, h)
  +hol = ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, o, fl, h)
  +hnd2 = ST.g_nodup(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, o, fl, h)
  +hocc = ST.g_occ(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, o, fl, h)
  +hmap = ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, o, fl, h)
  +crit = ST.g_crit(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, o, fl, h)
  +pop = ST.g_pop(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, o, fl, h)
  +hnd = SP.nodup_app_l(o, fl, hnd2)
  +hn = LS.notin_rm(a, s, b, hnd)
  +hbr = TL.alllt_r(a, Con{s, b}, fresh, hol)
  +hsf = L.and_left(Nat.is_lt(s, fresh), DST.alllt(b, fresh), hbr)
  +hs = N.lt_le_trans(s, fresh, P, hsf, hfr)
  +hlo = K.alllt_mono(o, fresh, P, hfr, hol)
  +hla = TL.alllt_l(a, Con{s, b}, P, hlo)
  +hlb = L.and_right(Nat.is_lt(s, P), DST.alllt(b, P), TL.alllt_r(a, Con{s, b}, P, hlo))
  +h7 = SP.alllt_join(a, b, fresh, TL.alllt_l(a, Con{s, b}, fresh, hol), L.and_right(Nat.is_lt(s, fresh), DST.alllt(b, fresh), hbr))
  +hlab = K.alllt_mono(ab, fresh, P, hfr, h7)
  +h9 = LS.nodup_rm(a, s, b, fl, hnd2)
  +hsfl = TB.not_false(DST.lmem(s, fl), L.and_left(Bool.not(DST.lmem(s, fl)), DST.nodup(fl), SP.nodup_app_r(ab, Con{s, fl}, h9)))
  +hdaf = RM.disj_tail(a, s, fl, disj_app_l(a, b, Con{s, fl}, SP.nodup_disj(ab, Con{s, fl}, h9)))
  +pfn1 = TS.tnup_pf(depth, tn, a, hdb, pfn)
  +ps = AR.slots(U32, tp)
  +ns = AR.slots(U32, tn)
  +PU = RT.pupd(ps, b, lastv)
  +NU = RT.nupd(ns, a, hdb)
  +e1 = TS.tpup_slots(depth, tp, b, lastv, pfp, hlb)
  +e2 = AR.upd_slots(U32, depth, tn1, s, v, hs, pfn1)
  +e3 = TS.tnup_slots(depth, tn, a, hdb, pfn, hla)
  +hlp = L.subst(Nat, z => {DST.alllt(o, z) == True{} : Bool}, P, SC.length(U32, ps), Equal.sym(Nat, SC.length(U32, ps), P, AR.slots_length(U32, depth, tp, pfp)), hlo)
  +hln = L.subst(Nat, z => {DST.alllt(o, z) == True{} : Bool}, P, SC.length(U32, ns), Equal.sym(Nat, SC.length(U32, ns), P, AR.slots_length(U32, depth, tn, pfn)), hlo)
  +r0 = RM.lk_cut(a, s, b, ps, ns, hnd, hlp, hln, ST.g_lk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, o, fl, h))
  +h11 = Equal.trans(Bool, DST.lk(ab, D.nil(), D.nil(), AR.slots(U32, TS.tpup(depth, tp, b, lastv)), AR.slots(U32, AR.upd(U32, depth, tn1, s, v))), DST.lk(ab, D.nil(), D.nil(), PU, AR.slots(U32, AR.upd(U32, depth, tn1, s, v))), True{},
    Equal.cong(List<&2, U32>, Bool, z => DST.lk(ab, D.nil(), D.nil(), z, AR.slots(U32, AR.upd(U32, depth, tn1, s, v))), AR.slots(U32, TS.tpup(depth, tp, b, lastv)), PU, e1),
    Equal.trans(Bool, DST.lk(ab, D.nil(), D.nil(), PU, AR.slots(U32, AR.upd(U32, depth, tn1, s, v))), DST.lk(ab, D.nil(), D.nil(), PU, SC.update(U32, NU, s, v)), True{},
      Equal.trans(Bool, DST.lk(ab, D.nil(), D.nil(), PU, AR.slots(U32, AR.upd(U32, depth, tn1, s, v))), DST.lk(ab, D.nil(), D.nil(), PU, SC.update(U32, AR.slots(U32, tn1), s, v)), DST.lk(ab, D.nil(), D.nil(), PU, SC.update(U32, NU, s, v)),
        Equal.cong(List<&2, U32>, Bool, z => DST.lk(ab, D.nil(), D.nil(), PU, z), AR.slots(U32, AR.upd(U32, depth, tn1, s, v)), SC.update(U32, AR.slots(U32, tn1), s, v), e2),
        Equal.cong(List<&2, U32>, Bool, z => DST.lk(ab, D.nil(), D.nil(), PU, SC.update(U32, z, s, v)), AR.slots(U32, tn1), NU, e3)),
      Equal.trans(Bool, DST.lk(ab, D.nil(), D.nil(), PU, SC.update(U32, NU, s, v)), DST.lk(ab, D.nil(), D.nil(), PU, NU), True{}, LK.lk_frame_n(ab, D.nil(), D.nil(), PU, NU, s, v, hn), r0)))
  +hlt1 = L.subst(Nat, z => {Nat.is_lt(s, z) == True{} : Bool}, P, SC.length(U32, AR.slots(U32, tn1)), Equal.sym(Nat, SC.length(U32, AR.slots(U32, tn1)), P, AR.slots_length(U32, depth, tn1, pfn1)), hs)
  +hfk_tail = Equal.trans(Bool, ST.fk(fl, SC.update(U32, AR.slots(U32, tn1), s, v)), ST.fk(fl, AR.slots(U32, tn1)), True{},
    LS.fk_frame(fl, AR.slots(U32, tn1), s, v, hsfl),
    Equal.trans(Bool, ST.fk(fl, AR.slots(U32, tn1)), ST.fk(fl, NU), True{},
      Equal.cong(List<&2, U32>, Bool, z => ST.fk(fl, z), AR.slots(U32, tn1), NU, e3),
      Equal.trans(Bool, ST.fk(fl, NU), ST.fk(fl, ns), True{}, LS.fk_frame_nupd(fl, ns, a, hdb, hdaf), ST.g_fk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, o, fl, h))))
  +hfk_head = L.subst(U32, z => {U32.is_eq(z, DST.hd_or(fl, D.nil())) == True{} : Bool}, v, DST.lat(SC.update(U32, AR.slots(U32, tn1), s, v), s), Equal.sym(U32, DST.lat(SC.update(U32, AR.slots(U32, tn1), s, v), s), v, LK.lat_same(AR.slots(U32, tn1), s, v, hlt1)),
    RT.eq_self(DST.hd_or(fl, D.nil()), v, Equal.sym(U32, DST.hd_or(fl, D.nil()), v, RM.hd_or_nil(fl))))
  +h12 = L.subst(List<&2, U32>, z => {ST.fk(Con{s, fl}, z) == True{} : Bool}, SC.update(U32, AR.slots(U32, tn1), s, v), AR.slots(U32, AR.upd(U32, depth, tn1, s, v)), Equal.sym(List<&2, U32>, AR.slots(U32, AR.upd(U32, depth, tn1, s, v)), SC.update(U32, AR.slots(U32, tn1), s, v), e2),
    L.and_intro(U32.is_eq(DST.lat(SC.update(U32, AR.slots(U32, tn1), s, v), s), DST.hd_or(fl, D.nil())), ST.fk(fl, SC.update(U32, AR.slots(U32, tn1), s, v)), hfk_head, hfk_tail))
  +h13 = L.subst(List<&2, F.Slot<V>>, z => {ST.all_occ(V, z, ab) == True{} : Bool}, SC.update(F.Slot<V>, es, s, F.Vacant{}), AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, F.Vacant{})), Equal.sym(List<&2, F.Slot<V>>, AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s, F.Vacant{})), SC.update(F.Slot<V>, es, s, F.Vacant{}), AR.upd_slots(F.Slot<V>, depth, te, s, F.Vacant{}, hs, pfe)),
    Equal.trans(Bool, ST.all_occ(V, SC.update(F.Slot<V>, es, s, F.Vacant{}), ab), ST.all_occ(V, es, ab), True{}, LS.occ_frame(V, es, s, F.Vacant{}, ab, hn), LS.occ_cut(V, es, a, s, b, hocc)))
  +hmab = LS.am_cut(table, ks, a, s, b, hmap)
  +h14 = TB.am_del(table, k, ks, ab, crit, nk_part(table, ks, ab, s, depth, hd, hs, hlab, hn, lk_slot(table, ks, a, s, b, hmap), hmab), hmab)
  +lab = SC.length(Nat, ab)
  +lfl = SC.length(Nat, fl)
  +ecount = Equal.trans(Nat, Nat.add(lab, 1n+lfl), 1n+Nat.add(lab, lfl), Nat.add(SC.length(Nat, o), lfl), N.add_succ(lab, lfl), Equal.cong(Nat, Nat, z => Nat.add(z, lfl), 1n+lab, SC.length(Nat, o), Equal.sym(Nat, SC.length(Nat, o), 1n+lab, len_cut(a, s, b))))
  +h10 = L.subst(Nat, z => {Nat.is_eq(z, fresh) == True{} : Bool}, Nat.add(SC.length(Nat, o), lfl), Nat.add(lab, 1n+lfl), Equal.sym(Nat, Nat.add(lab, 1n+lfl), Nat.add(SC.length(Nat, o), lfl), ecount), ST.g_count(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, o, fl, h))
  +h19 = N.le_trans(lab, SC.length(Nat, o), U32.to_nat(cap), L.subst(Nat, z => {Nat.is_le(lab, z) == True{} : Bool}, 1n+lab, SC.length(Nat, o), Equal.sym(Nat, SC.length(Nat, o), 1n+lab, len_cut(a, s, b)), N.le_succ(lab)), ST.g_n(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, o, fl, h))
  ST.inv_mk(~V, cap, fresh, depth, life, sbd(tc, metric), Map.del(&2, Maybe<&2, U32>, table, k), tk, AR.upd(F.Slot<V>, depth, te, s, F.Vacant{}), TS.tpup(depth, tp, b, lastv), AR.upd(U32, depth, tn1, s, v), ab, Con{s, fl},
    hd, ST.g_tk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, o, fl, h), AR.upd_perfect(F.Slot<V>, depth, te, s, F.Vacant{}, pfe), TS.tpup_pf(depth, tp, b, lastv, pfp), AR.upd_perfect(U32, depth, tn1, s, v, pfn1), sbd_pf(tc, metric, pfc), hfr, h7,
    L.and_intro(Nat.is_lt(s, fresh), DST.alllt(fl, fresh), hsf, ST.g_fllt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, o, fl, h)), h9, h10, h11, h12, h13, h14, TB.incl_del(table, ks, a, s, b, crit, pop, ST.g_incl(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, o, fl, h)),
    DelCrit.preserves_critbit(Maybe<&2, U32>, table, k, crit), DelPop.preserves_populated(U32, table, k, pop), ST.g_cap(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, o, fl, h), h19)

# no slot of xs holds the key q of slot s (q equal, as a String, to s's key)
def nk_part_q(+t: Map<&2, Maybe<&2, U32>>, +ks: List<&2, String>, +xs: List<&2, Nat>, +s: Nat, +q: String, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hs: {Nat.is_lt(s, SC.pow2(depth)) == True{} : Bool}, +hl: {DST.alllt(xs, SC.pow2(depth)) == True{} : Bool}, +hn: {DST.lmem(s, xs) == False{} : Bool}, +hlk: {TB.lk(t, q) == Some{U32.from_nat(s)} : Maybe<&2, U32>}, +hm: {ST.all_mapped(t, ks, xs) == True{} : Bool}) -> {TB.none_key(ks, xs, q) == True{} : Bool}:
  TB.nk_all(t, ks, xs, q, Some{U32.from_nat(s)}, hlk, hm, TB.nomap_some(s, xs, depth, hd, hs, hl, hn))
