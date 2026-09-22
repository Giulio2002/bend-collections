import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/array.bend as AR
import ../lib/u32.bend as U
import ../../spec/common.bend as SC
import ../../src/lru/fast.bend as F
import support/link_primitives.bend as D
import ../../types/lru_model.bend as T
import support/links_state.bend as DST
import support/links_facts.bend as DF
import support/links_items.bend as IT
import support/links_nbrs.bend as NB
import support/links_rmfacts.bend as RMF
import support/links_core.bend as K
import ./state.bend as ST
import ./readfacts.bend as RF
import ./rs.bend as RS

# A good shadow is determined by the cache it builds (real_inj): the arrays by
# thaw/freeze, the lifetime by the Stamp round trip, the ghost recency order by
# walking the next links from the head, the ghost free list by walking the free
# chain. So the shadow-form laws pin the abstract state.

def walk(k: Nat, +at: U32, +ns: List<&2, U32>) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      Con{Nat.sub(U32.to_nat(at), 1n), walk(p, DST.lat(ns, Nat.sub(U32.to_nat(at), 1n)), ns)}

def slot_of(+x: Nat, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hx: {Nat.is_lt(x, SC.pow2(depth)) == True{} : Bool}) -> {Nat.sub(U32.to_nat(DST.ln(x)), 1n) == x : Nat}:
  Equal.trans(Nat, Nat.sub(U32.to_nat(DST.ln(x)), 1n), Nat.sub(1n+x, 1n), x, Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), U32.to_nat(DST.ln(x)), 1n+x, DF.ln_nat(x, depth, hd, hx)), N.sub_zero(x))

# the next links along a list, with e after its last element, spell the list
def walk_lk(+xs: List<&2, Nat>, +prev: U32, +e: U32, +ps: List<&2, U32>, +ns: List<&2, U32>, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {DST.alllt(xs, SC.pow2(depth)) == True{} : Bool}, +hk: {DST.lk(xs, prev, e, ps, ns) == True{} : Bool}) -> {walk(SC.length(Nat, xs), DST.hd_or(xs, e), ns) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = IT.lt_head(x, t, SC.pow2(depth), hl)
      +es = slot_of(x, depth, hd, hx)
      +hk2 = L.and_right(U32.is_eq(DST.lat(ps, x), prev), Bool.and(U32.is_eq(DST.lat(ns, x), DST.hd_or(t, e)), DST.lk(t, DST.ln(x), e, ps, ns)), hk)
      +enx = NB.ueq_true(DST.lat(ns, x), DST.hd_or(t, e), L.and_left(U32.is_eq(DST.lat(ns, x), DST.hd_or(t, e)), DST.lk(t, DST.ln(x), e, ps, ns), hk2))
      +ih = walk_lk(t, DST.ln(x), e, ps, ns, depth, hd, IT.lt_tail(x, t, SC.pow2(depth), hl), L.and_right(U32.is_eq(DST.lat(ns, x), DST.hd_or(t, e)), DST.lk(t, DST.ln(x), e, ps, ns), hk2))
      Equal.trans(List<&2, Nat>, Con{Nat.sub(U32.to_nat(DST.ln(x)), 1n), walk(SC.length(Nat, t), DST.lat(ns, Nat.sub(U32.to_nat(DST.ln(x)), 1n)), ns)}, Con{x, walk(SC.length(Nat, t), DST.lat(ns, x), ns)}, Con{x, t},
        Equal.cong(Nat, List<&2, Nat>, z => Con{z, walk(SC.length(Nat, t), DST.lat(ns, z), ns)}, Nat.sub(U32.to_nat(DST.ln(x)), 1n), x, es),
        Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Con{x, z}, walk(SC.length(Nat, t), DST.lat(ns, x), ns), t, Equal.trans(List<&2, Nat>, walk(SC.length(Nat, t), DST.lat(ns, x), ns), walk(SC.length(Nat, t), DST.hd_or(t, e), ns), t, Equal.cong(U32, List<&2, Nat>, z => walk(SC.length(Nat, t), z, ns), DST.lat(ns, x), DST.hd_or(t, e), enx), ih)))

# the free chain spells the free list
def walk_fk(+xs: List<&2, Nat>, +ns: List<&2, U32>, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {DST.alllt(xs, SC.pow2(depth)) == True{} : Bool}, +hk: {ST.fk(xs, ns) == True{} : Bool}) -> {walk(SC.length(Nat, xs), DST.hd_or(xs, D.nil()), ns) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = IT.lt_head(x, t, SC.pow2(depth), hl)
      +es = slot_of(x, depth, hd, hx)
      +enx = NB.ueq_true(DST.lat(ns, x), DST.hd_or(t, D.nil()), L.and_left(U32.is_eq(DST.lat(ns, x), DST.hd_or(t, D.nil())), ST.fk(t, ns), hk))
      +ih = walk_fk(t, ns, depth, hd, IT.lt_tail(x, t, SC.pow2(depth), hl), L.and_right(U32.is_eq(DST.lat(ns, x), DST.hd_or(t, D.nil())), ST.fk(t, ns), hk))
      Equal.trans(List<&2, Nat>, Con{Nat.sub(U32.to_nat(DST.ln(x)), 1n), walk(SC.length(Nat, t), DST.lat(ns, Nat.sub(U32.to_nat(DST.ln(x)), 1n)), ns)}, Con{x, walk(SC.length(Nat, t), DST.lat(ns, x), ns)}, Con{x, t},
        Equal.cong(Nat, List<&2, Nat>, z => Con{z, walk(SC.length(Nat, t), DST.lat(ns, z), ns)}, Nat.sub(U32.to_nat(DST.ln(x)), 1n), x, es),
        Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Con{x, z}, walk(SC.length(Nat, t), DST.lat(ns, x), ns), t, Equal.trans(List<&2, Nat>, walk(SC.length(Nat, t), DST.lat(ns, x), ns), walk(SC.length(Nat, t), DST.hd_or(t, D.nil()), ns), t, Equal.cong(U32, List<&2, Nat>, z => walk(SC.length(Nat, t), z, ns), DST.lat(ns, x), DST.hd_or(t, D.nil()), enx), ih)))

# ---- field readers of the cache ----

def f_cap(~V: Data, f: F.Fast<V>) -> U32:
  F.F{+cap, n, fresh, size, depth, ttl, life, counts, table, kys, ents, ch} = f
  cap

def f_n(~V: Data, f: F.Fast<V>) -> U32:
  F.F{cap, +n, fresh, size, depth, ttl, life, counts, table, kys, ents, ch} = f
  n

def f_fresh(~V: Data, f: F.Fast<V>) -> U32:
  F.F{cap, n, +fresh, size, depth, ttl, life, counts, table, kys, ents, ch} = f
  fresh

def f_depth(~V: Data, f: F.Fast<V>) -> Nat:
  F.F{cap, n, fresh, size, +depth, ttl, life, counts, table, kys, ents, ch} = f
  depth

def f_life(~V: Data, f: F.Fast<V>) -> F.Stamp:
  F.F{cap, n, fresh, size, depth, ttl, +life, counts, table, kys, ents, ch} = f
  life

def f_counts(~V: Data, f: F.Fast<V>) -> AR.Tree<U32>:
  F.F{cap, n, fresh, size, depth, ttl, life, counts, table, kys, ents, ch} = f
  AR.freeze(U32, counts)

def f_table(~V: Data, f: F.Fast<V>) -> Map<&2, Maybe<&2, U32>>:
  F.F{cap, n, fresh, size, depth, ttl, life, counts, +table, kys, ents, ch} = f
  table

def f_kys(~V: Data, f: F.Fast<V>) -> AR.Tree<String>:
  F.F{cap, n, fresh, size, depth, ttl, life, counts, table, kys, ents, ch} = f
  AR.freeze(String, kys)

def f_ents(~V: Data, f: F.Fast<V>) -> AR.Tree<F.Slot<V>>:
  F.F{cap, n, fresh, size, depth, ttl, life, counts, table, kys, ents, ch} = f
  AR.freeze(F.Slot<V>, ents)

def f_head(~V: Data, f: F.Fast<V>) -> U32:
  F.F{cap, n, fresh, size, depth, ttl, life, counts, table, kys, ents, ch} = f
  F.CH{+head, tail, free, prevs, nexts} = ch
  head

def f_free(~V: Data, f: F.Fast<V>) -> U32:
  F.F{cap, n, fresh, size, depth, ttl, life, counts, table, kys, ents, ch} = f
  F.CH{head, tail, +free, prevs, nexts} = ch
  free

def f_prevs(~V: Data, f: F.Fast<V>) -> AR.Tree<U32>:
  F.F{cap, n, fresh, size, depth, ttl, life, counts, table, kys, ents, ch} = f
  F.CH{head, tail, free, prevs, nexts} = ch
  AR.freeze(U32, prevs)

def f_nexts(~V: Data, f: F.Fast<V>) -> AR.Tree<U32>:
  F.F{cap, n, fresh, size, depth, ttl, life, counts, table, kys, ents, ch} = f
  F.CH{head, tail, free, prevs, nexts} = ch
  AR.freeze(U32, nexts)

def sh_eq(-V: Data, +cap1: U32, +cap2: U32, +fresh1: Nat, +fresh2: Nat, +depth1: Nat, +depth2: Nat, +life1: T.Int64, +life2: T.Int64, +tc1: AR.Tree<U32>, +tc2: AR.Tree<U32>, +table1: Map<&2, Maybe<&2, U32>>, +table2: Map<&2, Maybe<&2, U32>>, +tk1: AR.Tree<String>, +tk2: AR.Tree<String>, +te1: AR.Tree<F.Slot<V>>, +te2: AR.Tree<F.Slot<V>>, +tp1: AR.Tree<U32>, +tp2: AR.Tree<U32>, +tn1: AR.Tree<U32>, +tn2: AR.Tree<U32>, +ord1: List<&2, Nat>, +ord2: List<&2, Nat>, +fl1: List<&2, Nat>, +fl2: List<&2, Nat>, +e0: {cap1 == cap2 : U32}, +e1: {fresh1 == fresh2 : Nat}, +e2: {depth1 == depth2 : Nat}, +e3: {life1 == life2 : T.Int64}, +e4: {tc1 == tc2 : AR.Tree<U32>}, +e5: {table1 == table2 : Map<&2, Maybe<&2, U32>>}, +e6: {tk1 == tk2 : AR.Tree<String>}, +e7: {te1 == te2 : AR.Tree<F.Slot<V>>}, +e8: {tp1 == tp2 : AR.Tree<U32>}, +e9: {tn1 == tn2 : AR.Tree<U32>}, +e10: {ord1 == ord2 : List<&2, Nat>}, +e11: {fl1 == fl2 : List<&2, Nat>}) -> {ST.Sh{cap1, fresh1, depth1, life1, tc1, table1, tk1, te1, tp1, tn1, ord1, fl1} == ST.Sh{cap2, fresh2, depth2, life2, tc2, table2, tk2, te2, tp2, tn2, ord2, fl2} : ST.Shadow<V>}:
  L.subst(U32, z => {ST.Sh{cap1, fresh1, depth1, life1, tc1, table1, tk1, te1, tp1, tn1, ord1, fl1} == ST.Sh{z, fresh2, depth2, life2, tc2, table2, tk2, te2, tp2, tn2, ord2, fl2} : ST.Shadow<V>}, cap1, cap2, e0, L.subst(Nat, z => {ST.Sh{cap1, fresh1, depth1, life1, tc1, table1, tk1, te1, tp1, tn1, ord1, fl1} == ST.Sh{cap1, z, depth2, life2, tc2, table2, tk2, te2, tp2, tn2, ord2, fl2} : ST.Shadow<V>}, fresh1, fresh2, e1, L.subst(Nat, z => {ST.Sh{cap1, fresh1, depth1, life1, tc1, table1, tk1, te1, tp1, tn1, ord1, fl1} == ST.Sh{cap1, fresh1, z, life2, tc2, table2, tk2, te2, tp2, tn2, ord2, fl2} : ST.Shadow<V>}, depth1, depth2, e2, L.subst(T.Int64, z => {ST.Sh{cap1, fresh1, depth1, life1, tc1, table1, tk1, te1, tp1, tn1, ord1, fl1} == ST.Sh{cap1, fresh1, depth1, z, tc2, table2, tk2, te2, tp2, tn2, ord2, fl2} : ST.Shadow<V>}, life1, life2, e3, L.subst(AR.Tree<U32>, z => {ST.Sh{cap1, fresh1, depth1, life1, tc1, table1, tk1, te1, tp1, tn1, ord1, fl1} == ST.Sh{cap1, fresh1, depth1, life1, z, table2, tk2, te2, tp2, tn2, ord2, fl2} : ST.Shadow<V>}, tc1, tc2, e4, L.subst(Map<&2, Maybe<&2, U32>>, z => {ST.Sh{cap1, fresh1, depth1, life1, tc1, table1, tk1, te1, tp1, tn1, ord1, fl1} == ST.Sh{cap1, fresh1, depth1, life1, tc1, z, tk2, te2, tp2, tn2, ord2, fl2} : ST.Shadow<V>}, table1, table2, e5, L.subst(AR.Tree<String>, z => {ST.Sh{cap1, fresh1, depth1, life1, tc1, table1, tk1, te1, tp1, tn1, ord1, fl1} == ST.Sh{cap1, fresh1, depth1, life1, tc1, table1, z, te2, tp2, tn2, ord2, fl2} : ST.Shadow<V>}, tk1, tk2, e6, L.subst(AR.Tree<F.Slot<V>>, z => {ST.Sh{cap1, fresh1, depth1, life1, tc1, table1, tk1, te1, tp1, tn1, ord1, fl1} == ST.Sh{cap1, fresh1, depth1, life1, tc1, table1, tk1, z, tp2, tn2, ord2, fl2} : ST.Shadow<V>}, te1, te2, e7, L.subst(AR.Tree<U32>, z => {ST.Sh{cap1, fresh1, depth1, life1, tc1, table1, tk1, te1, tp1, tn1, ord1, fl1} == ST.Sh{cap1, fresh1, depth1, life1, tc1, table1, tk1, te1, z, tn2, ord2, fl2} : ST.Shadow<V>}, tp1, tp2, e8, L.subst(AR.Tree<U32>, z => {ST.Sh{cap1, fresh1, depth1, life1, tc1, table1, tk1, te1, tp1, tn1, ord1, fl1} == ST.Sh{cap1, fresh1, depth1, life1, tc1, table1, tk1, te1, tp1, z, ord2, fl2} : ST.Shadow<V>}, tn1, tn2, e9, L.subst(List<&2, Nat>, z => {ST.Sh{cap1, fresh1, depth1, life1, tc1, table1, tk1, te1, tp1, tn1, ord1, fl1} == ST.Sh{cap1, fresh1, depth1, life1, tc1, table1, tk1, te1, tp1, tn1, z, fl2} : ST.Shadow<V>}, ord1, ord2, e10, L.subst(List<&2, Nat>, z => {ST.Sh{cap1, fresh1, depth1, life1, tc1, table1, tk1, te1, tp1, tn1, ord1, fl1} == ST.Sh{cap1, fresh1, depth1, life1, tc1, table1, tk1, te1, tp1, tn1, ord1, z} : ST.Shadow<V>}, fl1, fl2, e11, {==}))))))))))))

def sub_add_cancel(a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), a) == b : Nat}:
  match a:
    case 0n:
      N.sub_zero(b)
    case 1n+p:
      sub_add_cancel(p, b)

def len_fl(+o: List<&2, Nat>, +fl: List<&2, Nat>, +fresh: Nat, +h: {Nat.is_eq(Nat.add(SC.length(Nat, o), SC.length(Nat, fl)), fresh) == True{} : Bool}) -> {SC.length(Nat, fl) == Nat.sub(fresh, SC.length(Nat, o)) : Nat}:
  +e = IT.eq_nat_true(Nat.add(SC.length(Nat, o), SC.length(Nat, fl)), fresh, h)
  Equal.trans(Nat, SC.length(Nat, fl), Nat.sub(Nat.add(SC.length(Nat, o), SC.length(Nat, fl)), SC.length(Nat, o)), Nat.sub(fresh, SC.length(Nat, o)),
    Equal.sym(Nat, Nat.sub(Nat.add(SC.length(Nat, o), SC.length(Nat, fl)), SC.length(Nat, o)), SC.length(Nat, fl), sub_add_cancel(SC.length(Nat, o), SC.length(Nat, fl))),
    Equal.cong(Nat, Nat, z => Nat.sub(z, SC.length(Nat, o)), Nat.add(SC.length(Nat, o), SC.length(Nat, fl)), fresh, e))

def from_nat_inj(+x: Nat, +y: Nat, +kx: Nat, +ky: Nat, +hkx: {Nat.is_le(kx, 32n) == True{} : Bool}, +hky: {Nat.is_le(ky, 32n) == True{} : Bool}, +hx: {Nat.is_lt(x, SC.pow2(kx)) == True{} : Bool}, +hy: {Nat.is_lt(y, SC.pow2(ky)) == True{} : Bool}, +e: {U32.from_nat(x) == U32.from_nat(y) : U32}) -> {x == y : Nat}:
  Equal.trans(Nat, x, U32.to_nat(U32.from_nat(x)), y, Equal.sym(Nat, U32.to_nat(U32.from_nat(x)), x, U.to_nat_from_nat(x, kx, hkx, hx)),
    Equal.trans(Nat, U32.to_nat(U32.from_nat(x)), U32.to_nat(U32.from_nat(y)), y, Equal.cong(U32, Nat, z => U32.to_nat(z), U32.from_nat(x), U32.from_nat(y), e), U.to_nat_from_nat(y, ky, hky, hy)))

def thaw_inj(-A: Data, +t1: AR.Tree<A>, +t2: AR.Tree<A>, +e: {AR.freeze(A, AR.thaw(A, t1)) == AR.freeze(A, AR.thaw(A, t2)) : AR.Tree<A>}) -> {t1 == t2 : AR.Tree<A>}:
  Equal.trans(AR.Tree<A>, t1, AR.freeze(A, AR.thaw(A, t1)), t2, Equal.sym(AR.Tree<A>, AR.freeze(A, AR.thaw(A, t1)), t1, AR.freeze_thaw(A, t1)), Equal.trans(AR.Tree<A>, AR.freeze(A, AR.thaw(A, t1)), AR.freeze(A, AR.thaw(A, t2)), t2, e, AR.freeze_thaw(A, t2)))

def life_inj(+l1: T.Int64, +l2: T.Int64, +e: {F.int_stamp(l1) == F.int_stamp(l2) : F.Stamp}) -> {l1 == l2 : T.Int64}:
  Equal.trans(T.Int64, l1, F.stamp_int(F.int_stamp(l1)), l2, Equal.sym(T.Int64, F.stamp_int(F.int_stamp(l1)), l1, RF.stamp_iso(l1)), Equal.trans(T.Int64, F.stamp_int(F.int_stamp(l1)), F.stamp_int(F.int_stamp(l2)), l2, Equal.cong(F.Stamp, T.Int64, z => F.stamp_int(z), F.int_stamp(l1), F.int_stamp(l2), e), RF.stamp_iso(l2)))

def ri2(~V: Data, +c1: U32, +f1: Nat, +d1: Nat, +l1: T.Int64, +tc1: AR.Tree<U32>, +tb1: Map<&2, Maybe<&2, U32>>, +tk1: AR.Tree<String>, +te1: AR.Tree<F.Slot<V>>, +tp1: AR.Tree<U32>, +tn1: AR.Tree<U32>, +o1: List<&2, Nat>, +fl1: List<&2, Nat>, b: ST.Shadow<V>, +ga: {ST.inv(~V, c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1) == True{} : Bool}, +gb: {ST.good(~V, b) == True{} : Bool}, +e: {ST.real(~V, ST.Sh{c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1}) == ST.real(~V, b) : F.Fast<V>}) -> {ST.Sh{c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1} == b : ST.Shadow<V>}:
  match b:
    case ST.Sh{+c2, +f2, +d2, +l2, +tc2, +tb2, +tk2, +te2, +tp2, +tn2, +o2, +fl2}:
      +hd1 = ST.g_depth(~V, c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1, ga)
      +hd2 = ST.g_depth(~V, c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2, gb)
      +k1 = N.lt_succ_le_succ(d1, 32n, N.le_lt_trans(d1, 31n, 32n, hd1, N.lt_succ(31n)))
      +k2 = N.lt_succ_le_succ(d2, 32n, N.le_lt_trans(d2, 31n, 32n, hd2, N.lt_succ(31n)))
      +hf1 = N.le_lt_trans(f1, SC.pow2(d1), SC.pow2(1n+d1), ST.g_fresh(~V, c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1, ga), N.pow2_lt_succ(d1))
      +hf2 = N.le_lt_trans(f2, SC.pow2(d2), SC.pow2(1n+d2), ST.g_fresh(~V, c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2, gb), N.pow2_lt_succ(d2))
      +hn1 = N.le_lt_trans(SC.length(Nat, o1), f1, SC.pow2(1n+d1), RS.ord_le(o1, fl1, f1, ST.g_count(~V, c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1, ga)), hf1)
      +hn2 = N.le_lt_trans(SC.length(Nat, o2), f2, SC.pow2(1n+d2), RS.ord_le(o2, fl2, f2, ST.g_count(~V, c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2, gb)), hf2)
      +ecap = Equal.cong(F.Fast<V>, U32, f => f_cap(~V, f), ST.real(~V, ST.Sh{c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1}), ST.real(~V, ST.Sh{c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2}), e)
      +edep = Equal.cong(F.Fast<V>, Nat, f => f_depth(~V, f), ST.real(~V, ST.Sh{c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1}), ST.real(~V, ST.Sh{c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2}), e)
      +elife = life_inj(l1, l2, Equal.cong(F.Fast<V>, F.Stamp, f => f_life(~V, f), ST.real(~V, ST.Sh{c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1}), ST.real(~V, ST.Sh{c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2}), e))
      +etc = thaw_inj(U32, tc1, tc2, Equal.cong(F.Fast<V>, AR.Tree<U32>, f => f_counts(~V, f), ST.real(~V, ST.Sh{c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1}), ST.real(~V, ST.Sh{c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2}), e))
      +etb = Equal.cong(F.Fast<V>, Map<&2, Maybe<&2, U32>>, f => f_table(~V, f), ST.real(~V, ST.Sh{c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1}), ST.real(~V, ST.Sh{c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2}), e)
      +etk = thaw_inj(String, tk1, tk2, Equal.cong(F.Fast<V>, AR.Tree<String>, f => f_kys(~V, f), ST.real(~V, ST.Sh{c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1}), ST.real(~V, ST.Sh{c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2}), e))
      +ete = thaw_inj(F.Slot<V>, te1, te2, Equal.cong(F.Fast<V>, AR.Tree<F.Slot<V>>, f => f_ents(~V, f), ST.real(~V, ST.Sh{c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1}), ST.real(~V, ST.Sh{c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2}), e))
      +etp = thaw_inj(U32, tp1, tp2, Equal.cong(F.Fast<V>, AR.Tree<U32>, f => f_prevs(~V, f), ST.real(~V, ST.Sh{c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1}), ST.real(~V, ST.Sh{c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2}), e))
      +etn = thaw_inj(U32, tn1, tn2, Equal.cong(F.Fast<V>, AR.Tree<U32>, f => f_nexts(~V, f), ST.real(~V, ST.Sh{c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1}), ST.real(~V, ST.Sh{c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2}), e))
      +efr = from_nat_inj(f1, f2, 1n+d1, 1n+d2, k1, k2, hf1, hf2, Equal.cong(F.Fast<V>, U32, f => f_fresh(~V, f), ST.real(~V, ST.Sh{c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1}), ST.real(~V, ST.Sh{c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2}), e))
      +eln = from_nat_inj(SC.length(Nat, o1), SC.length(Nat, o2), 1n+d1, 1n+d2, k1, k2, hn1, hn2, Equal.cong(F.Fast<V>, U32, f => f_n(~V, f), ST.real(~V, ST.Sh{c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1}), ST.real(~V, ST.Sh{c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2}), e))
      +ehd = Equal.cong(F.Fast<V>, U32, f => f_head(~V, f), ST.real(~V, ST.Sh{c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1}), ST.real(~V, ST.Sh{c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2}), e)
      +efh = Equal.cong(F.Fast<V>, U32, f => f_free(~V, f), ST.real(~V, ST.Sh{c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1}), ST.real(~V, ST.Sh{c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2}), e)
      +P1 = SC.pow2(d1)
      +P2 = SC.pow2(d2)
      +w1 = walk_lk(o1, D.nil(), D.nil(), AR.slots(U32, tp1), AR.slots(U32, tn1), d1, hd1, K.alllt_mono(o1, f1, P1, ST.g_fresh(~V, c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1, ga), ST.g_ordlt(~V, c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1, ga)), ST.g_lk(~V, c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1, ga))
      +w2 = walk_lk(o2, D.nil(), D.nil(), AR.slots(U32, tp2), AR.slots(U32, tn2), d2, hd2, K.alllt_mono(o2, f2, P2, ST.g_fresh(~V, c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2, gb), ST.g_ordlt(~V, c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2, gb)), ST.g_lk(~V, c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2, gb))
      +eo = Equal.trans(List<&2, Nat>, o1, walk(SC.length(Nat, o1), DST.hd_or(o1, D.nil()), AR.slots(U32, tn1)), o2, Equal.sym(List<&2, Nat>, walk(SC.length(Nat, o1), DST.hd_or(o1, D.nil()), AR.slots(U32, tn1)), o1, w1),
        Equal.trans(List<&2, Nat>, walk(SC.length(Nat, o1), DST.hd_or(o1, D.nil()), AR.slots(U32, tn1)), walk(SC.length(Nat, o2), DST.hd_or(o2, D.nil()), AR.slots(U32, tn2)), o2,
          Equal.trans(List<&2, Nat>, walk(SC.length(Nat, o1), DST.hd_or(o1, D.nil()), AR.slots(U32, tn1)), walk(SC.length(Nat, o2), DST.hd_or(o1, D.nil()), AR.slots(U32, tn1)), walk(SC.length(Nat, o2), DST.hd_or(o2, D.nil()), AR.slots(U32, tn2)),
            Equal.cong(Nat, List<&2, Nat>, z => walk(z, DST.hd_or(o1, D.nil()), AR.slots(U32, tn1)), SC.length(Nat, o1), SC.length(Nat, o2), eln),
            Equal.trans(List<&2, Nat>, walk(SC.length(Nat, o2), DST.hd_or(o1, D.nil()), AR.slots(U32, tn1)), walk(SC.length(Nat, o2), DST.hd_or(o2, D.nil()), AR.slots(U32, tn1)), walk(SC.length(Nat, o2), DST.hd_or(o2, D.nil()), AR.slots(U32, tn2)),
              Equal.cong(U32, List<&2, Nat>, z => walk(SC.length(Nat, o2), z, AR.slots(U32, tn1)), DST.hd_or(o1, D.nil()), DST.hd_or(o2, D.nil()), Equal.trans(U32, DST.hd_or(o1, D.nil()), DST.hd(o1), DST.hd_or(o2, D.nil()), RMF.hd_or_nil(o1), Equal.trans(U32, DST.hd(o1), DST.hd(o2), DST.hd_or(o2, D.nil()), ehd, Equal.sym(U32, DST.hd_or(o2, D.nil()), DST.hd(o2), RMF.hd_or_nil(o2))))),
              Equal.cong(AR.Tree<U32>, List<&2, Nat>, t => walk(SC.length(Nat, o2), DST.hd_or(o2, D.nil()), AR.slots(U32, t)), tn1, tn2, etn))),
          w2))
      +wf1 = walk_fk(fl1, AR.slots(U32, tn1), d1, hd1, K.alllt_mono(fl1, f1, P1, ST.g_fresh(~V, c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1, ga), ST.g_fllt(~V, c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1, ga)), ST.g_fk(~V, c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1, ga))
      +wf2 = walk_fk(fl2, AR.slots(U32, tn2), d2, hd2, K.alllt_mono(fl2, f2, P2, ST.g_fresh(~V, c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2, gb), ST.g_fllt(~V, c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2, gb)), ST.g_fk(~V, c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2, gb))
      +elf = Equal.trans(Nat, SC.length(Nat, fl1), Nat.sub(f1, SC.length(Nat, o1)), SC.length(Nat, fl2), len_fl(o1, fl1, f1, ST.g_count(~V, c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1, ga)),
        Equal.trans(Nat, Nat.sub(f1, SC.length(Nat, o1)), Nat.sub(f2, SC.length(Nat, o2)), SC.length(Nat, fl2),
          Equal.trans(Nat, Nat.sub(f1, SC.length(Nat, o1)), Nat.sub(f2, SC.length(Nat, o1)), Nat.sub(f2, SC.length(Nat, o2)), Equal.cong(Nat, Nat, z => Nat.sub(z, SC.length(Nat, o1)), f1, f2, efr), Equal.cong(Nat, Nat, z => Nat.sub(f2, z), SC.length(Nat, o1), SC.length(Nat, o2), eln)),
          Equal.sym(Nat, SC.length(Nat, fl2), Nat.sub(f2, SC.length(Nat, o2)), len_fl(o2, fl2, f2, ST.g_count(~V, c2, f2, d2, l2, tc2, tb2, tk2, te2, tp2, tn2, o2, fl2, gb)))))
      +efl = Equal.trans(List<&2, Nat>, fl1, walk(SC.length(Nat, fl1), DST.hd_or(fl1, D.nil()), AR.slots(U32, tn1)), fl2, Equal.sym(List<&2, Nat>, walk(SC.length(Nat, fl1), DST.hd_or(fl1, D.nil()), AR.slots(U32, tn1)), fl1, wf1),
        Equal.trans(List<&2, Nat>, walk(SC.length(Nat, fl1), DST.hd_or(fl1, D.nil()), AR.slots(U32, tn1)), walk(SC.length(Nat, fl2), DST.hd_or(fl2, D.nil()), AR.slots(U32, tn2)), fl2,
          Equal.trans(List<&2, Nat>, walk(SC.length(Nat, fl1), DST.hd_or(fl1, D.nil()), AR.slots(U32, tn1)), walk(SC.length(Nat, fl2), DST.hd_or(fl1, D.nil()), AR.slots(U32, tn1)), walk(SC.length(Nat, fl2), DST.hd_or(fl2, D.nil()), AR.slots(U32, tn2)),
            Equal.cong(Nat, List<&2, Nat>, z => walk(z, DST.hd_or(fl1, D.nil()), AR.slots(U32, tn1)), SC.length(Nat, fl1), SC.length(Nat, fl2), elf),
            Equal.trans(List<&2, Nat>, walk(SC.length(Nat, fl2), DST.hd_or(fl1, D.nil()), AR.slots(U32, tn1)), walk(SC.length(Nat, fl2), DST.hd_or(fl2, D.nil()), AR.slots(U32, tn1)), walk(SC.length(Nat, fl2), DST.hd_or(fl2, D.nil()), AR.slots(U32, tn2)),
              Equal.cong(U32, List<&2, Nat>, z => walk(SC.length(Nat, fl2), z, AR.slots(U32, tn1)), DST.hd_or(fl1, D.nil()), DST.hd_or(fl2, D.nil()), Equal.trans(U32, DST.hd_or(fl1, D.nil()), DST.hd(fl1), DST.hd_or(fl2, D.nil()), RMF.hd_or_nil(fl1), Equal.trans(U32, DST.hd(fl1), DST.hd(fl2), DST.hd_or(fl2, D.nil()), efh, Equal.sym(U32, DST.hd_or(fl2, D.nil()), DST.hd(fl2), RMF.hd_or_nil(fl2))))),
              Equal.cong(AR.Tree<U32>, List<&2, Nat>, t => walk(SC.length(Nat, fl2), DST.hd_or(fl2, D.nil()), AR.slots(U32, t)), tn1, tn2, etn))),
          wf2))
      sh_eq(V, c1, c2, f1, f2, d1, d2, l1, l2, tc1, tc2, tb1, tb2, tk1, tk2, te1, te2, tp1, tp2, tn1, tn2, o1, o2, fl1, fl2, ecap, efr, edep, elife, etc, etb, etk, ete, etp, etn, eo, efl)

def real_inj(~V: Data, a: ST.Shadow<V>, +b: ST.Shadow<V>, +ga: {ST.good(~V, a) == True{} : Bool}, +gb: {ST.good(~V, b) == True{} : Bool}, +e: {ST.real(~V, a) == ST.real(~V, b) : F.Fast<V>}) -> {a == b : ST.Shadow<V>}:
  match a:
    case ST.Sh{+c1, +f1, +d1, +l1, +tc1, +tb1, +tk1, +te1, +tp1, +tn1, +o1, +fl1}:
      ri2(~V, c1, f1, d1, l1, tc1, tb1, tk1, te1, tp1, tn1, o1, fl1, b, ga, gb, e)
