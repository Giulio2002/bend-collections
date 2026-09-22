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
import support/link_primitives.bend as D
import ../../types/lru_model.bend as T
import ../../types/lru_fast.bend as E
import support/links_state.bend as DST
import support/links_split.bend as SP
import support/links_core.bend as K
import support/links_items.bend as IT
import support/links_alive.bend as AL
import support/links_insfacts.bend as IF
import support/links_facts.bend as DF
import ./state.bend as ST
import ./table.bend as TB
import ./ents.bend as EN
import ./rs.bend as RS
import ./remove.bend as RM
import ./insert.bend as INS
import ./addfacts.bend as AF
import ./add.bend as ADD
import ../../reference/lru/proofs/lookup_refinement.bend as LR
import ../../reference/lru/proofs/canonical_string.bend as CS
import ../../reference/lru/proofs/map_delete_frame.bend as DelFrame
import ../../reference/lru/proofs/map_routing.bend as R
import support/links_links.bend as LK
import support/links_tset.bend as TS

# Inserting an absent key when the cache has room: the free list's head is
# reused if there is one, else the next fresh slot, growing the arrays first
# when they are full. The capacity premise to_nat(cap) <= 2^q, q <= 31 bounds
# the arrays (they only grow while fresh < cap).

def ins_room(-V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +key: String, +e: F.Slot<V>, room: Bool) -> ST.Shadow<V>:
  match room:
    case True{}:
      INS.ins_sh(V, cap, 1n+fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, fresh, key, e)
    case False{}:
      INS.ins_sh(V, cap, 1n+fresh, 1n+depth, life, tc, table, AR.TNode{tk, AR.trep(String, depth, "")}, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}, AR.TNode{tp, AR.trep(U32, depth, 0)}, AR.TNode{tn, AR.trep(U32, depth, 0)}, ord, Nil{}, fresh, key, e)

def ins_fl(-V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, fl: List<&2, Nat>, +key: String, +e: F.Slot<V>) -> ST.Shadow<V>:
  match fl:
    case Con{+f0, +rest}:
      INS.ins_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, rest, f0, key, e)
    case Nil{}:
      ins_room(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, key, e, Nat.is_lt(fresh, SC.pow2(depth)))

def ins_g(-V: Data, sh: ST.Shadow<V>, +key: String, +e: F.Slot<V>) -> ST.Shadow<V>:
  match sh:
    case ST.Sh{+cap, +fresh, +depth, +life, +tc, +table, +tk, +te, +tp, +tn, +ord, fl}:
      ins_fl(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, e)

# ---- arithmetic for the room / growth decision ----

def lt_of_pow2(+d: Nat, +q: Nat, +h: {Nat.is_lt(SC.pow2(d), SC.pow2(q)) == True{} : Bool}, c: Bool, +ec: {Nat.is_lt(d, q) == c : Bool}) -> {Nat.is_lt(d, q) == True{} : Bool}:
  match c:
    case True{}:
      ec
    case False{}:
      +hle = N.pow2_mono(q, d, N.not_lt_le(d, q, ec))
      Empty.absurd({Nat.is_lt(d, q) == True{} : Bool}, L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(SC.pow2(d), SC.pow2(d)), True{}, Equal.sym(Bool, Nat.is_lt(SC.pow2(d), SC.pow2(d)), False{}, N.lt_irrefl(SC.pow2(d))), N.lt_le_trans(SC.pow2(d), SC.pow2(q), SC.pow2(d), h, hle))))

# the order is as long as fresh when the free list is empty
def len_fresh(+ord: List<&2, Nat>, +fresh: Nat, +h: {Nat.is_eq(Nat.add(SC.length(Nat, ord), SC.length(Nat, Nil{})), fresh) == True{} : Bool}) -> {SC.length(Nat, ord) == fresh : Nat}:
  Equal.trans(Nat, SC.length(Nat, ord), Nat.add(SC.length(Nat, ord), 0n), fresh, Equal.sym(Nat, Nat.add(SC.length(Nat, ord), 0n), SC.length(Nat, ord), N.add_zero(SC.length(Nat, ord))), IT.eq_nat_true(Nat.add(SC.length(Nat, ord), 0n), fresh, h))

def grow_depth(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}, +hroom: {Nat.is_lt(SC.length(Nat, ord), U32.to_nat(cap)) == True{} : Bool}, +hfull: {Nat.is_lt(fresh, SC.pow2(depth)) == False{} : Bool}) -> {Nat.is_lt(depth, 31n) == True{} : Bool}:
  +elen = len_fresh(ord, fresh, ST.g_count(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h))
  +hfc = L.subst(Nat, z => {Nat.is_lt(z, U32.to_nat(cap)) == True{} : Bool}, SC.length(Nat, ord), fresh, elen, hroom)
  +hp = N.le_lt_trans(SC.pow2(depth), fresh, SC.pow2(q), N.not_lt_le(fresh, SC.pow2(depth), hfull), N.lt_le_trans(fresh, U32.to_nat(cap), SC.pow2(q), hfc, hcq))
  N.lt_le_trans(depth, q, 31n, lt_of_pow2(depth, q, hp, Nat.is_lt(depth, q), {==}), hq)

# ---- the runtime ----

def insr_real(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +key: String, e: F.Slot<V>, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}, +hroom: {Nat.is_lt(SC.length(Nat, ord), U32.to_nat(cap)) == True{} : Bool}, room: Bool, +er: {Nat.is_lt(fresh, SC.pow2(depth)) == room : Bool}) -> {F.insert_new(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}}), key, e) == ST.real(~V, ins_room(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, key, e, room)) : F.Fast<V>}:
  match room:
    case True{}:
      INS.ins_fresh_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, key, e, ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h), ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h), ST.g_tk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h), ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h), ST.g_tp(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h), ST.g_tn(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h), K.alllt_mono(ord, fresh, SC.pow2(depth), ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h), ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h)), er)
    case False{}:
      INS.ins_grow_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, key, e, ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h), ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h), ST.g_tk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h), ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h), ST.g_tp(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h), ST.g_tn(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h), K.alllt_mono(ord, fresh, SC.pow2(depth), ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h), ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h)), grow_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, h, q, hq, hcq, hroom, er), ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h), er)

def insf_real(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, fl: List<&2, Nat>, +key: String, e: F.Slot<V>, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}, +hroom: {Nat.is_lt(SC.length(Nat, ord), U32.to_nat(cap)) == True{} : Bool}) -> {F.insert_new(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, e) == ST.real(~V, ins_fl(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, e)) : F.Fast<V>}:
  match fl:
    case Con{+f0, +rest}:
      +hf0 = N.lt_le_trans(f0, fresh, SC.pow2(depth), L.and_left(Nat.is_lt(f0, fresh), DST.alllt(rest, fresh), ST.g_fllt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h)), ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h))
      INS.ins_free_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, f0, rest, key, e, ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h), ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h), ST.g_tk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h), ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h), ST.g_tp(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h), ST.g_tn(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h), K.alllt_mono(ord, fresh, SC.pow2(depth), ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h), ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h)), hf0, ST.g_fk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h))
    case Nil{}:
      insr_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, key, e, h, q, hq, hcq, hroom, Nat.is_lt(fresh, SC.pow2(depth)), {==})

# ---- the invariant ----

def len_s1(+ord: List<&2, Nat>, +s: Nat, +c: Nat, +h: {Nat.is_lt(SC.length(Nat, ord), c) == True{} : Bool}) -> {Nat.is_le(SC.length(Nat, SC.append(Nat, ord, Con{s, Nil{}})), c) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(z, c) == True{} : Bool}, 1n+SC.length(Nat, ord), SC.length(Nat, SC.append(Nat, ord, Con{s, Nil{}})), Equal.sym(Nat, SC.length(Nat, SC.append(Nat, ord, Con{s, Nil{}})), 1n+SC.length(Nat, ord), INS.len_snoc(ord, s)), N.lt_succ_le_succ(SC.length(Nat, ord), c, h))

def fresh_nd(+ord: List<&2, Nat>, +fresh: Nat, +hol: {DST.alllt(ord, fresh) == True{} : Bool}, +hnd: {DST.nodup(SC.append(Nat, ord, Nil{})) == True{} : Bool}) -> {DST.nodup(SC.append(Nat, SC.append(Nat, ord, Con{fresh, Nil{}}), Nil{})) == True{} : Bool}:
  +on = SC.append(Nat, ord, Nil{})
  +hf = IF.f_notin(on, fresh, L.subst(List<&2, Nat>, z => {DST.alllt(z, fresh) == True{} : Bool}, ord, on, Equal.sym(List<&2, Nat>, on, ord, LL.append_nil(Nat, ord)), hol))
  +r = IF.nodup_ins(ord, Nil{}, fresh, hf, hnd)
  L.subst(List<&2, Nat>, z => {DST.nodup(z) == True{} : Bool}, SC.append(Nat, ord, Con{fresh, Nil{}}), SC.append(Nat, SC.append(Nat, ord, Con{fresh, Nil{}}), Nil{}), Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, ord, Con{fresh, Nil{}}), Nil{}), SC.append(Nat, ord, Con{fresh, Nil{}}), LL.append_nil(Nat, SC.append(Nat, ord, Con{fresh, Nil{}}))), r)

def fresh_cnt(+ord: List<&2, Nat>, +fresh: Nat, +elen: {SC.length(Nat, ord) == fresh : Nat}) -> {Nat.is_eq(Nat.add(SC.length(Nat, SC.append(Nat, ord, Con{fresh, Nil{}})), SC.length(Nat, Nil{})), 1n+fresh) == True{} : Bool}:
  +l2 = SC.length(Nat, SC.append(Nat, ord, Con{fresh, Nil{}}))
  +e = Equal.trans(Nat, Nat.add(l2, 0n), l2, 1n+fresh, N.add_zero(l2), Equal.trans(Nat, l2, 1n+SC.length(Nat, ord), 1n+fresh, INS.len_snoc(ord, fresh), Equal.cong(Nat, Nat, z => 1n+z, SC.length(Nat, ord), fresh, elen)))
  L.subst(Nat, z => {Nat.is_eq(z, 1n+fresh) == True{} : Bool}, 1n+fresh, Nat.add(l2, 0n), Equal.sym(Nat, Nat.add(l2, 0n), 1n+fresh, e), AL.lmem_self(1n+fresh))

def fresh_ol(+ord: List<&2, Nat>, +fresh: Nat, +hol: {DST.alllt(ord, fresh) == True{} : Bool}) -> {DST.alllt(SC.append(Nat, ord, Con{fresh, Nil{}}), 1n+fresh) == True{} : Bool}:
  SP.alllt_join(ord, Con{fresh, Nil{}}, 1n+fresh, IF.alllt_succ(ord, fresh, hol), L.and_intro(Nat.is_lt(fresh, 1n+fresh), True{}, N.lt_succ(fresh), {==}))

def insr_inv(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +key: String, +e: F.Slot<V>, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}) == True{} : Bool}, +hno: {TB.lk(table, key) == None{} : Maybe<&2, U32>}, +ho: {ST.is_occ(V, e) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}, +hroom: {Nat.is_lt(SC.length(Nat, ord), U32.to_nat(cap)) == True{} : Bool}, room: Bool, +er: {Nat.is_lt(fresh, SC.pow2(depth)) == room : Bool}) -> {ST.good(~V, ins_room(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, key, e, room)) == True{} : Bool}:
  match room:
    case True{}:
      +hol = ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h)
      +elen = len_fresh(ord, fresh, ST.g_count(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h))
      INS.ins_inv(~V, cap, fresh, 1n+fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, Nil{}, fresh, key, e, h, hno, ho, er, N.lt_succ_le_succ(fresh, SC.pow2(depth), er), fresh_ol(ord, fresh, hol), {==}, fresh_nd(ord, fresh, hol, ST.g_nodup(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h)), fresh_cnt(ord, fresh, elen), {==}, len_s1(ord, fresh, U32.to_nat(cap), hroom))
    case False{}:
      +hol = ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h)
      +elen = len_fresh(ord, fresh, ST.g_count(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h))
      +hdl = grow_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, h, q, hq, hcq, hroom, er)
      +h2 = INS.grow_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h, hdl)
      +hs1 = N.le_lt_trans(fresh, SC.pow2(depth), SC.pow2(1n+depth), ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h), N.pow2_lt_succ(depth))
      INS.ins_inv(~V, cap, fresh, 1n+fresh, 1n+depth, life, tc, table, AR.TNode{tk, AR.trep(String, depth, "")}, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}, AR.TNode{tp, AR.trep(U32, depth, 0)}, AR.TNode{tn, AR.trep(U32, depth, 0)}, ord, Nil{}, Nil{}, fresh, key, e, h2, hno, ho, hs1, N.lt_succ_le_succ(fresh, SC.pow2(1n+depth), hs1), fresh_ol(ord, fresh, hol), {==}, fresh_nd(ord, fresh, hol, ST.g_nodup(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h)), fresh_cnt(ord, fresh, elen), {==}, len_s1(ord, fresh, U32.to_nat(cap), hroom))

def insf_inv(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, fl: List<&2, Nat>, +key: String, +e: F.Slot<V>, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +hno: {TB.lk(table, key) == None{} : Maybe<&2, U32>}, +ho: {ST.is_occ(V, e) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}, +hroom: {Nat.is_lt(SC.length(Nat, ord), U32.to_nat(cap)) == True{} : Bool}) -> {ST.good(~V, ins_fl(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, e)) == True{} : Bool}:
  match fl:
    case Con{+f0, +rest}:
      +hfl = ST.g_fllt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h)
      +hsf = L.and_left(Nat.is_lt(f0, fresh), DST.alllt(rest, fresh), hfl)
      +hf0 = N.lt_le_trans(f0, fresh, SC.pow2(depth), hsf, ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h))
      +hnd = L.subst(List<&2, Nat>, z => {DST.nodup(z) == True{} : Bool}, SC.append(Nat, ord, Con{f0, rest}), SC.append(Nat, SC.append(Nat, ord, Con{f0, Nil{}}), rest), Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, ord, Con{f0, Nil{}}), rest), SC.append(Nat, ord, Con{f0, rest}), LL.append_assoc(Nat, ord, Con{f0, Nil{}}, rest)), ST.g_nodup(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h))
      +lo = SC.length(Nat, ord)
      +lr = SC.length(Nat, rest)
      +ecnt = Equal.trans(Nat, Nat.add(SC.length(Nat, SC.append(Nat, ord, Con{f0, Nil{}})), lr), Nat.add(1n+lo, lr), Nat.add(lo, 1n+lr),
        Equal.cong(Nat, Nat, z => Nat.add(z, lr), SC.length(Nat, SC.append(Nat, ord, Con{f0, Nil{}})), 1n+lo, INS.len_snoc(ord, f0)),
        Equal.sym(Nat, Nat.add(lo, 1n+lr), 1n+Nat.add(lo, lr), N.add_succ(lo, lr)))
      +hcnt = L.subst(Nat, z => {Nat.is_eq(z, fresh) == True{} : Bool}, Nat.add(lo, 1n+lr), Nat.add(SC.length(Nat, SC.append(Nat, ord, Con{f0, Nil{}})), lr), Equal.sym(Nat, Nat.add(SC.length(Nat, SC.append(Nat, ord, Con{f0, Nil{}})), lr), Nat.add(lo, 1n+lr), ecnt), ST.g_count(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h))
      INS.ins_inv(~V, cap, fresh, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, rest, f0, key, e, h, hno, ho, hf0, ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h),
        SP.alllt_join(ord, Con{f0, Nil{}}, fresh, ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h), L.and_intro(Nat.is_lt(f0, fresh), True{}, hsf, {==})),
        L.and_right(Nat.is_lt(f0, fresh), DST.alllt(rest, fresh), hfl), hnd, hcnt,
        L.and_right(U32.is_eq(DST.lat(AR.slots(U32, tn), f0), DST.hd_or(rest, D.nil())), ST.fk(rest, AR.slots(U32, tn)), ST.g_fk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h)),
        len_s1(ord, f0, U32.to_nat(cap), hroom))
    case Nil{}:
      insr_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, key, e, h, hno, ho, q, hq, hcq, hroom, Nat.is_lt(fresh, SC.pow2(depth)), {==})

# ---- the model ----

def insr_model(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +key: String, +v: V, +now: T.Int64, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}, +hroom: {Nat.is_lt(SC.length(Nat, ord), U32.to_nat(cap)) == True{} : Bool}, room: Bool, +er: {Nat.is_lt(fresh, SC.pow2(depth)) == room : Bool}) -> {ST.model(~V, ins_room(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, key, AF.entry(~V, life, v, now), room)) == S.LM{cap, life, S.snoc(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), S.En{key, v, NS.deadline(now, life)}), T.bump(0n, ST.mets(AR.slots(U32, tc)))} : S.Model<V>}:
  match room:
    case True{}:
      INS.ins_model(~V, cap, 1n+fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, fresh, key, v, now, er, IF.f_notin(ord, fresh, ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h)), ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h), ST.g_tk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h), ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h))
    case False{}:
      +P0 = SC.pow2(depth)
      +pfk = ST.g_tk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h)
      +pfe = ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h)
      +ks = AR.slots(String, tk)
      +es = AR.slots(F.Slot<V>, te)
      +zk = AR.slots(String, AR.trep(String, depth, ""))
      +ze = AR.slots(F.Slot<V>, AR.trep(F.Slot<V>, depth, F.Vacant{}))
      +hlo = K.alllt_mono(ord, fresh, P0, ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h), ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h))
      +hlk = L.subst(Nat, z => {DST.alllt(ord, z) == True{} : Bool}, P0, SC.length(String, ks), Equal.sym(Nat, SC.length(String, ks), P0, AR.slots_length(String, depth, tk, pfk)), hlo)
      +hle = L.subst(Nat, z => {DST.alllt(ord, z) == True{} : Bool}, P0, SC.length(F.Slot<V>, es), Equal.sym(Nat, SC.length(F.Slot<V>, es), P0, AR.slots_length(F.Slot<V>, depth, te, pfe)), hlo)
      +hs1 = N.le_lt_trans(fresh, P0, SC.pow2(1n+depth), ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h), N.pow2_lt_succ(depth))
      +r = INS.ins_model(~V, cap, 1n+fresh, 1n+depth, life, tc, table, AR.TNode{tk, AR.trep(String, depth, "")}, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}, AR.TNode{tp, AR.trep(U32, depth, 0)}, AR.TNode{tn, AR.trep(U32, depth, 0)}, ord, Nil{}, fresh, key, v, now, hs1, IF.f_notin(ord, fresh, ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h)), ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Nil{}, h), L.and_intro(AR.perfect(String, depth, tk), AR.perfect(String, depth, AR.trep(String, depth, "")), pfk, AR.trep_perfect(String, depth, "")), L.and_intro(AR.perfect(F.Slot<V>, depth, te), AR.perfect(F.Slot<V>, depth, AR.trep(F.Slot<V>, depth, F.Vacant{})), pfe, AR.trep_perfect(F.Slot<V>, depth, F.Vacant{})))
      Equal.trans(S.Model<V>, ST.model(~V, INS.ins_sh(V, cap, 1n+fresh, 1n+depth, life, tc, table, AR.TNode{tk, AR.trep(String, depth, "")}, AR.TNode{te, AR.trep(F.Slot<V>, depth, F.Vacant{})}, AR.TNode{tp, AR.trep(U32, depth, 0)}, AR.TNode{tn, AR.trep(U32, depth, 0)}, ord, Nil{}, fresh, key, AF.entry(~V, life, v, now))), S.LM{cap, life, S.snoc(V, ST.ents(V, SC.append(String, ks, zk), SC.append(F.Slot<V>, es, ze), ord), S.En{key, v, NS.deadline(now, life)}), T.bump(0n, ST.mets(AR.slots(U32, tc)))}, S.LM{cap, life, S.snoc(V, ST.ents(V, ks, es, ord), S.En{key, v, NS.deadline(now, life)}), T.bump(0n, ST.mets(AR.slots(U32, tc)))},
        r,
        Equal.cong(List<&2, S.Ent<V>>, S.Model<V>, z => S.LM{cap, life, S.snoc(V, z, S.En{key, v, NS.deadline(now, life)}), T.bump(0n, ST.mets(AR.slots(U32, tc)))}, ST.ents(V, SC.append(String, ks, zk), SC.append(F.Slot<V>, es, ze), ord), ST.ents(V, ks, es, ord), INS.ents_grow(V, ks, zk, es, ze, ord, hlk, hle)))

def insf_model(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, fl: List<&2, Nat>, +key: String, +v: V, +now: T.Int64, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}, +hroom: {Nat.is_lt(SC.length(Nat, ord), U32.to_nat(cap)) == True{} : Bool}) -> {ST.model(~V, ins_fl(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, AF.entry(~V, life, v, now))) == S.LM{cap, life, S.snoc(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), S.En{key, v, NS.deadline(now, life)}), T.bump(0n, ST.mets(AR.slots(U32, tc)))} : S.Model<V>}:
  match fl:
    case Con{+f0, +rest}:
      +hfl = ST.g_fllt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h)
      +hf0 = N.lt_le_trans(f0, fresh, SC.pow2(depth), L.and_left(Nat.is_lt(f0, fresh), DST.alllt(rest, fresh), hfl), ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h))
      +hn = SP.disj_mem(ord, Con{f0, rest}, f0, SP.nodup_disj(ord, Con{f0, rest}, ST.g_nodup(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h)), TB.or_true_l(Nat.is_eq(f0, f0), DST.lmem(f0, rest), AL.lmem_self(f0)))
      INS.ins_model(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, rest, f0, key, v, now, hf0, hn, ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h), ST.g_tk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h), ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, Con{f0, rest}, h))
    case Nil{}:
      insr_model(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, key, v, now, h, q, hq, hcq, hroom, Nat.is_lt(fresh, SC.pow2(depth)), {==})

# ---- add: the ghost result ----

def hd_nat(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{+x, t}:
      x

def ad_none(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +v: V, +now: T.Int64, full: Bool) -> ST.Shadow<V> & Bool:
  match full:
    case False{}:
      (ins_fl(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, AF.entry(~V, life, v, now)), False{})
    case True{}:
      (ins_g(V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, hd_nat(ord), fl, 1n), key, AF.entry(~V, life, v, now)), True{})

def ad_ghost(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +v: V, +now: T.Int64, m: Maybe<&2, U32>, +full: Bool) -> ST.Shadow<V> & Bool:
  match m:
    case Some{+x}:
      (ADD.rep_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, TB.firstk(AR.slots(String, tk), ord, key), AF.entry(~V, life, v, now)), False{})
    case None{}:
      ad_none(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, full)

def apb(~V: Data, g: ST.Shadow<V> & Bool) -> F.Fast<V> & Bool:
  (sh, b) = g
  (ST.real(~V, sh), b)

def mpb(~V: Data, g: ST.Shadow<V> & Bool) -> S.Model<V> & E.Obs<V>:
  (sh, b) = g
  (ST.model(~V, sh), E.OFlag{b})

def gpb(~V: Data, g: ST.Shadow<V> & Bool) -> Bool:
  (sh, b) = g
  ST.good(~V, sh)

# ---- facts about the full / not-full test ----

def u32_le_nat(+a: U32, +b: U32) -> {U32.is_le(a, b) == Nat.is_le(U32.to_nat(a), U32.to_nat(b)) : Bool}:
  Equal.cong(Cmp, Bool, c => Cmp.is_le(c), U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), U.u32_cmp(a, b))

def len_nat(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(SC.length(Nat, ord))) == SC.length(Nat, ord) : Nat}:
  +hd = ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)
  +hle = N.le_trans(SC.length(Nat, ord), fresh, SC.pow2(depth), RS.ord_le(ord, fl, fresh, ST.g_count(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)), ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
  U.to_nat_from_nat(SC.length(Nat, ord), 1n+depth, N.lt_succ_le_succ(depth, 32n, N.le_lt_trans(depth, 31n, 32n, hd, N.lt_succ(31n))), N.le_lt_trans(SC.length(Nat, ord), SC.pow2(depth), SC.pow2(1n+depth), hle, N.pow2_lt_succ(depth)))

def room_of(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +ef: {U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))) == False{} : Bool}) -> {Nat.is_lt(SC.length(Nat, ord), U32.to_nat(cap)) == True{} : Bool}:
  +e1 = Equal.trans(Bool, Nat.is_le(U32.to_nat(cap), U32.to_nat(U32.from_nat(SC.length(Nat, ord)))), U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))), False{}, Equal.sym(Bool, U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))), Nat.is_le(U32.to_nat(cap), U32.to_nat(U32.from_nat(SC.length(Nat, ord)))), u32_le_nat(cap, U32.from_nat(SC.length(Nat, ord)))), ef)
  +e2 = L.subst(Nat, z => {Nat.is_le(U32.to_nat(cap), z) == False{} : Bool}, U32.to_nat(U32.from_nat(SC.length(Nat, ord))), SC.length(Nat, ord), len_nat(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), e1)
  N.not_le_lt(U32.to_nat(cap), SC.length(Nat, ord), e2)

def le0_eq(x: Nat, +h: {Nat.is_le(x, 0n) == True{} : Bool}) -> {Nat.is_eq(x, 0n) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({Nat.is_eq(1n+p, 0n) == True{} : Bool}, L.false_true(h))

# a full cache is not empty (the capacity is positive)
def full_nonempty(+cap: U32, +hcap: {Bool.not(U32.is_eq(cap, 0)) == True{} : Bool}, +ef: {U32.is_le(cap, U32.from_nat(SC.length(Nat, Nil{}))) == True{} : Bool}) -> Empty:
  +e1 = Equal.trans(Bool, Nat.is_le(U32.to_nat(cap), 0n), U32.is_le(cap, 0), True{}, Equal.sym(Bool, U32.is_le(cap, 0), Nat.is_le(U32.to_nat(cap), 0n), u32_le_nat(cap, 0)), ef)
  +e2 = Equal.trans(Bool, U32.is_eq(cap, 0), Nat.is_eq(U32.to_nat(cap), 0n), True{}, DF.u32_eq_nat(cap, 0), le0_eq(U32.to_nat(cap), e1))
  L.false_true(L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, U32.is_eq(cap, 0), True{}, e2, hcap))

# ---- add: the runtime ----

def evict_real(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +s0: Nat, +rest: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl) == True{} : Bool}) -> {F.evict_oldest(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl})) == ST.real(~V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, s0, fl, 1n)) : F.Fast<V>}:
  +hm = TB.or_true_l(Nat.is_eq(s0, s0), DST.lmem(s0, rest), AL.lmem_self(s0))
  +hs0 = N.lt_le_trans(s0, fresh, SC.pow2(depth), L.and_left(Nat.is_lt(s0, fresh), DST.alllt(rest, fresh), ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h)), ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h))
  +r = Equal.cong(F.Fast<V> & Maybe<&2, V>, F.Fast<V>, p => F.drop_val(~V, p), F.remove_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), U32.from_nat(s0), 1n), (ST.real(~V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, s0, fl, 1n)), F.slot_val(~V, ST.sat(V, AR.slots(F.Slot<V>, te), s0))), RM.rm_at_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, s0, 1n, hm, h))
  L.subst(U32, z => {F.drop_val(~V, F.remove_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), z, 1n)) == ST.real(~V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, s0, fl, 1n)) : F.Fast<V>}, U32.from_nat(s0), F.slot(DST.ln(s0)), Equal.sym(U32, F.slot(DST.ln(s0)), U32.from_nat(s0), DF.slot_ln(s0, depth, ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h), hs0)), r)

# the order after evicting its head is shorter than the capacity
def room_after(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +s0: Nat, +rest: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl) == True{} : Bool}) -> {Nat.is_lt(SC.length(Nat, SC.append(Nat, SP.spre(Con{s0, rest}, s0), SP.spost(Con{s0, rest}, s0))), U32.to_nat(cap)) == True{} : Bool}:
  +hm = TB.or_true_l(Nat.is_eq(s0, s0), DST.lmem(s0, rest), AL.lmem_self(s0))
  +a = SP.spre(Con{s0, rest}, s0)
  +b = SP.spost(Con{s0, rest}, s0)
  +elen = Equal.trans(Nat, SC.length(Nat, Con{s0, rest}), SC.length(Nat, SC.append(Nat, a, Con{s0, b})), 1n+SC.length(Nat, SC.append(Nat, a, b)), Equal.cong(List<&2, Nat>, Nat, z => SC.length(Nat, z), Con{s0, rest}, SC.append(Nat, a, Con{s0, b}), SP.split_eq(Con{s0, rest}, s0, hm)), RS.len_cut(a, s0, b))
  N.succ_le_lt(SC.length(Nat, SC.append(Nat, a, b)), U32.to_nat(cap), L.subst(Nat, z => {Nat.is_le(z, U32.to_nat(cap)) == True{} : Bool}, SC.length(Nat, Con{s0, rest}), 1n+SC.length(Nat, SC.append(Nat, a, b)), elen, ST.g_n(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h)))

def ad_full_real(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +v: V, +now: T.Int64, +ef: {U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}) -> {(F.insert_new(~V, F.evict_oldest(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl})), key, AF.entry(~V, life, v, now)), True{}) == apb(~V, (ins_g(V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, hd_nat(ord), fl, 1n), key, AF.entry(~V, life, v, now)), True{})) : F.Fast<V> & Bool}:
  match ord:
    case Nil{}:
      Empty.absurd({(F.insert_new(~V, F.evict_oldest(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Nil{}, fl})), key, AF.entry(~V, life, v, now)), True{}) == apb(~V, (ins_g(V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Nil{}, 0n, fl, 1n), key, AF.entry(~V, life, v, now)), True{})) : F.Fast<V> & Bool}, full_nonempty(cap, ST.g_cap(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Nil{}, fl, h), ef))
    case Con{+s0, +rest}:
      +hm = TB.or_true_l(Nat.is_eq(s0, s0), DST.lmem(s0, rest), AL.lmem_self(s0))
      +e = AF.entry(~V, life, v, now)
      +h2 = RM.rm_at_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, s0, 1n, hm, h)
      +r1 = Equal.cong(F.Fast<V>, F.Fast<V>, f => F.insert_new(~V, f, key, e), F.evict_oldest(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl})), ST.real(~V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, s0, fl, 1n)), evict_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, s0, rest, fl, h))
      +r2 = insf_real(~V, cap, fresh, depth, life, RS.sbd(tc, 1n), Map.del(&2, Maybe<&2, U32>, table, ST.kat(AR.slots(String, tk), s0)), tk, AR.upd(F.Slot<V>, depth, te, s0, F.Vacant{}), TS.tpup(depth, tp, SP.spost(Con{s0, rest}, s0), LK.lastl(SP.spre(Con{s0, rest}, s0), D.nil())), AR.upd(U32, depth, TS.tnup(depth, tn, SP.spre(Con{s0, rest}, s0), DST.hd_or(SP.spost(Con{s0, rest}, s0), D.nil())), s0, DST.hd(fl)), SC.append(Nat, SP.spre(Con{s0, rest}, s0), SP.spost(Con{s0, rest}, s0)), Con{s0, fl}, key, e, h2, q, hq, hcq, room_after(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, s0, rest, fl, h))
      Equal.cong(F.Fast<V>, F.Fast<V> & Bool, f => (f, True{}), F.insert_new(~V, F.evict_oldest(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl})), key, e), ST.real(~V, ins_g(V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, s0, fl, 1n), key, e)), Equal.trans(F.Fast<V>, F.insert_new(~V, F.evict_oldest(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl})), key, e), F.insert_new(~V, ST.real(~V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, s0, fl, 1n)), key, e), ST.real(~V, ins_g(V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, s0, fl, 1n), key, e)), r1, r2))

def ad_none_real(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +v: V, +now: T.Int64, full: Bool, +ef: {U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))) == full : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}) -> {F.room_then_insert(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, AF.entry(~V, life, v, now), full) == apb(~V, ad_none(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, full)) : F.Fast<V> & Bool}:
  match full:
    case False{}:
      Equal.cong(F.Fast<V>, F.Fast<V> & Bool, f => (f, False{}), F.insert_new(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, AF.entry(~V, life, v, now)), ST.real(~V, ins_fl(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, AF.entry(~V, life, v, now))), insf_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, AF.entry(~V, life, v, now), h, q, hq, hcq, room_of(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h, ef)))
    case True{}:
      ad_full_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, ef, h, q, hq, hcq)

def ad_real_m(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +v: V, +now: T.Int64, m: Maybe<&2, U32>, +em: {TB.lk(table, key) == m : Maybe<&2, U32>}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}) -> {F.add_pick(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, AF.entry(~V, life, v, now), m, U32.is_le(cap, U32.from_nat(SC.length(Nat, ord)))) == apb(~V, ad_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, m, U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))))) : F.Fast<V> & Bool}:
  match m:
    case Some{+x}:
      +ks = AR.slots(String, tk)
      +s = TB.firstk(ks, ord, key)
      +ex = TB.locate(table, ks, ord, key, x, em, ST.g_crit(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_pop(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_incl(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
      +hk = RM.found_k(table, ks, ord, key, x, em, ST.g_crit(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_pop(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_incl(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
      +e = AF.entry(~V, life, v, now)
      Equal.cong(F.Fast<V>, F.Fast<V> & Bool, f => (f, False{}), F.replace(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), x, e), ST.real(~V, ADD.rep_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, e)),
        L.subst(U32, z => {F.replace(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), z, e) == ST.real(~V, ADD.rep_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, e)) : F.Fast<V>}, U32.from_nat(s), x, Equal.sym(U32, x, U32.from_nat(s), ex), ADD.rep_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, e, L.and_left(DST.lmem(s, ord), String.eq(ST.kat(ks, s), key), hk), h)))
    case None{}:
      ad_none_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))), {==}, h, q, hq, hcq)

def add_real(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +v: V, +now: T.Int64, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}) -> {F.add(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, v, F.int_stamp(now)) == apb(~V, ad_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, TB.lk(table, key), U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))))) : F.Fast<V> & Bool}:
  L.subst(Map<&2, Maybe<&2, U32>> & Maybe<&2, U32>, z => {F.add_found(~V, cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), AR.thaw(String, tk), AR.thaw(F.Slot<V>, te), F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, key, AF.entry(~V, life, v, now), z) == apb(~V, ad_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, TB.lk(table, key), U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))))) : F.Fast<V> & Bool}, TB.mpair(table, TB.lk(table, key)), Map.get(Maybe<&2, U32>, None{}, table, key), Equal.sym(Map<&2, Maybe<&2, U32>> & Maybe<&2, U32>, Map.get(Maybe<&2, U32>, None{}, table, key), TB.mpair(table, TB.lk(table, key)), TB.get_pair(table, key)),
    ad_real_m(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, TB.lk(table, key), {==}, h, q, hq, hcq))

# ---- add: the invariant ----

def ad_full_inv(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +v: V, +now: T.Int64, +ef: {U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))) == True{} : Bool}, +em: {TB.lk(table, key) == None{} : Maybe<&2, U32>}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}) -> {gpb(~V, (ins_g(V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, hd_nat(ord), fl, 1n), key, AF.entry(~V, life, v, now)), True{})) == True{} : Bool}:
  match ord:
    case Nil{}:
      Empty.absurd({gpb(~V, (ins_g(V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Nil{}, 0n, fl, 1n), key, AF.entry(~V, life, v, now)), True{})) == True{} : Bool}, full_nonempty(cap, ST.g_cap(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Nil{}, fl, h), ef))
    case Con{+s0, +rest}:
      +ks = AR.slots(String, tk)
      +hm = TB.or_true_l(Nat.is_eq(s0, s0), DST.lmem(s0, rest), AL.lmem_self(s0))
      +h2 = RM.rm_at_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, s0, 1n, hm, h)
      +crit = ST.g_crit(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h)
      +hne = CS.symmetric_false(ST.kat(ks, s0), key, TB.nk_elem(table, ST.kat(ks, s0), s0, key, None{}, em, TB.am_at(table, ks, Con{s0, rest}, s0, ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h), hm), {==}))
      +efr = DelFrame.other_lookup_unchanged(U32, table, ST.kat(ks, s0), key, R.critbit_certificate(Maybe<&2, U32>, table, crit), TB.different_of(key, ST.kat(ks, s0), hne))
      +hno2 = Equal.trans(Maybe<&2, U32>, TB.lk(Map.del(&2, Maybe<&2, U32>, table, ST.kat(ks, s0)), key), TB.lk(table, key), None{}, efr, em)
      insf_inv(~V, cap, fresh, depth, life, RS.sbd(tc, 1n), Map.del(&2, Maybe<&2, U32>, table, ST.kat(AR.slots(String, tk), s0)), tk, AR.upd(F.Slot<V>, depth, te, s0, F.Vacant{}), TS.tpup(depth, tp, SP.spost(Con{s0, rest}, s0), LK.lastl(SP.spre(Con{s0, rest}, s0), D.nil())), AR.upd(U32, depth, TS.tnup(depth, tn, SP.spre(Con{s0, rest}, s0), DST.hd_or(SP.spost(Con{s0, rest}, s0), D.nil())), s0, DST.hd(fl)), SC.append(Nat, SP.spre(Con{s0, rest}, s0), SP.spost(Con{s0, rest}, s0)), Con{s0, fl}, key, AF.entry(~V, life, v, now), h2, hno2, AF.entry_occ(~V, life, v, now), q, hq, hcq, room_after(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, s0, rest, fl, h))

def ad_none_inv(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +v: V, +now: T.Int64, full: Bool, +ef: {U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))) == full : Bool}, +em: {TB.lk(table, key) == None{} : Maybe<&2, U32>}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}) -> {gpb(~V, ad_none(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, full)) == True{} : Bool}:
  match full:
    case False{}:
      insf_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, AF.entry(~V, life, v, now), h, em, AF.entry_occ(~V, life, v, now), q, hq, hcq, room_of(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h, ef))
    case True{}:
      ad_full_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, ef, em, h, q, hq, hcq)

def ad_inv_m(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +v: V, +now: T.Int64, m: Maybe<&2, U32>, +em: {TB.lk(table, key) == m : Maybe<&2, U32>}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}) -> {gpb(~V, ad_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, m, U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))))) == True{} : Bool}:
  match m:
    case Some{+x}:
      +ks = AR.slots(String, tk)
      +s = TB.firstk(ks, ord, key)
      +hk = RM.found_k(table, ks, ord, key, x, em, ST.g_crit(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_pop(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_incl(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
      ADD.rep_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, AF.entry(~V, life, v, now), AF.entry_occ(~V, life, v, now), L.and_left(DST.lmem(s, ord), String.eq(ST.kat(ks, s), key), hk), h)
    case None{}:
      ad_none_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))), {==}, em, h, q, hq, hcq)

def add_inv(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +v: V, +now: T.Int64, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}) -> {gpb(~V, ad_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, TB.lk(table, key), U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))))) == True{} : Bool}:
  ad_inv_m(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, TB.lk(table, key), {==}, h, q, hq, hcq)

# ---- add: the model ----

def ad_full_model(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +v: V, +now: T.Int64, +ef: {U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}) -> {(S.LM{cap, life, S.snoc(V, S.tail(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord)), S.En{key, v, NS.deadline(now, life)}), T.bump(0n, T.bump(1n, ST.mets(AR.slots(U32, tc))))}, E.OFlag{True{}}) == mpb(~V, (ins_g(V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, hd_nat(ord), fl, 1n), key, AF.entry(~V, life, v, now)), True{})) : S.Model<V> & E.Obs<V>}:
  match ord:
    case Nil{}:
      Empty.absurd({(S.LM{cap, life, S.snoc(V, S.tail(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), Nil{})), S.En{key, v, NS.deadline(now, life)}), T.bump(0n, T.bump(1n, ST.mets(AR.slots(U32, tc))))}, E.OFlag{True{}}) == mpb(~V, (ins_g(V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Nil{}, 0n, fl, 1n), key, AF.entry(~V, life, v, now)), True{})) : S.Model<V> & E.Obs<V>}, full_nonempty(cap, ST.g_cap(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Nil{}, fl, h), ef))
    case Con{+s0, +rest}:
      +ks = AR.slots(String, tk)
      +es = AR.slots(F.Slot<V>, te)
      +k0 = ST.kat(ks, s0)
      +hm = TB.or_true_l(Nat.is_eq(s0, s0), DST.lmem(s0, rest), AL.lmem_self(s0))
      +a = SP.spre(Con{s0, rest}, s0)
      +b = SP.spost(Con{s0, rest}, s0)
      +esp = SP.split_eq(Con{s0, rest}, s0, hm)
      +hs2 = RM.split_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, s0, hm, h)
      +P0 = SC.pow2(depth)
      +hfr = ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h)
      +hol = ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h)
      +hs0 = N.lt_le_trans(s0, fresh, P0, L.and_left(Nat.is_lt(s0, fresh), DST.alllt(rest, fresh), hol), hfr)
      +hlo2 = K.alllt_mono(SC.append(Nat, a, Con{s0, b}), fresh, P0, ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s0, b}), fl, hs2), ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s0, b}), fl, hs2))
      +hocc = ST.g_occ(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h)
      +hmp = ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h)
      +ho = L.and_left(ST.is_occ(V, ST.sat(V, es, s0)), ST.all_occ(V, es, rest), hocc)
      +hnd0 = SP.nodup_app_l(Con{s0, rest}, fl, ST.g_nodup(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h))
      +hn0 = TB.not_false(DST.lmem(s0, rest), L.and_left(Bool.not(DST.lmem(s0, rest)), DST.nodup(rest), hnd0))
      +hlr = K.alllt_mono(rest, fresh, P0, hfr, L.and_right(Nat.is_lt(s0, fresh), DST.alllt(rest, fresh), hol))
      +hnk = RS.nk_part(table, ks, rest, s0, depth, ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h), hs0, hlr, hn0, RS.lk_slot(table, ks, Nil{}, s0, rest, hmp), L.and_right(ST.mapped(table, k0, s0), ST.all_mapped(table, ks, rest), hmp))
      +E1 = ST.ents(V, ks, AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s0, F.Vacant{})), SC.append(Nat, a, b))
      +xs = ST.ents(V, ks, es, Con{s0, rest})
      +er = ST.ents(V, ks, es, rest)
      +eE1 = Equal.trans(List<&2, S.Ent<V>>, E1, S.drop(V, ST.ents(V, ks, es, SC.append(Nat, a, Con{s0, b})), k0), S.tail(V, xs),
        RS.rs_ents(V, depth, table, tk, te, a, s0, b, ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h), ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h), hs0, hlo2, SP.nodup_app_l(SC.append(Nat, a, Con{s0, b}), fl, ST.g_nodup(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s0, b}), fl, hs2)), ST.g_occ(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s0, b}), fl, hs2), ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, SC.append(Nat, a, Con{s0, b}), fl, hs2)),
        Equal.trans(List<&2, S.Ent<V>>, S.drop(V, ST.ents(V, ks, es, SC.append(Nat, a, Con{s0, b})), k0), S.drop(V, xs, k0), S.tail(V, xs),
          Equal.cong(List<&2, Nat>, List<&2, S.Ent<V>>, z => S.drop(V, ST.ents(V, ks, es, z), k0), SC.append(Nat, a, Con{s0, b}), Con{s0, rest}, Equal.sym(List<&2, Nat>, Con{s0, rest}, SC.append(Nat, a, Con{s0, b}), esp)),
          Equal.trans(List<&2, S.Ent<V>>, S.drop(V, xs, k0), S.drop(V, er, k0), S.tail(V, xs),
            EN.drop_here(V, k0, ST.sat(V, es, s0), er, k0, LR.string_reflexive(k0), ho),
            Equal.trans(List<&2, S.Ent<V>>, S.drop(V, er, k0), er, S.tail(V, xs), EN.drop_none(V, ks, es, rest, k0, hnk), Equal.sym(List<&2, S.Ent<V>>, S.tail(V, xs), er, EN.ent_tail(V, k0, ST.sat(V, es, s0), er, ho))))))
      +r = insf_model(~V, cap, fresh, depth, life, RS.sbd(tc, 1n), Map.del(&2, Maybe<&2, U32>, table, ST.kat(AR.slots(String, tk), s0)), tk, AR.upd(F.Slot<V>, depth, te, s0, F.Vacant{}), TS.tpup(depth, tp, SP.spost(Con{s0, rest}, s0), LK.lastl(SP.spre(Con{s0, rest}, s0), D.nil())), AR.upd(U32, depth, TS.tnup(depth, tn, SP.spre(Con{s0, rest}, s0), DST.hd_or(SP.spost(Con{s0, rest}, s0), D.nil())), s0, DST.hd(fl)), SC.append(Nat, SP.spre(Con{s0, rest}, s0), SP.spost(Con{s0, rest}, s0)), Con{s0, fl}, key, v, now, RM.rm_at_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, s0, 1n, hm, h), q, hq, hcq, room_after(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, s0, rest, fl, h))
      +M1 = ST.mets(AR.slots(U32, RS.sbd(tc, 1n)))
      +emod = Equal.trans(S.Model<V>, ST.model(~V, ins_g(V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, s0, fl, 1n), key, AF.entry(~V, life, v, now))), S.LM{cap, life, S.snoc(V, E1, S.En{key, v, NS.deadline(now, life)}), T.bump(0n, M1)}, S.LM{cap, life, S.snoc(V, S.tail(V, xs), S.En{key, v, NS.deadline(now, life)}), T.bump(0n, T.bump(1n, ST.mets(AR.slots(U32, tc))))},
        r,
        Equal.trans(S.Model<V>, S.LM{cap, life, S.snoc(V, E1, S.En{key, v, NS.deadline(now, life)}), T.bump(0n, M1)}, S.LM{cap, life, S.snoc(V, S.tail(V, xs), S.En{key, v, NS.deadline(now, life)}), T.bump(0n, M1)}, S.LM{cap, life, S.snoc(V, S.tail(V, xs), S.En{key, v, NS.deadline(now, life)}), T.bump(0n, T.bump(1n, ST.mets(AR.slots(U32, tc))))},
          Equal.cong(List<&2, S.Ent<V>>, S.Model<V>, z => S.LM{cap, life, S.snoc(V, z, S.En{key, v, NS.deadline(now, life)}), T.bump(0n, M1)}, E1, S.tail(V, xs), eE1),
          Equal.cong(T.Metrics, S.Model<V>, z => S.LM{cap, life, S.snoc(V, S.tail(V, xs), S.En{key, v, NS.deadline(now, life)}), T.bump(0n, z)}, M1, T.bump(1n, ST.mets(AR.slots(U32, tc))), RS.mets_drop(tc, 1n, ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h)))))
      Equal.cong(S.Model<V>, S.Model<V> & E.Obs<V>, z => (z, E.OFlag{True{}}), S.LM{cap, life, S.snoc(V, S.tail(V, xs), S.En{key, v, NS.deadline(now, life)}), T.bump(0n, T.bump(1n, ST.mets(AR.slots(U32, tc))))}, ST.model(~V, ins_g(V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, s0, fl, 1n), key, AF.entry(~V, life, v, now))), Equal.sym(S.Model<V>, ST.model(~V, ins_g(V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, s0, fl, 1n), key, AF.entry(~V, life, v, now))), S.LM{cap, life, S.snoc(V, S.tail(V, xs), S.En{key, v, NS.deadline(now, life)}), T.bump(0n, T.bump(1n, ST.mets(AR.slots(U32, tc))))}, emod))

def ad_none_model(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +v: V, +now: T.Int64, full: Bool, +ef: {U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))) == full : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}) -> {S.add_absent(V, cap, life, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), ST.mets(AR.slots(U32, tc)), S.En{key, v, NS.deadline(now, life)}, full) == mpb(~V, ad_none(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, full)) : S.Model<V> & E.Obs<V>}:
  match full:
    case False{}:
      Equal.cong(S.Model<V>, S.Model<V> & E.Obs<V>, z => (z, E.OFlag{False{}}), S.LM{cap, life, S.snoc(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), S.En{key, v, NS.deadline(now, life)}), T.bump(0n, ST.mets(AR.slots(U32, tc)))}, ST.model(~V, ins_fl(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, AF.entry(~V, life, v, now))), Equal.sym(S.Model<V>, ST.model(~V, ins_fl(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, AF.entry(~V, life, v, now))), S.LM{cap, life, S.snoc(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), S.En{key, v, NS.deadline(now, life)}), T.bump(0n, ST.mets(AR.slots(U32, tc)))}, insf_model(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, h, q, hq, hcq, room_of(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h, ef))))
    case True{}:
      ad_full_model(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, ef, h, q, hq, hcq)

def ad_model_m(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +v: V, +now: T.Int64, m: Maybe<&2, U32>, +em: {TB.lk(table, key) == m : Maybe<&2, U32>}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}) -> {S.add_found(V, cap, life, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), ST.mets(AR.slots(U32, tc)), key, S.En{key, v, NS.deadline(now, life)}, S.find(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), key)) == mpb(~V, ad_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, m, U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))))) : S.Model<V> & E.Obs<V>}:
  match m:
    case Some{+x}:
      +ks = AR.slots(String, tk)
      +s = TB.firstk(ks, ord, key)
      +ex = TB.locate(table, ks, ord, key, x, em, ST.g_crit(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_pop(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_incl(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
      +hk = RM.found_k(table, ks, ord, key, x, em, ST.g_crit(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_pop(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_incl(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
      +elk = Equal.trans(Maybe<&2, U32>, TB.lk(table, key), Some{x}, Some{U32.from_nat(s)}, em, Equal.cong(U32, Maybe<&2, U32>, z => Some{z}, x, U32.from_nat(s), ex))
      ADD.rep_model(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, s, key, v, now, elk, L.and_right(DST.lmem(s, ord), String.eq(ST.kat(ks, s), key), hk), L.and_left(DST.lmem(s, ord), String.eq(ST.kat(ks, s), key), hk), h)
    case None{}:
      +ks = AR.slots(String, tk)
      +es = AR.slots(F.Slot<V>, te)
      +xs = ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord)
      +hnk = TB.nk_all(table, ks, ord, key, None{}, em, ST.g_mapped(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), TB.nomap_none(ord))
      +elen = EN.len_ents(V, ks, es, ord, ST.g_occ(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
      L.subst(Maybe<&2, S.Ent<V>>, z => {S.add_found(V, cap, life, xs, ST.mets(AR.slots(U32, tc)), key, S.En{key, v, NS.deadline(now, life)}, z) == mpb(~V, ad_none(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))))) : S.Model<V> & E.Obs<V>}, None{}, S.find(V, xs, key), Equal.sym(Maybe<&2, S.Ent<V>>, S.find(V, xs, key), None{}, EN.find_none(V, ks, es, ord, key, hnk)),
        L.subst(Nat, z => {S.add_absent(V, cap, life, xs, ST.mets(AR.slots(U32, tc)), S.En{key, v, NS.deadline(now, life)}, U32.is_le(cap, U32.from_nat(z))) == mpb(~V, ad_none(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))))) : S.Model<V> & E.Obs<V>}, SC.length(Nat, ord), S.len(V, xs), Equal.sym(Nat, S.len(V, xs), SC.length(Nat, ord), elen),
          ad_none_model(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))), {==}, h, q, hq, hcq)))

def add_model(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +v: V, +now: T.Int64, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}) -> {S.add_found(V, cap, life, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), ST.mets(AR.slots(U32, tc)), key, S.En{key, v, NS.deadline(now, life)}, S.find(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), key)) == mpb(~V, ad_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, TB.lk(table, key), U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))))) : S.Model<V> & E.Obs<V>}:
  ad_model_m(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, TB.lk(table, key), {==}, h, q, hq, hcq)
