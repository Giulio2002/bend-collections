import Base
import ../lib/nat.bend as N
import ../lib/array.bend as AR
import ../lib/u32.bend as U
import ../../spec/common.bend as SC
import ../../spec/lru_fast.bend as S
import ../../src/lru/fast.bend as F
import ../../src/lru/time.bend as Time
import ../../types/lru_model.bend as T
import support/links_state.bend as DST
import support/links_tolist.bend as TL
import ./state.bend as ST
import ./ents.bend as EN

# len, capacity, set_lifetime, metrics and purge.

# ---- metrics: reading the ten limbs back as the five 64-bit counters ----

def counter_ok(+tc: AR.Tree<U32>, +c: U32, +i: Nat, +ec1: {U32.shl(c) == U32.from_nat(i) : U32}, +ec2: {U32.inc(U32.shl(c)) == U32.from_nat(1n+i) : U32}, +pf: {AR.perfect(U32, 4n, tc) == True{} : Bool}, +hi: {Nat.is_lt(1n+i, 16n) == True{} : Bool}) -> {F.counter(c, AR.thaw(U32, tc)) == (AR.thaw(U32, tc), ST.pk(AR.slots(U32, tc), i, 1n+i)) : Array<U32> & Word(64n)}:
  +cs = AR.slots(U32, tc)
  +hi0 = N.lt_trans(i, 1n+i, 16n, N.lt_succ(i), hi)
  +g0 = Equal.trans(Array<U32> & U32, Array.get(U32, AR.thaw(U32, tc), U32.shl(c)), Array.get(U32, AR.thaw(U32, tc), U32.from_nat(i)), (AR.thaw(U32, tc), DST.lat(cs, i)), Equal.cong(U32, Array<U32> & U32, z => Array.get(U32, AR.thaw(U32, tc), z), U32.shl(c), U32.from_nat(i), ec1), TL.get_at(U32, 4n, tc, i, 0, {==}, pf, hi0))
  +g1 = Equal.trans(Array<U32> & U32, Array.get(U32, AR.thaw(U32, tc), U32.inc(U32.shl(c))), Array.get(U32, AR.thaw(U32, tc), U32.from_nat(1n+i)), (AR.thaw(U32, tc), DST.lat(cs, 1n+i)), Equal.cong(U32, Array<U32> & U32, z => Array.get(U32, AR.thaw(U32, tc), z), U32.inc(U32.shl(c)), U32.from_nat(1n+i), ec2), TL.get_at(U32, 4n, tc, 1n+i, 0, {==}, pf, hi))
  Equal.trans(Array<U32> & Word(64n), F.limb_word(c, Array.get(U32, AR.thaw(U32, tc), U32.shl(c))), F.limb_word(c, (AR.thaw(U32, tc), DST.lat(cs, i))), (AR.thaw(U32, tc), ST.pk(cs, i, 1n+i)),
    Equal.cong(Array<U32> & U32, Array<U32> & Word(64n), r => F.limb_word(c, r), Array.get(U32, AR.thaw(U32, tc), U32.shl(c)), (AR.thaw(U32, tc), DST.lat(cs, i)), g0),
    Equal.cong(Array<U32> & U32, Array<U32> & Word(64n), r => F.limb_hi(DST.lat(cs, i), r), Array.get(U32, AR.thaw(U32, tc), U32.inc(U32.shl(c))), (AR.thaw(U32, tc), DST.lat(cs, 1n+i)), g1))

def mstep_ok(+tc: AR.Tree<U32>, +c: U32, +i: Nat, +ws: List<&2, Word(64n)>, +ec1: {U32.shl(c) == U32.from_nat(i) : U32}, +ec2: {U32.inc(U32.shl(c)) == U32.from_nat(1n+i) : U32}, +pf: {AR.perfect(U32, 4n, tc) == True{} : Bool}, +hi: {Nat.is_lt(1n+i, 16n) == True{} : Bool}) -> {F.m_step(c, (AR.thaw(U32, tc), ws)) == (AR.thaw(U32, tc), Con{ST.pk(AR.slots(U32, tc), i, 1n+i), ws}) : Array<U32> & List<&2, Word(64n)>}:
  Equal.cong(Array<U32> & Word(64n), Array<U32> & List<&2, Word(64n)>, r => F.m_cons(ws, r), F.counter(c, AR.thaw(U32, tc)), (AR.thaw(U32, tc), ST.pk(AR.slots(U32, tc), i, 1n+i)), counter_ok(tc, c, i, ec1, ec2, pf, hi))

def metrics_ok(+tc: AR.Tree<U32>, +pf: {AR.perfect(U32, 4n, tc) == True{} : Bool}) -> {F.to_metrics(AR.thaw(U32, tc)) == (AR.thaw(U32, tc), ST.mets(AR.slots(U32, tc))) : Array<U32> & T.Metrics}:
  +cs = AR.slots(U32, tc)
  +s4 = mstep_ok(tc, 4, 8n, Nil{}, {==}, {==}, pf, {==})
  +s3 = Equal.trans(Array<U32> & List<&2, Word(64n)>, F.m_step(3, F.m_step(4, (AR.thaw(U32, tc), Nil{}))), F.m_step(3, (AR.thaw(U32, tc), Con{ST.pk(cs, 8n, 9n), Nil{}})), (AR.thaw(U32, tc), Con{ST.pk(cs, 6n, 7n), Con{ST.pk(cs, 8n, 9n), Nil{}}}), Equal.cong(Array<U32> & List<&2, Word(64n)>, Array<U32> & List<&2, Word(64n)>, r => F.m_step(3, r), F.m_step(4, (AR.thaw(U32, tc), Nil{})), (AR.thaw(U32, tc), Con{ST.pk(cs, 8n, 9n), Nil{}}), s4), mstep_ok(tc, 3, 6n, Con{ST.pk(cs, 8n, 9n), Nil{}}, {==}, {==}, pf, {==}))
  +s2 = Equal.trans(Array<U32> & List<&2, Word(64n)>, F.m_step(2, F.m_step(3, F.m_step(4, (AR.thaw(U32, tc), Nil{})))), F.m_step(2, (AR.thaw(U32, tc), Con{ST.pk(cs, 6n, 7n), Con{ST.pk(cs, 8n, 9n), Nil{}}})), (AR.thaw(U32, tc), Con{ST.pk(cs, 4n, 5n), Con{ST.pk(cs, 6n, 7n), Con{ST.pk(cs, 8n, 9n), Nil{}}}}), Equal.cong(Array<U32> & List<&2, Word(64n)>, Array<U32> & List<&2, Word(64n)>, r => F.m_step(2, r), F.m_step(3, F.m_step(4, (AR.thaw(U32, tc), Nil{}))), (AR.thaw(U32, tc), Con{ST.pk(cs, 6n, 7n), Con{ST.pk(cs, 8n, 9n), Nil{}}}), s3), mstep_ok(tc, 2, 4n, Con{ST.pk(cs, 6n, 7n), Con{ST.pk(cs, 8n, 9n), Nil{}}}, {==}, {==}, pf, {==}))
  +s1 = Equal.trans(Array<U32> & List<&2, Word(64n)>, F.m_step(1, F.m_step(2, F.m_step(3, F.m_step(4, (AR.thaw(U32, tc), Nil{}))))), F.m_step(1, (AR.thaw(U32, tc), Con{ST.pk(cs, 4n, 5n), Con{ST.pk(cs, 6n, 7n), Con{ST.pk(cs, 8n, 9n), Nil{}}}})), (AR.thaw(U32, tc), Con{ST.pk(cs, 2n, 3n), Con{ST.pk(cs, 4n, 5n), Con{ST.pk(cs, 6n, 7n), Con{ST.pk(cs, 8n, 9n), Nil{}}}}}), Equal.cong(Array<U32> & List<&2, Word(64n)>, Array<U32> & List<&2, Word(64n)>, r => F.m_step(1, r), F.m_step(2, F.m_step(3, F.m_step(4, (AR.thaw(U32, tc), Nil{})))), (AR.thaw(U32, tc), Con{ST.pk(cs, 4n, 5n), Con{ST.pk(cs, 6n, 7n), Con{ST.pk(cs, 8n, 9n), Nil{}}}}), s2), mstep_ok(tc, 1, 2n, Con{ST.pk(cs, 4n, 5n), Con{ST.pk(cs, 6n, 7n), Con{ST.pk(cs, 8n, 9n), Nil{}}}}, {==}, {==}, pf, {==}))
  +s0 = Equal.trans(Array<U32> & List<&2, Word(64n)>, F.m_step(0, F.m_step(1, F.m_step(2, F.m_step(3, F.m_step(4, (AR.thaw(U32, tc), Nil{})))))), F.m_step(0, (AR.thaw(U32, tc), Con{ST.pk(cs, 2n, 3n), Con{ST.pk(cs, 4n, 5n), Con{ST.pk(cs, 6n, 7n), Con{ST.pk(cs, 8n, 9n), Nil{}}}}})), (AR.thaw(U32, tc), Con{ST.pk(cs, 0n, 1n), Con{ST.pk(cs, 2n, 3n), Con{ST.pk(cs, 4n, 5n), Con{ST.pk(cs, 6n, 7n), Con{ST.pk(cs, 8n, 9n), Nil{}}}}}}), Equal.cong(Array<U32> & List<&2, Word(64n)>, Array<U32> & List<&2, Word(64n)>, r => F.m_step(0, r), F.m_step(1, F.m_step(2, F.m_step(3, F.m_step(4, (AR.thaw(U32, tc), Nil{}))))), (AR.thaw(U32, tc), Con{ST.pk(cs, 2n, 3n), Con{ST.pk(cs, 4n, 5n), Con{ST.pk(cs, 6n, 7n), Con{ST.pk(cs, 8n, 9n), Nil{}}}}}), s1), mstep_ok(tc, 0, 0n, Con{ST.pk(cs, 2n, 3n), Con{ST.pk(cs, 4n, 5n), Con{ST.pk(cs, 6n, 7n), Con{ST.pk(cs, 8n, 9n), Nil{}}}}}, {==}, {==}, pf, {==}))
  Equal.cong(Array<U32> & List<&2, Word(64n)>, Array<U32> & T.Metrics, r => F.m_fin(r), F.m_step(0, F.m_step(1, F.m_step(2, F.m_step(3, F.m_step(4, (AR.thaw(U32, tc), Nil{})))))), (AR.thaw(U32, tc), Con{ST.pk(cs, 0n, 1n), Con{ST.pk(cs, 2n, 3n), Con{ST.pk(cs, 4n, 5n), Con{ST.pk(cs, 6n, 7n), Con{ST.pk(cs, 8n, 9n), Nil{}}}}}}), s0)

def metrics_real(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {F.metrics(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl})) == (ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), ST.mets(AR.slots(U32, tc))) : F.Fast<V> & T.Metrics}:
  Equal.cong(Array<U32> & T.Metrics, F.Fast<V> & T.Metrics, r => F.metrics_fin(~V, cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), table, AR.thaw(String, tk), AR.thaw(F.Slot<V>, te), F.CH{DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, r), F.to_metrics(AR.thaw(U32, tc)), (AR.thaw(U32, tc), ST.mets(AR.slots(U32, tc))), metrics_ok(tc, ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)))

# ---- len ----

def len_obs(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {U32.from_nat(SC.length(Nat, ord)) == U32.from_nat(S.len(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord))) : U32}:
  Equal.cong(Nat, U32, z => U32.from_nat(z), SC.length(Nat, ord), S.len(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord)), Equal.sym(Nat, S.len(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord)), SC.length(Nat, ord), EN.len_ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord, ST.g_occ(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))))

# ---- purge ----

def pg_sh(-V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>) -> ST.Shadow<V>:
  ST.Sh{cap, 0n, depth, life, AR.trep(U32, 4n, 0), Map.new(&2, Maybe<&2, U32>), tk, te, tp, tn, Nil{}, Nil{}}

def purge_real(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>) -> {F.purge(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl})) == (ST.real(~V, pg_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn)), U32.from_nat(SC.length(Nat, ord))) : F.Fast<V> & U32}:
  Equal.cong(Array<U32>, F.Fast<V> & U32, z => (F.F{cap, 0, 0, U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), z, Map.new(&2, Maybe<&2, U32>), AR.thaw(String, tk), AR.thaw(F.Slot<V>, te), F.CH{F.nil(), F.nil(), F.nil(), AR.thaw(U32, tp), AR.thaw(U32, tn)}}, U32.from_nat(SC.length(Nat, ord))), F.zero_ctr(), AR.thaw(U32, AR.trep(U32, 4n, 0)), AR.new(U32, 4n, 0))

def purge_inv(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {ST.good(~V, pg_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn)) == True{} : Bool}:
  ST.inv_mk(~V, cap, 0n, depth, life, AR.trep(U32, 4n, 0), Map.new(&2, Maybe<&2, U32>), tk, te, tp, tn, Nil{}, Nil{},
    ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_tk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_tp(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_tn(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), AR.trep_perfect(U32, 4n, 0), N.zero_le(SC.pow2(depth)),
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, ST.g_cap(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), N.zero_le(U32.to_nat(cap)))

def purge_model(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>) -> {ST.model(~V, pg_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn)) == S.LM{cap, life, Nil{}, T.zero_metrics()} : S.Model<V>}:
  {==}
