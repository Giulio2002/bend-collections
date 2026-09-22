import ./packed_zero.bend as OptZero
import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../spec/lru_fast.bend as S
import ../../spec/lru_numeric.bend as NS
import ../../src/lru/fast.bend as F
import ../../types/lru_model.bend as T
import ../../types/lru_fast.bend as E
import ./state.bend as ST
import ./table.bend as TB
import ./ents.bend as EN
import ./remove.bend as RM
import ./read.bend as RD
import ./addop.bend as AO
import ./simple.bend as SI
import ./resize.bend as RZ
import ./keys.bend as KY

# One public operation of the indexed LRU against the spec: the runtime step on
# the abstraction of a good shadow is the abstraction of a good shadow, the two
# observations agree, and the model follows the spec step. The capacity premise
# (to_nat(cap) <= 2^q, q <= 31, and every Resize capacity within 2^q) bounds
# the arrays.

def scap(-V: Data, sh: ST.Shadow<V>) -> U32:
  match sh:
    case ST.Sh{+cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}:
      cap

def mcap(-V: Data, m: S.Model<V>) -> U32:
  match m:
    case S.LM{+cap, life, xs, c}:
      cap

def op_ok(-V: Data, +q: Nat, op: E.Op<V>) -> Bool:
  match op:
    case E.Resize{+c}:
      Nat.is_le(U32.to_nat(c), SC.pow2(q))
    case _:
      True{}

def StepOK(~V: Data, sh: ST.Shadow<V>, op: E.Op<V>) -> Type:
  Sigma<&1, &1, ST.Shadow<V>, sh2 => Sigma<&1, &1, E.Obs<V>, o => {F.step(~V, ST.real(~V, sh), op) == (ST.real(~V, sh2), o) : F.Fast<V> & E.Obs<V>} & ({ST.good(~V, sh2) == True{} : Bool} & {(ST.model(~V, sh2), o) == S.step(V, ST.model(~V, sh), op) : S.Model<V> & E.Obs<V>})>>

def mk(~V: Data, -sh: ST.Shadow<V>, -op: E.Op<V>, sh2: ST.Shadow<V>, o: E.Obs<V>, e1: {F.step(~V, ST.real(~V, sh), op) == (ST.real(~V, sh2), o) : F.Fast<V> & E.Obs<V>}, e2: {ST.good(~V, sh2) == True{} : Bool}, e3: {(ST.model(~V, sh2), o) == S.step(V, ST.model(~V, sh), op) : S.Model<V> & E.Obs<V>}) -> StepOK(~V, sh, op):
  (sh2, (o, (e1, (e2, e3))))

# ---- ghost pairs ----

def gs(-V: Data, g: ST.Shadow<V> & Maybe<&2, V>) -> ST.Shadow<V>:
  (s, v) = g
  s

def gv(-V: Data, g: ST.Shadow<V> & Maybe<&2, V>) -> Maybe<&2, V>:
  (s, v) = g
  v

def rp_val(~V: Data, g: ST.Shadow<V> & Maybe<&2, V>) -> {F.obs_val(~V, RM.rp(~V, g)) == (ST.real(~V, gs(V, g)), E.OVal{gv(V, g)}) : F.Fast<V> & E.Obs<V>}:
  (s, v) = g
  {==}

def mp_val(~V: Data, g: ST.Shadow<V> & Maybe<&2, V>) -> {S.pair_obs(V, RM.mp(~V, g)) == (ST.model(~V, gs(V, g)), E.OVal{gv(V, g)}) : S.Model<V> & E.Obs<V>}:
  (s, v) = g
  {==}

def gp_eq(~V: Data, g: ST.Shadow<V> & Maybe<&2, V>) -> {RM.gp(~V, g) == ST.good(~V, gs(V, g)) : Bool}:
  (s, v) = g
  {==}

def vflag(-V: Data, m: Maybe<&2, V>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

def rf_m(~V: Data, +s: ST.Shadow<V>, m: Maybe<&2, V>) -> {F.obs_flag(~V, F.is_some_v(~V, (ST.real(~V, s), m))) == (ST.real(~V, s), E.OFlag{vflag(V, m)}) : F.Fast<V> & E.Obs<V>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def rp_flag(~V: Data, g: ST.Shadow<V> & Maybe<&2, V>) -> {F.obs_flag(~V, F.is_some_v(~V, RM.rp(~V, g))) == (ST.real(~V, gs(V, g)), E.OFlag{vflag(V, gv(V, g))}) : F.Fast<V> & E.Obs<V>}:
  (+s, v) = g
  rf_m(~V, s, v)

def mf_m(~V: Data, +s: ST.Shadow<V>, m: Maybe<&2, V>) -> {S.flag_obs(V, (ST.model(~V, s), m)) == (ST.model(~V, s), E.OFlag{vflag(V, m)}) : S.Model<V> & E.Obs<V>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def mp_flag(~V: Data, g: ST.Shadow<V> & Maybe<&2, V>) -> {S.flag_obs(V, RM.mp(~V, g)) == (ST.model(~V, gs(V, g)), E.OFlag{vflag(V, gv(V, g))}) : S.Model<V> & E.Obs<V>}:
  (+s, v) = g
  mf_m(~V, s, v)

def bs(-V: Data, g: ST.Shadow<V> & Bool) -> ST.Shadow<V>:
  (s, b) = g
  s

def bb(-V: Data, g: ST.Shadow<V> & Bool) -> Bool:
  (s, b) = g
  b

def ap_flag(~V: Data, g: ST.Shadow<V> & Bool) -> {F.obs_flag(~V, AO.apb(~V, g)) == (ST.real(~V, bs(V, g)), E.OFlag{bb(V, g)}) : F.Fast<V> & E.Obs<V>}:
  (s, b) = g
  {==}

def mp_b(~V: Data, g: ST.Shadow<V> & Bool) -> {AO.mpb(~V, g) == (ST.model(~V, bs(V, g)), E.OFlag{bb(V, g)}) : S.Model<V> & E.Obs<V>}:
  (s, b) = g
  {==}

def gp_b(~V: Data, g: ST.Shadow<V> & Bool) -> {AO.gpb(~V, g) == ST.good(~V, bs(V, g)) : Bool}:
  (s, b) = g
  {==}

# ---- the operations ----

def len_ok(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> StepOK(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Len{}):
  mk(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Len{}, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.ONum{U32.from_nat(SC.length(Nat, ord))}, {==}, h,
    Equal.cong(U32, S.Model<V> & E.Obs<V>, z => (ST.model(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), E.ONum{z}), U32.from_nat(SC.length(Nat, ord)), U32.from_nat(S.len(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord))), SI.len_obs(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)))

def cap_ok(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> StepOK(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Capacity{}):
  mk(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Capacity{}, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.ONum{cap}, {==}, h, {==})

def life_ok(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +ns: T.Int64, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> StepOK(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.SetLifetime{ns}):
  mk(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.SetLifetime{ns}, ST.Sh{cap, fresh, depth, ns, tc, table, tk, te, tp, tn, ord, fl}, E.OUnit{}, Equal.cong(F.Fast<V>, F.Fast<V> & E.Obs<V>, z => (z, E.OUnit{}), F.set_lifetime(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), ns), OptZero.original(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), ns), OptZero.lifetime_ok(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), ns)), h, {==})

def metrics_ok(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> StepOK(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Metrics{}):
  mk(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Metrics{}, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.OMetrics{ST.mets(AR.slots(U32, tc))},
    Equal.cong(F.Fast<V> & T.Metrics, F.Fast<V> & E.Obs<V>, r => F.obs_metrics(~V, r), F.metrics(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl})), (ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), ST.mets(AR.slots(U32, tc))), SI.metrics_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)),
    h, {==})

def purge_ok(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> StepOK(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Purge{}):
  mk(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Purge{}, SI.pg_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn), E.ONum{U32.from_nat(SC.length(Nat, ord))},
    Equal.cong(F.Fast<V> & U32, F.Fast<V> & E.Obs<V>, r => F.obs_num(~V, r), F.purge(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl})), (ST.real(~V, SI.pg_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn)), U32.from_nat(SC.length(Nat, ord))), SI.purge_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl)),
    SI.purge_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h),
    Equal.cong(U32, S.Model<V> & E.Obs<V>, z => (ST.model(~V, SI.pg_sh(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn)), E.ONum{z}), U32.from_nat(SC.length(Nat, ord)), U32.from_nat(S.len(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord))), SI.len_obs(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)))

def remove_ok(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> StepOK(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Remove{key}):
  mk(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Remove{key}, gs(V, RM.rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key))), E.OVal{gv(V, RM.rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key)))},
    Equal.trans(F.Fast<V> & E.Obs<V>, F.obs_val(~V, F.remove(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key)), F.obs_val(~V, RM.rp(~V, RM.rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key)))), (ST.real(~V, gs(V, RM.rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key)))), E.OVal{gv(V, RM.rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key)))}),
      Equal.cong(F.Fast<V> & Maybe<&2, V>, F.Fast<V> & E.Obs<V>, r => F.obs_val(~V, r), F.remove(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key), RM.rp(~V, RM.rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key))), RM.remove_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, h)),
      rp_val(~V, RM.rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key)))),
    Equal.trans(Bool, ST.good(~V, gs(V, RM.rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key)))), RM.gp(~V, RM.rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key))), True{}, Equal.sym(Bool, RM.gp(~V, RM.rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key))), ST.good(~V, gs(V, RM.rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key)))), gp_eq(~V, RM.rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key)))), RM.remove_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, h)),
    Equal.sym(S.Model<V> & E.Obs<V>, S.pair_obs(V, S.remove(V, ST.model(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key)), (ST.model(~V, gs(V, RM.rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key)))), E.OVal{gv(V, RM.rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key)))}),
      Equal.trans(S.Model<V> & E.Obs<V>, S.pair_obs(V, S.remove(V, ST.model(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key)), S.pair_obs(V, RM.mp(~V, RM.rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key)))), (ST.model(~V, gs(V, RM.rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key)))), E.OVal{gv(V, RM.rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key)))}),
        Equal.cong(S.Model<V> & Maybe<&2, V>, S.Model<V> & E.Obs<V>, r => S.pair_obs(V, r), S.remove(V, ST.model(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key), RM.mp(~V, RM.rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key))), RM.remove_model(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, h)),
        mp_val(~V, RM.rm_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, TB.lk(table, key))))))

def rg(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +now: T.Int64, +tracked: Bool) -> ST.Shadow<V> & Maybe<&2, V>:
  RD.rd_ghost(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked, TB.lk(table, key))

def rd_step_real(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +now: T.Int64, +tracked: Bool, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {F.obs_val(~V, F.read(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, F.int_stamp(now), tracked)) == (ST.real(~V, gs(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked))), E.OVal{gv(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked))}) : F.Fast<V> & E.Obs<V>}:
  Equal.trans(F.Fast<V> & E.Obs<V>, F.obs_val(~V, F.read(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, F.int_stamp(now), tracked)), F.obs_val(~V, RM.rp(~V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked))), (ST.real(~V, gs(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked))), E.OVal{gv(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked))}),
    Equal.cong(F.Fast<V> & Maybe<&2, V>, F.Fast<V> & E.Obs<V>, r => F.obs_val(~V, r), F.read(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, F.int_stamp(now), tracked), RM.rp(~V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked)), RD.read_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked, h)),
    rp_val(~V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked)))

def rd_step_good(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +now: T.Int64, +tracked: Bool, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {ST.good(~V, gs(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked))) == True{} : Bool}:
  Equal.trans(Bool, ST.good(~V, gs(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked))), RM.gp(~V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked)), True{}, Equal.sym(Bool, RM.gp(~V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked)), ST.good(~V, gs(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked))), gp_eq(~V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked))), RD.read_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked, h))

def rd_step_model(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +now: T.Int64, +tracked: Bool, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {(ST.model(~V, gs(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked))), E.OVal{gv(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked))}) == S.pair_obs(V, S.read(V, ST.model(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, now, tracked)) : S.Model<V> & E.Obs<V>}:
  Equal.sym(S.Model<V> & E.Obs<V>, S.pair_obs(V, S.read(V, ST.model(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, now, tracked)), (ST.model(~V, gs(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked))), E.OVal{gv(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked))}),
    Equal.trans(S.Model<V> & E.Obs<V>, S.pair_obs(V, S.read(V, ST.model(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, now, tracked)), S.pair_obs(V, RM.mp(~V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked))), (ST.model(~V, gs(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked))), E.OVal{gv(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked))}),
      Equal.cong(S.Model<V> & Maybe<&2, V>, S.Model<V> & E.Obs<V>, r => S.pair_obs(V, r), S.read(V, ST.model(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, now, tracked), RM.mp(~V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked)), RD.read_model(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked, h)),
      mp_val(~V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, tracked))))

def get_ok(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +now: T.Int64, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> StepOK(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Get{key, now}):
  mk(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Get{key, now}, gs(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, True{})), E.OVal{gv(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, True{}))}, rd_step_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, True{}, h), rd_step_good(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, True{}, h), rd_step_model(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, True{}, h))

def peek_ok(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +now: T.Int64, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> StepOK(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Peek{key, now}):
  mk(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Peek{key, now}, gs(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{})), E.OVal{gv(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{}))}, rd_step_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{}, h), rd_step_good(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{}, h), rd_step_model(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{}, h))

def contains_ok(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +now: T.Int64, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> StepOK(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Contains{key, now}):
  mk(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Contains{key, now}, gs(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{})), E.OFlag{vflag(V, gv(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{})))},
    Equal.trans(F.Fast<V> & E.Obs<V>, F.obs_flag(~V, F.is_some_v(~V, F.read(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, F.int_stamp(now), False{}))), F.obs_flag(~V, F.is_some_v(~V, RM.rp(~V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{})))), (ST.real(~V, gs(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{}))), E.OFlag{vflag(V, gv(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{})))}),
      Equal.cong(F.Fast<V> & Maybe<&2, V>, F.Fast<V> & E.Obs<V>, r => F.obs_flag(~V, F.is_some_v(~V, r)), F.read(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, F.int_stamp(now), False{}), RM.rp(~V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{})), RD.read_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{}, h)),
      rp_flag(~V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{}))),
    rd_step_good(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{}, h),
    Equal.sym(S.Model<V> & E.Obs<V>, S.flag_obs(V, S.read(V, ST.model(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, now, False{})), (ST.model(~V, gs(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{}))), E.OFlag{vflag(V, gv(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{})))}),
      Equal.trans(S.Model<V> & E.Obs<V>, S.flag_obs(V, S.read(V, ST.model(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, now, False{})), S.flag_obs(V, RM.mp(~V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{}))), (ST.model(~V, gs(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{}))), E.OFlag{vflag(V, gv(V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{})))}),
        Equal.cong(S.Model<V> & Maybe<&2, V>, S.Model<V> & E.Obs<V>, r => S.flag_obs(V, r), S.read(V, ST.model(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, now, False{}), RM.mp(~V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{})), RD.read_model(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{}, h)),
        mp_flag(~V, rg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, False{})))))

def ag(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +v: V, +now: T.Int64) -> ST.Shadow<V> & Bool:
  AO.ad_ghost(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, TB.lk(table, key), U32.is_le(cap, U32.from_nat(SC.length(Nat, ord))))

def add_ok(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +key: String, +v: V, +now: T.Int64, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hcq: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}) -> StepOK(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Add{key, v, now}):
  mk(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Add{key, v, now}, bs(V, ag(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now)), E.OFlag{bb(V, ag(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now))},
    Equal.trans(F.Fast<V> & E.Obs<V>, F.obs_flag(~V, F.add(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, v, F.int_stamp(now))), F.obs_flag(~V, AO.apb(~V, ag(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now))), (ST.real(~V, bs(V, ag(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now))), E.OFlag{bb(V, ag(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now))}),
      Equal.cong(F.Fast<V> & Bool, F.Fast<V> & E.Obs<V>, r => F.obs_flag(~V, r), F.add(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), key, v, F.int_stamp(now)), AO.apb(~V, ag(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now)), AO.add_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, h, q, hq, hcq)),
      ap_flag(~V, ag(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now))),
    Equal.trans(Bool, ST.good(~V, bs(V, ag(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now))), AO.gpb(~V, ag(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now)), True{}, Equal.sym(Bool, AO.gpb(~V, ag(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now)), ST.good(~V, bs(V, ag(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now))), gp_b(~V, ag(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now))), AO.add_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, h, q, hq, hcq)),
    Equal.sym(S.Model<V> & E.Obs<V>, S.add_found(V, cap, life, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), ST.mets(AR.slots(U32, tc)), key, S.En{key, v, NS.deadline(now, life)}, S.find(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), key)), (ST.model(~V, bs(V, ag(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now))), E.OFlag{bb(V, ag(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now))}),
      Equal.trans(S.Model<V> & E.Obs<V>, S.add_found(V, cap, life, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), ST.mets(AR.slots(U32, tc)), key, S.En{key, v, NS.deadline(now, life)}, S.find(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), key)), AO.mpb(~V, ag(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now)), (ST.model(~V, bs(V, ag(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now))), E.OFlag{bb(V, ag(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now))}),
        AO.add_model(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, h, q, hq, hcq),
        mp_b(~V, ag(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now)))))

# ---- resize ----

def sub_le(a: Nat, b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ +ap 0n:
      N.le_refl(1n+ap)
    case 1n+ +ap 1n+ +bp:
      N.le_trans(Nat.sub(ap, bp), ap, 1n+ap, sub_le(ap, bp), N.le_succ(ap))

def rzg(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +c: U32) -> ST.Shadow<V> & Nat:
  RZ.sr_g(V, SC.length(Nat, ord), ST.Sh{c, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl})

def zs(-V: Data, g: ST.Shadow<V> & Nat) -> ST.Shadow<V>:
  (s, k) = g
  s

def zk(-V: Data, g: ST.Shadow<V> & Nat) -> Nat:
  (s, k) = g
  k

def rz_fin(~V: Data, g: ST.Shadow<V> & Nat) -> {F.obs_resized(~V, F.resize_fin(~V, RZ.srp(~V, g, 0n))) == (ST.real(~V, zs(V, g)), E.OResized{Done{U32.from_nat(zk(V, g))}}) : F.Fast<V> & E.Obs<V>}:
  (+s, +k) = g
  Equal.cong(Nat, F.Fast<V> & E.Obs<V>, z => (ST.real(~V, s), E.OResized{Done{U32.from_nat(z)}}), Nat.add(k, 0n), k, N.add_zero(k))

def rz_mp(~V: Data, g: ST.Shadow<V> & Nat) -> {RZ.sr_mp(~V, g) == (ST.model(~V, zs(V, g)), zk(V, g)) : S.Model<V> & Nat}:
  (s, k) = g
  {==}

def rz_gd(~V: Data, g: ST.Shadow<V> & Nat) -> {RZ.sr_gd(~V, g) == ST.good(~V, zs(V, g)) : Bool}:
  (s, k) = g
  {==}

def rzo(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +c: U32, zero: Bool) -> ST.Shadow<V> & E.Obs<V>:
  match zero:
    case True{}:
      (ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.OResized{Fail{"capacity must be positive"}})
    case False{}:
      (zs(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c)), E.OResized{Done{U32.from_nat(zk(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c)))}})

def os(-V: Data, g: ST.Shadow<V> & E.Obs<V>) -> ST.Shadow<V>:
  (s, o) = g
  s

def oo(-V: Data, g: ST.Shadow<V> & E.Obs<V>) -> E.Obs<V>:
  (s, o) = g
  o

def rz_c(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +c: U32, zero: Bool, +ez: {U32.is_eq(c, 0) == zero : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {F.obs_resized(~V, F.resize_go(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), c, zero)) == (ST.real(~V, os(V, rzo(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c, zero))), oo(V, rzo(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c, zero))) : F.Fast<V> & E.Obs<V>}:
  match zero:
    case True{}:
      {==}
    case False{}:
      +e1 = Equal.cong(Nat, F.Fast<V> & E.Obs<V>, n => F.obs_resized(~V, F.resize_fin(~V, F.shrink(~V, n, c, F.SR{ST.real(~V, ST.Sh{c, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), 0}))), U32.to_nat(U32.from_nat(SC.length(Nat, ord))), SC.length(Nat, ord), AO.len_nat(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
      +e2 = Equal.cong(F.Shr<V>, F.Fast<V> & E.Obs<V>, r => F.obs_resized(~V, F.resize_fin(~V, r)), F.shrink(~V, SC.length(Nat, ord), c, F.SR{ST.real(~V, ST.Sh{c, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), U32.from_nat(0n)}), RZ.srp(~V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c), 0n), RZ.sr_real(~V, SC.length(Nat, ord), cap, c, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, 0n, h))
      Equal.trans(F.Fast<V> & E.Obs<V>, F.obs_resized(~V, F.resize_fin(~V, F.shrink(~V, U32.to_nat(U32.from_nat(SC.length(Nat, ord))), c, F.SR{ST.real(~V, ST.Sh{c, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), 0}))), F.obs_resized(~V, F.resize_fin(~V, F.shrink(~V, SC.length(Nat, ord), c, F.SR{ST.real(~V, ST.Sh{c, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), 0}))), (ST.real(~V, zs(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c))), E.OResized{Done{U32.from_nat(zk(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c)))}}),
        e1, Equal.trans(F.Fast<V> & E.Obs<V>, F.obs_resized(~V, F.resize_fin(~V, F.shrink(~V, SC.length(Nat, ord), c, F.SR{ST.real(~V, ST.Sh{c, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), 0}))), F.obs_resized(~V, F.resize_fin(~V, RZ.srp(~V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c), 0n))), (ST.real(~V, zs(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c))), E.OResized{Done{U32.from_nat(zk(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c)))}}), e2, rz_fin(~V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c))))

def rz_good(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +c: U32, zero: Bool, +ez: {U32.is_eq(c, 0) == zero : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {ST.good(~V, os(V, rzo(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c, zero))) == True{} : Bool}:
  match zero:
    case True{}:
      h
    case False{}:
      +k = Nat.sub(SC.length(Nat, ord), U32.to_nat(c))
      +hc = L.not_false(U32.is_eq(c, 0), ez)
      Equal.trans(Bool, ST.good(~V, zs(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c))), RZ.sr_gd(~V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c)), True{}, Equal.sym(Bool, RZ.sr_gd(~V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c)), ST.good(~V, zs(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c))), rz_gd(~V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c))), RZ.sr_inv(~V, SC.length(Nat, ord), cap, c, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, k, {==}, sub_le(SC.length(Nat, ord), U32.to_nat(c)), hc, h))

def rz_model(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +c: U32, zero: Bool, +ez: {U32.is_eq(c, 0) == zero : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {(ST.model(~V, os(V, rzo(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c, zero))), oo(V, rzo(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c, zero))) == S.resize_go(V, cap, life, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), ST.mets(AR.slots(U32, tc)), c, zero) : S.Model<V> & E.Obs<V>}:
  match zero:
    case True{}:
      {==}
    case False{}:
      +xs = ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord)
      +k = Nat.sub(SC.length(Nat, ord), U32.to_nat(c))
      +r = Equal.trans(S.Model<V> & Nat, (ST.model(~V, zs(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c))), zk(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c))), RZ.sr_mp(~V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c)), (S.LM{c, life, S.dropn(V, k, xs), S.bumpn(k, 1n, ST.mets(AR.slots(U32, tc)))}, k), Equal.sym(S.Model<V> & Nat, RZ.sr_mp(~V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c)), (ST.model(~V, zs(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c))), zk(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c))), rz_mp(~V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c))), RZ.sr_model(~V, SC.length(Nat, ord), cap, c, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, k, {==}, sub_le(SC.length(Nat, ord), U32.to_nat(c)), h))
      +em = L.pair_fst(S.Model<V>, Nat, ST.model(~V, zs(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c))), zk(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c)), S.LM{c, life, S.dropn(V, k, xs), S.bumpn(k, 1n, ST.mets(AR.slots(U32, tc)))}, k, r)
      +ek = L.pair_snd(S.Model<V>, Nat, ST.model(~V, zs(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c))), zk(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c)), S.LM{c, life, S.dropn(V, k, xs), S.bumpn(k, 1n, ST.mets(AR.slots(U32, tc)))}, k, r)
      +elen = Equal.cong(Nat, Nat, z => Nat.sub(z, U32.to_nat(c)), SC.length(Nat, ord), S.len(V, xs), Equal.sym(Nat, S.len(V, xs), SC.length(Nat, ord), EN.len_ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord, ST.g_occ(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))))
      +e1 = Equal.trans(S.Model<V> & E.Obs<V>, (ST.model(~V, zs(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c))), E.OResized{Done{U32.from_nat(zk(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c)))}}), (S.LM{c, life, S.dropn(V, k, xs), S.bumpn(k, 1n, ST.mets(AR.slots(U32, tc)))}, E.OResized{Done{U32.from_nat(zk(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c)))}}), (S.LM{c, life, S.dropn(V, k, xs), S.bumpn(k, 1n, ST.mets(AR.slots(U32, tc)))}, E.OResized{Done{U32.from_nat(k)}}),
        Equal.cong(S.Model<V>, S.Model<V> & E.Obs<V>, z => (z, E.OResized{Done{U32.from_nat(zk(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c)))}}), ST.model(~V, zs(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c))), S.LM{c, life, S.dropn(V, k, xs), S.bumpn(k, 1n, ST.mets(AR.slots(U32, tc)))}, em),
        Equal.cong(Nat, S.Model<V> & E.Obs<V>, z => (S.LM{c, life, S.dropn(V, k, xs), S.bumpn(k, 1n, ST.mets(AR.slots(U32, tc)))}, E.OResized{Done{U32.from_nat(z)}}), zk(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c)), k, ek))
      Equal.trans(S.Model<V> & E.Obs<V>, (ST.model(~V, zs(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c))), E.OResized{Done{U32.from_nat(zk(V, rzg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c)))}}), (S.LM{c, life, S.dropn(V, k, xs), S.bumpn(k, 1n, ST.mets(AR.slots(U32, tc)))}, E.OResized{Done{U32.from_nat(k)}}), S.resize_go(V, cap, life, xs, ST.mets(AR.slots(U32, tc)), c, False{}),
        e1,
        Equal.cong(Nat, S.Model<V> & E.Obs<V>, z => (S.LM{c, life, S.dropn(V, z, xs), S.bumpn(z, 1n, ST.mets(AR.slots(U32, tc)))}, E.OResized{Done{U32.from_nat(z)}}), k, Nat.sub(S.len(V, xs), U32.to_nat(c)), elen))

def resize_ok(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +c: U32, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> StepOK(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Resize{c}):
  mk(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Resize{c}, os(V, rzo(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c, U32.is_eq(c, 0))), oo(V, rzo(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c, U32.is_eq(c, 0))),
    rz_c(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c, U32.is_eq(c, 0), {==}, h), rz_good(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c, U32.is_eq(c, 0), {==}, h), rz_model(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c, U32.is_eq(c, 0), {==}, h))

# ---- keys ----

def kg(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +now: T.Int64) -> ST.Shadow<V>:
  KY.st_g(V, SC.length(Nat, ord), ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, now)

def keys_ok(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +now: T.Int64, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> StepOK(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Keys{now}):
  +g2 = KY.st_inv(~V, SC.length(Nat, ord), cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now, N.le_refl(SC.length(Nat, ord)), h)
  +e1 = Equal.cong(Nat, F.Fast<V> & E.Obs<V>, n => F.obs_keys(~V, F.keys_list(~V, F.exp_go(~V, n, F.int_stamp(now), (ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), True{})))), U32.to_nat(U32.from_nat(SC.length(Nat, ord))), SC.length(Nat, ord), AO.len_nat(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
  +e2 = Equal.cong(F.Fast<V>, F.Fast<V> & E.Obs<V>, f => F.obs_keys(~V, F.keys_list(~V, f)), F.exp_go(~V, SC.length(Nat, ord), F.int_stamp(now), (ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), True{})), ST.real(~V, kg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now)), KY.st_real(~V, SC.length(Nat, ord), cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now, N.le_refl(SC.length(Nat, ord)), h))
  mk(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, E.Keys{now}, kg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now), E.OKeys{S.keys(V, KY.ents_of(V, kg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now)))},
    Equal.trans(F.Fast<V> & E.Obs<V>, F.obs_keys(~V, F.keys_list(~V, F.exp_go(~V, U32.to_nat(U32.from_nat(SC.length(Nat, ord))), F.int_stamp(now), (ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), True{})))), F.obs_keys(~V, F.keys_list(~V, F.exp_go(~V, SC.length(Nat, ord), F.int_stamp(now), (ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), True{})))), (ST.real(~V, kg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now)), E.OKeys{S.keys(V, KY.ents_of(V, kg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now)))}),
      e1, Equal.trans(F.Fast<V> & E.Obs<V>, F.obs_keys(~V, F.keys_list(~V, F.exp_go(~V, SC.length(Nat, ord), F.int_stamp(now), (ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), True{})))), F.obs_keys(~V, F.keys_list(~V, ST.real(~V, kg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now)))), (ST.real(~V, kg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now)), E.OKeys{S.keys(V, KY.ents_of(V, kg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now)))}), e2, KY.klist_ok(~V, kg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now), g2))),
    g2,
    Equal.sym(S.Model<V> & E.Obs<V>, S.keys_fin(V, cap, life, S.strip(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), ST.mets(AR.slots(U32, tc)), now)), KY.kobs(~V, kg(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now)), KY.st_model(~V, SC.length(Nat, ord), cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now, N.le_refl(SC.length(Nat, ord)), h)))
