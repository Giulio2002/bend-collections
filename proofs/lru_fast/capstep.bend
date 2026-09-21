import Base
import ../lib/logic.bend as L
import ../../spec/common.bend as SC
import ../../spec/lru_fast.bend as S
import ../../spec/lru_numeric.bend as NS
import ../../types/lru_model.bend as T
import ../../types/lru_fast.bend as E

# Every spec step keeps the capacity, except Resize to a positive capacity,
# which installs it: a capacity bound 2^q carries through a trace whose Resize
# capacities are within 2^q.

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

def fst_m(-V: Data, r: S.Model<V> & Maybe<&2, V>) -> S.Model<V>:
  Pair.fst(S.Model<V>, Maybe<&2, V>, r)

def fst_o(-V: Data, r: S.Model<V> & E.Obs<V>) -> S.Model<V>:
  Pair.fst(S.Model<V>, E.Obs<V>, r)

# ---- reads keep the capacity ----

def rl_cap(-V: Data, +cap: U32, +life: T.Int64, +xs: List<&2, S.Ent<V>>, +m: T.Metrics, +key: String, +x: S.Ent<V>, tracked: Bool) -> {mcap(V, fst_m(V, S.read_live(V, cap, life, xs, m, key, x, tracked))) == cap : U32}:
  match tracked:
    case False{}:
      {==}
    case True{}:
      {==}

def re_cap(-V: Data, +cap: U32, +life: T.Int64, +xs: List<&2, S.Ent<V>>, +m: T.Metrics, +key: String, +x: S.Ent<V>, +tracked: Bool, expired: Bool) -> {mcap(V, fst_m(V, S.read_expiry(V, cap, life, xs, m, key, x, tracked, expired))) == cap : U32}:
  match expired:
    case True{}:
      {==}
    case False{}:
      rl_cap(V, cap, life, xs, m, key, x, tracked)

def rx_cap(-V: Data, +cap: U32, +life: T.Int64, +xs: List<&2, S.Ent<V>>, +m: T.Metrics, +key: String, x: S.Ent<V>, +now: T.Int64, +tracked: Bool) -> {mcap(V, fst_m(V, S.read_ent(V, cap, life, xs, m, key, x, now, tracked))) == cap : U32}:
  match x:
    case S.En{+k, +v, +d}:
      re_cap(V, cap, life, xs, m, key, S.En{k, v, d}, tracked, NS.expired(d, now))

def rf_cap(-V: Data, +cap: U32, +life: T.Int64, +xs: List<&2, S.Ent<V>>, +m: T.Metrics, +key: String, +now: T.Int64, +tracked: Bool, found: Maybe<&2, S.Ent<V>>) -> {mcap(V, fst_m(V, S.read_found(V, cap, life, xs, m, key, now, tracked, found))) == cap : U32}:
  match found:
    case None{}:
      {==}
    case Some{x}:
      rx_cap(V, cap, life, xs, m, key, x, now, tracked)

def pair_fst(-V: Data, r: S.Model<V> & Maybe<&2, V>) -> {fst_o(V, S.pair_obs(V, r)) == fst_m(V, r) : S.Model<V>}:
  (s, v) = r
  {==}

def flag_fst_m(-V: Data, +s: S.Model<V>, v: Maybe<&2, V>) -> {fst_o(V, S.flag_obs(V, (s, v))) == s : S.Model<V>}:
  match v:
    case None{}:
      {==}
    case Some{x}:
      {==}

def flag_fst(-V: Data, r: S.Model<V> & Maybe<&2, V>) -> {fst_o(V, S.flag_obs(V, r)) == fst_m(V, r) : S.Model<V>}:
  (+s, v) = r
  flag_fst_m(V, s, v)

# ---- add, remove, keys ----

def aa_cap(-V: Data, +cap: U32, +life: T.Int64, +xs: List<&2, S.Ent<V>>, +m: T.Metrics, +e: S.Ent<V>, full: Bool) -> {mcap(V, fst_o(V, S.add_absent(V, cap, life, xs, m, e, full))) == cap : U32}:
  match full:
    case False{}:
      {==}
    case True{}:
      {==}

def af_cap(-V: Data, +cap: U32, +life: T.Int64, +xs: List<&2, S.Ent<V>>, +m: T.Metrics, +key: String, +e: S.Ent<V>, found: Maybe<&2, S.Ent<V>>) -> {mcap(V, fst_o(V, S.add_found(V, cap, life, xs, m, key, e, found))) == cap : U32}:
  match found:
    case None{}:
      aa_cap(V, cap, life, xs, m, e, U32.is_le(cap, U32.from_nat(S.len(V, xs))))
    case Some{old}:
      {==}

def rm_cap_x(-V: Data, +cap: U32, +life: T.Int64, +xs: List<&2, S.Ent<V>>, +m: T.Metrics, +key: String, x: S.Ent<V>) -> {mcap(V, fst_m(V, S.remove_found(V, cap, life, xs, m, key, Some{x}))) == cap : U32}:
  match x:
    case S.En{k, v, d}:
      {==}

def rm_cap(-V: Data, +cap: U32, +life: T.Int64, +xs: List<&2, S.Ent<V>>, +m: T.Metrics, +key: String, found: Maybe<&2, S.Ent<V>>) -> {mcap(V, fst_m(V, S.remove_found(V, cap, life, xs, m, key, found))) == cap : U32}:
  match found:
    case None{}:
      {==}
    case Some{x}:
      rm_cap_x(V, cap, life, xs, m, key, x)

def kf_cap(-V: Data, +cap: U32, +life: T.Int64, r: List<&2, S.Ent<V>> & T.Metrics) -> {mcap(V, fst_o(V, S.keys_fin(V, cap, life, r))) == cap : U32}:
  (xs, m) = r
  {==}

# ---- one step ----

def keep(-V: Data, +cap: U32, +q: Nat, +mc: U32, +e: {mc == cap : U32}, +hm: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}) -> {Nat.is_le(U32.to_nat(mc), SC.pow2(q)) == True{} : Bool}:
  L.subst(U32, z => {Nat.is_le(U32.to_nat(z), SC.pow2(q)) == True{} : Bool}, cap, mc, Equal.sym(U32, mc, cap, e), hm)

def rz_cap(-V: Data, +cap: U32, +life: T.Int64, +xs: List<&2, S.Ent<V>>, +m: T.Metrics, +c: U32, +q: Nat, +hm: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}, +hop: {Nat.is_le(U32.to_nat(c), SC.pow2(q)) == True{} : Bool}, zero: Bool) -> {Nat.is_le(U32.to_nat(mcap(V, fst_o(V, S.resize_go(V, cap, life, xs, m, c, zero)))), SC.pow2(q)) == True{} : Bool}:
  match zero:
    case True{}:
      hm
    case False{}:
      hop

def cap_step(-V: Data, m: S.Model<V>, op: E.Op<V>, +q: Nat, +hm: {Nat.is_le(U32.to_nat(mcap(V, m)), SC.pow2(q)) == True{} : Bool}, +hop: {op_ok(V, q, op) == True{} : Bool}) -> {Nat.is_le(U32.to_nat(mcap(V, fst_o(V, S.step(V, m, op)))), SC.pow2(q)) == True{} : Bool}:
  match m:
    case S.LM{+cap, +life, +xs, +mt}:
      match op:
        case E.Len{}:
          hm
        case E.Capacity{}:
          hm
        case E.SetLifetime{+ns}:
          hm
        case E.Metrics{}:
          hm
        case E.Add{+key, +v, +now}:
          keep(V, cap, q, mcap(V, fst_o(V, S.add_found(V, cap, life, xs, mt, key, S.En{key, v, NS.deadline(now, life)}, S.find(V, xs, key)))), af_cap(V, cap, life, xs, mt, key, S.En{key, v, NS.deadline(now, life)}, S.find(V, xs, key)), hm)
        case E.Get{+key, +now}:
          keep(V, cap, q, mcap(V, fst_o(V, S.pair_obs(V, S.read_found(V, cap, life, xs, mt, key, now, True{}, S.find(V, xs, key))))), Equal.trans(U32, mcap(V, fst_o(V, S.pair_obs(V, S.read_found(V, cap, life, xs, mt, key, now, True{}, S.find(V, xs, key))))), mcap(V, fst_m(V, S.read_found(V, cap, life, xs, mt, key, now, True{}, S.find(V, xs, key)))), cap, Equal.cong(S.Model<V>, U32, z => mcap(V, z), fst_o(V, S.pair_obs(V, S.read_found(V, cap, life, xs, mt, key, now, True{}, S.find(V, xs, key)))), fst_m(V, S.read_found(V, cap, life, xs, mt, key, now, True{}, S.find(V, xs, key))), pair_fst(V, S.read_found(V, cap, life, xs, mt, key, now, True{}, S.find(V, xs, key)))), rf_cap(V, cap, life, xs, mt, key, now, True{}, S.find(V, xs, key))), hm)
        case E.Peek{+key, +now}:
          keep(V, cap, q, mcap(V, fst_o(V, S.pair_obs(V, S.read_found(V, cap, life, xs, mt, key, now, False{}, S.find(V, xs, key))))), Equal.trans(U32, mcap(V, fst_o(V, S.pair_obs(V, S.read_found(V, cap, life, xs, mt, key, now, False{}, S.find(V, xs, key))))), mcap(V, fst_m(V, S.read_found(V, cap, life, xs, mt, key, now, False{}, S.find(V, xs, key)))), cap, Equal.cong(S.Model<V>, U32, z => mcap(V, z), fst_o(V, S.pair_obs(V, S.read_found(V, cap, life, xs, mt, key, now, False{}, S.find(V, xs, key)))), fst_m(V, S.read_found(V, cap, life, xs, mt, key, now, False{}, S.find(V, xs, key))), pair_fst(V, S.read_found(V, cap, life, xs, mt, key, now, False{}, S.find(V, xs, key)))), rf_cap(V, cap, life, xs, mt, key, now, False{}, S.find(V, xs, key))), hm)
        case E.Contains{+key, +now}:
          keep(V, cap, q, mcap(V, fst_o(V, S.flag_obs(V, S.read_found(V, cap, life, xs, mt, key, now, False{}, S.find(V, xs, key))))), Equal.trans(U32, mcap(V, fst_o(V, S.flag_obs(V, S.read_found(V, cap, life, xs, mt, key, now, False{}, S.find(V, xs, key))))), mcap(V, fst_m(V, S.read_found(V, cap, life, xs, mt, key, now, False{}, S.find(V, xs, key)))), cap, Equal.cong(S.Model<V>, U32, z => mcap(V, z), fst_o(V, S.flag_obs(V, S.read_found(V, cap, life, xs, mt, key, now, False{}, S.find(V, xs, key)))), fst_m(V, S.read_found(V, cap, life, xs, mt, key, now, False{}, S.find(V, xs, key))), flag_fst(V, S.read_found(V, cap, life, xs, mt, key, now, False{}, S.find(V, xs, key)))), rf_cap(V, cap, life, xs, mt, key, now, False{}, S.find(V, xs, key))), hm)
        case E.Remove{+key}:
          keep(V, cap, q, mcap(V, fst_o(V, S.pair_obs(V, S.remove_found(V, cap, life, xs, mt, key, S.find(V, xs, key))))), Equal.trans(U32, mcap(V, fst_o(V, S.pair_obs(V, S.remove_found(V, cap, life, xs, mt, key, S.find(V, xs, key))))), mcap(V, fst_m(V, S.remove_found(V, cap, life, xs, mt, key, S.find(V, xs, key)))), cap, Equal.cong(S.Model<V>, U32, z => mcap(V, z), fst_o(V, S.pair_obs(V, S.remove_found(V, cap, life, xs, mt, key, S.find(V, xs, key)))), fst_m(V, S.remove_found(V, cap, life, xs, mt, key, S.find(V, xs, key))), pair_fst(V, S.remove_found(V, cap, life, xs, mt, key, S.find(V, xs, key)))), rm_cap(V, cap, life, xs, mt, key, S.find(V, xs, key))), hm)
        case E.Purge{}:
          hm
        case E.Resize{+c}:
          rz_cap(V, cap, life, xs, mt, c, q, hm, hop, U32.is_eq(c, 0))
        case E.Keys{+now}:
          keep(V, cap, q, mcap(V, fst_o(V, S.keys_fin(V, cap, life, S.strip(V, xs, mt, now)))), kf_cap(V, cap, life, S.strip(V, xs, mt, now)), hm)
