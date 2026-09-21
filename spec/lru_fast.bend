import Base
import ../types/lru_model.bend as T
import ../types/lru_fast.bend as E
import ./lru_numeric.bend as N

# Independent model of the LRU cache with lifetimes (the semantics of the
# retained reference/lru cache, restated for the indexed runtime
# src/lru/fast.bend): the capacity, the lifetime, the entries in RECENCY
# ORDER (oldest first) with their deadlines, and the five 64-bit counters
# (inserts, evictions, removals, hits, misses; T.bump counts one of them).
# A deadline of zero means "never expires" (N.deadline yields zero for a
# zero lifetime; N.expired never holds for it). Keys are compared with
# String.eq; the operations keep them distinct. Nothing here refers to maps,
# arrays or links.

type Ent<-V: Data> is Data:
  En{key: String, value: V, deadline: T.Int64}

type Model<-V: Data> is Data:
  LM{cap: U32, life: T.Int64, ents: List<&2, Ent<V>>, counts: T.Metrics}

def zero_time() -> T.Int64:
  T.I64{Word.zero(64n)}

# ---- list mathematics ----

def len(-V: Data, xs: List<&2, Ent<V>>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, t}:
      1n+len(V, t)

def find_at(-V: Data, b: Bool, x: Ent<V>, rest: Maybe<&2, Ent<V>>) -> Maybe<&2, Ent<V>>:
  match b:
    case True{}:
      Some{x}
    case False{}:
      rest

def find(-V: Data, xs: List<&2, Ent<V>>, +key: String) -> Maybe<&2, Ent<V>>:
  match xs:
    case Nil{}:
      None{}
    case Con{En{+k, v, d}, t}:
      find_at(V, String.eq(k, key), En{k, v, d}, find(V, t, key))

def drop_at(-V: Data, b: Bool, x: Ent<V>, rest: List<&2, Ent<V>>) -> List<&2, Ent<V>>:
  match b:
    case True{}:
      rest
    case False{}:
      Con{x, rest}

# the entries without the one for key
def drop(-V: Data, xs: List<&2, Ent<V>>, +key: String) -> List<&2, Ent<V>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{En{+k, v, d}, t}:
      drop_at(V, String.eq(k, key), En{k, v, d}, drop(V, t, key))

def snoc(-V: Data, xs: List<&2, Ent<V>>, y: Ent<V>) -> List<&2, Ent<V>>:
  match xs:
    case Nil{}:
      Con{y, Nil{}}
    case Con{x, t}:
      Con{x, snoc(V, t, y)}

def tail(-V: Data, xs: List<&2, Ent<V>>) -> List<&2, Ent<V>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      t

def dropn(-V: Data, k: Nat, xs: List<&2, Ent<V>>) -> List<&2, Ent<V>>:
  match k:
    case 0n:
      xs
    case 1n+p:
      dropn(V, p, tail(V, xs))

def bumpn(k: Nat, +i: Nat, m: T.Metrics) -> T.Metrics:
  match k:
    case 0n:
      m
    case 1n+p:
      bumpn(p, i, T.bump(i, m))

def keys(-V: Data, xs: List<&2, Ent<V>>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{En{k, v, d}, t}:
      Con{k, keys(V, t)}

def count_if(b: Bool, +i: Nat, m: T.Metrics) -> T.Metrics:
  match b:
    case True{}:
      T.bump(i, m)
    case False{}:
      m

# ---- construction ----

def new_checked(-V: Data, +cap: U32, zero: Bool, reserved: Bool) -> Result<&2, &2, String, Model<V>>:
  match zero reserved:
    case True{} r:
      Fail{"capacity must be positive"}
    case False{} True{}:
      Fail{"size must not be 0XFFFFFFFF"}
    case False{} False{}:
      Done{LM{cap, zero_time(), Nil{}, T.zero_metrics()}}

# ---- add ----

# The oldest entry is evicted first when the cache is full.
def new(-V: Data, +cap: U32) -> Result<&2, &2, String, Model<V>>:
  new_checked(V, cap, U32.is_eq(cap, 0), U32.is_eq(cap, 4294967295))

def add_absent(-V: Data, +cap: U32, +life: T.Int64, xs: List<&2, Ent<V>>, m: T.Metrics, e: Ent<V>, full: Bool) -> Model<V> & E.Obs<V>:
  match full:
    case False{}:
      (LM{cap, life, snoc(V, xs, e), T.bump(0n, m)}, E.OFlag{False{}})
    case True{}:
      (LM{cap, life, snoc(V, tail(V, xs), e), T.bump(0n, T.bump(1n, m))}, E.OFlag{True{}})

def add_found(-V: Data, +cap: U32, +life: T.Int64, +xs: List<&2, Ent<V>>, m: T.Metrics, +key: String, e: Ent<V>, found: Maybe<&2, Ent<V>>) -> Model<V> & E.Obs<V>:
  match found:
    case None{}:
      add_absent(V, cap, life, xs, m, e, U32.is_le(cap, U32.from_nat(len(V, xs))))
    case Some{old}:
      (LM{cap, life, snoc(V, drop(V, xs, key), e), T.bump(0n, m)}, E.OFlag{False{}})

# ---- reads ----

def val_of(-V: Data, x: Ent<V>) -> V:
  match x:
    case En{k, v, d}:
      v

def read_live(-V: Data, +cap: U32, +life: T.Int64, +xs: List<&2, Ent<V>>, m: T.Metrics, +key: String, +x: Ent<V>, tracked: Bool) -> Model<V> & Maybe<&2, V>:
  match tracked:
    case False{}:
      (LM{cap, life, xs, m}, Some{val_of(V, x)})
    case True{}:
      (LM{cap, life, snoc(V, drop(V, xs, key), x), T.bump(3n, m)}, Some{val_of(V, x)})

def read_expiry(-V: Data, +cap: U32, +life: T.Int64, +xs: List<&2, Ent<V>>, m: T.Metrics, +key: String, +x: Ent<V>, +tracked: Bool, expired: Bool) -> Model<V> & Maybe<&2, V>:
  match expired:
    case True{}:
      (LM{cap, life, drop(V, xs, key), count_if(tracked, 4n, T.bump(2n, m))}, None{})
    case False{}:
      read_live(V, cap, life, xs, m, key, x, tracked)

def read_ent(-V: Data, +cap: U32, +life: T.Int64, +xs: List<&2, Ent<V>>, m: T.Metrics, +key: String, x: Ent<V>, +now: T.Int64, +tracked: Bool) -> Model<V> & Maybe<&2, V>:
  match x:
    case En{+k, +v, +d}:
      read_expiry(V, cap, life, xs, m, key, En{k, v, d}, tracked, N.expired(d, now))

def read_found(-V: Data, +cap: U32, +life: T.Int64, +xs: List<&2, Ent<V>>, m: T.Metrics, +key: String, +now: T.Int64, +tracked: Bool, found: Maybe<&2, Ent<V>>) -> Model<V> & Maybe<&2, V>:
  match found:
    case None{}:
      (LM{cap, life, xs, count_if(tracked, 4n, m)}, None{})
    case Some{x}:
      read_ent(V, cap, life, xs, m, key, x, now, tracked)

# get touches and counts a hit or a miss; peek and contains do neither. An
# expired entry is removed (counted as a removal) by every read.
def read(-V: Data, +s: Model<V>, +key: String, +now: T.Int64, +tracked: Bool) -> Model<V> & Maybe<&2, V>:
  match s:
    case LM{+cap, +life, +xs, m}:
      read_found(V, cap, life, xs, m, key, now, tracked, find(V, xs, key))

# ---- remove / purge / resize / keys ----

def remove_found(-V: Data, +cap: U32, +life: T.Int64, +xs: List<&2, Ent<V>>, m: T.Metrics, +key: String, found: Maybe<&2, Ent<V>>) -> Model<V> & Maybe<&2, V>:
  match found:
    case None{}:
      (LM{cap, life, xs, m}, None{})
    case Some{En{k, v, d}}:
      (LM{cap, life, drop(V, xs, key), T.bump(2n, m)}, Some{v})

def remove(-V: Data, +s: Model<V>, +key: String) -> Model<V> & Maybe<&2, V>:
  match s:
    case LM{+cap, +life, +xs, m}:
      remove_found(V, cap, life, xs, m, key, find(V, xs, key))

# A positive capacity is set and the oldest entries are evicted until the
# cache fits (each counted as an eviction); capacity 0 fails, no change.
def resize_go(-V: Data, +c0: U32, +life: T.Int64, +xs: List<&2, Ent<V>>, m: T.Metrics, +cap: U32, zero: Bool) -> Model<V> & E.Obs<V>:
  match zero:
    case True{}:
      (LM{c0, life, xs, m}, E.OResized{Fail{"capacity must be positive"}})
    case False{}:
      (LM{cap, life, dropn(V, Nat.sub(len(V, xs), U32.to_nat(cap)), xs), bumpn(Nat.sub(len(V, xs), U32.to_nat(cap)), 1n, m)}, E.OResized{Done{U32.from_nat(Nat.sub(len(V, xs), U32.to_nat(cap)))}})

# The expired oldest prefix is removed (each a removal) before the keys, oldest
# first, are reported.
def strip_at(-V: Data, x: Ent<V>, t: List<&2, Ent<V>>, m: T.Metrics, expired: Bool, rest: List<&2, Ent<V>> & T.Metrics) -> List<&2, Ent<V>> & T.Metrics:
  match expired:
    case False{}:
      (Con{x, t}, m)
    case True{}:
      rest

def strip(-V: Data, xs: List<&2, Ent<V>>, +m: T.Metrics, +now: T.Int64) -> List<&2, Ent<V>> & T.Metrics:
  match xs:
    case Nil{}:
      (Nil{}, m)
    case Con{En{k, v, +d}, +t}:
      strip_at(V, En{k, v, d}, t, m, N.expired(d, now), strip(V, t, T.bump(2n, m), now))

def keys_fin(-V: Data, +cap: U32, +life: T.Int64, r: List<&2, Ent<V>> & T.Metrics) -> Model<V> & E.Obs<V>:
  (+xs, m) = r
  (LM{cap, life, xs, m}, E.OKeys{keys(V, xs)})

def pair_obs(-V: Data, r: Model<V> & Maybe<&2, V>) -> Model<V> & E.Obs<V>:
  (s, v) = r
  (s, E.OVal{v})

def flag_obs(-V: Data, r: Model<V> & Maybe<&2, V>) -> Model<V> & E.Obs<V>:
  (s, v) = r
  match v:
    case None{}:
      (s, E.OFlag{False{}})
    case Some{x}:
      (s, E.OFlag{True{}})

# ---- one operation ----

def step(-V: Data, +s: Model<V>, op: E.Op<V>) -> Model<V> & E.Obs<V>:
  match s op:
    case LM{+cap, +life, +xs, m} E.Len{}:
      (LM{cap, life, xs, m}, E.ONum{U32.from_nat(len(V, xs))})
    case LM{+cap, +life, +xs, m} E.Capacity{}:
      (LM{cap, life, xs, m}, E.ONum{cap})
    case LM{+cap, +life, +xs, m} E.SetLifetime{+ns}:
      (LM{cap, ns, xs, m}, E.OUnit{})
    case LM{+cap, +life, +xs, +m} E.Metrics{}:
      (LM{cap, life, xs, m}, E.OMetrics{m})
    case LM{+cap, +life, +xs, m} E.Add{+key, v, +now}:
      add_found(V, cap, life, xs, m, key, En{key, v, N.deadline(now, life)}, find(V, xs, key))
    case LM{+cap, +life, +xs, m} E.Get{+key, +now}:
      pair_obs(V, read(V, LM{cap, life, xs, m}, key, now, True{}))
    case LM{+cap, +life, +xs, m} E.Peek{+key, +now}:
      pair_obs(V, read(V, LM{cap, life, xs, m}, key, now, False{}))
    case LM{+cap, +life, +xs, m} E.Contains{+key, +now}:
      flag_obs(V, read(V, LM{cap, life, xs, m}, key, now, False{}))
    case LM{+cap, +life, +xs, m} E.Remove{+key}:
      pair_obs(V, remove(V, LM{cap, life, xs, m}, key))
    case LM{+cap, +life, +xs, m} E.Purge{}:
      (LM{cap, life, Nil{}, T.zero_metrics()}, E.ONum{U32.from_nat(len(V, xs))})
    case LM{+c0, +life, +xs, m} E.Resize{+cap}:
      resize_go(V, c0, life, xs, m, cap, U32.is_eq(cap, 0))
    case LM{+cap, +life, +xs, m} E.Keys{+now}:
      keys_fin(V, cap, life, strip(V, xs, m, now))

def cons_obs(-V: Data, o: E.Obs<V>, r: Model<V> & List<&2, E.Obs<V>>) -> Model<V> & List<&2, E.Obs<V>>:
  (s, os) = r
  (s, Con{o, os})

def run(-V: Data, ops: List<&2, E.Op<V>>, +s: Model<V>) -> Model<V> & List<&2, E.Obs<V>>:
  match ops:
    case Nil{}:
      (s, Nil{})
    case Con{+op, rest}:
      cons_obs(V, Pair.snd(Model<V>, E.Obs<V>, step(V, s, op)), run(V, rest, Pair.fst(Model<V>, E.Obs<V>, step(V, s, op))))
