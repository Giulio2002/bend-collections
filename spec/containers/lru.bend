import Base
import ../../src/math/u64.bend as W
import ./hash_table.bend as HT

# Independent model of the LRU cache: a list of entries, oldest first, with a
# capacity, a lifetime and five 64-bit counters. Nothing here refers to
# buckets, slots, links or arrays; key equality is the association list's
# (HT.str_eq), 64-bit arithmetic is src/math/u64.bend's (proved in
# proofs/math/u64.bend and proofs/math/u64div.bend).
#
# Semantics (as benchmarks/native/lru.c): add replaces a present key in place
# and makes it the newest, or appends a new key after evicting the oldest
# when full, counting an insertion (and an eviction); get touches and counts
# a hit or a miss; peek and contains neither touch nor count; a read that
# finds an expired entry removes it (a removal) and reads as a miss; remove
# counts a removal; purge clears entries and counters; resize(0) fails;
# resize(c) evicts the oldest until the cache fits; keys first drops the
# expired oldest prefix (removals); new rejects 0 and 0xFFFFFFFF.

# t = 1: timed, due at dl; t = 0: immortal
type Ent<-V: Data> is Data:
  LE{key: String, val: V, t: U32, dl: W.U64}

type Ctr is Data:
  CT{ins: W.U64, ev: W.U64, rm: W.U64, hit: W.U64, miss: W.U64}

# on != 0: entries get a lifetime of `life` milliseconds
type Lru<-V: Data> is Data:
  L{cap: U32, on: U32, life: W.U64, es: List<&2, Ent<V>>, +c: Ctr}

type Made<-V: Data> is Data:
  Made{l: Lru<V>}
  Rejected{reason: String}

# ---- counters ----

def inc_hi(+lo: U32, +hi: U32, wrap: Bool) -> W.U64:
  match wrap:
    case True{}:
      W.U64{lo, U32.inc(hi)}
    case False{}:
      W.U64{lo, hi}

# x + 1, wrapping at 2^64
def inc64(x: W.U64) -> W.U64:
  match x:
    case W.U64{+lo, +hi}:
      inc_hi(U32.inc(lo), hi, U32.is_eq(U32.inc(lo), 0))

def zero_ctr() -> Ctr:
  CT{W.zero(), W.zero(), W.zero(), W.zero(), W.zero()}

def c_ins(c: Ctr) -> Ctr:
  match c:
    case CT{a, b, d, e, f}:
      CT{inc64(a), b, d, e, f}

def c_ev(c: Ctr) -> Ctr:
  match c:
    case CT{a, b, d, e, f}:
      CT{a, inc64(b), d, e, f}

def c_rm(c: Ctr) -> Ctr:
  match c:
    case CT{a, b, d, e, f}:
      CT{a, b, inc64(d), e, f}

def c_hit(c: Ctr) -> Ctr:
  match c:
    case CT{a, b, d, e, f}:
      CT{a, b, d, inc64(e), f}

def c_miss(c: Ctr) -> Ctr:
  match c:
    case CT{a, b, d, e, f}:
      CT{a, b, d, e, inc64(f)}

def c_miss_if(c: Ctr, tracked: Bool) -> Ctr:
  match tracked:
    case True{}:
      c_miss(c)
    case False{}:
      c

# ---- lifetimes ----

# a zero deadline never expires; otherwise deadline <= now (signed)
def expired(+d: W.U64, now: W.U64) -> Bool:
  Bool.pick(Bool, W.is_zero(d), False{}, W.le_signed(d, now))

def gone(~V: Data, e: Ent<V>, now: W.U64) -> Bool:
  match e:
    case LE{k, v, +t, +d}:
      Bool.pick(Bool, U32.is_eq(t, 0), False{}, expired(d, now))

# the entry add stores: immortal without a lifetime, else due at now + life
def mk_c(~V: Data, +life: W.U64, +key: String, v: V, +now: W.U64, off: Bool) -> Ent<V>:
  match off:
    case True{}:
      LE{key, v, 0, W.zero()}
    case False{}:
      LE{key, v, 1, W.add(now, life)}

def mk(~V: Data, +on: U32, +life: W.U64, +key: String, v: V, +now: W.U64) -> Ent<V>:
  mk_c(~V, life, key, v, now, U32.is_eq(on, 0))

# ---- the entry list ----

def keys_of(~V: Data, es: List<&2, Ent<V>>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{LE{k, v, t, d}, r}:
      Con{k, keys_of(~V, r)}

def find(~V: Data, es: List<&2, Ent<V>>, +key: String) -> Maybe<&2, Ent<V>>:
  match es:
    case Nil{}:
      None{}
    case Con{+e, r}:
      match e:
        case LE{+k, +v, +t, +d}:
          Bool.pick(Maybe<&2, Ent<V>>, HT.str_eq(k, key), Some{LE{k, v, t, d}}, find(~V, r, key))

# the list without key's entry
def drop(~V: Data, es: List<&2, Ent<V>>, +key: String) -> List<&2, Ent<V>>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+e, +r}:
      match e:
        case LE{+k, +v, +t, +d}:
          Bool.pick(List<&2, Ent<V>>, HT.str_eq(k, key), r, Con{LE{k, v, t, d}, drop(~V, r, key)})

def snoc(~V: Data, es: List<&2, Ent<V>>, e: Ent<V>) -> List<&2, Ent<V>>:
  match es:
    case Nil{}:
      Con{e, Nil{}}
    case Con{h, t}:
      Con{h, snoc(~V, t, e)}

def length(~V: Data, es: List<&2, Ent<V>>) -> Nat:
  match es:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+length(~V, t)

def tail(~V: Data, es: List<&2, Ent<V>>) -> List<&2, Ent<V>>:
  match es:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def val_of(~V: Data, e: Ent<V>) -> V:
  match e:
    case LE{k, v, t, d}:
      v

# ---- operations ----

def new_c(~V: Data, +cap: U32, zero: Bool, reserved: Bool) -> Made<V>:
  match zero reserved:
    case True{} r:
      Rejected{"capacity must be positive"}
    case False{} True{}:
      Rejected{"size must not be 0XFFFFFFFF"}
    case False{} False{}:
      Made{L{cap, 0, W.zero(), Nil{}, zero_ctr()}}

def new(~V: Data, +cap: U32) -> Made<V>:
  new_c(~V, cap, U32.is_eq(cap, 0), U32.is_eq(cap, 4294967295))

def capacity(~V: Data, l: Lru<V>) -> U32:
  match l:
    case L{cap, on, life, es, c}:
      cap

def len(~V: Data, l: Lru<V>) -> U32:
  match l:
    case L{cap, on, life, es, c}:
      U32.from_nat(length(~V, es))

def counters(~V: Data, l: Lru<V>) -> Ctr:
  match l:
    case L{cap, on, life, es, c}:
      c

def set_lifetime(~V: Data, l: Lru<V>, +ns: W.U64) -> Lru<V>:
  match l:
    case L{cap, on, life, es, c}:
      L{cap, W.carry(Bool.not(W.is_zero(ns))), W.div_small_signed(ns, 1000000), es, c}

# drop the oldest entry, counted by f
def drop_oldest(~V: Data, l: Lru<V>) -> Lru<V>:
  match l:
    case L{cap, on, life, es, c}:
      L{cap, on, life, tail(~V, es), c}

def add_absent(~V: Data, +cap: U32, +on: U32, +life: W.U64, es: List<&2, Ent<V>>, +c: Ctr, e: Ent<V>, full: Bool) -> Lru<V> & Bool:
  match full:
    case True{}:
      (L{cap, on, life, snoc(~V, tail(~V, es), e), c_ins(c_ev(c))}, True{})
    case False{}:
      (L{cap, on, life, snoc(~V, es, e), c_ins(c)}, False{})

def add_found(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, e: Ent<V>, m: Maybe<&2, Ent<V>>) -> Lru<V> & Bool:
  match m:
    case Some{old}:
      (L{cap, on, life, snoc(~V, drop(~V, es, key), e), c_ins(c)}, False{})
    case None{}:
      add_absent(~V, cap, on, life, es, c, e, U32.is_le(cap, U32.from_nat(length(~V, es))))

# insert or replace key; the Bool reports whether an entry was evicted
def add(~V: Data, l: Lru<V>, +key: String, v: V, +now: W.U64) -> Lru<V> & Bool:
  match l:
    case L{+cap, +on, +life, +es, +c}:
      add_found(~V, cap, on, life, es, c, key, mk(~V, on, life, key, v, now), find(~V, es, key))

def read_live(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +e: Ent<V>, tracked: Bool) -> Lru<V> & Maybe<&2, V>:
  match tracked:
    case True{}:
      (L{cap, on, life, snoc(~V, drop(~V, es, key), e), c_hit(c)}, Some{val_of(~V, e)})
    case False{}:
      (L{cap, on, life, es, c}, Some{val_of(~V, e)})

def read_found(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +now: W.U64, +tracked: Bool, m: Maybe<&2, Ent<V>>) -> Lru<V> & Maybe<&2, V>:
  match m:
    case None{}:
      (L{cap, on, life, es, c_miss_if(c, tracked)}, None{})
    case Some{+e}:
      Bool.pick(Lru<V> & Maybe<&2, V>, gone(~V, e, now), (L{cap, on, life, drop(~V, es, key), c_miss_if(c_rm(c), tracked)}, None{}), read_live(~V, cap, on, life, es, c, key, e, tracked))

# tracked (get): touch, count a hit or a miss; untracked (peek): neither
def read(~V: Data, l: Lru<V>, +key: String, +now: W.U64, +tracked: Bool) -> Lru<V> & Maybe<&2, V>:
  match l:
    case L{+cap, +on, +life, +es, +c}:
      read_found(~V, cap, on, life, es, c, key, now, tracked, find(~V, es, key))

def get(~V: Data, l: Lru<V>, +key: String, +now: W.U64) -> Lru<V> & Maybe<&2, V>:
  read(~V, l, key, now, True{})

def peek(~V: Data, l: Lru<V>, +key: String, +now: W.U64) -> Lru<V> & Maybe<&2, V>:
  read(~V, l, key, now, False{})

def contains_found(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +now: W.U64, m: Maybe<&2, Ent<V>>) -> Lru<V> & Bool:
  match m:
    case None{}:
      (L{cap, on, life, es, c}, False{})
    case Some{+e}:
      Bool.pick(Lru<V> & Bool, gone(~V, e, now), (L{cap, on, life, drop(~V, es, key), c_rm(c)}, False{}), (L{cap, on, life, es, c}, True{}))

def contains(~V: Data, l: Lru<V>, +key: String, +now: W.U64) -> Lru<V> & Bool:
  match l:
    case L{+cap, +on, +life, +es, +c}:
      contains_found(~V, cap, on, life, es, c, key, now, find(~V, es, key))

def remove_found(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, m: Maybe<&2, Ent<V>>) -> Lru<V> & Maybe<&2, V>:
  match m:
    case None{}:
      (L{cap, on, life, es, c}, None{})
    case Some{e}:
      (L{cap, on, life, drop(~V, es, key), c_rm(c)}, Some{val_of(~V, e)})

def remove(~V: Data, l: Lru<V>, +key: String) -> Lru<V> & Maybe<&2, V>:
  match l:
    case L{+cap, +on, +life, +es, +c}:
      remove_found(~V, cap, on, life, es, c, key, find(~V, es, key))

def purge(~V: Data, l: Lru<V>) -> Lru<V> & U32:
  match l:
    case L{+cap, +on, +life, +es, +c}:
      (L{cap, on, life, Nil{}, zero_ctr()}, U32.from_nat(length(~V, es)))

# evict the oldest until the cache fits, counting them
def shrink(~V: Data, fuel: Nat, l: Lru<V>, +ev: U32) -> Lru<V> & U32:
  match fuel:
    case 0n:
      (l, ev)
    case 1n+p:
      match l:
        case L{+cap, +on, +life, +es, +c}:
          Bool.pick(Lru<V> & U32, U32.is_lt(cap, U32.from_nat(length(~V, es))), shrink(~V, p, L{cap, on, life, tail(~V, es), c_ev(c)}, U32.inc(ev)), (L{cap, on, life, es, c}, ev))

def rs_done(~V: Data, r: Lru<V> & U32) -> Lru<V> & Result<&2, &2, String, U32>:
  match r:
    case Tuple{l, +ev}:
      (l, Done{ev})

def resize_c(~V: Data, +c0: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +cap: U32, zero: Bool) -> Lru<V> & Result<&2, &2, String, U32>:
  match zero:
    case True{}:
      (L{c0, on, life, es, c}, Fail{"capacity must be positive"})
    case False{}:
      rs_done(~V, shrink(~V, length(~V, es), L{cap, on, life, es, c}, 0))

# capacity 0 fails; otherwise evict the oldest until the cache fits
def resize(~V: Data, l: Lru<V>, +cap: U32) -> Lru<V> & Result<&2, &2, String, U32>:
  match l:
    case L{+c0, +on, +life, +es, +c}:
      resize_c(~V, c0, on, life, es, c, cap, U32.is_eq(cap, 0))

# drop the expired oldest prefix, each a removal
def expire(~V: Data, fuel: Nat, l: Lru<V>, +now: W.U64) -> Lru<V>:
  match fuel:
    case 0n:
      l
    case 1n+p:
      match l:
        case L{+cap, +on, +life, +es, +c}:
          match es:
            case Nil{}:
              L{cap, on, life, Nil{}, c}
            case Con{+e, +r}:
              Bool.pick(Lru<V>, gone(~V, e, now), expire(~V, p, L{cap, on, life, r, c_rm(c)}, now), L{cap, on, life, Con{e, r}, c})

def keys_fin(~V: Data, l: Lru<V>) -> Lru<V> & List<&2, String>:
  match l:
    case L{+cap, +on, +life, +es, +c}:
      (L{cap, on, life, es, c}, keys_of(~V, es))

# the keys oldest first, after the expired oldest prefix is dropped
def keys(~V: Data, l: Lru<V>, +now: W.U64) -> Lru<V> & List<&2, String>:
  match l:
    case L{+cap, +on, +life, +es, +c}:
      keys_fin(~V, expire(~V, length(~V, es), L{cap, on, life, es, c}, now))

# ---- contract (SPARK formal containers) ----
# Each `<Subprogram>.<clause>` definition below states one Post clause of
# that SPARK subprogram, as a proposition on this model; the table names the
# clauses. proofs/containers/lru/ proves every clause under its clause name,
# and its `impl` lemma carries them to the implementation.
#
# Contracts of the LRU cache in the style of SPARK's formal hashed maps
# (SPARKlib src/spark-containers-formal-hashed_maps.ads, AdaCore/SPARKlib
# master), extended with the recency order an LRU adds. They are stated on
# the independent model (this file: the entries oldest first, a capacity,
# counters); proof.bend's refinement theorems (new_ok, capacity_ok, len_ok,
# get_ok, peek_ok, contains_ok, add_ok, remove_ok, resize_ok, purge_ok,
# keys_ok) show that the implementation returns exactly the model's result,
# so every clause below holds of the implementation.
#
#   SPARK subprogram (.ads line)     ours       clauses
#   Empty_Map (103)                  new        new_empty, new_rejects_zero, new_rejects_max
#   Length (117)                     len        length_value
#   Capacity (400)                   capacity   capacity_value
#   Include (729), present key       add        add_present_order, add_present_newest, add_present_length
#   Include / Insert (619), room     add        add_room_order, add_room_newest, add_room_length
#   Include, full (LRU eviction)     add        add_evict_order, add_evict_newest, add_evict_length
#   Element (1039) + touch           get        get_hit, get_hit_newest, get_miss
#   Element (1039), no touch         peek       peek_hit, peek_miss
#   Contains (1032)                  contains   contains_live, contains_absent, contains_expired
#   Delete (891) / Exclude (851)     remove     remove_present, remove_absent
#   Clear (427)                      purge      purge_value
#   Iter_Model (1078)                keys       keys_fin_value
# Expiry: an entry past its deadline reads as absent and is removed
# (read_expired, contains_expired). Not in this API: "=", Is_Empty, Assign/
# Copy/Move, cursors (First/Next/Has_Element/Key/Element by cursor), Find,
# Replace (fails if absent), Insert that fails if present. The model's keys
# are unique (every add drops the old entry first), but that invariant is
# not re-exported here, so clauses are stated through find/drop rather than
# as pointwise lookup frames.

def last_go(~V: Data, t: List<&2, Ent<V>>, h: Ent<V>) -> Maybe<&2, Ent<V>>:
  match t:
    case Nil{}:
      Some{h}
    case Con{h2, t2}:
      last_go(~V, t2, h2)

def last(~V: Data, es: List<&2, Ent<V>>) -> Maybe<&2, Ent<V>>:
  match es:
    case Nil{}:
      None{}
    case Con{h, t}:
      last_go(~V, t, h)

def es_of(~V: Data, l: Lru<V>) -> List<&2, Ent<V>>:
  match l:
    case L{cap, on, life, es, c}:
      es

# Empty_Map (103)
def Empty_Map.new_empty(~V: Data, +cap: U32, +hz: {U32.is_eq(cap, 0) == False{} : Bool}, +hm: {U32.is_eq(cap, 4294967295) == False{} : Bool}) -> Type:
  {new(~V, cap) == Made{L{cap, 0, W.zero(), Nil{}, zero_ctr()}} : Made<V>}

# Empty_Map (103)
def Empty_Map.new_rejects_zero(~V: Data) -> Type:
  {new(~V, 0) == Rejected{"capacity must be positive"} : Made<V>}

# Empty_Map (103)
def Empty_Map.new_rejects_max(~V: Data) -> Type:
  {new(~V, 4294967295) == Rejected{"size must not be 0XFFFFFFFF"} : Made<V>}

# Length (117)
def Length.length_value(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr) -> Type:
  {len(~V, L{cap, on, life, es, c}) == U32.from_nat(length(~V, es)) : U32}

# Capacity (400)
def Capacity.capacity_value(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr) -> Type:
  {capacity(~V, L{cap, on, life, es, c}) == cap : U32}

# Include (729), present key
def Include.add_present_order(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +v: V, +now: W.U64, +old: Ent<V>, +hf: {find(~V, es, key) == Some{old} : Maybe<&2, Ent<V>>}) -> Type:
  {add(~V, L{cap, on, life, es, c}, key, v, now) == (L{cap, on, life, snoc(~V, drop(~V, es, key), mk(~V, on, life, key, v, now)), c_ins(c)}, False{}) : Lru<V> & Bool}

# Include (729), present key
def Include.add_present_newest(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +v: V, +now: W.U64, +old: Ent<V>, +hf: {find(~V, es, key) == Some{old} : Maybe<&2, Ent<V>>}) -> Type:
  {last(~V, es_of(~V, Pair.fst(Lru<V>, Bool, add(~V, L{cap, on, life, es, c}, key, v, now)))) == Some{mk(~V, on, life, key, v, now)} : Maybe<&2, Ent<V>>}

# Include (729), present key
def Include.add_present_length(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +v: V, +now: W.U64, +old: Ent<V>, +hf: {find(~V, es, key) == Some{old} : Maybe<&2, Ent<V>>}) -> Type:
  {length(~V, es_of(~V, Pair.fst(Lru<V>, Bool, add(~V, L{cap, on, life, es, c}, key, v, now)))) == 1n+length(~V, drop(~V, es, key)) : Nat}

# Include / Insert (619), room
def Include.add_room_order(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +v: V, +now: W.U64, +hf: {find(~V, es, key) == None{} : Maybe<&2, Ent<V>>}, +hr: {U32.is_le(cap, U32.from_nat(length(~V, es))) == False{} : Bool}) -> Type:
  {add(~V, L{cap, on, life, es, c}, key, v, now) == (L{cap, on, life, snoc(~V, es, mk(~V, on, life, key, v, now)), c_ins(c)}, False{}) : Lru<V> & Bool}

# Include / Insert (619), room
def Include.add_room_newest(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +v: V, +now: W.U64, +hf: {find(~V, es, key) == None{} : Maybe<&2, Ent<V>>}, +hr: {U32.is_le(cap, U32.from_nat(length(~V, es))) == False{} : Bool}) -> Type:
  {last(~V, es_of(~V, Pair.fst(Lru<V>, Bool, add(~V, L{cap, on, life, es, c}, key, v, now)))) == Some{mk(~V, on, life, key, v, now)} : Maybe<&2, Ent<V>>}

# Include / Insert (619), room
def Include.add_room_length(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +v: V, +now: W.U64, +hf: {find(~V, es, key) == None{} : Maybe<&2, Ent<V>>}, +hr: {U32.is_le(cap, U32.from_nat(length(~V, es))) == False{} : Bool}) -> Type:
  {length(~V, es_of(~V, Pair.fst(Lru<V>, Bool, add(~V, L{cap, on, life, es, c}, key, v, now)))) == 1n+length(~V, es) : Nat}

# Include, full (LRU eviction)
def Include.add_evict_order(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +v: V, +now: W.U64, +hf: {find(~V, es, key) == None{} : Maybe<&2, Ent<V>>}, +hfu: {U32.is_le(cap, U32.from_nat(length(~V, es))) == True{} : Bool}) -> Type:
  {add(~V, L{cap, on, life, es, c}, key, v, now) == (L{cap, on, life, snoc(~V, tail(~V, es), mk(~V, on, life, key, v, now)), c_ins(c_ev(c))}, True{}) : Lru<V> & Bool}

# Include, full (LRU eviction)
def Include.add_evict_newest(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +v: V, +now: W.U64, +hf: {find(~V, es, key) == None{} : Maybe<&2, Ent<V>>}, +hfu: {U32.is_le(cap, U32.from_nat(length(~V, es))) == True{} : Bool}) -> Type:
  {last(~V, es_of(~V, Pair.fst(Lru<V>, Bool, add(~V, L{cap, on, life, es, c}, key, v, now)))) == Some{mk(~V, on, life, key, v, now)} : Maybe<&2, Ent<V>>}

# Include, full (LRU eviction)
def Include.add_evict_length(~V: Data, +cap: U32, +on: U32, +life: W.U64, +h: Ent<V>, +t: List<&2, Ent<V>>, +c: Ctr, +key: String, +v: V, +now: W.U64, +hf: {find(~V, Con{h, t}, key) == None{} : Maybe<&2, Ent<V>>}, +hfu: {U32.is_le(cap, U32.from_nat(length(~V, Con{h, t}))) == True{} : Bool}) -> Type:
  {length(~V, es_of(~V, Pair.fst(Lru<V>, Bool, add(~V, L{cap, on, life, Con{h, t}, c}, key, v, now)))) == length(~V, Con{h, t}) : Nat}

# Element (1039) + touch
def Element.get_hit(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +now: W.U64, +e: Ent<V>, +hf: {find(~V, es, key) == Some{e} : Maybe<&2, Ent<V>>}, +hg: {gone(~V, e, now) == False{} : Bool}) -> Type:
  {get(~V, L{cap, on, life, es, c}, key, now) == (L{cap, on, life, snoc(~V, drop(~V, es, key), e), c_hit(c)}, Some{val_of(~V, e)}) : Lru<V> & Maybe<&2, V>}

# Element (1039) + touch
def Element.get_hit_newest(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +now: W.U64, +e: Ent<V>, +hf: {find(~V, es, key) == Some{e} : Maybe<&2, Ent<V>>}, +hg: {gone(~V, e, now) == False{} : Bool}) -> Type:
  {last(~V, es_of(~V, Pair.fst(Lru<V>, Maybe<&2, V>, get(~V, L{cap, on, life, es, c}, key, now)))) == Some{e} : Maybe<&2, Ent<V>>}

# Element (1039) + touch
def Element.get_miss(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +now: W.U64, +hf: {find(~V, es, key) == None{} : Maybe<&2, Ent<V>>}) -> Type:
  {get(~V, L{cap, on, life, es, c}, key, now) == (L{cap, on, life, es, c_miss_if(c, True{})}, None{}) : Lru<V> & Maybe<&2, V>}

# Iter_Model (1078)
def Iter_Model.read_expired(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +now: W.U64, +tracked: Bool, +e: Ent<V>, +hf: {find(~V, es, key) == Some{e} : Maybe<&2, Ent<V>>}, +hg: {gone(~V, e, now) == True{} : Bool}) -> Type:
  {read(~V, L{cap, on, life, es, c}, key, now, tracked) == (L{cap, on, life, drop(~V, es, key), c_miss_if(c_rm(c), tracked)}, None{}) : Lru<V> & Maybe<&2, V>}

# Element (1039), no touch
def Element.peek_hit(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +now: W.U64, +e: Ent<V>, +hf: {find(~V, es, key) == Some{e} : Maybe<&2, Ent<V>>}, +hg: {gone(~V, e, now) == False{} : Bool}) -> Type:
  {peek(~V, L{cap, on, life, es, c}, key, now) == (L{cap, on, life, es, c}, Some{val_of(~V, e)}) : Lru<V> & Maybe<&2, V>}

# Element (1039), no touch
def Element.peek_miss(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +now: W.U64, +hf: {find(~V, es, key) == None{} : Maybe<&2, Ent<V>>}) -> Type:
  {peek(~V, L{cap, on, life, es, c}, key, now) == (L{cap, on, life, es, c_miss_if(c, False{})}, None{}) : Lru<V> & Maybe<&2, V>}

# Contains (1032)
def Contains.contains_live(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +now: W.U64, +e: Ent<V>, +hf: {find(~V, es, key) == Some{e} : Maybe<&2, Ent<V>>}, +hg: {gone(~V, e, now) == False{} : Bool}) -> Type:
  {contains(~V, L{cap, on, life, es, c}, key, now) == (L{cap, on, life, es, c}, True{}) : Lru<V> & Bool}

# Contains (1032)
def Contains.contains_expired(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +now: W.U64, +e: Ent<V>, +hf: {find(~V, es, key) == Some{e} : Maybe<&2, Ent<V>>}, +hg: {gone(~V, e, now) == True{} : Bool}) -> Type:
  {contains(~V, L{cap, on, life, es, c}, key, now) == (L{cap, on, life, drop(~V, es, key), c_rm(c)}, False{}) : Lru<V> & Bool}

# Contains (1032)
def Contains.contains_absent(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +now: W.U64, +hf: {find(~V, es, key) == None{} : Maybe<&2, Ent<V>>}) -> Type:
  {contains(~V, L{cap, on, life, es, c}, key, now) == (L{cap, on, life, es, c}, False{}) : Lru<V> & Bool}

# Delete (891) / Exclude (851)
def Delete.remove_present(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +e: Ent<V>, +hf: {find(~V, es, key) == Some{e} : Maybe<&2, Ent<V>>}) -> Type:
  {remove(~V, L{cap, on, life, es, c}, key) == (L{cap, on, life, drop(~V, es, key), c_rm(c)}, Some{val_of(~V, e)}) : Lru<V> & Maybe<&2, V>}

# Delete (891) / Exclude (851)
def Delete.remove_absent(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr, +key: String, +hf: {find(~V, es, key) == None{} : Maybe<&2, Ent<V>>}) -> Type:
  {remove(~V, L{cap, on, life, es, c}, key) == (L{cap, on, life, es, c}, None{}) : Lru<V> & Maybe<&2, V>}

# Clear (427)
def Clear.purge_value(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr) -> Type:
  {purge(~V, L{cap, on, life, es, c}) == (L{cap, on, life, Nil{}, zero_ctr()}, U32.from_nat(length(~V, es))) : Lru<V> & U32}

# Iter_Model (1078)
def Iter_Model.keys_fin_value(~V: Data, +cap: U32, +on: U32, +life: W.U64, +es: List<&2, Ent<V>>, +c: Ctr) -> Type:
  {keys_fin(~V, L{cap, on, life, es, c}) == (L{cap, on, life, es, c}, keys_of(~V, es)) : Lru<V> & List<&2, String>}
