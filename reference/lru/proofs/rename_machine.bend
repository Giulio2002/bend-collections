import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../src/time.bend as Time
import ../src/entry_ops.bend as Entry
import ../types/model.bend as T
import ../src/public.bend as Pub
import ../src/driver.bend as D
import ../spec/clock.bend as Clock
import ./rename_map.bend as RM

# The actual cache operations over any key type K with codec enc commute with
# renaming each stored original key to its code (RM.rn_cache): running the
# K-keyed cache and renaming equals running the String-keyed cache on the
# renamed state with renamed keys. No invariant or injectivity is needed.

def rn_event(~K: Data, ~enc: K -> String, -V: Data, e: T.Event<K, V>) -> T.Event<String, V>:
  T.Evicted{k, v} = e
  T.Evicted{enc(k), v}

def rn_events(~K: Data, ~enc: K -> String, -V: Data, xs: List<&2, T.Event<K, V>>) -> List<&2, T.Event<String, V>>:
  match xs:
    case Nil{}: Nil{}
    case Con{e, rest}: Con{rn_event(~K, ~enc, V, e), rn_events(~K, ~enc, V, rest)}

def rn_step(~K: Data, ~enc: K -> String, -V: Data, s: C.Step<K, V>) -> C.Step<String, V>:
  C.Out{c, item, flag, evs} = s
  C.Out{RM.rn_cache(~K, ~enc, V, c), RM.rn_item(~K, ~enc, V, item), flag, rn_events(~K, ~enc, V, evs)}

def rn_entries(~K: Data, ~enc: K -> String, -V: Data, xs: List<&2, T.Entry<K, V>>) -> List<&2, T.Entry<String, V>>:
  match xs:
    case Nil{}: Nil{}
    case Con{e, rest}: Con{RM.rn_entry(~K, ~enc, V, e), rn_entries(~K, ~enc, V, rest)}

def rn_keys(~K: Data, ~enc: K -> String, ks: List<&2, K>) -> List<&2, String>:
  match ks:
    case Nil{}: Nil{}
    case Con{k, rest}: Con{enc(k), rn_keys(~K, ~enc, rest)}

# ---------------------------------------------------------------------------
# Cache primitives.
def lookup(~K: Data, ~enc: K -> String, -V: Data, c: C.Cache<K, V>, +code: String) -> {C.lookup(String, V, RM.rn_cache(~K, ~enc, V, c), code) == RM.rn_item(~K, ~enc, V, C.lookup(K, V, c, code)) : Maybe<&2, T.Entry<String, V>>}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  RM.get(~K, ~enc, V, table, code)

def len(~K: Data, ~enc: K -> String, -V: Data, c: C.Cache<K, V>) -> {C.len(String, V, RM.rn_cache(~K, ~enc, V, c)) == C.len(K, V, c) : Nat}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  {==}

def capacity(~K: Data, ~enc: K -> String, -V: Data, c: C.Cache<K, V>) -> {C.capacity(String, V, RM.rn_cache(~K, ~enc, V, c)) == C.capacity(K, V, c) : Nat}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  {==}

def map_size(~K: Data, ~enc: K -> String, -V: Data, c: C.Cache<K, V>) -> {C.map_size(String, V, RM.rn_cache(~K, ~enc, V, c)) == C.map_size(K, V, c) : Nat}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  RM.size(~K, ~enc, V, table)

def cb_events(~K: Data, ~enc: K -> String, -V: Data, cb: Bool, +entry: T.Entry<K, V>) -> {C.events(String, V, cb, RM.rn_entry(~K, ~enc, V, entry)) == rn_events(~K, ~enc, V, C.events(K, V, cb, entry)) : List<&2, T.Event<String, V>>}:
  match cb:
    case False{}: {==}
    case True{}:
      T.Item{k, v, d} = entry
      {==}

def remove_present(~K: Data, ~enc: K -> String, -V: Data, c: C.Cache<K, V>, +key: String, +evict: Bool, +entry: T.Entry<K, V>) -> {C.remove_present(String, V, RM.rn_cache(~K, ~enc, V, c), key, evict, RM.rn_entry(~K, ~enc, V, entry)) == rn_step(~K, ~enc, V, C.remove_present(K, V, c, key, evict, entry)) : C.Step<String, V>}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  %RM.del(~K, ~enc, V, table, key) : {C.Out{C.State{cap, _, C.without(order, key), life, C.removal_counts(counts, evict), cb}, Some{RM.rn_entry(~K, ~enc, V, entry)}, True{}, C.events(String, V, cb, RM.rn_entry(~K, ~enc, V, entry))} == rn_step(~K, ~enc, V, C.remove_present(K, V, C.State{cap, table, order, life, counts, cb}, key, evict, entry)) : C.Step<String, V>}
  %Equal.sym(List<&2, T.Event<String, V>>, C.events(String, V, cb, RM.rn_entry(~K, ~enc, V, entry)), rn_events(~K, ~enc, V, C.events(K, V, cb, entry)), cb_events(~K, ~enc, V, cb, entry)) : {C.Out{C.State{cap, RM.rn_map(~K, ~enc, V, Map.del(&2, Maybe<&2, T.Entry<K, V>>, table, key)), C.without(order, key), life, C.removal_counts(counts, evict), cb}, Some{RM.rn_entry(~K, ~enc, V, entry)}, True{}, _} == rn_step(~K, ~enc, V, C.remove_present(K, V, C.State{cap, table, order, life, counts, cb}, key, evict, entry)) : C.Step<String, V>}
  {==}

def remove_found(~K: Data, ~enc: K -> String, -V: Data, +c: C.Cache<K, V>, +key: String, +evict: Bool, found: Maybe<&2, T.Entry<K, V>>) -> {C.remove_found(String, V, RM.rn_cache(~K, ~enc, V, c), key, evict, RM.rn_item(~K, ~enc, V, found)) == rn_step(~K, ~enc, V, C.remove_found(K, V, c, key, evict, found)) : C.Step<String, V>}:
  match found:
    case None{}: {==}
    case Some{+entry}: remove_present(~K, ~enc, V, c, key, evict, entry)

def remove_encoded(~K: Data, ~enc: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, +evict: Bool) -> {C.remove_encoded(String, V, RM.rn_cache(~K, ~enc, V, c), code, evict) == rn_step(~K, ~enc, V, C.remove_encoded(K, V, c, code, evict)) : C.Step<String, V>}:
  %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, RM.rn_cache(~K, ~enc, V, c), code), RM.rn_item(~K, ~enc, V, C.lookup(K, V, c, code)), lookup(~K, ~enc, V, c, code)) : {C.remove_found(String, V, RM.rn_cache(~K, ~enc, V, c), code, evict, _) == rn_step(~K, ~enc, V, C.remove_found(K, V, c, code, evict, C.lookup(K, V, c, code))) : C.Step<String, V>}
  remove_found(~K, ~enc, V, c, code, evict, C.lookup(K, V, c, code))

def oldest_remove(~K: Data, ~enc: K -> String, -V: Data, +c: C.Cache<K, V>, order: List<&2, String>, +evict: Bool) -> {C.oldest_remove(String, V, RM.rn_cache(~K, ~enc, V, c), order, evict) == rn_step(~K, ~enc, V, C.oldest_remove(K, V, c, order, evict)) : C.Step<String, V>}:
  match order:
    case Nil{}: {==}
    case Con{+k, rest}: remove_encoded(~K, ~enc, V, c, k, evict)

def remove_oldest(~K: Data, ~enc: K -> String, -V: Data, c: C.Cache<K, V>, +evict: Bool) -> {C.remove_oldest(String, V, RM.rn_cache(~K, ~enc, V, c), evict) == rn_step(~K, ~enc, V, C.remove_oldest(K, V, c, evict)) : C.Step<String, V>}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  oldest_remove(~K, ~enc, V, C.State{cap, table, order, life, counts, cb}, order, evict)

def remove(~K: Data, ~enc: K -> String, -V: Data, +c: C.Cache<K, V>, +key: K) -> {C.remove(String, V, Codec.string_encode, RM.rn_cache(~K, ~enc, V, c), enc(key)) == rn_step(~K, ~enc, V, C.remove(K, V, enc, c, key)) : C.Step<String, V>}:
  remove_encoded(~K, ~enc, V, c, enc(key), False{})

def store(~K: Data, ~enc: K -> String, -V: Data, c: C.Cache<K, V>, +code: String, +key: K, +value: V, +deadline: T.Int64, +flag: Bool, +evs: List<&2, T.Event<K, V>>) -> {C.store(String, V, RM.rn_cache(~K, ~enc, V, c), code, enc(key), value, deadline, flag, rn_events(~K, ~enc, V, evs)) == rn_step(~K, ~enc, V, C.store(K, V, c, code, key, value, deadline, flag, evs)) : C.Step<String, V>}:
  C.State{+cap, +table, +order, +life, T.Counts{+i, +e, +r, +h, +m}, +cb} = c
  %RM.set(~K, ~enc, V, table, code, Some{T.Item{key, value, deadline}}) : {C.Out{C.State{cap, _, List.append(&2, String, C.without(order, code), Con{code, Nil{}}), life, T.Counts{Word.inc(64n, i), e, r, h, m}, cb}, None{}, flag, rn_events(~K, ~enc, V, evs)} == rn_step(~K, ~enc, V, C.store(K, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, code, key, value, deadline, flag, evs)) : C.Step<String, V>}
  {==}

def counted(~K: Data, ~enc: K -> String, -V: Data, step: C.Step<K, V>, +tracked: Bool, +hit: Bool) -> {C.counted(String, V, rn_step(~K, ~enc, V, step), tracked, hit) == rn_step(~K, ~enc, V, C.counted(K, V, step, tracked, hit)) : C.Step<String, V>}:
  C.Out{C.State{cap, m, order, life, counts, cb}, item, flag, evs} = step
  {==}

def miss_after_remove(~K: Data, ~enc: K -> String, -V: Data, step: C.Step<K, V>, +tracked: Bool) -> {C.miss_after_remove(String, V, rn_step(~K, ~enc, V, step), tracked) == rn_step(~K, ~enc, V, C.miss_after_remove(K, V, step, tracked)) : C.Step<String, V>}:
  C.Out{+c, +item, flag, +evs} = step
  counted(~K, ~enc, V, C.Out{c, item, False{}, evs}, tracked, False{})

def read_live(~K: Data, ~enc: K -> String, -V: Data, c: C.Cache<K, V>, +code: String, +entry: T.Entry<K, V>, +tracked: Bool) -> {C.read_live(String, V, RM.rn_cache(~K, ~enc, V, c), code, RM.rn_entry(~K, ~enc, V, entry), tracked) == rn_step(~K, ~enc, V, C.read_live(K, V, c, code, entry, tracked)) : C.Step<String, V>}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  {==}

def read_expiry(~K: Data, ~enc: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, +entry: T.Entry<K, V>, +tracked: Bool, expired: Bool) -> {C.read_expiry(String, V, RM.rn_cache(~K, ~enc, V, c), code, RM.rn_entry(~K, ~enc, V, entry), tracked, expired) == rn_step(~K, ~enc, V, C.read_expiry(K, V, c, code, entry, tracked, expired)) : C.Step<String, V>}:
  match expired:
    case False{}: read_live(~K, ~enc, V, c, code, entry, tracked)
    case True{}:
      Equal.trans(C.Step<String, V>, C.miss_after_remove(String, V, C.remove_encoded(String, V, RM.rn_cache(~K, ~enc, V, c), code, False{}), tracked), C.miss_after_remove(String, V, rn_step(~K, ~enc, V, C.remove_encoded(K, V, c, code, False{})), tracked), rn_step(~K, ~enc, V, C.miss_after_remove(K, V, C.remove_encoded(K, V, c, code, False{}), tracked)), Equal.cong(C.Step<String, V>, C.Step<String, V>, s => C.miss_after_remove(String, V, s, tracked), C.remove_encoded(String, V, RM.rn_cache(~K, ~enc, V, c), code, False{}), rn_step(~K, ~enc, V, C.remove_encoded(K, V, c, code, False{})), remove_encoded(~K, ~enc, V, c, code, False{})), miss_after_remove(~K, ~enc, V, C.remove_encoded(K, V, c, code, False{}), tracked))

def read_found(~K: Data, ~enc: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, now: T.Int64, +tracked: Bool, found: Maybe<&2, T.Entry<K, V>>) -> {C.read_found(String, V, RM.rn_cache(~K, ~enc, V, c), code, now, tracked, RM.rn_item(~K, ~enc, V, found)) == rn_step(~K, ~enc, V, C.read_found(K, V, c, code, now, tracked, found)) : C.Step<String, V>}:
  match found:
    case None{}: counted(~K, ~enc, V, C.Out{c, None{}, False{}, Nil{}}, tracked, False{})
    case Some{T.Item{+k, +v, +d}}: read_expiry(~K, ~enc, V, c, code, T.Item{k, v, d}, tracked, Time.expired(d, now))

def read_encoded(~K: Data, ~enc: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, now: T.Int64, +tracked: Bool) -> {C.read_encoded(String, V, RM.rn_cache(~K, ~enc, V, c), code, now, tracked) == rn_step(~K, ~enc, V, C.read_encoded(K, V, c, code, now, tracked)) : C.Step<String, V>}:
  %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, RM.rn_cache(~K, ~enc, V, c), code), RM.rn_item(~K, ~enc, V, C.lookup(K, V, c, code)), lookup(~K, ~enc, V, c, code)) : {C.read_found(String, V, RM.rn_cache(~K, ~enc, V, c), code, now, tracked, _) == rn_step(~K, ~enc, V, C.read_found(K, V, c, code, now, tracked, C.lookup(K, V, c, code))) : C.Step<String, V>}
  read_found(~K, ~enc, V, c, code, now, tracked, C.lookup(K, V, c, code))

def step_cache(~K: Data, ~enc: K -> String, -V: Data, step: C.Step<K, V>) -> {C.step_cache(String, V, rn_step(~K, ~enc, V, step)) == RM.rn_cache(~K, ~enc, V, C.step_cache(K, V, step)) : C.Cache<String, V>}:
  C.Out{c, item, flag, evs} = step
  {==}

def first_entry(~K: Data, ~enc: K -> String, -V: Data, +c: C.Cache<K, V>, order: List<&2, String>) -> {C.first_entry(String, V, RM.rn_cache(~K, ~enc, V, c), order) == RM.rn_item(~K, ~enc, V, C.first_entry(K, V, c, order)) : Maybe<&2, T.Entry<String, V>>}:
  match order:
    case Nil{}: {==}
    case Con{+k, rest}: lookup(~K, ~enc, V, c, k)

def oldest_entry(~K: Data, ~enc: K -> String, -V: Data, c: C.Cache<K, V>) -> {C.oldest_entry(String, V, RM.rn_cache(~K, ~enc, V, c)) == RM.rn_item(~K, ~enc, V, C.oldest_entry(K, V, c)) : Maybe<&2, T.Entry<String, V>>}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  first_entry(~K, ~enc, V, C.State{cap, table, order, life, counts, cb}, order)

def collect_entry(~K: Data, ~enc: K -> String, -V: Data, found: Maybe<&2, T.Entry<K, V>>, rest: List<&2, T.Entry<K, V>>) -> {C.collect_entry(String, V, RM.rn_item(~K, ~enc, V, found), rn_entries(~K, ~enc, V, rest)) == rn_entries(~K, ~enc, V, C.collect_entry(K, V, found, rest)) : List<&2, T.Entry<String, V>>}:
  match found:
    case None{}: {==}
    case Some{e}: {==}

def entries_go(~K: Data, ~enc: K -> String, -V: Data, order: List<&2, String>, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>) -> {C.entries_go(String, V, order, RM.rn_map(~K, ~enc, V, table)) == rn_entries(~K, ~enc, V, C.entries_go(K, V, order, table)) : List<&2, T.Entry<String, V>>}:
  match order:
    case Nil{}: {==}
    case Con{+k, +rest}:
      %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup_result(String, V, Map.get(Maybe<&2, T.Entry<String, V>>, None{}, RM.rn_map(~K, ~enc, V, table), k)), RM.rn_item(~K, ~enc, V, C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, k))), RM.get(~K, ~enc, V, table, k)) : {C.collect_entry(String, V, _, C.entries_go(String, V, rest, RM.rn_map(~K, ~enc, V, table))) == rn_entries(~K, ~enc, V, C.entries_go(K, V, Con{k, rest}, table)) : List<&2, T.Entry<String, V>>}
      %Equal.sym(List<&2, T.Entry<String, V>>, C.entries_go(String, V, rest, RM.rn_map(~K, ~enc, V, table)), rn_entries(~K, ~enc, V, C.entries_go(K, V, rest, table)), entries_go(~K, ~enc, V, rest, table)) : {C.collect_entry(String, V, RM.rn_item(~K, ~enc, V, C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, k))), _) == rn_entries(~K, ~enc, V, C.entries_go(K, V, Con{k, rest}, table)) : List<&2, T.Entry<String, V>>}
      collect_entry(~K, ~enc, V, C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, k)), C.entries_go(K, V, rest, table))

def entries(~K: Data, ~enc: K -> String, -V: Data, c: C.Cache<K, V>) -> {C.entries(String, V, RM.rn_cache(~K, ~enc, V, c)) == rn_entries(~K, ~enc, V, C.entries(K, V, c)) : List<&2, T.Entry<String, V>>}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  entries_go(~K, ~enc, V, order, table)

def keys_of(~K: Data, ~enc: K -> String, -V: Data, xs: List<&2, T.Entry<K, V>>) -> {Entry.keys_of(String, V, rn_entries(~K, ~enc, V, xs)) == rn_keys(~K, ~enc, Entry.keys_of(K, V, xs)) : List<&2, String>}:
  match xs:
    case Nil{}: {==}
    case Con{T.Item{+k, v, d}, +rest}:
      %Equal.sym(List<&2, String>, Entry.keys_of(String, V, rn_entries(~K, ~enc, V, rest)), rn_keys(~K, ~enc, Entry.keys_of(K, V, rest)), keys_of(~K, ~enc, V, rest)) : {Con{enc(k), _} == Con{enc(k), rn_keys(~K, ~enc, Entry.keys_of(K, V, rest))} : List<&2, String>}
      {==}

def values_of(~K: Data, ~enc: K -> String, -V: Data, xs: List<&2, T.Entry<K, V>>) -> {Entry.values_of(String, V, rn_entries(~K, ~enc, V, xs)) == Entry.values_of(K, V, xs) : List<&2, V>}:
  match xs:
    case Nil{}: {==}
    case Con{T.Item{k, +v, d}, +rest}:
      %Equal.sym(List<&2, V>, Entry.values_of(String, V, rn_entries(~K, ~enc, V, rest)), Entry.values_of(K, V, rest), values_of(~K, ~enc, V, rest)) : {Con{v, _} == Con{v, Entry.values_of(K, V, rest)} : List<&2, V>}
      {==}

def refresh_prepare_found(~K: Data, ~enc: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, found: Maybe<&2, T.Entry<K, V>>) -> {Entry.refresh_prepare_found(String, V, RM.rn_cache(~K, ~enc, V, c), code, RM.rn_item(~K, ~enc, V, found)) == rn_step(~K, ~enc, V, Entry.refresh_prepare_found(K, V, c, code, found)) : C.Step<String, V>}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  match found:
    case None{}: {==}
    case Some{+entry}: read_live(~K, ~enc, V, C.State{cap, table, order, life, counts, cb}, code, entry, True{})

def refresh_prepare(~K: Data, ~enc: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String) -> {Entry.refresh_prepare(String, V, RM.rn_cache(~K, ~enc, V, c), code) == rn_step(~K, ~enc, V, Entry.refresh_prepare(K, V, c, code)) : C.Step<String, V>}:
  %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, RM.rn_cache(~K, ~enc, V, c), code), RM.rn_item(~K, ~enc, V, C.lookup(K, V, c, code)), lookup(~K, ~enc, V, c, code)) : {Entry.refresh_prepare_found(String, V, RM.rn_cache(~K, ~enc, V, c), code, _) == rn_step(~K, ~enc, V, Entry.refresh_prepare_found(K, V, c, code, C.lookup(K, V, c, code))) : C.Step<String, V>}
  refresh_prepare_found(~K, ~enc, V, c, code, C.lookup(K, V, c, code))

def refresh_at(~K: Data, ~enc: K -> String, -V: Data, c: C.Cache<K, V>, +code: String, entry: T.Entry<K, V>, lifetime: T.Int64, now: T.Int64) -> {Entry.refresh_at(String, V, RM.rn_cache(~K, ~enc, V, c), code, RM.rn_entry(~K, ~enc, V, entry), lifetime, now) == RM.rn_cache(~K, ~enc, V, Entry.refresh_at(K, V, c, code, entry, lifetime, now)) : C.Cache<String, V>}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  T.Item{+k, +v, old} = entry
  %RM.set(~K, ~enc, V, table, code, Some{T.Item{k, v, Time.deadline(now, lifetime)}}) : {C.State{cap, _, order, life, counts, cb} == C.State{cap, RM.rn_map(~K, ~enc, V, Map.set(&2, Maybe<&2, T.Entry<K, V>>, table, code, Some{T.Item{k, v, Time.deadline(now, lifetime)}})), order, life, counts, cb} : C.Cache<String, V>}
  {==}

# ---------------------------------------------------------------------------
# Public machine. Keys inside answers, shapes and pending states are renamed.
def rn_answer(~K: Data, ~enc: K -> String, -V: Data, a: Pub.Answer<K, V>) -> Pub.Answer<String, V>:
  match a:
    case Pub.Empty{}: Pub.Empty{}
    case Pub.Boolean{b}: Pub.Boolean{b}
    case Pub.Value{v, f}: Pub.Value{v, f}
    case Pub.Oldest{k, v, f}: Pub.Oldest{enc(k), v, f}
    case Pub.KeyList{ks}: Pub.KeyList{rn_keys(~K, ~enc, ks)}
    case Pub.ValueList{vs}: Pub.ValueList{vs}
    case Pub.Length{n}: Pub.Length{n}
    case Pub.Counters{m}: Pub.Counters{m}
    case Pub.Storage{leaves, recency, cap, m}: Pub.Storage{leaves, recency, cap, m}

def rn_shape(~K: Data, ~enc: K -> String, s: Pub.Shape<K>) -> Pub.Shape<String>:
  match s:
    case Pub.Flag{}: Pub.Flag{}
    case Pub.ValueOnly{}: Pub.ValueOnly{}
    case Pub.Captured{k}: Pub.Captured{enc(k)}
    case Pub.Nothing{}: Pub.Nothing{}
    case Pub.AllKeys{}: Pub.AllKeys{}
    case Pub.AllValues{}: Pub.AllValues{}

def rn_pending(~K: Data, ~enc: K -> String, -V: Data, p: Pub.Pending<K, V>) -> Pub.Pending<String, V>:
  match p:
    case Pub.AddWait{c, code, key, value, ns, evicted}: Pub.AddWait{RM.rn_cache(~K, ~enc, V, c), code, enc(key), value, ns, evicted}
    case Pub.ReadWait{c, code, tracked, shape}: Pub.ReadWait{RM.rn_cache(~K, ~enc, V, c), code, tracked, rn_shape(~K, ~enc, shape)}
    case Pub.RefreshWait{c, code, entry, ns}: Pub.RefreshWait{RM.rn_cache(~K, ~enc, V, c), code, RM.rn_entry(~K, ~enc, V, entry), ns}
    case Pub.ExpireWait{c, remaining, shape}: Pub.ExpireWait{RM.rn_cache(~K, ~enc, V, c), remaining, rn_shape(~K, ~enc, shape)}

def rn_progress(~K: Data, ~enc: K -> String, -V: Data, p: Pub.Progress<K, V>) -> Pub.Progress<String, V>:
  match p:
    case Pub.Finished{c, a}: Pub.Finished{RM.rn_cache(~K, ~enc, V, c), rn_answer(~K, ~enc, V, a)}
    case Pub.Waiting{pending}: Pub.Waiting{rn_pending(~K, ~enc, V, pending)}

def rn_request(~K: Data, ~enc: K -> String, -V: Data, r: Pub.Request<K, V>) -> Pub.Request<String, V>:
  match r:
    case Pub.Add{k, v}: Pub.Add{enc(k), v}
    case Pub.AddWithLifetime{k, v, ns}: Pub.AddWithLifetime{enc(k), v, ns}
    case Pub.Get{k}: Pub.Get{enc(k)}
    case Pub.GetAndRefresh{k, ns}: Pub.GetAndRefresh{enc(k), ns}
    case Pub.Peek{k}: Pub.Peek{enc(k)}
    case Pub.Contains{k}: Pub.Contains{enc(k)}
    case Pub.Remove{k}: Pub.Remove{enc(k)}
    case Pub.RemoveOldest{}: Pub.RemoveOldest{}
    case Pub.GetOldest{}: Pub.GetOldest{}
    case Pub.Keys{}: Pub.Keys{}
    case Pub.Values{}: Pub.Values{}
    case Pub.Purge{}: Pub.Purge{}
    case Pub.PurgeExpired{}: Pub.PurgeExpired{}
    case Pub.Len{}: Pub.Len{}
    case Pub.SetLifetime{ns}: Pub.SetLifetime{ns}
    case Pub.Metrics{}: Pub.Metrics{}
    case Pub.ResetMetrics{}: Pub.ResetMetrics{}
    case Pub.Diagnostics{}: Pub.Diagnostics{}

def rn_requests(~K: Data, ~enc: K -> String, -V: Data, rs: List<&2, Pub.Request<K, V>>) -> List<&2, Pub.Request<String, V>>:
  match rs:
    case Nil{}: Nil{}
    case Con{r, rest}: Con{rn_request(~K, ~enc, V, r), rn_requests(~K, ~enc, V, rest)}

def p_item_value(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, item: Maybe<&2, T.Entry<K, V>>, +present: Bool) -> {Pub.item_value(String, V, zero_value, RM.rn_item(~K, ~enc, V, item), present) == Pub.item_value(K, V, zero_value, item, present) : V}:
  match item:
    case None{}: {==}
    case Some{T.Item{k, v, d}}:
      match present:
        case True{}: {==}
        case False{}: {==}

def p_item_key(~K: Data, ~enc: K -> String, -V: Data, +zero_key: K, item: Maybe<&2, T.Entry<K, V>>, +present: Bool) -> {Pub.item_key(String, V, enc(zero_key), RM.rn_item(~K, ~enc, V, item), present) == enc(Pub.item_key(K, V, zero_key, item, present)) : String}:
  match item:
    case None{}: {==}
    case Some{T.Item{k, v, d}}:
      match present:
        case True{}: {==}
        case False{}: {==}

def p_shaped(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, +c: C.Cache<K, V>, +item: Maybe<&2, T.Entry<K, V>>, +present: Bool, shape: Pub.Shape<K>) -> {Pub.shaped(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), RM.rn_item(~K, ~enc, V, item), present, rn_shape(~K, ~enc, shape)) == rn_answer(~K, ~enc, V, Pub.shaped(K, V, zero_value, c, item, present, shape)) : Pub.Answer<String, V>}:
  match shape:
    case Pub.Flag{}: {==}
    case Pub.ValueOnly{}: Equal.cong(V, Pub.Answer<String, V>, x => Pub.Value{x, present}, Pub.item_value(String, V, zero_value, RM.rn_item(~K, ~enc, V, item), present), Pub.item_value(K, V, zero_value, item, present), p_item_value(~K, ~enc, V, zero_value, item, present))
    case Pub.Captured{+key}: Equal.cong(V, Pub.Answer<String, V>, x => Pub.Oldest{enc(key), x, present}, Pub.item_value(String, V, zero_value, RM.rn_item(~K, ~enc, V, item), present), Pub.item_value(K, V, zero_value, item, present), p_item_value(~K, ~enc, V, zero_value, item, present))
    case Pub.Nothing{}: {==}
    case Pub.AllKeys{}: Equal.cong(List<&2, String>, Pub.Answer<String, V>, x => Pub.KeyList{x}, Entry.keys_of(String, V, C.entries(String, V, RM.rn_cache(~K, ~enc, V, c))), rn_keys(~K, ~enc, Entry.keys_of(K, V, C.entries(K, V, c))), Equal.trans(List<&2, String>, Entry.keys_of(String, V, C.entries(String, V, RM.rn_cache(~K, ~enc, V, c))), Entry.keys_of(String, V, rn_entries(~K, ~enc, V, C.entries(K, V, c))), rn_keys(~K, ~enc, Entry.keys_of(K, V, C.entries(K, V, c))), Equal.cong(List<&2, T.Entry<String, V>>, List<&2, String>, xs => Entry.keys_of(String, V, xs), C.entries(String, V, RM.rn_cache(~K, ~enc, V, c)), rn_entries(~K, ~enc, V, C.entries(K, V, c)), entries(~K, ~enc, V, c)), keys_of(~K, ~enc, V, C.entries(K, V, c))))
    case Pub.AllValues{}: Equal.cong(List<&2, V>, Pub.Answer<String, V>, x => Pub.ValueList{x}, Entry.values_of(String, V, C.entries(String, V, RM.rn_cache(~K, ~enc, V, c))), Entry.values_of(K, V, C.entries(K, V, c)), Equal.trans(List<&2, V>, Entry.values_of(String, V, C.entries(String, V, RM.rn_cache(~K, ~enc, V, c))), Entry.values_of(String, V, rn_entries(~K, ~enc, V, C.entries(K, V, c))), Entry.values_of(K, V, C.entries(K, V, c)), Equal.cong(List<&2, T.Entry<String, V>>, List<&2, V>, xs => Entry.values_of(String, V, xs), C.entries(String, V, RM.rn_cache(~K, ~enc, V, c)), rn_entries(~K, ~enc, V, C.entries(K, V, c)), entries(~K, ~enc, V, c)), values_of(~K, ~enc, V, C.entries(K, V, c))))

def p_finish_step(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, step: C.Step<K, V>, +shape: Pub.Shape<K>) -> {Pub.finish_step(String, V, zero_value, rn_step(~K, ~enc, V, step), rn_shape(~K, ~enc, shape)) == rn_progress(~K, ~enc, V, Pub.finish_step(K, V, zero_value, step, shape)) : Pub.Progress<String, V>}:
  C.Out{+c, +item, +flag, evs} = step
  Equal.cong(Pub.Answer<String, V>, Pub.Progress<String, V>, a => Pub.Finished{RM.rn_cache(~K, ~enc, V, c), a}, Pub.shaped(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), RM.rn_item(~K, ~enc, V, item), flag, rn_shape(~K, ~enc, shape)), rn_answer(~K, ~enc, V, Pub.shaped(K, V, zero_value, c, item, flag, shape)), p_shaped(~K, ~enc, V, zero_value, c, item, flag, shape))

def p_prepare_room(~K: Data, ~enc: K -> String, -V: Data, +c: C.Cache<K, V>, full: Bool) -> {Pub.prepare_room(String, V, RM.rn_cache(~K, ~enc, V, c), full) == rn_step(~K, ~enc, V, Pub.prepare_room(K, V, c, full)) : C.Step<String, V>}:
  match full:
    case False{}: {==}
    case True{}: remove_oldest(~K, ~enc, V, c, True{})

def p_prepare_found(~K: Data, ~enc: K -> String, -V: Data, c: C.Cache<K, V>, found: Maybe<&2, T.Entry<K, V>>) -> {Pub.prepare_found(String, V, RM.rn_cache(~K, ~enc, V, c), RM.rn_item(~K, ~enc, V, found)) == rn_step(~K, ~enc, V, Pub.prepare_found(K, V, c, found)) : C.Step<String, V>}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  match found:
    case Some{entry}: {==}
    case None{}: p_prepare_room(~K, ~enc, V, C.State{cap, table, order, life, counts, cb}, Nat.is_ge(List.length(&2, String, order), cap))

def p_retained_key(~K: Data, ~enc: K -> String, -V: Data, +key: K, found: Maybe<&2, T.Entry<K, V>>) -> {Pub.retained_key(String, V, enc(key), RM.rn_item(~K, ~enc, V, found)) == enc(Pub.retained_key(K, V, key, found)) : String}:
  match found:
    case Some{T.Item{o, v, d}}: {==}
    case None{}: {==}

def p_finish_add(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, +c: C.Cache<K, V>, +code: String, +key: K, +value: V, +deadline: T.Int64, +evicted: Bool) -> {Pub.finish_add(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), code, enc(key), value, deadline, evicted) == rn_progress(~K, ~enc, V, Pub.finish_add(K, V, zero_value, c, code, key, value, deadline, evicted)) : Pub.Progress<String, V>}:
  Equal.trans(Pub.Progress<String, V>, Pub.finish_step(String, V, zero_value, C.store(String, V, RM.rn_cache(~K, ~enc, V, c), code, enc(key), value, deadline, evicted, Nil{}), Pub.Flag{}), Pub.finish_step(String, V, zero_value, rn_step(~K, ~enc, V, C.store(K, V, c, code, key, value, deadline, evicted, Nil{})), Pub.Flag{}), rn_progress(~K, ~enc, V, Pub.finish_step(K, V, zero_value, C.store(K, V, c, code, key, value, deadline, evicted, Nil{}), Pub.Flag{})), Equal.cong(C.Step<String, V>, Pub.Progress<String, V>, s => Pub.finish_step(String, V, zero_value, s, Pub.Flag{}), C.store(String, V, RM.rn_cache(~K, ~enc, V, c), code, enc(key), value, deadline, evicted, Nil{}), rn_step(~K, ~enc, V, C.store(K, V, c, code, key, value, deadline, evicted, Nil{})), store(~K, ~enc, V, c, code, key, value, deadline, evicted, Nil{})), p_finish_step(~K, ~enc, V, zero_value, C.store(K, V, c, code, key, value, deadline, evicted, Nil{}), Pub.Flag{}))

def p_add_lifetime(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, +c: C.Cache<K, V>, +code: String, +key: K, +value: V, +ns: T.Int64, +evicted: Bool, immortal: Bool) -> {Pub.add_lifetime(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), code, enc(key), value, ns, evicted, immortal) == rn_progress(~K, ~enc, V, Pub.add_lifetime(K, V, zero_value, c, code, key, value, ns, evicted, immortal)) : Pub.Progress<String, V>}:
  match immortal:
    case True{}: p_finish_add(~K, ~enc, V, zero_value, c, code, key, value, Pub.zero_time(), evicted)
    case False{}: {==}

def p_add_prepared(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, step: C.Step<K, V>, +code: String, +key: K, +value: V, +ns: T.Int64) -> {Pub.add_prepared(String, V, zero_value, rn_step(~K, ~enc, V, step), code, enc(key), value, ns) == rn_progress(~K, ~enc, V, Pub.add_prepared(K, V, zero_value, step, code, key, value, ns)) : Pub.Progress<String, V>}:
  C.Out{+c, item, +flag, evs} = step
  p_add_lifetime(~K, ~enc, V, zero_value, c, code, key, value, ns, flag, Time.is_zero(ns))

def p_add_found(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, +c: C.Cache<K, V>, +code: String, +key: K, +value: V, +ns: T.Int64, +found: Maybe<&2, T.Entry<K, V>>) -> {Pub.add_found(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), code, enc(key), value, ns, RM.rn_item(~K, ~enc, V, found)) == rn_progress(~K, ~enc, V, Pub.add_found(K, V, zero_value, c, code, key, value, ns, found)) : Pub.Progress<String, V>}:
  %Equal.sym(C.Step<String, V>, Pub.prepare_found(String, V, RM.rn_cache(~K, ~enc, V, c), RM.rn_item(~K, ~enc, V, found)), rn_step(~K, ~enc, V, Pub.prepare_found(K, V, c, found)), p_prepare_found(~K, ~enc, V, c, found)) : {Pub.add_prepared(String, V, zero_value, _, code, Pub.retained_key(String, V, enc(key), RM.rn_item(~K, ~enc, V, found)), value, ns) == rn_progress(~K, ~enc, V, Pub.add_found(K, V, zero_value, c, code, key, value, ns, found)) : Pub.Progress<String, V>}
  %Equal.sym(String, Pub.retained_key(String, V, enc(key), RM.rn_item(~K, ~enc, V, found)), enc(Pub.retained_key(K, V, key, found)), p_retained_key(~K, ~enc, V, key, found)) : {Pub.add_prepared(String, V, zero_value, rn_step(~K, ~enc, V, Pub.prepare_found(K, V, c, found)), code, _, value, ns) == rn_progress(~K, ~enc, V, Pub.add_found(K, V, zero_value, c, code, key, value, ns, found)) : Pub.Progress<String, V>}
  p_add_prepared(~K, ~enc, V, zero_value, Pub.prepare_found(K, V, c, found), code, Pub.retained_key(K, V, key, found), value, ns)

def p_add_with_lifetime(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, +c: C.Cache<K, V>, +code: String, +key: K, +value: V, +ns: T.Int64) -> {Pub.add_with_lifetime(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), code, enc(key), value, ns) == rn_progress(~K, ~enc, V, Pub.add_with_lifetime(K, V, zero_value, c, code, key, value, ns)) : Pub.Progress<String, V>}:
  %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, RM.rn_cache(~K, ~enc, V, c), code), RM.rn_item(~K, ~enc, V, C.lookup(K, V, c, code)), lookup(~K, ~enc, V, c, code)) : {Pub.add_found(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), code, enc(key), value, ns, _) == rn_progress(~K, ~enc, V, Pub.add_found(K, V, zero_value, c, code, key, value, ns, C.lookup(K, V, c, code))) : Pub.Progress<String, V>}
  p_add_found(~K, ~enc, V, zero_value, c, code, key, value, ns, C.lookup(K, V, c, code))

def p_add(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, c: C.Cache<K, V>, +code: String, +key: K, +value: V) -> {Pub.add(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), code, enc(key), value) == rn_progress(~K, ~enc, V, Pub.add(K, V, zero_value, c, code, key, value)) : Pub.Progress<String, V>}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  p_add_with_lifetime(~K, ~enc, V, zero_value, C.State{cap, table, order, life, counts, cb}, code, key, value, life)

def p_finish_read(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, +c: C.Cache<K, V>, +code: String, +now: T.Int64, +tracked: Bool, +shape: Pub.Shape<K>) -> {Pub.finish_read(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), code, now, tracked, rn_shape(~K, ~enc, shape)) == rn_progress(~K, ~enc, V, Pub.finish_read(K, V, zero_value, c, code, now, tracked, shape)) : Pub.Progress<String, V>}:
  Equal.trans(Pub.Progress<String, V>, Pub.finish_step(String, V, zero_value, C.read_encoded(String, V, RM.rn_cache(~K, ~enc, V, c), code, now, tracked), rn_shape(~K, ~enc, shape)), Pub.finish_step(String, V, zero_value, rn_step(~K, ~enc, V, C.read_encoded(K, V, c, code, now, tracked)), rn_shape(~K, ~enc, shape)), rn_progress(~K, ~enc, V, Pub.finish_step(K, V, zero_value, C.read_encoded(K, V, c, code, now, tracked), shape)), Equal.cong(C.Step<String, V>, Pub.Progress<String, V>, s => Pub.finish_step(String, V, zero_value, s, rn_shape(~K, ~enc, shape)), C.read_encoded(String, V, RM.rn_cache(~K, ~enc, V, c), code, now, tracked), rn_step(~K, ~enc, V, C.read_encoded(K, V, c, code, now, tracked)), read_encoded(~K, ~enc, V, c, code, now, tracked)), p_finish_step(~K, ~enc, V, zero_value, C.read_encoded(K, V, c, code, now, tracked), shape))

def p_read_lifetime(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, +c: C.Cache<K, V>, +code: String, +tracked: Bool, +shape: Pub.Shape<K>, immortal: Bool) -> {Pub.read_lifetime(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), code, tracked, rn_shape(~K, ~enc, shape), immortal) == rn_progress(~K, ~enc, V, Pub.read_lifetime(K, V, zero_value, c, code, tracked, shape, immortal)) : Pub.Progress<String, V>}:
  match immortal:
    case True{}: p_finish_read(~K, ~enc, V, zero_value, c, code, Pub.zero_time(), tracked, shape)
    case False{}: {==}

def p_read_found(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, +c: C.Cache<K, V>, +code: String, +tracked: Bool, +shape: Pub.Shape<K>, found: Maybe<&2, T.Entry<K, V>>) -> {Pub.read_found(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), code, tracked, rn_shape(~K, ~enc, shape), RM.rn_item(~K, ~enc, V, found)) == rn_progress(~K, ~enc, V, Pub.read_found(K, V, zero_value, c, code, tracked, shape, found)) : Pub.Progress<String, V>}:
  match found:
    case None{}: p_finish_read(~K, ~enc, V, zero_value, c, code, Pub.zero_time(), tracked, shape)
    case Some{T.Item{k, v, +d}}: p_read_lifetime(~K, ~enc, V, zero_value, c, code, tracked, shape, Time.is_zero(d))

def p_read(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, +c: C.Cache<K, V>, +code: String, +tracked: Bool, +shape: Pub.Shape<K>) -> {Pub.read(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), code, tracked, rn_shape(~K, ~enc, shape)) == rn_progress(~K, ~enc, V, Pub.read(K, V, zero_value, c, code, tracked, shape)) : Pub.Progress<String, V>}:
  %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, RM.rn_cache(~K, ~enc, V, c), code), RM.rn_item(~K, ~enc, V, C.lookup(K, V, c, code)), lookup(~K, ~enc, V, c, code)) : {Pub.read_found(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), code, tracked, rn_shape(~K, ~enc, shape), _) == rn_progress(~K, ~enc, V, Pub.read_found(K, V, zero_value, c, code, tracked, shape, C.lookup(K, V, c, code))) : Pub.Progress<String, V>}
  p_read_found(~K, ~enc, V, zero_value, c, code, tracked, shape, C.lookup(K, V, c, code))

def p_oldest_found(~K: Data, ~enc: K -> String, -V: Data, +zero_key: K, +zero_value: V, +c: C.Cache<K, V>, +code: String, found: Maybe<&2, T.Entry<K, V>>) -> {Pub.oldest_found(String, V, enc(zero_key), zero_value, RM.rn_cache(~K, ~enc, V, c), code, RM.rn_item(~K, ~enc, V, found)) == rn_progress(~K, ~enc, V, Pub.oldest_found(K, V, zero_key, zero_value, c, code, found)) : Pub.Progress<String, V>}:
  match found:
    case None{}: {==}
    case Some{T.Item{k, v, d}}: p_read(~K, ~enc, V, zero_value, c, code, False{}, Pub.Captured{k})

def p_oldest_order(~K: Data, ~enc: K -> String, -V: Data, +zero_key: K, +zero_value: V, +c: C.Cache<K, V>, order: List<&2, String>) -> {Pub.oldest_order(String, V, enc(zero_key), zero_value, RM.rn_cache(~K, ~enc, V, c), order) == rn_progress(~K, ~enc, V, Pub.oldest_order(K, V, zero_key, zero_value, c, order)) : Pub.Progress<String, V>}:
  match order:
    case Nil{}: {==}
    case Con{+code, rest}:
      %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, RM.rn_cache(~K, ~enc, V, c), code), RM.rn_item(~K, ~enc, V, C.lookup(K, V, c, code)), lookup(~K, ~enc, V, c, code)) : {Pub.oldest_found(String, V, enc(zero_key), zero_value, RM.rn_cache(~K, ~enc, V, c), code, _) == rn_progress(~K, ~enc, V, Pub.oldest_found(K, V, zero_key, zero_value, c, code, C.lookup(K, V, c, code))) : Pub.Progress<String, V>}
      p_oldest_found(~K, ~enc, V, zero_key, zero_value, c, code, C.lookup(K, V, c, code))

def p_get_oldest(~K: Data, ~enc: K -> String, -V: Data, +zero_key: K, +zero_value: V, c: C.Cache<K, V>) -> {Pub.get_oldest(String, V, enc(zero_key), zero_value, RM.rn_cache(~K, ~enc, V, c)) == rn_progress(~K, ~enc, V, Pub.get_oldest(K, V, zero_key, zero_value, c)) : Pub.Progress<String, V>}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  p_oldest_order(~K, ~enc, V, zero_key, zero_value, C.State{cap, table, order, life, counts, cb}, order)

def p_finish_refresh(~K: Data, ~enc: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, entry: T.Entry<K, V>, +ns: T.Int64, +now: T.Int64) -> {Pub.finish_refresh(String, V, RM.rn_cache(~K, ~enc, V, c), code, RM.rn_entry(~K, ~enc, V, entry), ns, now) == rn_progress(~K, ~enc, V, Pub.finish_refresh(K, V, c, code, entry, ns, now)) : Pub.Progress<String, V>}:
  T.Item{+k, +v, +d} = entry
  Equal.cong(C.Cache<String, V>, Pub.Progress<String, V>, x => Pub.Finished{x, Pub.Value{v, True{}}}, Entry.refresh_at(String, V, RM.rn_cache(~K, ~enc, V, c), code, T.Item{enc(k), v, d}, ns, now), RM.rn_cache(~K, ~enc, V, Entry.refresh_at(K, V, c, code, T.Item{k, v, d}, ns, now)), refresh_at(~K, ~enc, V, c, code, T.Item{k, v, d}, ns, now))

def p_refresh_lifetime(~K: Data, ~enc: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, +entry: T.Entry<K, V>, +ns: T.Int64, immortal: Bool) -> {Pub.refresh_lifetime(String, V, RM.rn_cache(~K, ~enc, V, c), code, RM.rn_entry(~K, ~enc, V, entry), ns, immortal) == rn_progress(~K, ~enc, V, Pub.refresh_lifetime(K, V, c, code, entry, ns, immortal)) : Pub.Progress<String, V>}:
  match immortal:
    case True{}: p_finish_refresh(~K, ~enc, V, c, code, entry, Pub.zero_time(), Pub.zero_time())
    case False{}: {==}

def p_refresh_prepared(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, +code: String, +ns: T.Int64, step: C.Step<K, V>) -> {Pub.refresh_prepared(String, V, zero_value, code, ns, rn_step(~K, ~enc, V, step)) == rn_progress(~K, ~enc, V, Pub.refresh_prepared(K, V, zero_value, code, ns, step)) : Pub.Progress<String, V>}:
  match step:
    case C.Out{+c, item, flag, evs}:
      match item:
        case None{}: {==}
        case Some{+entry}:
          match flag:
            case True{}: p_refresh_lifetime(~K, ~enc, V, c, code, entry, ns, Time.is_zero(ns))
            case False{}: {==}

def p_refresh(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, +c: C.Cache<K, V>, +code: String, +ns: T.Int64) -> {Pub.refresh(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), code, ns) == rn_progress(~K, ~enc, V, Pub.refresh(K, V, zero_value, c, code, ns)) : Pub.Progress<String, V>}:
  Equal.trans(Pub.Progress<String, V>, Pub.refresh_prepared(String, V, zero_value, code, ns, Entry.refresh_prepare(String, V, RM.rn_cache(~K, ~enc, V, c), code)), Pub.refresh_prepared(String, V, zero_value, code, ns, rn_step(~K, ~enc, V, Entry.refresh_prepare(K, V, c, code))), rn_progress(~K, ~enc, V, Pub.refresh_prepared(K, V, zero_value, code, ns, Entry.refresh_prepare(K, V, c, code))), Equal.cong(C.Step<String, V>, Pub.Progress<String, V>, s => Pub.refresh_prepared(String, V, zero_value, code, ns, s), Entry.refresh_prepare(String, V, RM.rn_cache(~K, ~enc, V, c), code), rn_step(~K, ~enc, V, Entry.refresh_prepare(K, V, c, code)), refresh_prepare(~K, ~enc, V, c, code)), p_refresh_prepared(~K, ~enc, V, zero_value, code, ns, Entry.refresh_prepare(K, V, c, code)))

def p_complete(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, +c: C.Cache<K, V>, +shape: Pub.Shape<K>) -> {Pub.complete(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), rn_shape(~K, ~enc, shape)) == rn_progress(~K, ~enc, V, Pub.complete(K, V, zero_value, c, shape)) : Pub.Progress<String, V>}:
  Equal.cong(Pub.Answer<String, V>, Pub.Progress<String, V>, a => Pub.Finished{RM.rn_cache(~K, ~enc, V, c), a}, Pub.shaped(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), None{}, False{}, rn_shape(~K, ~enc, shape)), rn_answer(~K, ~enc, V, Pub.shaped(K, V, zero_value, c, None{}, False{}, shape)), p_shaped(~K, ~enc, V, zero_value, c, None{}, False{}, shape))

def p_expire_lifetime(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, +c: C.Cache<K, V>, +remaining: Nat, +shape: Pub.Shape<K>, immortal: Bool) -> {Pub.expire_lifetime(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), remaining, rn_shape(~K, ~enc, shape), immortal) == rn_progress(~K, ~enc, V, Pub.expire_lifetime(K, V, zero_value, c, remaining, shape, immortal)) : Pub.Progress<String, V>}:
  match immortal:
    case True{}: p_complete(~K, ~enc, V, zero_value, c, shape)
    case False{}: {==}

def p_expire_entry(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, +c: C.Cache<K, V>, +remaining: Nat, +shape: Pub.Shape<K>, entry: Maybe<&2, T.Entry<K, V>>) -> {Pub.expire_entry(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), remaining, rn_shape(~K, ~enc, shape), RM.rn_item(~K, ~enc, V, entry)) == rn_progress(~K, ~enc, V, Pub.expire_entry(K, V, zero_value, c, remaining, shape, entry)) : Pub.Progress<String, V>}:
  match entry:
    case None{}: p_complete(~K, ~enc, V, zero_value, c, shape)
    case Some{T.Item{k, v, +d}}: p_expire_lifetime(~K, ~enc, V, zero_value, c, remaining, shape, Time.is_zero(d))

def p_expire_next(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, +c: C.Cache<K, V>, remaining: Nat, +shape: Pub.Shape<K>) -> {Pub.expire_next(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), remaining, rn_shape(~K, ~enc, shape)) == rn_progress(~K, ~enc, V, Pub.expire_next(K, V, zero_value, c, remaining, shape)) : Pub.Progress<String, V>}:
  match remaining:
    case 0n: p_complete(~K, ~enc, V, zero_value, c, shape)
    case 1n+p:
      %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.oldest_entry(String, V, RM.rn_cache(~K, ~enc, V, c)), RM.rn_item(~K, ~enc, V, C.oldest_entry(K, V, c)), oldest_entry(~K, ~enc, V, c)) : {Pub.expire_entry(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), p, rn_shape(~K, ~enc, shape), _) == rn_progress(~K, ~enc, V, Pub.expire_entry(K, V, zero_value, c, p, shape, C.oldest_entry(K, V, c))) : Pub.Progress<String, V>}
      p_expire_entry(~K, ~enc, V, zero_value, c, p, shape, C.oldest_entry(K, V, c))

def p_expire_decide(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, +c: C.Cache<K, V>, +remaining: Nat, +shape: Pub.Shape<K>, expired: Bool) -> {Pub.expire_decide(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), remaining, rn_shape(~K, ~enc, shape), expired) == rn_progress(~K, ~enc, V, Pub.expire_decide(K, V, zero_value, c, remaining, shape, expired)) : Pub.Progress<String, V>}:
  match expired:
    case False{}: p_complete(~K, ~enc, V, zero_value, c, shape)
    case True{}:
      %Equal.sym(C.Step<String, V>, C.remove_oldest(String, V, RM.rn_cache(~K, ~enc, V, c), False{}), rn_step(~K, ~enc, V, C.remove_oldest(K, V, c, False{})), remove_oldest(~K, ~enc, V, c, False{})) : {Pub.expire_next(String, V, zero_value, C.step_cache(String, V, _), remaining, rn_shape(~K, ~enc, shape)) == rn_progress(~K, ~enc, V, Pub.expire_next(K, V, zero_value, C.step_cache(K, V, C.remove_oldest(K, V, c, False{})), remaining, shape)) : Pub.Progress<String, V>}
      %Equal.sym(C.Cache<String, V>, C.step_cache(String, V, rn_step(~K, ~enc, V, C.remove_oldest(K, V, c, False{}))), RM.rn_cache(~K, ~enc, V, C.step_cache(K, V, C.remove_oldest(K, V, c, False{}))), step_cache(~K, ~enc, V, C.remove_oldest(K, V, c, False{}))) : {Pub.expire_next(String, V, zero_value, _, remaining, rn_shape(~K, ~enc, shape)) == rn_progress(~K, ~enc, V, Pub.expire_next(K, V, zero_value, C.step_cache(K, V, C.remove_oldest(K, V, c, False{})), remaining, shape)) : Pub.Progress<String, V>}
      p_expire_next(~K, ~enc, V, zero_value, C.step_cache(K, V, C.remove_oldest(K, V, c, False{})), remaining, shape)

def p_expire_sampled(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, +c: C.Cache<K, V>, +remaining: Nat, +shape: Pub.Shape<K>, +now: T.Int64, entry: Maybe<&2, T.Entry<K, V>>) -> {Pub.expire_sampled(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), remaining, rn_shape(~K, ~enc, shape), now, RM.rn_item(~K, ~enc, V, entry)) == rn_progress(~K, ~enc, V, Pub.expire_sampled(K, V, zero_value, c, remaining, shape, now, entry)) : Pub.Progress<String, V>}:
  match entry:
    case None{}: p_complete(~K, ~enc, V, zero_value, c, shape)
    case Some{T.Item{k, v, +d}}: p_expire_decide(~K, ~enc, V, zero_value, c, remaining, shape, Time.expired(d, now))

def p_expire(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, c: C.Cache<K, V>, +shape: Pub.Shape<K>) -> {Pub.expire(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), rn_shape(~K, ~enc, shape)) == rn_progress(~K, ~enc, V, Pub.expire(K, V, zero_value, c, shape)) : Pub.Progress<String, V>}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  p_expire_next(~K, ~enc, V, zero_value, C.State{cap, table, order, life, counts, cb}, List.length(&2, String, order), shape)

def p_purge(~K: Data, ~enc: K -> String, -V: Data, c: C.Cache<K, V>) -> {Pub.purge(String, V, RM.rn_cache(~K, ~enc, V, c)) == RM.rn_cache(~K, ~enc, V, Pub.purge(K, V, c)) : C.Cache<String, V>}:
  C.State{cap, table, order, life, counts, cb} = c
  {==}

def p_removed_oldest(~K: Data, ~enc: K -> String, -V: Data, +zero_key: K, +zero_value: V, step: C.Step<K, V>) -> {Pub.removed_oldest(String, V, enc(zero_key), zero_value, rn_step(~K, ~enc, V, step)) == rn_progress(~K, ~enc, V, Pub.removed_oldest(K, V, zero_key, zero_value, step)) : Pub.Progress<String, V>}:
  C.Out{+c, +item, +flag, evs} = step
  %Equal.sym(String, Pub.item_key(String, V, enc(zero_key), RM.rn_item(~K, ~enc, V, item), flag), enc(Pub.item_key(K, V, zero_key, item, flag)), p_item_key(~K, ~enc, V, zero_key, item, flag)) : {Pub.Finished{RM.rn_cache(~K, ~enc, V, c), Pub.Oldest{_, Pub.item_value(String, V, zero_value, RM.rn_item(~K, ~enc, V, item), flag), flag}} == rn_progress(~K, ~enc, V, Pub.removed_oldest(K, V, zero_key, zero_value, C.Out{c, item, flag, evs})) : Pub.Progress<String, V>}
  %Equal.sym(V, Pub.item_value(String, V, zero_value, RM.rn_item(~K, ~enc, V, item), flag), Pub.item_value(K, V, zero_value, item, flag), p_item_value(~K, ~enc, V, zero_value, item, flag)) : {Pub.Finished{RM.rn_cache(~K, ~enc, V, c), Pub.Oldest{enc(Pub.item_key(K, V, zero_key, item, flag)), _, flag}} == rn_progress(~K, ~enc, V, Pub.removed_oldest(K, V, zero_key, zero_value, C.Out{c, item, flag, evs})) : Pub.Progress<String, V>}
  {==}

def p_start(~K: Data, ~enc: K -> String, -V: Data, +zero_key: K, +zero_value: V, request: Pub.Request<K, V>, +c: C.Cache<K, V>) -> {Pub.start(String, V, Codec.string_encode, enc(zero_key), zero_value, RM.rn_cache(~K, ~enc, V, c), rn_request(~K, ~enc, V, request)) == rn_progress(~K, ~enc, V, Pub.start(K, V, enc, zero_key, zero_value, c, request)) : Pub.Progress<String, V>}:
  match request:
    case Pub.Add{+k, v}: p_add(~K, ~enc, V, zero_value, c, enc(k), k, v)
    case Pub.AddWithLifetime{+k, v, ns}: p_add_with_lifetime(~K, ~enc, V, zero_value, c, enc(k), k, v, ns)
    case Pub.Get{k}: p_read(~K, ~enc, V, zero_value, c, enc(k), True{}, Pub.ValueOnly{})
    case Pub.GetAndRefresh{k, ns}: p_refresh(~K, ~enc, V, zero_value, c, enc(k), ns)
    case Pub.Peek{k}: p_read(~K, ~enc, V, zero_value, c, enc(k), False{}, Pub.ValueOnly{})
    case Pub.Contains{k}: p_read(~K, ~enc, V, zero_value, c, enc(k), False{}, Pub.Flag{})
    case Pub.Remove{+k}: Equal.trans(Pub.Progress<String, V>, Pub.finish_step(String, V, zero_value, C.remove(String, V, Codec.string_encode, RM.rn_cache(~K, ~enc, V, c), enc(k)), Pub.Flag{}), Pub.finish_step(String, V, zero_value, rn_step(~K, ~enc, V, C.remove(K, V, enc, c, k)), Pub.Flag{}), rn_progress(~K, ~enc, V, Pub.finish_step(K, V, zero_value, C.remove(K, V, enc, c, k), Pub.Flag{})), Equal.cong(C.Step<String, V>, Pub.Progress<String, V>, s => Pub.finish_step(String, V, zero_value, s, Pub.Flag{}), C.remove(String, V, Codec.string_encode, RM.rn_cache(~K, ~enc, V, c), enc(k)), rn_step(~K, ~enc, V, C.remove(K, V, enc, c, k)), remove(~K, ~enc, V, c, k)), p_finish_step(~K, ~enc, V, zero_value, C.remove(K, V, enc, c, k), Pub.Flag{}))
    case Pub.RemoveOldest{}: Equal.trans(Pub.Progress<String, V>, Pub.removed_oldest(String, V, enc(zero_key), zero_value, C.remove_oldest(String, V, RM.rn_cache(~K, ~enc, V, c), False{})), Pub.removed_oldest(String, V, enc(zero_key), zero_value, rn_step(~K, ~enc, V, C.remove_oldest(K, V, c, False{}))), rn_progress(~K, ~enc, V, Pub.removed_oldest(K, V, zero_key, zero_value, C.remove_oldest(K, V, c, False{}))), Equal.cong(C.Step<String, V>, Pub.Progress<String, V>, s => Pub.removed_oldest(String, V, enc(zero_key), zero_value, s), C.remove_oldest(String, V, RM.rn_cache(~K, ~enc, V, c), False{}), rn_step(~K, ~enc, V, C.remove_oldest(K, V, c, False{})), remove_oldest(~K, ~enc, V, c, False{})), p_removed_oldest(~K, ~enc, V, zero_key, zero_value, C.remove_oldest(K, V, c, False{})))
    case Pub.GetOldest{}: p_get_oldest(~K, ~enc, V, zero_key, zero_value, c)
    case Pub.Keys{}: p_expire(~K, ~enc, V, zero_value, c, Pub.AllKeys{})
    case Pub.Values{}: p_expire(~K, ~enc, V, zero_value, c, Pub.AllValues{})
    case Pub.Purge{}: Equal.cong(C.Cache<String, V>, Pub.Progress<String, V>, x => Pub.Finished{x, Pub.Empty{}}, Pub.purge(String, V, RM.rn_cache(~K, ~enc, V, c)), RM.rn_cache(~K, ~enc, V, Pub.purge(K, V, c)), p_purge(~K, ~enc, V, c))
    case Pub.PurgeExpired{}: p_expire(~K, ~enc, V, zero_value, c, Pub.Nothing{})
    case Pub.Len{}:
      C.State{cap, table, order, life, counts, cb} = c
      {==}
    case Pub.SetLifetime{ns}:
      C.State{cap, table, order, life, counts, cb} = c
      {==}
    case Pub.Metrics{}:
      C.State{cap, table, order, life, counts, cb} = c
      {==}
    case Pub.ResetMetrics{}:
      C.State{cap, table, order, life, counts, cb} = c
      {==}
    case Pub.Diagnostics{}:
      C.State{+cap, +table, +order, +life, +counts, +cb} = c
      Equal.cong(Nat, Pub.Progress<String, V>, n => Pub.Finished{C.State{cap, RM.rn_map(~K, ~enc, V, table), order, life, counts, cb}, Pub.Storage{n, List.length(&2, String, order), cap, counts}}, Map.size(&2, Maybe<&2, T.Entry<String, V>>, RM.rn_map(~K, ~enc, V, table)), Map.size(&2, Maybe<&2, T.Entry<K, V>>, table), RM.size(~K, ~enc, V, table))

def p_resume(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, pending: Pub.Pending<K, V>, +now: T.Int64) -> {Pub.resume(String, V, zero_value, rn_pending(~K, ~enc, V, pending), now) == rn_progress(~K, ~enc, V, Pub.resume(K, V, zero_value, pending, now)) : Pub.Progress<String, V>}:
  match pending:
    case Pub.AddWait{c, code, key, value, ns, evicted}: p_finish_add(~K, ~enc, V, zero_value, c, code, key, value, Time.deadline(now, ns), evicted)
    case Pub.ReadWait{c, code, tracked, shape}: p_finish_read(~K, ~enc, V, zero_value, c, code, now, tracked, shape)
    case Pub.RefreshWait{c, code, entry, ns}: p_finish_refresh(~K, ~enc, V, c, code, entry, ns, now)
    case Pub.ExpireWait{+c, remaining, shape}:
      %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.oldest_entry(String, V, RM.rn_cache(~K, ~enc, V, c)), RM.rn_item(~K, ~enc, V, C.oldest_entry(K, V, c)), oldest_entry(~K, ~enc, V, c)) : {Pub.expire_sampled(String, V, zero_value, RM.rn_cache(~K, ~enc, V, c), remaining, rn_shape(~K, ~enc, shape), now, _) == rn_progress(~K, ~enc, V, Pub.expire_sampled(K, V, zero_value, c, remaining, shape, now, C.oldest_entry(K, V, c))) : Pub.Progress<String, V>}
      p_expire_sampled(~K, ~enc, V, zero_value, c, remaining, shape, now, C.oldest_entry(K, V, c))

def p_abandon(~K: Data, ~enc: K -> String, -V: Data, pending: Pub.Pending<K, V>) -> {Pub.abandon(String, V, rn_pending(~K, ~enc, V, pending)) == RM.rn_cache(~K, ~enc, V, Pub.abandon(K, V, pending)) : C.Cache<String, V>}:
  match pending:
    case Pub.AddWait{c, code, key, value, ns, evicted}: {==}
    case Pub.ReadWait{c, code, tracked, shape}: {==}
    case Pub.RefreshWait{c, code, entry, ns}: {==}
    case Pub.ExpireWait{c, remaining, shape}: {==}

# ---------------------------------------------------------------------------
# Driver.
def rn_outcome(~K: Data, ~enc: K -> String, -V: Data, o: D.Outcome<K, V>) -> D.Outcome<String, V>:
  match o:
    case D.Returned{c, answer, remaining, requests}: D.Returned{RM.rn_cache(~K, ~enc, V, c), rn_answer(~K, ~enc, V, answer), remaining, requests}
    case D.Failed{c, error, remaining, requests}: D.Failed{RM.rn_cache(~K, ~enc, V, c), error, remaining, requests}

def rn_outcomes(~K: Data, ~enc: K -> String, -V: Data, os: List<&2, D.Outcome<K, V>>) -> List<&2, D.Outcome<String, V>>:
  match os:
    case Nil{}: Nil{}
    case Con{o, rest}: Con{rn_outcome(~K, ~enc, V, o), rn_outcomes(~K, ~enc, V, rest)}

def rn_trace(~K: Data, ~enc: K -> String, -V: Data, t: D.Trace<K, V>) -> D.Trace<String, V>:
  D.Ran{c, events, outcomes, requests} = t
  D.Ran{RM.rn_cache(~K, ~enc, V, c), events, rn_outcomes(~K, ~enc, V, outcomes), requests}

def d_bump(~K: Data, ~enc: K -> String, -V: Data, o: D.Outcome<K, V>) -> {D.bump(String, V, rn_outcome(~K, ~enc, V, o)) == rn_outcome(~K, ~enc, V, D.bump(K, V, o)) : D.Outcome<String, V>}:
  match o:
    case D.Returned{c, answer, remaining, requests}: {==}
    case D.Failed{c, error, remaining, requests}: {==}

def d_drive(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, events: List<&2, Clock.Event>, progress: Pub.Progress<K, V>) -> {D.drive(String, V, zero_value, events, rn_progress(~K, ~enc, V, progress)) == rn_outcome(~K, ~enc, V, D.drive(K, V, zero_value, events, progress)) : D.Outcome<String, V>}:
  match events:
    case Nil{}:
      match progress:
        case Pub.Finished{c, a}: {==}
        case Pub.Waiting{pending}: Equal.cong(C.Cache<String, V>, D.Outcome<String, V>, x => D.Failed{x, Clock.Exhausted{}, Nil{}, 1n}, Pub.abandon(String, V, rn_pending(~K, ~enc, V, pending)), RM.rn_cache(~K, ~enc, V, Pub.abandon(K, V, pending)), p_abandon(~K, ~enc, V, pending))
    case Con{event, +tail}:
      match event:
        case Clock.InvalidSample{+reason}:
          match progress:
            case Pub.Finished{c, a}: {==}
            case Pub.Waiting{pending}: Equal.cong(C.Cache<String, V>, D.Outcome<String, V>, x => D.Failed{x, Clock.Invalid{reason}, tail, 1n}, Pub.abandon(String, V, rn_pending(~K, ~enc, V, pending)), RM.rn_cache(~K, ~enc, V, Pub.abandon(K, V, pending)), p_abandon(~K, ~enc, V, pending))
        case Clock.ProviderException{+reason}:
          match progress:
            case Pub.Finished{c, a}: {==}
            case Pub.Waiting{pending}: Equal.cong(C.Cache<String, V>, D.Outcome<String, V>, x => D.Failed{x, Clock.Thrown{reason}, tail, 1n}, Pub.abandon(String, V, rn_pending(~K, ~enc, V, pending)), RM.rn_cache(~K, ~enc, V, Pub.abandon(K, V, pending)), p_abandon(~K, ~enc, V, pending))
        case Clock.Sample{+now}:
          match progress:
            case Pub.Finished{c, a}: {==}
            case Pub.Waiting{+pending}: Equal.trans(D.Outcome<String, V>, D.bump(String, V, D.drive(String, V, zero_value, tail, Pub.resume(String, V, zero_value, rn_pending(~K, ~enc, V, pending), now))), D.bump(String, V, rn_outcome(~K, ~enc, V, D.drive(K, V, zero_value, tail, Pub.resume(K, V, zero_value, pending, now)))), rn_outcome(~K, ~enc, V, D.bump(K, V, D.drive(K, V, zero_value, tail, Pub.resume(K, V, zero_value, pending, now)))), Equal.cong(D.Outcome<String, V>, D.Outcome<String, V>, o => D.bump(String, V, o), D.drive(String, V, zero_value, tail, Pub.resume(String, V, zero_value, rn_pending(~K, ~enc, V, pending), now)), rn_outcome(~K, ~enc, V, D.drive(K, V, zero_value, tail, Pub.resume(K, V, zero_value, pending, now))), Equal.trans(D.Outcome<String, V>, D.drive(String, V, zero_value, tail, Pub.resume(String, V, zero_value, rn_pending(~K, ~enc, V, pending), now)), D.drive(String, V, zero_value, tail, rn_progress(~K, ~enc, V, Pub.resume(K, V, zero_value, pending, now))), rn_outcome(~K, ~enc, V, D.drive(K, V, zero_value, tail, Pub.resume(K, V, zero_value, pending, now))), Equal.cong(Pub.Progress<String, V>, D.Outcome<String, V>, p => D.drive(String, V, zero_value, tail, p), Pub.resume(String, V, zero_value, rn_pending(~K, ~enc, V, pending), now), rn_progress(~K, ~enc, V, Pub.resume(K, V, zero_value, pending, now)), p_resume(~K, ~enc, V, zero_value, pending, now)), d_drive(~K, ~enc, V, zero_value, tail, Pub.resume(K, V, zero_value, pending, now)))), d_bump(~K, ~enc, V, D.drive(K, V, zero_value, tail, Pub.resume(K, V, zero_value, pending, now))))

def d_execute(~K: Data, ~enc: K -> String, -V: Data, +zero_key: K, +zero_value: V, +c: C.Cache<K, V>, +events: List<&2, Clock.Event>, +request: Pub.Request<K, V>) -> {D.execute(~String, ~Codec.string_encode, V, enc(zero_key), zero_value, RM.rn_cache(~K, ~enc, V, c), events, rn_request(~K, ~enc, V, request)) == rn_outcome(~K, ~enc, V, D.execute(~K, ~enc, V, zero_key, zero_value, c, events, request)) : D.Outcome<String, V>}:
  Equal.trans(D.Outcome<String, V>, D.drive(String, V, zero_value, events, Pub.start(String, V, Codec.string_encode, enc(zero_key), zero_value, RM.rn_cache(~K, ~enc, V, c), rn_request(~K, ~enc, V, request))), D.drive(String, V, zero_value, events, rn_progress(~K, ~enc, V, Pub.start(K, V, enc, zero_key, zero_value, c, request))), rn_outcome(~K, ~enc, V, D.drive(K, V, zero_value, events, Pub.start(K, V, enc, zero_key, zero_value, c, request))), Equal.cong(Pub.Progress<String, V>, D.Outcome<String, V>, p => D.drive(String, V, zero_value, events, p), Pub.start(String, V, Codec.string_encode, enc(zero_key), zero_value, RM.rn_cache(~K, ~enc, V, c), rn_request(~K, ~enc, V, request)), rn_progress(~K, ~enc, V, Pub.start(K, V, enc, zero_key, zero_value, c, request)), p_start(~K, ~enc, V, zero_key, zero_value, request, c)), d_drive(~K, ~enc, V, zero_value, events, Pub.start(K, V, enc, zero_key, zero_value, c, request)))

def d_prepend(~K: Data, ~enc: K -> String, -V: Data, o: D.Outcome<K, V>, t: D.Trace<K, V>) -> {D.prepend(String, V, rn_outcome(~K, ~enc, V, o), rn_trace(~K, ~enc, V, t)) == rn_trace(~K, ~enc, V, D.prepend(K, V, o, t)) : D.Trace<String, V>}:
  match o:
    case D.Returned{c2, answer, remaining, requests}:
      D.Ran{c, events, outcomes, count} = t
      {==}
    case D.Failed{c2, error, remaining, requests}:
      D.Ran{c, events, outcomes, count} = t
      {==}

def d_run_cons(~K: Data, ~enc: K -> String, -V: Data, +zero_key: K, +zero_value: V, +tail: List<&2, Pub.Request<K, V>>, o: D.Outcome<K, V>, ih: @+c2: C.Cache<K, V> -> @+ev2: List<&2, Clock.Event> -> {D.run(~String, ~Codec.string_encode, V, rn_requests(~K, ~enc, V, tail), RM.rn_cache(~K, ~enc, V, c2), enc(zero_key), zero_value, ev2) == rn_trace(~K, ~enc, V, D.run(~K, ~enc, V, tail, c2, zero_key, zero_value, ev2)) : D.Trace<String, V>}) -> {D.prepend(String, V, rn_outcome(~K, ~enc, V, o), D.run(~String, ~Codec.string_encode, V, rn_requests(~K, ~enc, V, tail), D.cache(String, V, rn_outcome(~K, ~enc, V, o)), enc(zero_key), zero_value, D.remaining(String, V, rn_outcome(~K, ~enc, V, o)))) == rn_trace(~K, ~enc, V, D.prepend(K, V, o, D.run(~K, ~enc, V, tail, D.cache(K, V, o), zero_key, zero_value, D.remaining(K, V, o)))) : D.Trace<String, V>}:
  match o:
    case D.Returned{+c2, +answer, +remaining, +requests}: Equal.trans(D.Trace<String, V>, D.prepend(String, V, rn_outcome(~K, ~enc, V, D.Returned{c2, answer, remaining, requests}), D.run(~String, ~Codec.string_encode, V, rn_requests(~K, ~enc, V, tail), RM.rn_cache(~K, ~enc, V, c2), enc(zero_key), zero_value, remaining)), D.prepend(String, V, rn_outcome(~K, ~enc, V, D.Returned{c2, answer, remaining, requests}), rn_trace(~K, ~enc, V, D.run(~K, ~enc, V, tail, c2, zero_key, zero_value, remaining))), rn_trace(~K, ~enc, V, D.prepend(K, V, D.Returned{c2, answer, remaining, requests}, D.run(~K, ~enc, V, tail, c2, zero_key, zero_value, remaining))), Equal.cong(D.Trace<String, V>, D.Trace<String, V>, t => D.prepend(String, V, rn_outcome(~K, ~enc, V, D.Returned{c2, answer, remaining, requests}), t), D.run(~String, ~Codec.string_encode, V, rn_requests(~K, ~enc, V, tail), RM.rn_cache(~K, ~enc, V, c2), enc(zero_key), zero_value, remaining), rn_trace(~K, ~enc, V, D.run(~K, ~enc, V, tail, c2, zero_key, zero_value, remaining)), ih(c2)(remaining)), d_prepend(~K, ~enc, V, D.Returned{c2, answer, remaining, requests}, D.run(~K, ~enc, V, tail, c2, zero_key, zero_value, remaining)))
    case D.Failed{+c2, +error, +remaining, +requests}: Equal.trans(D.Trace<String, V>, D.prepend(String, V, rn_outcome(~K, ~enc, V, D.Failed{c2, error, remaining, requests}), D.run(~String, ~Codec.string_encode, V, rn_requests(~K, ~enc, V, tail), RM.rn_cache(~K, ~enc, V, c2), enc(zero_key), zero_value, remaining)), D.prepend(String, V, rn_outcome(~K, ~enc, V, D.Failed{c2, error, remaining, requests}), rn_trace(~K, ~enc, V, D.run(~K, ~enc, V, tail, c2, zero_key, zero_value, remaining))), rn_trace(~K, ~enc, V, D.prepend(K, V, D.Failed{c2, error, remaining, requests}, D.run(~K, ~enc, V, tail, c2, zero_key, zero_value, remaining))), Equal.cong(D.Trace<String, V>, D.Trace<String, V>, t => D.prepend(String, V, rn_outcome(~K, ~enc, V, D.Failed{c2, error, remaining, requests}), t), D.run(~String, ~Codec.string_encode, V, rn_requests(~K, ~enc, V, tail), RM.rn_cache(~K, ~enc, V, c2), enc(zero_key), zero_value, remaining), rn_trace(~K, ~enc, V, D.run(~K, ~enc, V, tail, c2, zero_key, zero_value, remaining)), ih(c2)(remaining)), d_prepend(~K, ~enc, V, D.Failed{c2, error, remaining, requests}, D.run(~K, ~enc, V, tail, c2, zero_key, zero_value, remaining)))

def d_run(~K: Data, ~enc: K -> String, -V: Data, requests: List<&2, Pub.Request<K, V>>, +c: C.Cache<K, V>, +zero_key: K, +zero_value: V, +events: List<&2, Clock.Event>) -> {D.run(~String, ~Codec.string_encode, V, rn_requests(~K, ~enc, V, requests), RM.rn_cache(~K, ~enc, V, c), enc(zero_key), zero_value, events) == rn_trace(~K, ~enc, V, D.run(~K, ~enc, V, requests, c, zero_key, zero_value, events)) : D.Trace<String, V>}:
  match requests:
    case Nil{}: {==}
    case Con{+request, +tail}:
      Equal.trans(D.Trace<String, V>, D.prepend(String, V, D.execute(~String, ~Codec.string_encode, V, enc(zero_key), zero_value, RM.rn_cache(~K, ~enc, V, c), events, rn_request(~K, ~enc, V, request)), D.run(~String, ~Codec.string_encode, V, rn_requests(~K, ~enc, V, tail), D.cache(String, V, D.execute(~String, ~Codec.string_encode, V, enc(zero_key), zero_value, RM.rn_cache(~K, ~enc, V, c), events, rn_request(~K, ~enc, V, request))), enc(zero_key), zero_value, D.remaining(String, V, D.execute(~String, ~Codec.string_encode, V, enc(zero_key), zero_value, RM.rn_cache(~K, ~enc, V, c), events, rn_request(~K, ~enc, V, request))))), D.prepend(String, V, rn_outcome(~K, ~enc, V, D.execute(~K, ~enc, V, zero_key, zero_value, c, events, request)), D.run(~String, ~Codec.string_encode, V, rn_requests(~K, ~enc, V, tail), D.cache(String, V, rn_outcome(~K, ~enc, V, D.execute(~K, ~enc, V, zero_key, zero_value, c, events, request))), enc(zero_key), zero_value, D.remaining(String, V, rn_outcome(~K, ~enc, V, D.execute(~K, ~enc, V, zero_key, zero_value, c, events, request))))), rn_trace(~K, ~enc, V, D.prepend(K, V, D.execute(~K, ~enc, V, zero_key, zero_value, c, events, request), D.run(~K, ~enc, V, tail, D.cache(K, V, D.execute(~K, ~enc, V, zero_key, zero_value, c, events, request)), zero_key, zero_value, D.remaining(K, V, D.execute(~K, ~enc, V, zero_key, zero_value, c, events, request))))), Equal.cong(D.Outcome<String, V>, D.Trace<String, V>, x => D.prepend(String, V, x, D.run(~String, ~Codec.string_encode, V, rn_requests(~K, ~enc, V, tail), D.cache(String, V, x), enc(zero_key), zero_value, D.remaining(String, V, x))), D.execute(~String, ~Codec.string_encode, V, enc(zero_key), zero_value, RM.rn_cache(~K, ~enc, V, c), events, rn_request(~K, ~enc, V, request)), rn_outcome(~K, ~enc, V, D.execute(~K, ~enc, V, zero_key, zero_value, c, events, request)), d_execute(~K, ~enc, V, zero_key, zero_value, c, events, request)), d_run_cons(~K, ~enc, V, zero_key, zero_value, tail, D.execute(~K, ~enc, V, zero_key, zero_value, c, events, request), c2 => ev2 => d_run(~K, ~enc, V, tail, c2, zero_key, zero_value, ev2)))
