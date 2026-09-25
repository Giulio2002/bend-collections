import Base
import ./map_set_frame.bend as SetFrame
import ./map_set_critbit.bend as SetCritbit
import ./map_delete_critbit.bend as DeleteCritbit
import ./map_delete_frame.bend as DeleteFrame
import ./map_delete_routes.bend as DeleteRoutes
import ./map_routing.bend as Routes
import ./map_lookup.bend as Lookup
import ./map_seek.bend as Seek
import ./map_delete.bend as Delete
import ./invariants.bend as Invariants
import ./map_insert.bend as Insert
import ../types/model.bend as T
import ../spec/cache.bend as S
import ../src/cache.bend as C

# Initial refinement is generic in original key/value types. The full abstraction
# of nonempty maps and its representation invariant remain separate obligations.
law initialization:
  for -K: Data
  for -V: Data
  for cap: Nat
  {C.len(K, V, C.init(K, V, cap)) == S.length(K, V, S.initial(K, V, cap)) : Nat}
def initialization(K, V, cap):
  {==}

law initialization_empty_lookup:
  for -K: Data
  for -V: Data
  for cap: Nat
  for code: String
  {C.lookup(K, V, C.init(K, V, cap), code) == None{} : Maybe<&2, T.Entry<K, V>>}
def initialization_empty_lookup(K, V, cap, code):
  {==}

law initialization_metrics:
  for -K: Data
  for -V: Data
  for cap: Nat
  {C.metrics(K, V, C.init(K, V, cap)) == T.zero_metrics() : T.Metrics}
def initialization_metrics(K, V, cap):
  {==}

# An actual operation law, quantified over every key and encoder, including
# encoders not yet proved injective (empty lookup does not need injectivity).
law empty_remove:
  for -K: Data
  for -V: Data
  for encode: K -> String
  for cap: Nat
  for key: K
  {C.remove(K, V, encode, C.init(K, V, cap), key) == C.Out{C.init(K, V, cap), None{}, False{}, Nil{}} : C.Step<K, V>}
def empty_remove(K, V, encode, cap, key):
  {==}

law empty_get:
  for -K: Data
  for -V: Data
  for encode: K -> String
  for cap: Nat
  for key: K
  for now: T.Int64
  {C.get(K, V, encode, C.init(K, V, cap), key, now) == C.Out{C.State{cap, MTip{}, Nil{}, T.I64{Word.zero(64n)}, T.Counts{Word.zero(64n), Word.zero(64n), Word.zero(64n), Word.zero(64n), Word.inc(64n, Word.zero(64n))}, False{}}, None{}, False{}, Nil{}} : C.Step<K, V>}
def empty_get(K, V, encode, cap, key, now):
  {==}

def binding_cons(-K: Data, -V: Data, item: Maybe<&2, T.Entry<K, V>>, rest: List<&2, T.Entry<K, V>>) -> List<&2, T.Entry<K, V>>:
  match item:
    case None{}:
      rest
    case Some{entry}:
      Con{entry, rest}

def bindings(-K: Data, -V: Data, xs: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>) -> List<&2, T.Entry<K, V>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{Tuple{code, item}, rest}:
      binding_cons(K, V, item, bindings(K, V, rest))

def keys_of(-K: Data, -V: Data, xs: List<&2, T.Entry<K, V>>) -> List<&2, K>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{T.Item{k, v, d}, rest}:
      Con{k, keys_of(K, V, rest)}

# Explicit abstraction, not the specification itself. Map validity, no stored
# None, and map/recency agreement must still be proved to make it faithful for
# every reachable nonempty state (otherwise inconsistent entries could be lost).
def abstract(-K: Data, -V: Data, +c: C.Cache<K, V>) -> S.Model<K, V>:
  C.State{cap, table, order, life, counts, cb} = c
  S.Abstract{cap, bindings(K, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)), keys_of(K, V, C.entries(K, V, c)), life, counts, cb}

def observe(-K: Data, -V: Data, step: C.Step<K, V>) -> S.Observation<K, V>:
  C.Out{c, item, flag, evs} = step
  S.Observed{abstract(K, V, c), item, flag, evs}

def abstract_created(-K: Data, -V: Data, result: Result<&2, &2, String, C.Cache<K, V>>) -> Result<&2, &2, String, S.Model<K, V>>:
  match result:
    case Fail{err}:
      Fail{err}
    case Done{c}:
      Done{abstract(K, V, c)}

law initial_state_refines:
  for -K: Data
  for -V: Data
  for capacity: Nat
  {abstract(K, V, C.init(K, V, capacity)) == S.initial(K, V, capacity) : S.Model<K, V>}
def initial_state_refines(K, V, capacity):
  {==}

law creation_decision_refines:
  for -K: Data
  for -V: Data
  for capacity: Nat
  for valid: Bool
  {abstract_created(K, V, C.new_checked(K, V, capacity, valid)) == S.create_decision(K, V, capacity, valid) : Result<&2, &2, String, S.Model<K, V>>}
def creation_decision_refines(K, V, capacity, valid):
  match valid:
    case False{}:
      {==}
    case True{}:
      {==}

law construct_refines:
  for -K: Data
  for -V: Data
  for capacity: U32
  for size: U32
  for zero: Bool
  for reserved: Bool
  for small: Bool
  {abstract_created(K, V, C.construct(K, V, capacity, size, zero, reserved, small)) == S.construct(K, V, capacity, size, zero, reserved, small) : Result<&2, &2, String, S.Model<K, V>>}
def construct_refines(K, V, capacity, size, zero, reserved, small):
  match zero reserved small:
    case True{} a b:
      {==}
    case False{} True{} b:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

law new_with_size_refines:
  for -K: Data
  for -V: Data
  for +capacity: U32
  for +size: U32
  {abstract_created(K, V, C.new_with_size(K, V, capacity, size)) == S.new_with_size(K, V, capacity, size) : Result<&2, &2, String, S.Model<K, V>>}
def new_with_size_refines(K, V, capacity, size):
  construct_refines(K, V, capacity, size, U32.is_eq(capacity, 0), U32.is_eq(size, 4294967295), U32.is_lt(size, capacity))

law empty_get_refines:
  for -K: Data
  for -V: Data
  for encode: K -> String
  for cap: Nat
  for key: K
  for now: T.Int64
  {observe(K, V, C.get(K, V, encode, C.init(K, V, cap), key, now)) == S.missing_get(K, V, S.initial(K, V, cap)) : S.Observation<K, V>}
def empty_get_refines(K, V, encode, cap, key, now):
  {==}

law empty_remove_refines:
  for -K: Data
  for -V: Data
  for encode: K -> String
  for cap: Nat
  for key: K
  {observe(K, V, C.remove(K, V, encode, C.init(K, V, cap), key)) == S.missing_remove(K, V, S.initial(K, V, cap)) : S.Observation<K, V>}
def empty_remove_refines(K, V, encode, cap, key):
  {==}

# These are universal actual-operation refinements, for every state. They do
# not establish or assume preservation of the still-unproved map invariant.
law set_lifetime_refines:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for ns: T.Int64
  {abstract(K, V, C.set_lifetime(K, V, c, ns)) == S.set_lifetime(K, V, abstract(K, V, c), ns) : S.Model<K, V>}
def set_lifetime_refines(K, V, c, ns):
  match c:
    case C.State{cap, table, order, life, counts, cb}:
      {==}

def abstract_reset(-K: Data, -V: Data, result: C.Cache<K, V> & T.Metrics) -> S.Model<K, V> & T.Metrics:
  (c, previous) = result
  (abstract(K, V, c), previous)

law reset_metrics_refines:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  {abstract_reset(K, V, C.reset_metrics(K, V, c)) == S.reset_metrics(K, V, abstract(K, V, c)) : S.Model<K, V> & T.Metrics}
def reset_metrics_refines(K, V, c):
  match c:
    case C.State{cap, table, order, life, counts, cb}:
      {==}

law lookup_projection_bridge:
  for -K: Data
  for -V: Data
  for result: Map<&2, Maybe<&2, T.Entry<K, V>>> & Maybe<&2, T.Entry<K, V>>
  {C.lookup_result(K, V, result) == Insert.value(Maybe<&2, T.Entry<K, V>>, result) : Maybe<&2, T.Entry<K, V>>}
def lookup_projection_bridge(K, V, result):
  match result:
    case Tuple{table, found}:
      {==}

# Actual native-Map write is observable through the actual cache lookup.
# This is a same-key storage property, not other-key or full operation refinement.
law store_lookup:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for +code: String
  for +key: K
  for +value: V
  for +deadline: T.Int64
  for flag: Bool
  for events: List<&2, T.LruEvent<K, V>>
  {C.lookup(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events)), code) == Some{T.Item{key, value, deadline}} : Maybe<&2, T.Entry<K, V>>}
def store_lookup(K, V, c, code, key, value, deadline, flag, events):
  match c:
    case C.State{cap, +table, order, life, T.Counts{i, e, r, h, m}, cb}:
      %Equal.sym(Maybe<&2, T.Entry<K, V>>, C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, Map.set(&2, Maybe<&2, T.Entry<K, V>>, table, code, Some{T.Item{key, value, deadline}}), code)), Insert.lookup(Maybe<&2, T.Entry<K, V>>, None{}, Map.set(&2, Maybe<&2, T.Entry<K, V>>, table, code, Some{T.Item{key, value, deadline}}), code), lookup_projection_bridge(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, Map.set(&2, Maybe<&2, T.Entry<K, V>>, table, code, Some{T.Item{key, value, deadline}}), code))) : {_ == Some{T.Item{key, value, deadline}} : Maybe<&2, T.Entry<K, V>>}
      Insert.set_same(Maybe<&2, T.Entry<K, V>>, None{}, table, code, Some{T.Item{key, value, deadline}})

# Every successful actual cache lookup names a real exact binding in native
# storage enumeration. This direction holds even before valid-tree preservation
# is established; it does not claim that all enumerated bindings are findable.
law lookup_enumerated:
  for -K: Data
  for -V: Data
  for +capacity: Nat
  for +table: Map<&2, Maybe<&2, T.Entry<K, V>>>
  for +order: List<&2, String>
  for +lifetime: T.Int64
  for +counts: T.Metrics
  for +cb: Bool
  for +code: String
  for +entry: T.Entry<K, V>
  for found: {C.lookup(K, V, C.State{capacity, table, order, lifetime, counts, cb}, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}
  Lookup.listed(T.Entry<K, V>, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table), code, entry)
def lookup_enumerated(K, V, capacity, table, order, lifetime, counts, cb, code, entry, found):
  Lookup.returned_value_enumerated(T.Entry<K, V>, table, code, entry, Equal.trans(Maybe<&2, T.Entry<K, V>>, Insert.lookup(Maybe<&2, T.Entry<K, V>>, None{}, table, code), C.lookup(K, V, C.State{capacity, table, order, lifetime, counts, cb}, code), Some{entry}, Equal.sym(Maybe<&2, T.Entry<K, V>>, C.lookup(K, V, C.State{capacity, table, order, lifetime, counts, cb}, code), Insert.lookup(Maybe<&2, T.Entry<K, V>>, None{}, table, code), lookup_projection_bridge(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, code))), found))

# The actual core removal, not a disconnected model of native deletion.
law removed_key_absent:
  for -K: Data
  for -V: Data
  for capacity: Nat
  for +table: Map<&2, Maybe<&2, T.Entry<K, V>>>
  for order: List<&2, String>
  for lifetime: T.Int64
  for counts: T.Metrics
  for cb: Bool
  for +code: String
  for evict: Bool
  for entry: T.Entry<K, V>
  for invariant: {Invariants.critbit(Maybe<&2, T.Entry<K, V>>, table) == True{} : Bool}
  {C.lookup(K, V, C.step_cache(K, V, C.remove_present(K, V, C.State{capacity, table, order, lifetime, counts, cb}, code, evict, entry)), code) == None{} : Maybe<&2, T.Entry<K, V>>}
def removed_key_absent(K, V, capacity, table, order, lifetime, counts, cb, code, evict, entry, invariant):
  Equal.trans(Maybe<&2, T.Entry<K, V>>, C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, Map.del(&2, Maybe<&2, T.Entry<K, V>>, table, code), code)), Insert.lookup(Maybe<&2, T.Entry<K, V>>, None{}, Map.del(&2, Maybe<&2, T.Entry<K, V>>, table, code), code), None{}, lookup_projection_bridge(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, Map.del(&2, Maybe<&2, T.Entry<K, V>>, table, code), code)), Delete.critbit_delete_same(T.Entry<K, V>, table, code, invariant))

law cache_lookup_seeks_key:
  for -K: Data
  for -V: Data
  for +capacity: Nat
  for +table: Map<&2, Maybe<&2, T.Entry<K, V>>>
  for +order: List<&2, String>
  for +lifetime: T.Int64
  for +counts: T.Metrics
  for +cb: Bool
  for +code: String
  for +entry: T.Entry<K, V>
  for found: {C.lookup(K, V, C.State{capacity, table, order, lifetime, counts, cb}, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}
  {Insert.seek_found(Maybe<&2, T.Entry<K, V>>, Map.seek(&2, Maybe<&2, T.Entry<K, V>>, table, code)) == Some{code} : Maybe<&2, String>}
def cache_lookup_seeks_key(K, V, capacity, table, order, lifetime, counts, cb, code, entry, found):
  Seek.successful_lookup_seeks_key(T.Entry<K, V>, table, code, entry, Equal.trans(Maybe<&2, T.Entry<K, V>>, Insert.lookup(Maybe<&2, T.Entry<K, V>>, None{}, table, code), C.lookup(K, V, C.State{capacity, table, order, lifetime, counts, cb}, code), Some{entry}, Equal.sym(Maybe<&2, T.Entry<K, V>>, C.lookup(K, V, C.State{capacity, table, order, lifetime, counts, cb}, code), Insert.lookup(Maybe<&2, T.Entry<K, V>>, None{}, table, code), lookup_projection_bridge(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, code))), found))

# Native deletion preserves the lookup-routing invariant through actual removal.
# This conditional local fact is not full reachable representation preservation.
def lookup_routing(-K: Data, -V: Data, c: C.Cache<K, V>) -> Type:
  C.State{cap, table, order, life, counts, cb} = c
  Routes.valid(Maybe<&2, T.Entry<K, V>>, table)

law removal_preserves_lookup_routing:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for evict: Bool
  for entry: T.Entry<K, V>
  for invariant: lookup_routing(K, V, c)
  lookup_routing(K, V, C.step_cache(K, V, C.remove_present(K, V, c, code, evict, entry)))
def removal_preserves_lookup_routing(K, V, c, code, evict, entry, invariant):
  C.State{cap, table, order, life, counts, cb} = c
  DeleteRoutes.preserves_valid(Maybe<&2, T.Entry<K, V>>, table, code, invariant)

law removal_preserves_other_lookup:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +removed: String
  for +key: String
  for evict: Bool
  for entry: T.Entry<K, V>
  for invariant: lookup_routing(K, V, c)
  for distinct: DeleteFrame.different(key, removed)
  {C.lookup(K, V, C.step_cache(K, V, C.remove_present(K, V, c, removed, evict, entry)), key) == C.lookup(K, V, c, key) : Maybe<&2, T.Entry<K, V>>}
def removal_preserves_other_lookup(K, V, c, removed, key, evict, entry, invariant, distinct):
  C.State{cap, +table, order, life, counts, cb} = c
  Equal.trans(Maybe<&2, T.Entry<K, V>>, C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, Map.del(&2, Maybe<&2, T.Entry<K, V>>, table, removed), key)), Insert.lookup(Maybe<&2, T.Entry<K, V>>, None{}, Map.del(&2, Maybe<&2, T.Entry<K, V>>, table, removed), key), C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, key)), lookup_projection_bridge(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, Map.del(&2, Maybe<&2, T.Entry<K, V>>, table, removed), key)), Equal.trans(Maybe<&2, T.Entry<K, V>>, Insert.lookup(Maybe<&2, T.Entry<K, V>>, None{}, Map.del(&2, Maybe<&2, T.Entry<K, V>>, table, removed), key), Insert.lookup(Maybe<&2, T.Entry<K, V>>, None{}, table, key), C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, key)), DeleteFrame.other_lookup_unchanged(T.Entry<K, V>, table, removed, key, invariant, distinct), Equal.sym(Maybe<&2, T.Entry<K, V>>, C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, key)), Insert.lookup(Maybe<&2, T.Entry<K, V>>, None{}, table, key), lookup_projection_bridge(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, key)))))


# Full native storage predicate through the executed core removal. This does
# not assert the still-open recency/identity or reachable-state invariants.
def storage_critbit(-K: Data, -V: Data, c: C.Cache<K, V>) -> Bool:
  C.State{cap, table, order, life, counts, cb} = c
  Invariants.critbit(Maybe<&2, T.Entry<K, V>>, table)

law removal_preserves_storage_critbit:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for evict: Bool
  for entry: T.Entry<K, V>
  for invariant: {storage_critbit(K, V, c) == True{} : Bool}
  {storage_critbit(K, V, C.step_cache(K, V, C.remove_present(K, V, c, code, evict, entry))) == True{} : Bool}
def removal_preserves_storage_critbit(K, V, c, code, evict, entry, invariant):
  C.State{cap, table, order, life, counts, cb} = c
  DeleteCritbit.preserves_critbit(Maybe<&2, T.Entry<K, V>>, table, code, invariant)


law store_preserves_storage_critbit:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for key: K
  for value: V
  for deadline: T.Int64
  for flag: Bool
  for events: List<&2, T.LruEvent<K, V>>
  for invariant: {storage_critbit(K, V, c) == True{} : Bool}
  {storage_critbit(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events))) == True{} : Bool}
def store_preserves_storage_critbit(K, V, c, code, key, value, deadline, flag, events, invariant):
  C.State{cap, table, order, life, counts, cb} = c
  T.Counts{i, e, r, h, misses} = counts
  SetCritbit.preserves_critbit(Maybe<&2, T.Entry<K, V>>, table, code, Some{T.Item{key, value, deadline}}, invariant)

# The actual store preserves every other encoded-key lookup. Storage validity
# remains an input premise until full cache reachability is established.
law store_other_lookup:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for +key: K
  for +value: V
  for +deadline: T.Int64
  for flag: Bool
  for events: List<&2, T.LruEvent<K, V>>
  for +query: String
  for unequal: {String.eq(query, code) == False{} : Bool}
  for invariant: {storage_critbit(K, V, c) == True{} : Bool}
  {C.lookup(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events)), query) == C.lookup(K, V, c, query) : Maybe<&2, T.Entry<K, V>>}
def store_other_lookup(K, V, c, code, key, value, deadline, flag, events, query, unequal, invariant):
  match c:
    case C.State{cap, +table, order, life, T.Counts{i, e, r, h, m}, cb}:
      %Equal.sym(Maybe<&2, T.Entry<K, V>>, C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, Map.set(&2, Maybe<&2, T.Entry<K, V>>, table, code, Some{T.Item{key, value, deadline}}), query)), Insert.lookup(Maybe<&2, T.Entry<K, V>>, None{}, Map.set(&2, Maybe<&2, T.Entry<K, V>>, table, code, Some{T.Item{key, value, deadline}}), query), lookup_projection_bridge(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, Map.set(&2, Maybe<&2, T.Entry<K, V>>, table, code, Some{T.Item{key, value, deadline}}), query))) : {_ == C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, query)) : Maybe<&2, T.Entry<K, V>>}
      %Equal.sym(Maybe<&2, T.Entry<K, V>>, C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, query)), Insert.lookup(Maybe<&2, T.Entry<K, V>>, None{}, table, query), lookup_projection_bridge(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, query))) : {Insert.lookup(Maybe<&2, T.Entry<K, V>>, None{}, Map.set(&2, Maybe<&2, T.Entry<K, V>>, table, code, Some{T.Item{key, value, deadline}}), query) == _ : Maybe<&2, T.Entry<K, V>>}
      SetFrame.other_lookup_unchanged(T.Entry<K, V>, table, code, Some{T.Item{key, value, deadline}}, query, unequal, invariant)
