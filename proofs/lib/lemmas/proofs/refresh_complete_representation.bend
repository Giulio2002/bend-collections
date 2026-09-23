import Base
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../src/codec.bend as Codec
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./representation_parts.bend as Parts
import ./refresh_representation.bend as Rep
import ./cache_refresh_identity.bend as Identity
import ./abstraction_recency.bend as Recency
import ./cache_storage_preservation.bend as Storage
import ./map_populated_inverse.bend as Inverse
import ./map_delete_prefix.bend as And
import ./map_routing.bend as R
import ./recency_unique.bend as Unique
import ./cache_key_identity.bend as Key
import ./refresh_lookup.bend as Lookup

def assemble(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, positive: {Nat.is_gt(C.capacity(K, V, c), 0n) == True{} : Bool}, bounded: {Nat.is_le(C.len(K, V, c), C.capacity(K, V, c)) == True{} : Bool}, unique: {Unique.unique_recency(K, V, c) == True{} : Bool}, +storage: {Storage.storage(K, V, c) == True{} : Bool}, identities: {Recency.cache_identities(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, c) == True{} : Bool}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  +membership = Storage.membership(K, V, C.State{cap, table, order, life, counts, cb}, storage)
  Rep.pack(~K, ~encode, V, cap, table, order, life, counts, cb, positive, bounded, unique, Storage.storage_has_unique_keys(K, V, C.State{cap, table, order, life, counts, cb}, storage), R.and_left(Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order), membership), R.and_right(Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order), membership), Storage.valid(K, V, C.State{cap, table, order, life, counts, cb}, storage), identities)

def at_entry(~K: Data, ~encode: K -> String, -V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, +code: String, entry: T.Entry<K, V>, +lifetime: T.Int64, +now: T.Int64, +found: {C.lookup(K, V, C.State{cap, table, order, life, counts, cb}, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}, positive: {Nat.is_gt(cap, 0n) == True{} : Bool}, bounded: {Nat.is_le(List.length(&2, String, order), cap) == True{} : Bool}, unique: {Inv.unique(order) == True{} : Bool}, valid: {Inv.critbit(Maybe<&2, T.Entry<K, V>>, table) == True{} : Bool}, identities: {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}, storage: {Storage.storage(K, V, C.State{cap, table, order, life, counts, cb}) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, P.refresh_at(K, V, C.State{cap, table, order, life, counts, cb}, code, entry, lifetime, now)) == True{} : Bool}:
  T.Item{+key, +value, +deadline} = entry
  assemble(~K, ~encode, V, P.refresh_at(K, V, C.State{cap, table, order, life, counts, cb}, code, T.Item{key, value, deadline}, lifetime, now), positive, bounded, unique, Storage.refresh_at(K, V, C.State{cap, table, order, life, counts, cb}, code, T.Item{key, value, deadline}, lifetime, now, storage, found), Identity.refresh_at(~K, ~encode, V, C.State{cap, table, order, life, counts, cb}, code, T.Item{key, value, deadline}, lifetime, now, valid, identities, found))

def from_components(~K: Data, ~encode: K -> String, -V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, +code: String, +entry: T.Entry<K, V>, +lifetime: T.Int64, +now: T.Int64, +found: {C.lookup(K, V, C.State{cap, table, order, life, counts, cb}, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}, positive: {Nat.is_gt(cap, 0n) == True{} : Bool}, bounded: {Nat.is_le(List.length(&2, String, order), cap) == True{} : Bool}, unique: {Inv.unique(order) == True{} : Bool}, native_unique: {Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}, forward: {Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}, backward: {Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order) == True{} : Bool}, +valid: {Inv.critbit(Maybe<&2, T.Entry<K, V>>, table) == True{} : Bool}, +identities: {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, P.refresh_at(K, V, C.State{cap, table, order, life, counts, cb}, code, entry, lifetime, now)) == True{} : Bool}:
  input_storage = Storage.pack(K, V, C.State{cap, table, order, life, counts, cb}, valid, Inverse.packed_tree(K, V, table, Parts.identities_packed(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table), identities)), And.conjunction(Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order), forward, backward))
  at_entry(~K, ~encode, V, cap, table, order, life, counts, cb, code, entry, lifetime, now, found, positive, bounded, unique, valid, identities, input_storage)

def at_parts(~K: Data, ~encode: K -> String, -V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, +code: String, +entry: T.Entry<K, V>, +lifetime: T.Int64, +now: T.Int64, +found: {C.lookup(K, V, C.State{cap, table, order, life, counts, cb}, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}, facts: {Nat.is_gt(cap, 0n) == True{} : Bool} & {Nat.is_le(List.length(&2, String, order), cap) == True{} : Bool} & {Inv.unique(order) == True{} : Bool} & {Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order) == True{} : Bool} & {Inv.critbit(Maybe<&2, T.Entry<K, V>>, table) == True{} : Bool} & {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, P.refresh_at(K, V, C.State{cap, table, order, life, counts, cb}, code, entry, lifetime, now)) == True{} : Bool}:
  (positive, bounded, unique, native_unique, forward, backward, valid, identities) = facts
  from_components(~K, ~encode, V, cap, table, order, life, counts, cb, code, entry, lifetime, now, found, positive, bounded, unique, native_unique, forward, backward, valid, identities)

def at(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, code: String, entry: T.Entry<K, V>, lifetime: T.Int64, now: T.Int64, found: {C.lookup(K, V, c, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, P.refresh_at(K, V, c, code, entry, lifetime, now)) == True{} : Bool}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  at_parts(~K, ~encode, V, cap, table, order, life, counts, cb, code, entry, lifetime, now, found, Parts.components(~K, ~encode, V, cap, table, order, life, counts, cb, invariant))

def complete(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, +entry: T.Entry<K, V>, lifetime: T.Int64, now: T.Int64, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}, returned: {Lookup.item(K, V, P.refresh_prepare(K, V, c, code)) == Some{entry} : Maybe<&2, T.Entry<K, V>>}) -> {Inv.representation(~K, ~encode, V, P.refresh_at(K, V, C.step_cache(K, V, P.refresh_prepare(K, V, c, code)), code, entry, lifetime, now)) == True{} : Bool}:
  at(~K, ~encode, V, C.step_cache(K, V, P.refresh_prepare(K, V, c, code)), code, entry, lifetime, now, Lookup.successful_prepare(K, V, c, code, entry, returned), Rep.prepare(~K, ~encode, V, c, code, invariant))

def string_complete(-V: Data, c: C.Cache<String, V>, code: String, entry: T.Entry<String, V>, lifetime: T.Int64, now: T.Int64, invariant: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, returned: {Lookup.item(String, V, P.refresh_prepare(String, V, c, code)) == Some{entry} : Maybe<&2, T.Entry<String, V>>}) -> {Inv.representation(~String, ~Codec.string_encode, V, P.refresh_at(String, V, C.step_cache(String, V, P.refresh_prepare(String, V, c, code)), code, entry, lifetime, now)) == True{} : Bool}:
  complete(~String, ~Codec.string_encode, V, c, code, entry, lifetime, now, invariant, returned)

def integer_complete(-V: Data, c: C.Cache<T.Integer, V>, code: String, entry: T.Entry<T.Integer, V>, lifetime: T.Int64, now: T.Int64, invariant: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}, returned: {Lookup.item(T.Integer, V, P.refresh_prepare(T.Integer, V, c, code)) == Some{entry} : Maybe<&2, T.Entry<T.Integer, V>>}) -> {Inv.representation(~T.Integer, ~Codec.integer_encode, V, P.refresh_at(T.Integer, V, C.step_cache(T.Integer, V, P.refresh_prepare(T.Integer, V, c, code)), code, entry, lifetime, now)) == True{} : Bool}:
  complete(~T.Integer, ~Codec.integer_encode, V, c, code, entry, lifetime, now, invariant, returned)

def word64_complete(-V: Data, c: C.Cache<Word(64n), V>, code: String, entry: T.Entry<Word(64n), V>, lifetime: T.Int64, now: T.Int64, invariant: {Inv.representation(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}, returned: {Lookup.item(Word(64n), V, P.refresh_prepare(Word(64n), V, c, code)) == Some{entry} : Maybe<&2, T.Entry<Word(64n), V>>}) -> {Inv.representation(~Word(64n), ~Key.word64_encode, V, P.refresh_at(Word(64n), V, C.step_cache(Word(64n), V, P.refresh_prepare(Word(64n), V, c, code)), code, entry, lifetime, now)) == True{} : Bool}:
  complete(~Word(64n), ~Key.word64_encode, V, c, code, entry, lifetime, now, invariant, returned)

