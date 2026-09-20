import Base
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../src/codec.bend as Codec
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./representation_parts.bend as Parts
import ./refresh_complete_representation.bend as Joint
import ./cache_delete_identities.bend as Identity
import ./cache_storage_preservation.bend as Storage
import ./map_populated_inverse.bend as Inverse
import ./map_delete_prefix.bend as And
import ./recency_unique.bend as Unique
import ./recency_bounds.bend as Bound
import ./cache_key_identity.bend as Key

def remove_present_parts(~K: Data, ~encode: K -> String, -V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, +code: String, +evict: Bool, +entry: T.Entry<K, V>, positive: {Nat.is_gt(cap, 0n) == True{} : Bool}, bounded: {Nat.is_le(List.length(&2, String, order), cap) == True{} : Bool}, unique: {Inv.unique(order) == True{} : Bool}, native_unique: {Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}, forward: {Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}, backward: {Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order) == True{} : Bool}, valid: {Inv.critbit(Maybe<&2, T.Entry<K, V>>, table) == True{} : Bool}, +identities: {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.remove_present(K, V, C.State{cap, table, order, life, counts, cb}, code, evict, entry))) == True{} : Bool}:
  input_storage = Storage.pack(K, V, C.State{cap, table, order, life, counts, cb}, valid, Inverse.packed_tree(K, V, table, Parts.identities_packed(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table), identities)), And.conjunction(Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order), forward, backward))
  Joint.assemble(~K, ~encode, V, C.step_cache(K, V, C.remove_present(K, V, C.State{cap, table, order, life, counts, cb}, code, evict, entry)), positive, Bound.le_transitive(List.length(&2, String, C.without(order, code)), List.length(&2, String, order), cap, Bound.without_bound(order, code), bounded), Unique.filtering_preserves_unique(order, code, unique), Storage.remove_present(K, V, C.State{cap, table, order, life, counts, cb}, code, evict, entry, input_storage), Identity.remove_present(~K, ~encode, V, C.State{cap, table, order, life, counts, cb}, code, evict, entry, identities))

def remove_present_unpack(~K: Data, ~encode: K -> String, -V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, +code: String, +evict: Bool, +entry: T.Entry<K, V>, facts: {Nat.is_gt(cap, 0n) == True{} : Bool} & {Nat.is_le(List.length(&2, String, order), cap) == True{} : Bool} & {Inv.unique(order) == True{} : Bool} & {Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order) == True{} : Bool} & {Inv.critbit(Maybe<&2, T.Entry<K, V>>, table) == True{} : Bool} & {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.remove_present(K, V, C.State{cap, table, order, life, counts, cb}, code, evict, entry))) == True{} : Bool}:
  (positive, bounded, unique, native_unique, forward, backward, valid, identities) = facts
  remove_present_parts(~K, ~encode, V, cap, table, order, life, counts, cb, code, evict, entry, positive, bounded, unique, native_unique, forward, backward, valid, identities)

def remove_present(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, code: String, evict: Bool, entry: T.Entry<K, V>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.remove_present(K, V, c, code, evict, entry))) == True{} : Bool}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  remove_present_unpack(~K, ~encode, V, cap, table, order, life, counts, cb, code, evict, entry, Parts.components(~K, ~encode, V, cap, table, order, life, counts, cb, invariant))

def detach_present_parts(~K: Data, ~encode: K -> String, -V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, +code: String, +entry: T.Entry<K, V>, positive: {Nat.is_gt(cap, 0n) == True{} : Bool}, bounded: {Nat.is_le(List.length(&2, String, order), cap) == True{} : Bool}, unique: {Inv.unique(order) == True{} : Bool}, native_unique: {Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}, forward: {Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}, backward: {Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order) == True{} : Bool}, valid: {Inv.critbit(Maybe<&2, T.Entry<K, V>>, table) == True{} : Bool}, +identities: {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, P.detach_present(K, V, C.State{cap, table, order, life, counts, cb}, code, entry))) == True{} : Bool}:
  input_storage = Storage.pack(K, V, C.State{cap, table, order, life, counts, cb}, valid, Inverse.packed_tree(K, V, table, Parts.identities_packed(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table), identities)), And.conjunction(Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order), forward, backward))
  Joint.assemble(~K, ~encode, V, C.step_cache(K, V, P.detach_present(K, V, C.State{cap, table, order, life, counts, cb}, code, entry)), positive, Bound.le_transitive(List.length(&2, String, C.without(order, code)), List.length(&2, String, order), cap, Bound.without_bound(order, code), bounded), Unique.filtering_preserves_unique(order, code, unique), Storage.protocol_detach_present(K, V, C.State{cap, table, order, life, counts, cb}, code, entry, input_storage), Identity.detach_present(~K, ~encode, V, C.State{cap, table, order, life, counts, cb}, code, entry, identities))

def detach_present_unpack(~K: Data, ~encode: K -> String, -V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, +code: String, +entry: T.Entry<K, V>, facts: {Nat.is_gt(cap, 0n) == True{} : Bool} & {Nat.is_le(List.length(&2, String, order), cap) == True{} : Bool} & {Inv.unique(order) == True{} : Bool} & {Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order) == True{} : Bool} & {Inv.critbit(Maybe<&2, T.Entry<K, V>>, table) == True{} : Bool} & {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, P.detach_present(K, V, C.State{cap, table, order, life, counts, cb}, code, entry))) == True{} : Bool}:
  (positive, bounded, unique, native_unique, forward, backward, valid, identities) = facts
  detach_present_parts(~K, ~encode, V, cap, table, order, life, counts, cb, code, entry, positive, bounded, unique, native_unique, forward, backward, valid, identities)

def detach_present(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, code: String, entry: T.Entry<K, V>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, P.detach_present(K, V, c, code, entry))) == True{} : Bool}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  detach_present_unpack(~K, ~encode, V, cap, table, order, life, counts, cb, code, entry, Parts.components(~K, ~encode, V, cap, table, order, life, counts, cb, invariant))

def remove_found(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, code: String, evict: Bool, found: Maybe<&2, T.Entry<K, V>>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.remove_found(K, V, c, code, evict, found))) == True{} : Bool}:
  match found:
    case None{}: invariant
    case Some{entry}: remove_present(~K, ~encode, V, c, code, evict, entry, invariant)

def detach_found(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, code: String, found: Maybe<&2, T.Entry<K, V>>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, P.detach_found(K, V, c, code, found))) == True{} : Bool}:
  match found:
    case None{}: invariant
    case Some{entry}: detach_present(~K, ~encode, V, c, code, entry, invariant)

def remove_encoded(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, evict: Bool, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.remove_encoded(K, V, c, code, evict))) == True{} : Bool}:
  remove_found(~K, ~encode, V, c, code, evict, C.lookup(K, V, c, code), invariant)

def detach(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, P.detach(K, V, c, code))) == True{} : Bool}:
  detach_found(~K, ~encode, V, c, code, C.lookup(K, V, c, code), invariant)

def oldest_remove(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, order: List<&2, String>, evict: Bool, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.oldest_remove(K, V, c, order, evict))) == True{} : Bool}:
  match order:
    case Nil{}: invariant
    case Con{code, rest}: remove_encoded(~K, ~encode, V, c, code, evict, invariant)

def detach_first(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, order: List<&2, String>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, P.detach_first(K, V, c, order))) == True{} : Bool}:
  match order:
    case Nil{}: invariant
    case Con{code, rest}: detach(~K, ~encode, V, c, code, invariant)

def remove_oldest(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, evict: Bool, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.remove_oldest(K, V, c, evict))) == True{} : Bool}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  oldest_remove(~K, ~encode, V, C.State{cap, table, order, life, counts, cb}, order, evict, invariant)

def detach_oldest(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, P.detach_oldest(K, V, c))) == True{} : Bool}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  detach_first(~K, ~encode, V, C.State{cap, table, order, life, counts, cb}, order, invariant)

def string_remove_oldest(-V: Data, c: C.Cache<String, V>, evict: Bool, invariant: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {Inv.representation(~String, ~Codec.string_encode, V, C.step_cache(String, V, C.remove_oldest(String, V, c, evict))) == True{} : Bool}:
  remove_oldest(~String, ~Codec.string_encode, V, c, evict, invariant)

def string_detach_oldest(-V: Data, c: C.Cache<String, V>, invariant: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {Inv.representation(~String, ~Codec.string_encode, V, C.step_cache(String, V, P.detach_oldest(String, V, c))) == True{} : Bool}:
  detach_oldest(~String, ~Codec.string_encode, V, c, invariant)

def integer_remove_oldest(-V: Data, c: C.Cache<T.Integer, V>, evict: Bool, invariant: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}) -> {Inv.representation(~T.Integer, ~Codec.integer_encode, V, C.step_cache(T.Integer, V, C.remove_oldest(T.Integer, V, c, evict))) == True{} : Bool}:
  remove_oldest(~T.Integer, ~Codec.integer_encode, V, c, evict, invariant)

def integer_detach_oldest(-V: Data, c: C.Cache<T.Integer, V>, invariant: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}) -> {Inv.representation(~T.Integer, ~Codec.integer_encode, V, C.step_cache(T.Integer, V, P.detach_oldest(T.Integer, V, c))) == True{} : Bool}:
  detach_oldest(~T.Integer, ~Codec.integer_encode, V, c, invariant)

def word64_remove_oldest(-V: Data, c: C.Cache<Word(64n), V>, evict: Bool, invariant: {Inv.representation(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}) -> {Inv.representation(~Word(64n), ~Key.word64_encode, V, C.step_cache(Word(64n), V, C.remove_oldest(Word(64n), V, c, evict))) == True{} : Bool}:
  remove_oldest(~Word(64n), ~Key.word64_encode, V, c, evict, invariant)

def word64_detach_oldest(-V: Data, c: C.Cache<Word(64n), V>, invariant: {Inv.representation(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}) -> {Inv.representation(~Word(64n), ~Key.word64_encode, V, C.step_cache(Word(64n), V, P.detach_oldest(Word(64n), V, c))) == True{} : Bool}:
  detach_oldest(~Word(64n), ~Key.word64_encode, V, c, invariant)

