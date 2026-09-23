import Base
import ../src/cache.bend as C
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./representation_parts.bend as Parts
import ./recency_unique.bend as Unique
import ./abstraction_recency.bend as Identity
import ./cache_storage_preservation.bend as Storage
import ./map_populated_inverse.bend as Inverse
import ./map_delete_prefix.bend as And

def positive_parts(~K: Data, ~encode: K -> String, -V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, facts: {Nat.is_gt(cap, 0n) == True{} : Bool} & {Nat.is_le(List.length(&2, String, order), cap) == True{} : Bool} & {Inv.unique(order) == True{} : Bool} & {Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order) == True{} : Bool} & {Inv.critbit(Maybe<&2, T.Entry<K, V>>, table) == True{} : Bool} & {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}) -> {Nat.is_gt(cap, 0n) == True{} : Bool}:
  (positive, bounded, unique, native_unique, forward, backward, valid, identities) = facts
  positive

def get_positive(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Nat.is_gt(C.capacity(K, V, c), 0n) == True{} : Bool}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  positive_parts(~K, ~encode, V, cap, table, order, life, counts, cb, Parts.components(~K, ~encode, V, cap, table, order, life, counts, cb, invariant))

def bounded_parts(~K: Data, ~encode: K -> String, -V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, facts: {Nat.is_gt(cap, 0n) == True{} : Bool} & {Nat.is_le(List.length(&2, String, order), cap) == True{} : Bool} & {Inv.unique(order) == True{} : Bool} & {Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order) == True{} : Bool} & {Inv.critbit(Maybe<&2, T.Entry<K, V>>, table) == True{} : Bool} & {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}) -> {Nat.is_le(List.length(&2, String, order), cap) == True{} : Bool}:
  (positive, bounded, unique, native_unique, forward, backward, valid, identities) = facts
  bounded

def get_bounded(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Nat.is_le(C.len(K, V, c), C.capacity(K, V, c)) == True{} : Bool}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  bounded_parts(~K, ~encode, V, cap, table, order, life, counts, cb, Parts.components(~K, ~encode, V, cap, table, order, life, counts, cb, invariant))

def unique_parts(~K: Data, ~encode: K -> String, -V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, facts: {Nat.is_gt(cap, 0n) == True{} : Bool} & {Nat.is_le(List.length(&2, String, order), cap) == True{} : Bool} & {Inv.unique(order) == True{} : Bool} & {Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order) == True{} : Bool} & {Inv.critbit(Maybe<&2, T.Entry<K, V>>, table) == True{} : Bool} & {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}) -> {Inv.unique(order) == True{} : Bool}:
  (positive, bounded, unique, native_unique, forward, backward, valid, identities) = facts
  unique

def get_unique(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Unique.unique_recency(K, V, c) == True{} : Bool}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  unique_parts(~K, ~encode, V, cap, table, order, life, counts, cb, Parts.components(~K, ~encode, V, cap, table, order, life, counts, cb, invariant))

def identities_parts(~K: Data, ~encode: K -> String, -V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, facts: {Nat.is_gt(cap, 0n) == True{} : Bool} & {Nat.is_le(List.length(&2, String, order), cap) == True{} : Bool} & {Inv.unique(order) == True{} : Bool} & {Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order) == True{} : Bool} & {Inv.critbit(Maybe<&2, T.Entry<K, V>>, table) == True{} : Bool} & {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}) -> {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}:
  (positive, bounded, unique, native_unique, forward, backward, valid, identities) = facts
  identities

def get_identities(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Identity.cache_identities(~K, ~encode, V, c) == True{} : Bool}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  identities_parts(~K, ~encode, V, cap, table, order, life, counts, cb, Parts.components(~K, ~encode, V, cap, table, order, life, counts, cb, invariant))

def storage_parts(~K: Data, ~encode: K -> String, -V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, facts: {Nat.is_gt(cap, 0n) == True{} : Bool} & {Nat.is_le(List.length(&2, String, order), cap) == True{} : Bool} & {Inv.unique(order) == True{} : Bool} & {Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order) == True{} : Bool} & {Inv.critbit(Maybe<&2, T.Entry<K, V>>, table) == True{} : Bool} & {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}) -> {Storage.storage(K, V, C.State{cap, table, order, life, counts, cb}) == True{} : Bool}:
  (positive, bounded, unique, native_unique, forward, backward, valid, identities) = facts
  Storage.pack(K, V, C.State{cap, table, order, life, counts, cb}, valid, Inverse.packed_tree(K, V, table, Parts.identities_packed(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table), identities)), And.conjunction(Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order), forward, backward))

def get_storage(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Storage.storage(K, V, c) == True{} : Bool}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  storage_parts(~K, ~encode, V, cap, table, order, life, counts, cb, Parts.components(~K, ~encode, V, cap, table, order, life, counts, cb, invariant))
