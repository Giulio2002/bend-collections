import Base
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../src/codec.bend as Codec
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./representation_parts.bend as Parts
import ./map_delete_prefix.bend as And
import ./cache_order.bend as Order
import ./recency_move_inclusion.bend as Move
import ./recency_unique.bend as Unique
import ./recency_bounds.bend as Bound
import ./cache_key_identity.bend as Key
import ./map_key_membership.bend as Keys

def pack(~K: Data, ~encode: K -> String, -V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, positive: {Nat.is_gt(cap, 0n) == True{} : Bool}, bounded: {Nat.is_le(List.length(&2, String, order), cap) == True{} : Bool}, unique: {Inv.unique(order) == True{} : Bool}, native_unique: {Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}, forward: {Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}, backward: {Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order) == True{} : Bool}, valid: {Inv.critbit(Maybe<&2, T.Entry<K, V>>, table) == True{} : Bool}, identity: {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.State{cap, table, order, life, counts, cb}) == True{} : Bool}:
  And.conjunction(Nat.is_gt(cap, 0n) && Nat.is_le(List.length(&2, String, order), cap) && Inv.unique(order) && Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) && Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) && Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, table), Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)), And.conjunction(Nat.is_gt(cap, 0n) && Nat.is_le(List.length(&2, String, order), cap) && Inv.unique(order) && Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) && Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) && Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order), Inv.critbit(Maybe<&2, T.Entry<K, V>>, table), And.conjunction(Nat.is_gt(cap, 0n) && Nat.is_le(List.length(&2, String, order), cap) && Inv.unique(order) && Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) && Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order), And.conjunction(Nat.is_gt(cap, 0n) && Nat.is_le(List.length(&2, String, order), cap) && Inv.unique(order) && Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), And.conjunction(Nat.is_gt(cap, 0n) && Nat.is_le(List.length(&2, String, order), cap) && Inv.unique(order), Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), And.conjunction(Nat.is_gt(cap, 0n) && Nat.is_le(List.length(&2, String, order), cap), Inv.unique(order), And.conjunction(Nat.is_gt(cap, 0n), Nat.is_le(List.length(&2, String, order), cap), positive, bounded), unique), native_unique), forward), backward), valid), identity)

def live_parts(~K: Data, ~encode: K -> String, -V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, +code: String, +entry: T.Entry<K, V>, +found: {C.lookup(K, V, C.State{cap, table, order, life, counts, cb}, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}, facts: {Nat.is_gt(cap, 0n) == True{} : Bool} & {Nat.is_le(List.length(&2, String, order), cap) == True{} : Bool} & {Inv.unique(order) == True{} : Bool} & {Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order) == True{} : Bool} & {Inv.critbit(Maybe<&2, T.Entry<K, V>>, table) == True{} : Bool} & {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.read_live(K, V, C.State{cap, table, order, life, counts, cb}, code, entry, True{}))) == True{} : Bool}:
  (positive, bounded, unique, native_unique, +forward, +backward, valid, identity) = facts
  +ordered = Order.lookup_is_ordered(K, V, C.State{cap, table, order, life, counts, cb}, code, entry, backward, found)
  pack(~K, ~encode, V, cap, table, Move.moved(order, code), life, C.hit_counts(counts, True{}, True{}), cb, positive,
    Bound.le_transitive(List.length(&2, String, Move.moved(order, code)), List.length(&2, String, order), cap, Order.live_read_does_not_grow(K, V, C.State{cap, table, order, life, counts, cb}, code, entry, True{}, backward, found), bounded),
    Unique.move_preserves_unique(order, code, unique), native_unique, Move.forward(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), code, forward, Keys.included_member(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), code, forward, ordered)), Move.backward(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order, code, backward), valid, identity)

def live(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, code: String, entry: T.Entry<K, V>, found: {C.lookup(K, V, c, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.read_live(K, V, c, code, entry, True{}))) == True{} : Bool}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  live_parts(~K, ~encode, V, cap, table, order, life, counts, cb, code, entry, found, Parts.components(~K, ~encode, V, cap, table, order, life, counts, cb, invariant))

def miss(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, P.finish_miss(K, V, c, True{})) == True{} : Bool}:
  C.State{cap, table, order, life, counts, cb} = c
  invariant

def found(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, result: Maybe<&2, T.Entry<K, V>>, decision: {C.lookup(K, V, c, code) == result : Maybe<&2, T.Entry<K, V>>}, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, P.refresh_prepare_found(K, V, c, code, result))) == True{} : Bool}:
  match result:
    case None{}: miss(~K, ~encode, V, c, invariant)
    case Some{entry}: live(~K, ~encode, V, c, code, entry, decision, invariant)

def prepare(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, P.refresh_prepare(K, V, c, code))) == True{} : Bool}:
  found(~K, ~encode, V, c, code, C.lookup(K, V, c, code), {==}, invariant)

law string_prepare:
  for -V: Data
  for c: C.Cache<String, V>
  for code: String
  for invariant: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}
  {Inv.representation(~String, ~Codec.string_encode, V, C.step_cache(String, V, P.refresh_prepare(String, V, c, code))) == True{} : Bool}
def string_prepare(V, c, code, invariant):
  prepare(~String, ~Codec.string_encode, V, c, code, invariant)

law integer_prepare:
  for -V: Data
  for c: C.Cache<T.Integer, V>
  for code: String
  for invariant: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}
  {Inv.representation(~T.Integer, ~Codec.integer_encode, V, C.step_cache(T.Integer, V, P.refresh_prepare(T.Integer, V, c, code))) == True{} : Bool}
def integer_prepare(V, c, code, invariant):
  prepare(~T.Integer, ~Codec.integer_encode, V, c, code, invariant)

law word64_prepare:
  for -V: Data
  for c: C.Cache<Word(64n), V>
  for code: String
  for invariant: {Inv.representation(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}
  {Inv.representation(~Word(64n), ~Key.word64_encode, V, C.step_cache(Word(64n), V, P.refresh_prepare(Word(64n), V, c, code))) == True{} : Bool}
def word64_prepare(V, c, code, invariant):
  prepare(~Word(64n), ~Key.word64_encode, V, c, code, invariant)

