import Base
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../src/time.bend as Time
import ../src/codec.bend as Codec
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./refinement.bend as F
import ./refresh_complete_representation.bend as Refresh
import ./read_representation.bend as Read
import ./configuration_representation.bend as Config
import ./cache_key_identity.bend as Key

# Lookup after the actual deadline update; this uses the native Map.set law.
def updated_lookup(-K: Data, -V: Data, c: C.Cache<K, V>, +code: String, +key: K, +value: V, old: T.Int64, +ns: T.Int64, +now: T.Int64) -> {C.lookup(K, V, P.refresh_at(K, V, c, code, T.Item{key, value, old}, ns, now), code) == Some{T.Item{key, value, Time.deadline(now, ns)}} : Maybe<&2, T.Entry<K, V>>}:
  C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb} = c
  F.store_lookup(K, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, code, key, value, Time.deadline(now, ns), False{}, Nil{})

def present(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, +key: K, +value: V, +old: T.Int64, +ns: T.Int64, +now: T.Int64, decision: {C.lookup(K, V, c, code) == Some{T.Item{key, value, old}} : Maybe<&2, T.Entry<K, V>>}, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.refresh_present(K, V, c, code, T.Item{key, value, Time.deadline(now, ns)}))) == True{} : Bool}:
  C.State{cap, table, order, life, counts, cb} = c
  Read.live(~K, ~encode, V, P.refresh_at(K, V, C.State{cap, table, order, life, counts, cb}, code, T.Item{key, value, old}, ns, now), code, T.Item{key, value, Time.deadline(now, ns)}, True{}, updated_lookup(K, V, C.State{cap, table, order, life, counts, cb}, code, key, value, old, ns, now), Refresh.at(~K, ~encode, V, C.State{cap, table, order, life, counts, cb}, code, T.Item{key, value, old}, ns, now, decision, invariant))

def found(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, code: String, ns: T.Int64, now: T.Int64, result: Maybe<&2, T.Entry<K, V>>, decision: {C.lookup(K, V, c, code) == result : Maybe<&2, T.Entry<K, V>>}, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.refresh_found(K, V, c, code, Time.deadline(now, ns), result))) == True{} : Bool}:
  match result:
    case None{}: Config.counted(~K, ~encode, V, C.Out{c, None{}, False{}, Nil{}}, True{}, False{}, invariant)
    case Some{T.Item{key, value, old}}: present(~K, ~encode, V, c, code, key, value, old, ns, now, decision, invariant)

def get_and_refresh(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +key: K, ns: T.Int64, now: T.Int64, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.get_and_refresh(K, V, encode, c, key, ns, now))) == True{} : Bool}:
  found(~K, ~encode, V, c, encode(key), ns, now, C.lookup(K, V, c, encode(key)), {==}, invariant)

def string_refresh(-V: Data, c: C.Cache<String, V>, key: String, ns: T.Int64, now: T.Int64, invariant: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {Inv.representation(~String, ~Codec.string_encode, V, C.step_cache(String, V, C.get_and_refresh(String, V, Codec.string_encode, c, key, ns, now))) == True{} : Bool}:
  get_and_refresh(~String, ~Codec.string_encode, V, c, key, ns, now, invariant)

def integer_refresh(-V: Data, c: C.Cache<T.Integer, V>, key: T.Integer, ns: T.Int64, now: T.Int64, invariant: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}) -> {Inv.representation(~T.Integer, ~Codec.integer_encode, V, C.step_cache(T.Integer, V, C.get_and_refresh(T.Integer, V, Codec.integer_encode, c, key, ns, now))) == True{} : Bool}:
  get_and_refresh(~T.Integer, ~Codec.integer_encode, V, c, key, ns, now, invariant)

def word64_refresh(-V: Data, c: C.Cache<Word(64n), V>, key: Word(64n), ns: T.Int64, now: T.Int64, invariant: {Inv.representation(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}) -> {Inv.representation(~Word(64n), ~Key.word64_encode, V, C.step_cache(Word(64n), V, C.get_and_refresh(Word(64n), V, Key.word64_encode, c, key, ns, now))) == True{} : Bool}:
  get_and_refresh(~Word(64n), ~Key.word64_encode, V, c, key, ns, now, invariant)
