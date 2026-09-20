import Base
import ../src/cache.bend as C
import ../src/time.bend as Time
import ../src/codec.bend as Codec
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./representation_access.bend as Access
import ./representation_parts.bend as Parts
import ./store_representation.bend as Store
import ./removal_representation.bend as Remove
import ./capacity_preservation.bend as Capacity
import ./cache_key_identity.bend as Key

def after_evict(~K: Data, ~encode: K -> String, -V: Data, +code: String, key: K, value: V, deadline: T.Int64, result: C.Step<K, V>, invariant: {Inv.representation(~K, ~encode, V, C.step_cache(K, V, result)) == True{} : Bool}, fresh: {code == encode(key) : String}, bounded: {Nat.is_le(C.len(K, V, C.step_cache(K, V, C.store_after_evict(K, V, code, key, value, deadline, result))), C.capacity(K, V, C.step_cache(K, V, result))) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.store_after_evict(K, V, code, key, value, deadline, result))) == True{} : Bool}:
  C.Out{c, item, flag, events} = result
  Store.store(~K, ~encode, V, c, code, key, value, deadline, flag, events, invariant, fresh, bounded)

def room(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, +key: K, +value: V, +deadline: T.Int64, full: Bool, +invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}, fresh: {code == encode(key) : String}, bounded: {Nat.is_le(C.len(K, V, C.step_cache(K, V, C.add_room(K, V, c, code, key, value, deadline, full))), C.capacity(K, V, c)) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.add_room(K, V, c, code, key, value, deadline, full))) == True{} : Bool}:
  match full:
    case False{}: Store.store(~K, ~encode, V, c, code, key, value, deadline, False{}, Nil{}, invariant, fresh, bounded)
    case True{}:
      after_evict(~K, ~encode, V, code, key, value, deadline, C.remove_oldest(K, V, c, True{}), Remove.remove_oldest(~K, ~encode, V, c, True{}, invariant), fresh, %Equal.sym(Nat, C.capacity(K, V, C.step_cache(K, V, C.remove_oldest(K, V, c, True{}))), C.capacity(K, V, c), Capacity.remove_oldest(K, V, c, True{})) : {Nat.is_le(C.len(K, V, C.step_cache(K, V, C.store_after_evict(K, V, code, key, value, deadline, C.remove_oldest(K, V, c, True{})))), _) == True{} : Bool} bounded)

def found(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, +key: K, +value: V, +deadline: T.Int64, result: Maybe<&2, T.Entry<K, V>>, decision: {C.lookup(K, V, c, code) == result : Maybe<&2, T.Entry<K, V>>}, +invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}, fresh: {code == encode(key) : String}, bounded: {Nat.is_le(C.len(K, V, C.step_cache(K, V, C.add_found(K, V, c, code, key, value, deadline, result))), C.capacity(K, V, c)) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.add_found(K, V, c, code, key, value, deadline, result))) == True{} : Bool}:
  match result:
    case None{}: room(~K, ~encode, V, c, code, key, value, deadline, Nat.is_ge(C.len(K, V, c), C.capacity(K, V, c)), invariant, fresh, bounded)
    case Some{T.Item{+original, +old, +expiry}}:
      Store.store(~K, ~encode, V, c, code, original, value, deadline, False{}, Nil{}, invariant, Key.lookup_code_identity(~K, ~encode, V, c, code, T.Item{original, old, expiry}, Access.get_identities(~K, ~encode, V, c, invariant), decision), bounded)

def add_with_lifetime(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +key: K, +value: V, +ns: T.Int64, +now: T.Int64, +invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.add_with_lifetime(K, V, encode, c, key, value, ns, now))) == True{} : Bool}:
  found(~K, ~encode, V, c, encode(key), key, value, Time.deadline(now, ns), C.lookup(K, V, c, encode(key)), {==}, invariant, {==}, Parts.add_bounded(~K, ~encode, V, c, key, value, ns, now, invariant))

def add(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, key: K, value: V, now: T.Int64, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.add(K, V, encode, c, key, value, now))) == True{} : Bool}:
  C.State{cap, table, order, +life, counts, cb} = c
  add_with_lifetime(~K, ~encode, V, C.State{cap, table, order, life, counts, cb}, key, value, life, now, invariant)

def string_add(-V: Data, c: C.Cache<String, V>, key: String, value: V, now: T.Int64, invariant: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {Inv.representation(~String, ~Codec.string_encode, V, C.step_cache(String, V, C.add(String, V, Codec.string_encode, c, key, value, now))) == True{} : Bool}:
  add(~String, ~Codec.string_encode, V, c, key, value, now, invariant)

def string_add_with_lifetime(-V: Data, c: C.Cache<String, V>, key: String, value: V, ns: T.Int64, now: T.Int64, invariant: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {Inv.representation(~String, ~Codec.string_encode, V, C.step_cache(String, V, C.add_with_lifetime(String, V, Codec.string_encode, c, key, value, ns, now))) == True{} : Bool}:
  add_with_lifetime(~String, ~Codec.string_encode, V, c, key, value, ns, now, invariant)

def integer_add(-V: Data, c: C.Cache<T.Integer, V>, key: T.Integer, value: V, now: T.Int64, invariant: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}) -> {Inv.representation(~T.Integer, ~Codec.integer_encode, V, C.step_cache(T.Integer, V, C.add(T.Integer, V, Codec.integer_encode, c, key, value, now))) == True{} : Bool}:
  add(~T.Integer, ~Codec.integer_encode, V, c, key, value, now, invariant)

def integer_add_with_lifetime(-V: Data, c: C.Cache<T.Integer, V>, key: T.Integer, value: V, ns: T.Int64, now: T.Int64, invariant: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}) -> {Inv.representation(~T.Integer, ~Codec.integer_encode, V, C.step_cache(T.Integer, V, C.add_with_lifetime(T.Integer, V, Codec.integer_encode, c, key, value, ns, now))) == True{} : Bool}:
  add_with_lifetime(~T.Integer, ~Codec.integer_encode, V, c, key, value, ns, now, invariant)

def word64_add(-V: Data, c: C.Cache<Word(64n), V>, key: Word(64n), value: V, now: T.Int64, invariant: {Inv.representation(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}) -> {Inv.representation(~Word(64n), ~Key.word64_encode, V, C.step_cache(Word(64n), V, C.add(Word(64n), V, Key.word64_encode, c, key, value, now))) == True{} : Bool}:
  add(~Word(64n), ~Key.word64_encode, V, c, key, value, now, invariant)

def word64_add_with_lifetime(-V: Data, c: C.Cache<Word(64n), V>, key: Word(64n), value: V, ns: T.Int64, now: T.Int64, invariant: {Inv.representation(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}) -> {Inv.representation(~Word(64n), ~Key.word64_encode, V, C.step_cache(Word(64n), V, C.add_with_lifetime(Word(64n), V, Key.word64_encode, c, key, value, ns, now))) == True{} : Bool}:
  add_with_lifetime(~Word(64n), ~Key.word64_encode, V, c, key, value, ns, now, invariant)

