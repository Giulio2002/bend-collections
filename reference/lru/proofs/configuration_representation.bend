import Base
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../src/time.bend as Time
import ../src/codec.bend as Codec
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./removal_representation.bend as Remove
import ./refresh_representation.bend as Refresh
import ./cache_key_identity.bend as Key

def set_lifetime(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, ns: T.Int64, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.set_lifetime(K, V, c, ns)) == True{} : Bool}:
  C.State{cap, table, order, life, counts, cb} = c
  invariant

def clear_metrics(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.clear_metrics(K, V, c)) == True{} : Bool}:
  C.State{cap, table, order, life, counts, cb} = c
  invariant

def finish_removal(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, evict: Bool, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, P.finish_removal(K, V, c, evict)) == True{} : Bool}:
  C.State{cap, table, order, life, counts, cb} = c
  invariant

def finish_miss(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, tracked: Bool, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, P.finish_miss(K, V, c, tracked)) == True{} : Bool}:
  C.State{cap, table, order, life, counts, cb} = c
  invariant

def reset_state(-K: Data, -V: Data, result: C.Cache<K, V> & T.Metrics) -> C.Cache<K, V>:
  (c, old) = result
  c

def reset_metrics(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, reset_state(K, V, C.reset_metrics(K, V, c))) == True{} : Bool}:
  C.State{cap, table, order, life, counts, cb} = c
  invariant

def counted(~K: Data, ~encode: K -> String, -V: Data, result: C.Step<K, V>, tracked: Bool, hit: Bool, invariant: {Inv.representation(~K, ~encode, V, C.step_cache(K, V, result)) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.counted(K, V, result, tracked, hit))) == True{} : Bool}:
  C.Out{C.State{cap, table, order, life, counts, cb}, item, flag, events} = result
  invariant

def miss_after_remove(~K: Data, ~encode: K -> String, -V: Data, result: C.Step<K, V>, tracked: Bool, invariant: {Inv.representation(~K, ~encode, V, C.step_cache(K, V, result)) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.miss_after_remove(K, V, result, tracked))) == True{} : Bool}:
  C.Out{c, item, flag, events} = result
  counted(~K, ~encode, V, C.Out{c, item, False{}, events}, tracked, False{}, invariant)

def prepare_room(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, full: Bool, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, P.prepare_room(K, V, c, full))) == True{} : Bool}:
  match full:
    case False{}: invariant
    case True{}: Remove.detach_oldest(~K, ~encode, V, c, invariant)

def prepare_found(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, result: Maybe<&2, T.Entry<K, V>>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, P.prepare_found(K, V, c, result))) == True{} : Bool}:
  match result:
    case Some{entry}: invariant
    case None{}: prepare_room(~K, ~encode, V, c, Nat.is_eq(C.len(K, V, c), C.capacity(K, V, c)), invariant)

def prepare_add(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, code: String, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, P.prepare_add(K, V, c, code))) == True{} : Bool}:
  prepare_found(~K, ~encode, V, c, C.lookup(K, V, c, code), invariant)

def finish_detached(~K: Data, ~encode: K -> String, -V: Data, result: C.Step<K, V>, evict: Bool, invariant: {Inv.representation(~K, ~encode, V, C.step_cache(K, V, result)) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, P.finish_detached(K, V, result, evict))) == True{} : Bool}:
  C.Out{c, item, flag, events} = result
  match flag:
    case False{}: invariant
    case True{}: finish_removal(~K, ~encode, V, c, evict, invariant)

def string_prepare_add(-V: Data, c: C.Cache<String, V>, code: String, invariant: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {Inv.representation(~String, ~Codec.string_encode, V, C.step_cache(String, V, P.prepare_add(String, V, c, code))) == True{} : Bool}:
  prepare_add(~String, ~Codec.string_encode, V, c, code, invariant)

def string_finish_removal(-V: Data, c: C.Cache<String, V>, evict: Bool, invariant: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {Inv.representation(~String, ~Codec.string_encode, V, P.finish_removal(String, V, c, evict)) == True{} : Bool}:
  finish_removal(~String, ~Codec.string_encode, V, c, evict, invariant)

def string_reset_metrics(-V: Data, c: C.Cache<String, V>, invariant: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {Inv.representation(~String, ~Codec.string_encode, V, reset_state(String, V, C.reset_metrics(String, V, c))) == True{} : Bool}:
  reset_metrics(~String, ~Codec.string_encode, V, c, invariant)

def string_set_lifetime(-V: Data, c: C.Cache<String, V>, ns: T.Int64, invariant: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {Inv.representation(~String, ~Codec.string_encode, V, C.set_lifetime(String, V, c, ns)) == True{} : Bool}:
  set_lifetime(~String, ~Codec.string_encode, V, c, ns, invariant)

def integer_prepare_add(-V: Data, c: C.Cache<T.Integer, V>, code: String, invariant: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}) -> {Inv.representation(~T.Integer, ~Codec.integer_encode, V, C.step_cache(T.Integer, V, P.prepare_add(T.Integer, V, c, code))) == True{} : Bool}:
  prepare_add(~T.Integer, ~Codec.integer_encode, V, c, code, invariant)

def integer_finish_removal(-V: Data, c: C.Cache<T.Integer, V>, evict: Bool, invariant: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}) -> {Inv.representation(~T.Integer, ~Codec.integer_encode, V, P.finish_removal(T.Integer, V, c, evict)) == True{} : Bool}:
  finish_removal(~T.Integer, ~Codec.integer_encode, V, c, evict, invariant)

def integer_reset_metrics(-V: Data, c: C.Cache<T.Integer, V>, invariant: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}) -> {Inv.representation(~T.Integer, ~Codec.integer_encode, V, reset_state(T.Integer, V, C.reset_metrics(T.Integer, V, c))) == True{} : Bool}:
  reset_metrics(~T.Integer, ~Codec.integer_encode, V, c, invariant)

def integer_set_lifetime(-V: Data, c: C.Cache<T.Integer, V>, ns: T.Int64, invariant: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}) -> {Inv.representation(~T.Integer, ~Codec.integer_encode, V, C.set_lifetime(T.Integer, V, c, ns)) == True{} : Bool}:
  set_lifetime(~T.Integer, ~Codec.integer_encode, V, c, ns, invariant)

def word64_prepare_add(-V: Data, c: C.Cache<Word(64n), V>, code: String, invariant: {Inv.representation(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}) -> {Inv.representation(~Word(64n), ~Key.word64_encode, V, C.step_cache(Word(64n), V, P.prepare_add(Word(64n), V, c, code))) == True{} : Bool}:
  prepare_add(~Word(64n), ~Key.word64_encode, V, c, code, invariant)

def word64_finish_removal(-V: Data, c: C.Cache<Word(64n), V>, evict: Bool, invariant: {Inv.representation(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}) -> {Inv.representation(~Word(64n), ~Key.word64_encode, V, P.finish_removal(Word(64n), V, c, evict)) == True{} : Bool}:
  finish_removal(~Word(64n), ~Key.word64_encode, V, c, evict, invariant)

def word64_reset_metrics(-V: Data, c: C.Cache<Word(64n), V>, invariant: {Inv.representation(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}) -> {Inv.representation(~Word(64n), ~Key.word64_encode, V, reset_state(Word(64n), V, C.reset_metrics(Word(64n), V, c))) == True{} : Bool}:
  reset_metrics(~Word(64n), ~Key.word64_encode, V, c, invariant)

def word64_set_lifetime(-V: Data, c: C.Cache<Word(64n), V>, ns: T.Int64, invariant: {Inv.representation(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}) -> {Inv.representation(~Word(64n), ~Key.word64_encode, V, C.set_lifetime(Word(64n), V, c, ns)) == True{} : Bool}:
  set_lifetime(~Word(64n), ~Key.word64_encode, V, c, ns, invariant)

