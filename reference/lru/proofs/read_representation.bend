import Base
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../src/time.bend as Time
import ../src/codec.bend as Codec
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./removal_representation.bend as Remove
import ./refresh_representation.bend as Refresh
import ./configuration_representation.bend as Config
import ./cache_key_identity.bend as Key

def untracked(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, code: String, entry: T.Entry<K, V>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.read_live(K, V, c, code, entry, False{}))) == True{} : Bool}:
  C.State{cap, table, order, life, counts, cb} = c
  invariant

def live(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, code: String, entry: T.Entry<K, V>, tracked: Bool, decision: {C.lookup(K, V, c, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.read_live(K, V, c, code, entry, tracked))) == True{} : Bool}:
  match tracked:
    case False{}: untracked(~K, ~encode, V, c, code, entry, invariant)
    case True{}: Refresh.live(~K, ~encode, V, c, code, entry, decision, invariant)

def expiry(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, entry: T.Entry<K, V>, tracked: Bool, expired: Bool, decision: {C.lookup(K, V, c, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.read_expiry(K, V, c, code, entry, tracked, expired))) == True{} : Bool}:
  match expired:
    case False{}: live(~K, ~encode, V, c, code, entry, tracked, decision, invariant)
    case True{}: Config.miss_after_remove(~K, ~encode, V, C.remove_encoded(K, V, c, code, False{}), tracked, Remove.remove_encoded(~K, ~encode, V, c, code, False{}, invariant))

def found(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, code: String, now: T.Int64, tracked: Bool, result: Maybe<&2, T.Entry<K, V>>, decision: {C.lookup(K, V, c, code) == result : Maybe<&2, T.Entry<K, V>>}, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.read_found(K, V, c, code, now, tracked, result))) == True{} : Bool}:
  match result:
    case None{}: Config.counted(~K, ~encode, V, C.Out{c, None{}, False{}, Nil{}}, tracked, False{}, invariant)
    case Some{T.Item{key, value, +deadline}}: expiry(~K, ~encode, V, c, code, T.Item{key, value, deadline}, tracked, Time.expired(deadline, now), decision, invariant)

def read_encoded(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, now: T.Int64, tracked: Bool, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.read_encoded(K, V, c, code, now, tracked))) == True{} : Bool}:
  found(~K, ~encode, V, c, code, now, tracked, C.lookup(K, V, c, code), {==}, invariant)

def read_cache(-K: Data, -V: Data, result: P.Read<K, V>) -> C.Cache<K, V>:
  P.Reading{step, removed} = result
  C.step_cache(K, V, step)

def expired_read(~K: Data, ~encode: K -> String, -V: Data, result: C.Step<K, V>, invariant: {Inv.representation(~K, ~encode, V, C.step_cache(K, V, result)) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, read_cache(K, V, P.expired_read(K, V, result))) == True{} : Bool}:
  C.Out{c, item, flag, events} = result
  invariant

def decide_read(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, entry: T.Entry<K, V>, tracked: Bool, expired: Bool, decision: {C.lookup(K, V, c, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, read_cache(K, V, P.decide_read(K, V, c, code, entry, tracked, expired))) == True{} : Bool}:
  match expired:
    case False{}: live(~K, ~encode, V, c, code, entry, tracked, decision, invariant)
    case True{}: expired_read(~K, ~encode, V, P.detach(K, V, c, code), Remove.detach(~K, ~encode, V, c, code, invariant))

def protocol_found(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, code: String, now: T.Int64, tracked: Bool, result: Maybe<&2, T.Entry<K, V>>, decision: {C.lookup(K, V, c, code) == result : Maybe<&2, T.Entry<K, V>>}, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, read_cache(K, V, P.read_found(K, V, c, code, now, tracked, result))) == True{} : Bool}:
  match result:
    case None{}: Config.finish_miss(~K, ~encode, V, c, tracked, invariant)
    case Some{T.Item{key, value, +deadline}}: decide_read(~K, ~encode, V, c, code, T.Item{key, value, deadline}, tracked, Time.expired(deadline, now), decision, invariant)

def protocol_read(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, now: T.Int64, tracked: Bool, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, read_cache(K, V, P.read(K, V, c, code, now, tracked))) == True{} : Bool}:
  protocol_found(~K, ~encode, V, c, code, now, tracked, C.lookup(K, V, c, code), {==}, invariant)

def oldest_read(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, order: List<&2, String>, now: T.Int64, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.oldest_read(K, V, c, order, now))) == True{} : Bool}:
  match order:
    case Nil{}: invariant
    case Con{code, tail}: read_encoded(~K, ~encode, V, c, code, now, False{}, invariant)

def get_oldest(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, now: T.Int64, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.get_oldest(K, V, c, now))) == True{} : Bool}:
  C.State{cap, table, +order, life, counts, cb} = c
  oldest_read(~K, ~encode, V, C.State{cap, table, order, life, counts, cb}, order, now, invariant)

def string_read_encoded(-V: Data, c: C.Cache<String, V>, code: String, now: T.Int64, tracked: Bool, invariant: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {Inv.representation(~String, ~Codec.string_encode, V, C.step_cache(String, V, C.read_encoded(String, V, c, code, now, tracked))) == True{} : Bool}:
  read_encoded(~String, ~Codec.string_encode, V, c, code, now, tracked, invariant)

def string_protocol_read(-V: Data, c: C.Cache<String, V>, code: String, now: T.Int64, tracked: Bool, invariant: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {Inv.representation(~String, ~Codec.string_encode, V, read_cache(String, V, P.read(String, V, c, code, now, tracked))) == True{} : Bool}:
  protocol_read(~String, ~Codec.string_encode, V, c, code, now, tracked, invariant)

def string_get_oldest(-V: Data, c: C.Cache<String, V>, now: T.Int64, invariant: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {Inv.representation(~String, ~Codec.string_encode, V, C.step_cache(String, V, C.get_oldest(String, V, c, now))) == True{} : Bool}:
  get_oldest(~String, ~Codec.string_encode, V, c, now, invariant)

def integer_read_encoded(-V: Data, c: C.Cache<T.Integer, V>, code: String, now: T.Int64, tracked: Bool, invariant: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}) -> {Inv.representation(~T.Integer, ~Codec.integer_encode, V, C.step_cache(T.Integer, V, C.read_encoded(T.Integer, V, c, code, now, tracked))) == True{} : Bool}:
  read_encoded(~T.Integer, ~Codec.integer_encode, V, c, code, now, tracked, invariant)

def integer_protocol_read(-V: Data, c: C.Cache<T.Integer, V>, code: String, now: T.Int64, tracked: Bool, invariant: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}) -> {Inv.representation(~T.Integer, ~Codec.integer_encode, V, read_cache(T.Integer, V, P.read(T.Integer, V, c, code, now, tracked))) == True{} : Bool}:
  protocol_read(~T.Integer, ~Codec.integer_encode, V, c, code, now, tracked, invariant)

def integer_get_oldest(-V: Data, c: C.Cache<T.Integer, V>, now: T.Int64, invariant: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}) -> {Inv.representation(~T.Integer, ~Codec.integer_encode, V, C.step_cache(T.Integer, V, C.get_oldest(T.Integer, V, c, now))) == True{} : Bool}:
  get_oldest(~T.Integer, ~Codec.integer_encode, V, c, now, invariant)

def word64_read_encoded(-V: Data, c: C.Cache<Word(64n), V>, code: String, now: T.Int64, tracked: Bool, invariant: {Inv.representation(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}) -> {Inv.representation(~Word(64n), ~Key.word64_encode, V, C.step_cache(Word(64n), V, C.read_encoded(Word(64n), V, c, code, now, tracked))) == True{} : Bool}:
  read_encoded(~Word(64n), ~Key.word64_encode, V, c, code, now, tracked, invariant)

def word64_protocol_read(-V: Data, c: C.Cache<Word(64n), V>, code: String, now: T.Int64, tracked: Bool, invariant: {Inv.representation(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}) -> {Inv.representation(~Word(64n), ~Key.word64_encode, V, read_cache(Word(64n), V, P.read(Word(64n), V, c, code, now, tracked))) == True{} : Bool}:
  protocol_read(~Word(64n), ~Key.word64_encode, V, c, code, now, tracked, invariant)

def word64_get_oldest(-V: Data, c: C.Cache<Word(64n), V>, now: T.Int64, invariant: {Inv.representation(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}) -> {Inv.representation(~Word(64n), ~Key.word64_encode, V, C.step_cache(Word(64n), V, C.get_oldest(Word(64n), V, c, now))) == True{} : Bool}:
  get_oldest(~Word(64n), ~Key.word64_encode, V, c, now, invariant)

