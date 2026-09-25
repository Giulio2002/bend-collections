import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../types/model.bend as T
import ../spec/cache.bend as S
import ../spec/clock.bend as Clock
import ../spec/public_commands.bend as Public
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./representation_parts.bend as Parts
import ./abstraction_recency.bend as Recency
import ./cache_key_identity.bend as Key

# Direct native-operation observations, before host conversions. Wrapping the
# native results below does not claim the TypeScript caller has been verified.
def metrics(-K: Data, -V: Data, c: C.Cache<K, V>, events: List<&2, Clock.ClockEvent>) -> {Public.Returned{F.abstract(K, V, c), Public.Counters{C.metrics(K, V, c)}, events, 0n} == Public.metrics(K, V, F.abstract(K, V, c), events) : Public.CmdResult<K, V>}:
  C.State{cap, table, order, life, counts, cb} = c
  {==}

def reset(-K: Data, -V: Data, c: C.Cache<K, V>, events: List<&2, Clock.ClockEvent>) -> {Public.Returned{F.abstract(K, V, C.clear_metrics(K, V, c)), Public.Counters{C.metrics(K, V, c)}, events, 0n} == Public.reset(K, V, F.abstract(K, V, c), events) : Public.CmdResult<K, V>}:
  C.State{cap, table, order, life, counts, cb} = c
  {==}

def encoded_length(~K: Data, ~encode: K -> String, keys: List<&2, K>) -> {List.length(&2, String, Recency.encode_keys(~K, ~encode, keys)) == List.length(&2, K, keys) : Nat}:
  match keys:
    case Nil{}: {==}
    case Con{key, +tail}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, String, Recency.encode_keys(~K, ~encode, tail)), List.length(&2, K, tail), encoded_length(~K, ~encode, tail))

def native_length(-K: Data, -V: Data, c: C.Cache<K, V>) -> {List.length(&2, String, Recency.native_order(K, V, c)) == C.len(K, V, c) : Nat}:
  C.State{cap, table, order, life, counts, cb} = c
  {==}

def model_length(-K: Data, -V: Data, s: S.Model<K, V>) -> {List.length(&2, K, Recency.model_order(K, V, s)) == S.length(K, V, s) : Nat}:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  {==}

def length(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, valid: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {C.len(K, V, c) == S.length(K, V, F.abstract(K, V, c)) : Nat}:
  Equal.trans(Nat, C.len(K, V, c), List.length(&2, String, Recency.native_order(K, V, c)), S.length(K, V, F.abstract(K, V, c)), Equal.sym(Nat, List.length(&2, String, Recency.native_order(K, V, c)), C.len(K, V, c), native_length(K, V, c)), Equal.trans(Nat, List.length(&2, String, Recency.native_order(K, V, c)), List.length(&2, String, Recency.encode_keys(~K, ~encode, Recency.model_order(K, V, F.abstract(K, V, c)))), S.length(K, V, F.abstract(K, V, c)), Equal.sym(Nat, List.length(&2, String, Recency.encode_keys(~K, ~encode, Recency.model_order(K, V, F.abstract(K, V, c)))), List.length(&2, String, Recency.native_order(K, V, c)), Equal.cong(List<&2, String>, Nat, xs => List.length(&2, String, xs), Recency.encode_keys(~K, ~encode, Recency.model_order(K, V, F.abstract(K, V, c))), Recency.native_order(K, V, c), Parts.recency_faithful(~K, ~encode, V, c, valid))), Equal.trans(Nat, List.length(&2, String, Recency.encode_keys(~K, ~encode, Recency.model_order(K, V, F.abstract(K, V, c)))), List.length(&2, K, Recency.model_order(K, V, F.abstract(K, V, c))), S.length(K, V, F.abstract(K, V, c)), encoded_length(~K, ~encode, Recency.model_order(K, V, F.abstract(K, V, c))), model_length(K, V, F.abstract(K, V, c)))))

def string_length(-V: Data, c: C.Cache<String, V>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {C.len(String, V, c) == S.length(String, V, F.abstract(String, V, c)) : Nat}:
  length(~String, ~Codec.string_encode, V, c, valid)

def integer_length(-V: Data, c: C.Cache<T.Integer, V>, valid: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}) -> {C.len(T.Integer, V, c) == S.length(T.Integer, V, F.abstract(T.Integer, V, c)) : Nat}:
  length(~T.Integer, ~Codec.integer_encode, V, c, valid)

def word64_length(-V: Data, c: C.Cache<Word(64n), V>, valid: {Inv.representation(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}) -> {C.len(Word(64n), V, c) == S.length(Word(64n), V, F.abstract(Word(64n), V, c)) : Nat}:
  length(~Word(64n), ~Key.word64_encode, V, c, valid)
