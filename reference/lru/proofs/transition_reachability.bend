import Base
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../src/codec.bend as Codec
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./representation_parts.bend as Parts
import ./add_representation.bend as Add
import ./read_representation.bend as Read
import ./core_refresh_representation.bend as Refresh
import ./refresh_representation.bend as Prepare
import ./removal_representation.bend as Remove
import ./configuration_representation.bend as Config
import ./aggregate_representation.bend as Aggregate
import ./cache_key_identity.bend as Key
import ./abstraction_recency.bend as Recency
import ./refinement.bend as F

# A closure of actual cache transitions, including intermediate protocol states.
# This proof-side driver establishes representation only. It is NOT the host
# dispatcher, an independent observable specification, or a transport theorem.
# Unchanged covers states retained on failures without asserting error behavior.
type Transition<-K: Data, -V: Data> is Data:
  Add{key: K, value: V, now: T.Int64}
  AddLifetime{key: K, value: V, ns: T.Int64, now: T.Int64}
  Read{key: K, now: T.Int64, tracked: Bool}
  Refresh{key: K, ns: T.Int64, now: T.Int64}
  Remove{key: K}
  RemoveOldest{}
  GetOldest{now: T.Int64}
  Lifetime{ns: T.Int64}
  Reset{}
  Purge{}
  PrepareAdd{code: String}
  PrepareRefresh{code: String}
  ProtocolRead{code: String, now: T.Int64, tracked: Bool}
  Detach{code: String}
  FinishRemoval{evict: Bool}
  FinishMiss{tracked: Bool}
  AggregateNext{remaining: Nat, mode: P.Mode}
  AggregateRemoval{remaining: Nat, mode: P.Mode}
  AggregateClock{remaining: Nat, mode: P.Mode, now: T.Int64}
  Unchanged{}

def step(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, op: Transition<K, V>) -> C.Cache<K, V>:
  match op:
    case Add{key, value, now}: C.step_cache(K, V, C.add(K, V, encode, c, key, value, now))
    case AddLifetime{key, value, ns, now}: C.step_cache(K, V, C.add_with_lifetime(K, V, encode, c, key, value, ns, now))
    case Read{key, now, tracked}: C.step_cache(K, V, C.read_encoded(K, V, c, encode(key), now, tracked))
    case Refresh{key, ns, now}: C.step_cache(K, V, C.get_and_refresh(K, V, encode, c, key, ns, now))
    case Remove{key}: C.step_cache(K, V, C.remove(K, V, encode, c, key))
    case RemoveOldest{}: C.step_cache(K, V, C.remove_oldest(K, V, c, False{}))
    case GetOldest{now}: C.step_cache(K, V, C.get_oldest(K, V, c, now))
    case Lifetime{ns}: C.set_lifetime(K, V, c, ns)
    case Reset{}: Config.reset_state(K, V, C.reset_metrics(K, V, c))
    case Purge{}: C.step_cache(K, V, C.purge(K, V, c))
    case PrepareAdd{code}: C.step_cache(K, V, P.prepare_add(K, V, c, code))
    case PrepareRefresh{code}: C.step_cache(K, V, P.refresh_prepare(K, V, c, code))
    case ProtocolRead{code, now, tracked}: Read.read_cache(K, V, P.read(K, V, c, code, now, tracked))
    case Detach{code}: C.step_cache(K, V, P.detach(K, V, c, code))
    case FinishRemoval{evict}: P.finish_removal(K, V, c, evict)
    case FinishMiss{tracked}: P.finish_miss(K, V, c, tracked)
    case AggregateNext{remaining, mode}: Aggregate.cache(K, V, P.aggregate_next(K, V, remaining, c, mode))
    case AggregateRemoval{remaining, mode}: Aggregate.cache(K, V, P.after_removal(K, V, remaining, c, mode))
    case AggregateClock{remaining, mode, now}: Aggregate.cache(K, V, P.after_clock(K, V, c, remaining, mode, now))
    case Unchanged{}: c

def preserves(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, op: Transition<K, V>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, step(~K, ~encode, V, c, op)) == True{} : Bool}:
  match op:
    case Add{key, value, now}: Add.add(~K, ~encode, V, c, key, value, now, invariant)
    case AddLifetime{key, value, ns, now}: Add.add_with_lifetime(~K, ~encode, V, c, key, value, ns, now, invariant)
    case Read{key, now, tracked}: Read.read_encoded(~K, ~encode, V, c, encode(key), now, tracked, invariant)
    case Refresh{key, ns, now}: Refresh.get_and_refresh(~K, ~encode, V, c, key, ns, now, invariant)
    case Remove{key}: Remove.remove_encoded(~K, ~encode, V, c, encode(key), False{}, invariant)
    case RemoveOldest{}: Remove.remove_oldest(~K, ~encode, V, c, False{}, invariant)
    case GetOldest{now}: Read.get_oldest(~K, ~encode, V, c, now, invariant)
    case Lifetime{ns}: Config.set_lifetime(~K, ~encode, V, c, ns, invariant)
    case Reset{}: Config.reset_metrics(~K, ~encode, V, c, invariant)
    case Purge{}: Aggregate.purge_loop(~K, ~encode, V, C.len(K, V, c), c, invariant)
    case PrepareAdd{code}: Config.prepare_add(~K, ~encode, V, c, code, invariant)
    case PrepareRefresh{code}: Prepare.prepare(~K, ~encode, V, c, code, invariant)
    case ProtocolRead{code, now, tracked}: Read.protocol_read(~K, ~encode, V, c, code, now, tracked, invariant)
    case Detach{code}: Remove.detach(~K, ~encode, V, c, code, invariant)
    case FinishRemoval{evict}: Config.finish_removal(~K, ~encode, V, c, evict, invariant)
    case FinishMiss{tracked}: Config.finish_miss(~K, ~encode, V, c, tracked, invariant)
    case AggregateNext{remaining, mode}: Aggregate.next(~K, ~encode, V, remaining, c, mode, invariant)
    case AggregateRemoval{remaining, mode}: Aggregate.after_removal(~K, ~encode, V, remaining, c, mode, invariant)
    case AggregateClock{remaining, mode, now}: Aggregate.after_clock(~K, ~encode, V, c, remaining, mode, now, invariant)
    case Unchanged{}: invariant

def run(~K: Data, ~encode: K -> String, -V: Data, ops: List<&2, Transition<K, V>>, c: C.Cache<K, V>) -> C.Cache<K, V>:
  match ops:
    case Nil{}: c
    case Con{op, tail}: run(~K, ~encode, V, tail, step(~K, ~encode, V, c, op))

def preserves_run(~K: Data, ~encode: K -> String, -V: Data, ops: List<&2, Transition<K, V>>, +c: C.Cache<K, V>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, run(~K, ~encode, V, ops, c)) == True{} : Bool}:
  match ops:
    case Nil{}: invariant
    case Con{+op, tail}: preserves_run(~K, ~encode, V, tail, step(~K, ~encode, V, c, op), preserves(~K, ~encode, V, c, op, invariant))

def initialized_run(~K: Data, ~encode: K -> String, -V: Data, +n: Nat, ops: List<&2, Transition<K, V>>) -> {Inv.representation(~K, ~encode, V, run(~K, ~encode, V, ops, C.init(K, V, 1n+n))) == True{} : Bool}:
  preserves_run(~K, ~encode, V, ops, C.init(K, V, 1n+n), Parts.initialized(~K, ~encode, V, n))

def string_initialized_run(-V: Data, n: Nat, ops: List<&2, Transition<String, V>>) -> {Inv.representation(~String, ~Codec.string_encode, V, run(~String, ~Codec.string_encode, V, ops, C.init(String, V, 1n+n))) == True{} : Bool}:
  initialized_run(~String, ~Codec.string_encode, V, n, ops)

def integer_initialized_run(-V: Data, n: Nat, ops: List<&2, Transition<T.Integer, V>>) -> {Inv.representation(~T.Integer, ~Codec.integer_encode, V, run(~T.Integer, ~Codec.integer_encode, V, ops, C.init(T.Integer, V, 1n+n))) == True{} : Bool}:
  initialized_run(~T.Integer, ~Codec.integer_encode, V, n, ops)

def word64_initialized_run(-V: Data, n: Nat, ops: List<&2, Transition<Word(64n), V>>) -> {Inv.representation(~Word(64n), ~Key.word64_encode, V, run(~Word(64n), ~Key.word64_encode, V, ops, C.init(Word(64n), V, 1n+n))) == True{} : Bool}:
  initialized_run(~Word(64n), ~Key.word64_encode, V, n, ops)

# The exact abstraction order follows without a representation premise at the
# call site: initialization and arbitrary transition preservation discharge it.
def initialized_recency(~K: Data, ~encode: K -> String, -V: Data, +n: Nat, +ops: List<&2, Transition<K, V>>) -> {Recency.encode_keys(~K, ~encode, Recency.model_order(K, V, F.abstract(K, V, run(~K, ~encode, V, ops, C.init(K, V, 1n+n))))) == Recency.native_order(K, V, run(~K, ~encode, V, ops, C.init(K, V, 1n+n))) : List<&2, String>}:
  Parts.recency_faithful(~K, ~encode, V, run(~K, ~encode, V, ops, C.init(K, V, 1n+n)), initialized_run(~K, ~encode, V, n, ops))

def string_initialized_recency(-V: Data, n: Nat, ops: List<&2, Transition<String, V>>) -> {Recency.encode_keys(~String, ~Codec.string_encode, Recency.model_order(String, V, F.abstract(String, V, run(~String, ~Codec.string_encode, V, ops, C.init(String, V, 1n+n))))) == Recency.native_order(String, V, run(~String, ~Codec.string_encode, V, ops, C.init(String, V, 1n+n))) : List<&2, String>}:
  initialized_recency(~String, ~Codec.string_encode, V, n, ops)

def integer_initialized_recency(-V: Data, n: Nat, ops: List<&2, Transition<T.Integer, V>>) -> {Recency.encode_keys(~T.Integer, ~Codec.integer_encode, Recency.model_order(T.Integer, V, F.abstract(T.Integer, V, run(~T.Integer, ~Codec.integer_encode, V, ops, C.init(T.Integer, V, 1n+n))))) == Recency.native_order(T.Integer, V, run(~T.Integer, ~Codec.integer_encode, V, ops, C.init(T.Integer, V, 1n+n))) : List<&2, String>}:
  initialized_recency(~T.Integer, ~Codec.integer_encode, V, n, ops)

def word64_initialized_recency(-V: Data, n: Nat, ops: List<&2, Transition<Word(64n), V>>) -> {Recency.encode_keys(~Word(64n), ~Key.word64_encode, Recency.model_order(Word(64n), V, F.abstract(Word(64n), V, run(~Word(64n), ~Key.word64_encode, V, ops, C.init(Word(64n), V, 1n+n))))) == Recency.native_order(Word(64n), V, run(~Word(64n), ~Key.word64_encode, V, ops, C.init(Word(64n), V, 1n+n))) : List<&2, String>}:
  initialized_recency(~Word(64n), ~Key.word64_encode, V, n, ops)
