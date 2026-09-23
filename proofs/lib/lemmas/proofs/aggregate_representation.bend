import Base
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../src/time.bend as Time
import ../src/codec.bend as Codec
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./removal_representation.bend as Remove
import ./configuration_representation.bend as Config
import ./cache_key_identity.bend as Key

# Observe the actual intermediate protocol state, including pending clocks and
# removal boundaries. This is not an alternate aggregate implementation.
def cache(-K: Data, -V: Data, result: P.Aggregate<K, V>) -> C.Cache<K, V>:
  match result:
    case P.Complete{c, keys, values}: c
    case P.NeedClock{c, remaining, kind}: c
    case P.RemovalReady{step, remaining, kind}: C.step_cache(K, V, step)

def complete(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, kind: P.Mode, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, cache(K, V, P.complete(K, V, c, kind))) == True{} : Bool}:
  match kind:
    case P.All{}: Config.clear_metrics(~K, ~encode, V, c, invariant)
    case P.Expired{}: invariant
    case P.KeyList{}: invariant
    case P.ValueList{}: invariant

def need_clock(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, remaining: Nat, kind: P.Mode, finite: Bool, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, cache(K, V, P.need_clock(K, V, c, remaining, kind, finite))) == True{} : Bool}:
  match finite:
    case False{}: complete(~K, ~encode, V, c, kind, invariant)
    case True{}: invariant

def next(~K: Data, ~encode: K -> String, -V: Data, remaining: Nat, +c: C.Cache<K, V>, kind: P.Mode, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, cache(K, V, P.aggregate_next(K, V, remaining, c, kind))) == True{} : Bool}:
  match remaining kind:
    case 0n k: complete(~K, ~encode, V, c, k, invariant)
    case 1n+p P.All{}: Remove.detach_oldest(~K, ~encode, V, c, invariant)
    case 1n+p P.Expired{}: need_clock(~K, ~encode, V, c, p, P.Expired{}, C.purge_needs_clock(K, V, c), invariant)
    case 1n+p P.KeyList{}: need_clock(~K, ~encode, V, c, p, P.KeyList{}, C.purge_needs_clock(K, V, c), invariant)
    case 1n+p P.ValueList{}: need_clock(~K, ~encode, V, c, p, P.ValueList{}, C.purge_needs_clock(K, V, c), invariant)

def after_removal(~K: Data, ~encode: K -> String, -V: Data, remaining: Nat, +c: C.Cache<K, V>, kind: P.Mode, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, cache(K, V, P.after_removal(K, V, remaining, c, kind))) == True{} : Bool}:
  next(~K, ~encode, V, remaining, P.finish_removal(K, V, c, False{}), kind, Config.finish_removal(~K, ~encode, V, c, False{}, invariant))

def clock_decide(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, remaining: Nat, kind: P.Mode, expired: Bool, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, cache(K, V, P.clock_decide(K, V, c, remaining, kind, expired))) == True{} : Bool}:
  match expired:
    case False{}: complete(~K, ~encode, V, c, kind, invariant)
    case True{}: Remove.detach_oldest(~K, ~encode, V, c, invariant)

def clock_entry(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, remaining: Nat, kind: P.Mode, now: T.Int64, entry: Maybe<&2, T.Entry<K, V>>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, cache(K, V, P.clock_entry(K, V, c, remaining, kind, now, entry))) == True{} : Bool}:
  match entry:
    case None{}: complete(~K, ~encode, V, c, kind, invariant)
    case Some{T.Item{key, value, deadline}}: clock_decide(~K, ~encode, V, c, remaining, kind, Time.expired(deadline, now), invariant)

def after_clock(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, remaining: Nat, kind: P.Mode, now: T.Int64, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, cache(K, V, P.after_clock(K, V, c, remaining, kind, now))) == True{} : Bool}:
  clock_entry(~K, ~encode, V, c, remaining, kind, now, C.oldest_entry(K, V, c), invariant)

def purge(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, cache(K, V, P.purge(K, V, c))) == True{} : Bool}:
  next(~K, ~encode, V, C.len(K, V, c), c, P.All{}, invariant)

def purge_expired(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, cache(K, V, P.purge_expired(K, V, c))) == True{} : Bool}:
  next(~K, ~encode, V, C.len(K, V, c), c, P.Expired{}, invariant)

def keys(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, cache(K, V, P.keys(K, V, c))) == True{} : Bool}:
  next(~K, ~encode, V, C.len(K, V, c), c, P.KeyList{}, invariant)

def values(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, cache(K, V, P.values(K, V, c))) == True{} : Bool}:
  next(~K, ~encode, V, C.len(K, V, c), c, P.ValueList{}, invariant)

def purge_loop(~K: Data, ~encode: K -> String, -V: Data, fuel: Nat, +c: C.Cache<K, V>, invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.purge_loop(K, V, fuel, c))) == True{} : Bool}:
  match fuel:
    case 0n: Config.clear_metrics(~K, ~encode, V, c, invariant)
    case 1n+p: purge_loop(~K, ~encode, V, p, C.step_cache(K, V, C.remove_oldest(K, V, c, False{})), Remove.remove_oldest(~K, ~encode, V, c, False{}, invariant))

def string_next(-V: Data, c: C.Cache<String, V>, remaining: Nat, kind: P.Mode, invariant: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {Inv.representation(~String, ~Codec.string_encode, V, cache(String, V, P.aggregate_next(String, V, remaining, c, kind))) == True{} : Bool}:
  next(~String, ~Codec.string_encode, V, remaining, c, kind, invariant)

def string_after_removal(-V: Data, c: C.Cache<String, V>, remaining: Nat, kind: P.Mode, invariant: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {Inv.representation(~String, ~Codec.string_encode, V, cache(String, V, P.after_removal(String, V, remaining, c, kind))) == True{} : Bool}:
  after_removal(~String, ~Codec.string_encode, V, remaining, c, kind, invariant)

def string_after_clock(-V: Data, c: C.Cache<String, V>, remaining: Nat, kind: P.Mode, now: T.Int64, invariant: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {Inv.representation(~String, ~Codec.string_encode, V, cache(String, V, P.after_clock(String, V, c, remaining, kind, now))) == True{} : Bool}:
  after_clock(~String, ~Codec.string_encode, V, c, remaining, kind, now, invariant)

def string_purge_loop(-V: Data, c: C.Cache<String, V>, fuel: Nat, invariant: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {Inv.representation(~String, ~Codec.string_encode, V, C.step_cache(String, V, C.purge_loop(String, V, fuel, c))) == True{} : Bool}:
  purge_loop(~String, ~Codec.string_encode, V, fuel, c, invariant)

def integer_next(-V: Data, c: C.Cache<T.Integer, V>, remaining: Nat, kind: P.Mode, invariant: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}) -> {Inv.representation(~T.Integer, ~Codec.integer_encode, V, cache(T.Integer, V, P.aggregate_next(T.Integer, V, remaining, c, kind))) == True{} : Bool}:
  next(~T.Integer, ~Codec.integer_encode, V, remaining, c, kind, invariant)

def integer_after_removal(-V: Data, c: C.Cache<T.Integer, V>, remaining: Nat, kind: P.Mode, invariant: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}) -> {Inv.representation(~T.Integer, ~Codec.integer_encode, V, cache(T.Integer, V, P.after_removal(T.Integer, V, remaining, c, kind))) == True{} : Bool}:
  after_removal(~T.Integer, ~Codec.integer_encode, V, remaining, c, kind, invariant)

def integer_after_clock(-V: Data, c: C.Cache<T.Integer, V>, remaining: Nat, kind: P.Mode, now: T.Int64, invariant: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}) -> {Inv.representation(~T.Integer, ~Codec.integer_encode, V, cache(T.Integer, V, P.after_clock(T.Integer, V, c, remaining, kind, now))) == True{} : Bool}:
  after_clock(~T.Integer, ~Codec.integer_encode, V, c, remaining, kind, now, invariant)

def integer_purge_loop(-V: Data, c: C.Cache<T.Integer, V>, fuel: Nat, invariant: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}) -> {Inv.representation(~T.Integer, ~Codec.integer_encode, V, C.step_cache(T.Integer, V, C.purge_loop(T.Integer, V, fuel, c))) == True{} : Bool}:
  purge_loop(~T.Integer, ~Codec.integer_encode, V, fuel, c, invariant)

def word64_next(-V: Data, c: C.Cache<Word(64n), V>, remaining: Nat, kind: P.Mode, invariant: {Inv.representation(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}) -> {Inv.representation(~Word(64n), ~Key.word64_encode, V, cache(Word(64n), V, P.aggregate_next(Word(64n), V, remaining, c, kind))) == True{} : Bool}:
  next(~Word(64n), ~Key.word64_encode, V, remaining, c, kind, invariant)

def word64_after_removal(-V: Data, c: C.Cache<Word(64n), V>, remaining: Nat, kind: P.Mode, invariant: {Inv.representation(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}) -> {Inv.representation(~Word(64n), ~Key.word64_encode, V, cache(Word(64n), V, P.after_removal(Word(64n), V, remaining, c, kind))) == True{} : Bool}:
  after_removal(~Word(64n), ~Key.word64_encode, V, remaining, c, kind, invariant)

def word64_after_clock(-V: Data, c: C.Cache<Word(64n), V>, remaining: Nat, kind: P.Mode, now: T.Int64, invariant: {Inv.representation(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}) -> {Inv.representation(~Word(64n), ~Key.word64_encode, V, cache(Word(64n), V, P.after_clock(Word(64n), V, c, remaining, kind, now))) == True{} : Bool}:
  after_clock(~Word(64n), ~Key.word64_encode, V, c, remaining, kind, now, invariant)

def word64_purge_loop(-V: Data, c: C.Cache<Word(64n), V>, fuel: Nat, invariant: {Inv.representation(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}) -> {Inv.representation(~Word(64n), ~Key.word64_encode, V, C.step_cache(Word(64n), V, C.purge_loop(Word(64n), V, fuel, c))) == True{} : Bool}:
  purge_loop(~Word(64n), ~Key.word64_encode, V, fuel, c, invariant)

