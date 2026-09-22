import Base
import ../types/model.bend as T
import ./clock.bend as Clock
import ./cache.bend as S
import ./numeric.bend as N
import ./operations.bend as O
import ./effectful_operations.bend as E

# Ordered abstract bindings, not implementation fuel or native Map traversal.
# Every successful removal is retained even when the next provider event fails.
type Prefix<-K: Data, -V: Data> is Data:
  Finished{removed: List<&2, T.Entry<K, V>>, retained: List<&2, T.Entry<K, V>>, remaining: List<&2, Clock.Event>, requests: Nat}
  Failed{error: Clock.Error, removed: List<&2, T.Entry<K, V>>, retained: List<&2, T.Entry<K, V>>, remaining: List<&2, Clock.Event>, requests: Nat}

def prepend(-K: Data, -V: Data, entry: T.Entry<K, V>, result: Prefix<K, V>) -> Prefix<K, V>:
  match result:
    case Finished{removed, retained, events, requests}: Finished{Con{entry, removed}, retained, events, 1n+requests}
    case Failed{error, removed, retained, events, requests}: Failed{error, Con{entry, removed}, retained, events, 1n+requests}

def decide(-K: Data, -V: Data, entry: T.Entry<K, V>, tail: List<&2, T.Entry<K, V>>, events: List<&2, Clock.Event>, rest: Prefix<K, V>, expired: Bool) -> Prefix<K, V>:
  match expired:
    case False{}: Finished{Nil{}, Con{entry, tail}, events, 1n}
    case True{}: prepend(K, V, entry, rest)

def sentinel(-K: Data, -V: Data, entry: T.Entry<K, V>, tail: List<&2, T.Entry<K, V>>, events: List<&2, Clock.Event>, result: Prefix<K, V>, immortal: Bool) -> Prefix<K, V>:
  match immortal:
    case True{}: Finished{Nil{}, Con{entry, tail}, events, 0n}
    case False{}: result

def prefix(-K: Data, -V: Data, ordered: List<&2, T.Entry<K, V>>, events: List<&2, Clock.Event>) -> Prefix<K, V>:
  match ordered events:
    case Nil{} remaining: Finished{Nil{}, Nil{}, remaining, 0n}
    case Con{T.Item{+key, +value, T.I64{+bits}}, +tail} Nil{}:
      sentinel(K, V, T.Item{key, value, T.I64{bits}}, tail, Nil{}, Failed{Clock.Exhausted{}, Nil{}, Con{T.Item{key, value, T.I64{bits}}, tail}, Nil{}, 1n}, N.zero(bits))
    case Con{T.Item{+key, +value, T.I64{+bits}}, +tail} Con{Clock.InvalidSample{+reason}, +remaining}:
      sentinel(K, V, T.Item{key, value, T.I64{bits}}, tail, Con{Clock.InvalidSample{reason}, remaining}, Failed{Clock.Invalid{reason}, Nil{}, Con{T.Item{key, value, T.I64{bits}}, tail}, remaining, 1n}, N.zero(bits))
    case Con{T.Item{+key, +value, T.I64{+bits}}, +tail} Con{Clock.ProviderException{+reason}, +remaining}:
      sentinel(K, V, T.Item{key, value, T.I64{bits}}, tail, Con{Clock.ProviderException{reason}, remaining}, Failed{Clock.Thrown{reason}, Nil{}, Con{T.Item{key, value, T.I64{bits}}, tail}, remaining, 1n}, N.zero(bits))
    case Con{T.Item{+key, +value, T.I64{+bits}}, +tail} Con{Clock.Sample{+now}, +remaining}:
      sentinel(K, V, T.Item{key, value, T.I64{bits}}, tail, Con{Clock.Sample{now}, remaining}, decide(K, V, T.Item{key, value, T.I64{bits}}, tail, remaining, prefix(K, V, tail, remaining), N.expired(T.I64{bits}, now)), N.zero(bits))

def apply_prefix(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, result: Prefix<K, V>) -> E.Outcome<K, V>:
  match result:
    case Finished{removed, retained, events, requests}: E.Returned{S.Observed{O.remove_entries(~K, ~same, V, removed, s), None{}, False{}, Nil{}}, events, requests}
    case Failed{error, removed, retained, events, requests}: E.Failed{O.remove_entries(~K, ~same, V, removed, s), error, events, requests}

def purge_expired(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, events: List<&2, Clock.Event>) -> E.Outcome<K, V>:
  apply_prefix(~K, ~same, V, s, prefix(K, V, O.all_entries(~K, ~same, V, s), events))
