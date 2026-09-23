import Base
import ../types/model.bend as T
import ./cache.bend as C
import ./time.bend as Time

# Shared entry operations used by the callback-free public machine.
# The historical phase protocol forwards here to retain its checked proofs.
# This module does not depend on that protocol or its aggregate/eviction phases.

def finish_miss(-K: Data, -V: Data, c: C.Cache<K, V>, tracked: Bool) -> C.Cache<K, V>:
  C.State{cap, table, order, life, counts, cb} = c
  C.State{cap, table, order, life, C.hit_counts(counts, tracked, False{}), cb}

def keys_of(-K: Data, -V: Data, xs: List<&2, T.Entry<K, V>>) -> List<&2, K>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{T.Item{k, v, d}, rest}:
      Con{k, keys_of(K, V, rest)}

def values_of(-K: Data, -V: Data, xs: List<&2, T.Entry<K, V>>) -> List<&2, V>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{T.Item{k, v, d}, rest}:
      Con{v, values_of(K, V, rest)}

def refresh_prepare_found(-K: Data, -V: Data, c: C.Cache<K, V>, code: String, found: Maybe<&2, T.Entry<K, V>>) -> C.Step<K, V>:
  match found:
    case None{}:
      C.Out{finish_miss(K, V, c, True{}), None{}, False{}, Nil{}}
    case Some{entry}:
      C.read_live(K, V, c, code, entry, True{})

def refresh_prepare(-K: Data, -V: Data, +c: C.Cache<K, V>, +code: String) -> C.Step<K, V>:
  refresh_prepare_found(K, V, c, code, C.lookup(K, V, c, code))

def refresh_at(-K: Data, -V: Data, c: C.Cache<K, V>, code: String, entry: T.Entry<K, V>, lifetime: T.Int64, now: T.Int64) -> C.Cache<K, V>:
  C.State{cap, table, order, life, counts, cb} = c
  T.Item{k, v, old} = entry
  C.State{cap, Map.set(&2, Maybe<&2, T.Entry<K, V>>, table, code, Some{T.Item{k, v, Time.deadline(now, lifetime)}}), order, life, counts, cb}
