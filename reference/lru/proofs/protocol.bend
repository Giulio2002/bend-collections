import Base
import ../types/model.bend as T
import ../src/cache.bend as C
import ../src/protocol.bend as P

law removal_found_phases:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for evict: Bool
  for found: Maybe<&2, T.Entry<K, V>>
  {P.finish_detached(K, V, P.detach_found(K, V, c, code, found), evict) == C.remove_found(K, V, c, code, evict, found) : C.Step<K, V>}
def removal_found_phases(K, V, c, code, evict, found):
  match c:
    case C.State{cap, table, order, life, counts, cb}:
      match found:
        case None{}:
          {==}
        case Some{entry}:
          {==}

law removal_phases:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for evict: Bool
  {P.finish_detached(K, V, P.detach(K, V, c, code), evict) == C.remove_encoded(K, V, c, code, evict) : C.Step<K, V>}
def removal_phases(K, V, c, code, evict):
  removal_found_phases(K, V, c, code, evict, C.lookup(K, V, c, code))

# Internal detach preserves metrics until the subsequent removal-count phase.
# This is a pure phase fact; the supported adapter executes no user callbacks.
law before_removal_count_metrics:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for entry: T.Entry<K, V>
  {C.metrics(K, V, C.step_cache(K, V, P.detach_present(K, V, c, code, entry))) == C.metrics(K, V, c) : T.Metrics}
def before_removal_count_metrics(K, V, c, code, entry):
  match c:
    case C.State{cap, table, order, life, counts, cb}:
      {==}
