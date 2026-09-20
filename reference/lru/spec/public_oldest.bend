import Base
import ../types/model.bend as T
import ./cache.bend as S
import ./operations.bend as O
import ./numeric.bend as N

# Full public GetOldest observation. The key is captured before expiry removal,
# as in pinned lru.go:561; a miss clears the value, not the captured key.
# Clock lists are supplied inputs, never expected answers. Exhaustion is failure.
type Reply<-K: Data, -V: Data> is Data:
  Returned{state: S.Model<K, V>, key: K, value: V, found: Bool, unused_clock: List<&2, T.Int64>}

def miss(-K: Data, -V: Data, s: S.Model<K, V>, zero_key: K, zero_value: V, times: List<&2, T.Int64>) -> Reply<K, V>:
  Returned{s, zero_key, zero_value, False{}, times}

def decide(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, +key: K, value: V, zero_value: V, times: List<&2, T.Int64>, expired: Bool) -> Reply<K, V>:
  match expired:
    case False{}:
      Returned{s, key, value, True{}, times}
    case True{}:
      Returned{O.observed_state(K, V, S.remove(~K, ~same, V, s, key)), key, zero_value, False{}, times}

def sample(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, key: K, value: V, deadline: T.Int64, zero_value: V, times: List<&2, T.Int64>) -> Result<&2, &2, String, Reply<K, V>>:
  match times:
    case Nil{}:
      Fail{"clock sample required"}
    case Con{now, rest}:
      Done{decide(~K, ~same, V, s, key, value, zero_value, rest, N.expired(deadline, now))}

def lifetime(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, key: K, value: V, deadline: T.Int64, zero_value: V, times: List<&2, T.Int64>, immortal: Bool) -> Result<&2, &2, String, Reply<K, V>>:
  match immortal:
    case True{}:
      Done{Returned{s, key, value, True{}, times}}
    case False{}:
      sample(~K, ~same, V, s, key, value, deadline, zero_value, times)

def binding(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, zero_key: K, zero_value: V, times: List<&2, T.Int64>, item: Maybe<&2, T.Entry<K, V>>) -> Result<&2, &2, String, Reply<K, V>>:
  match item:
    case None{}:
      # A nonempty order with a missing binding is an invalid representation,
      # not an empty cache. The public invariant must rule this branch out.
      Fail{"oldest binding missing"}
    case Some{T.Item{key, value, T.I64{+bits}}}:
      lifetime(~K, ~same, V, s, key, value, T.I64{bits}, zero_value, times, N.zero(bits))

def ordered(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, zero_key: K, zero_value: V, times: List<&2, T.Int64>, order: List<&2, K>) -> Result<&2, &2, String, Reply<K, V>>:
  S.Abstract{cap, bindings, recency, life, counts, cb} = s
  match order:
    case Nil{}:
      Done{miss(K, V, s, zero_key, zero_value, times)}
    case Con{key, tail}:
      binding(~K, ~same, V, s, zero_key, zero_value, times, S.find(~K, ~same, V, bindings, key))

def get_oldest(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, zero_key: K, zero_value: V, times: List<&2, T.Int64>) -> Result<&2, &2, String, Reply<K, V>>:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  ordered(~K, ~same, V, s, zero_key, zero_value, times, order)
