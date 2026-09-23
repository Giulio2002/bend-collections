import Base
import ./cache.bend as S
import ../types/model.bend as T

# Extensional finite-map equality deliberately ignores binding-list storage
# order. It preserves every queried entry (original key, value and deadline),
# exact observable recency, capacity, configuration, metrics and inert metadata.
# This is independent of the implementation and its abstraction function.
#
# Two models are related when their canonical forms are equal. The canonical
# form keeps every non-binding field exactly and replaces the binding list by
# (1) the lookup result at each recency key, in recency order, and (2) the
# bindings whose key is not in the recency list ("stray", normally empty), in
# list order. With a key equality that reflects equality, related models agree
# on S.find for EVERY key (proofs/canonical.bend, lookup_agreement). Unlike a
# pointwise function premise, this is one reusable equality proof.
type Canonical<-K: Data, -V: Data> is Data:
  Canon{capacity: Nat, recency: List<&2, K>, lifetime: T.Int64, counts: T.Metrics, callback: Bool, lookups: List<&2, Maybe<&2, T.Entry<K, V>>>, stray: List<&2, T.Entry<K, V>>}

def lookups(~K: Data, ~same: K -> K -> Bool, -V: Data, order: List<&2, K>, +bindings: List<&2, T.Entry<K, V>>) -> List<&2, Maybe<&2, T.Entry<K, V>>>:
  match order:
    case Nil{}: Nil{}
    case Con{+k, tail}: Con{S.find(~K, ~same, V, bindings, k), lookups(~K, ~same, V, tail, bindings)}

def member(~K: Data, ~same: K -> K -> Bool, order: List<&2, K>, +key: K) -> Bool:
  match order:
    case Nil{}: False{}
    case Con{k, tail}: Bool.or(same(k)(key), member(~K, ~same, tail, key))

def keep_stray(-K: Data, -V: Data, entry: T.Entry<K, V>, rest: List<&2, T.Entry<K, V>>, bound: Bool) -> List<&2, T.Entry<K, V>>:
  match bound:
    case True{}: rest
    case False{}: Con{entry, rest}

def stray(~K: Data, ~same: K -> K -> Bool, -V: Data, +order: List<&2, K>, bindings: List<&2, T.Entry<K, V>>) -> List<&2, T.Entry<K, V>>:
  match bindings:
    case Nil{}: Nil{}
    case Con{T.Item{+k, v, d}, tail}: keep_stray(K, V, T.Item{k, v, d}, stray(~K, ~same, V, order, tail), member(~K, ~same, order, k))

def canonical(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>) -> Canonical<K, V>:
  S.Abstract{cap, +bindings, +order, life, counts, cb} = s
  Canon{cap, order, life, counts, cb, lookups(~K, ~same, V, order, bindings), stray(~K, ~same, V, order, bindings)}

def states(~K: Data, ~same: K -> K -> Bool, -V: Data, a: S.Model<K, V>, b: S.Model<K, V>) -> Data:
  {canonical(~K, ~same, V, a) == canonical(~K, ~same, V, b) : Canonical<K, V>}

def observations(~K: Data, ~same: K -> K -> Bool, -V: Data, a: S.Observation<K, V>, b: S.Observation<K, V>) -> Type:
  match a b:
    case S.Observed{as, ai, af, ae} S.Observed{bs, bi, bf, be}:
      states(~K, ~same, V, as, bs) & {ai == bi : Maybe<&2, T.Entry<K, V>>} & {af == bf : Bool} & {ae == be : List<&2, T.Event<K, V>>}
