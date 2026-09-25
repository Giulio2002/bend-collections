import Base
import ../spec/cache.bend as S
import ../spec/operations.bend as O
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./spec_lookup.bend as Lookup

def reflexive(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>) -> E.states(~K, ~same, V, s, s):
  {==}

def symmetric(~K: Data, ~same: K -> K -> Bool, -V: Data, a: S.Model<K, V>, b: S.Model<K, V>, proof: E.states(~K, ~same, V, a, b)) -> E.states(~K, ~same, V, b, a):
  Equal.sym(E.Canonical<K, V>, E.canonical(~K, ~same, V, a), E.canonical(~K, ~same, V, b), proof)

def transitive(~K: Data, ~same: K -> K -> Bool, -V: Data, a: S.Model<K, V>, b: S.Model<K, V>, c: S.Model<K, V>, first: E.states(~K, ~same, V, a, b), second: E.states(~K, ~same, V, b, c)) -> E.states(~K, ~same, V, a, c):
  Equal.trans(E.Canonical<K, V>, E.canonical(~K, ~same, V, a), E.canonical(~K, ~same, V, b), E.canonical(~K, ~same, V, c), first, second)

def string_reflexive(-V: Data, s: S.Model<String, V>) -> E.states(~String, ~Lookup.string_same, V, s, s):
  reflexive(~String, ~Lookup.string_same, V, s)

def string_symmetric(-V: Data, a: S.Model<String, V>, b: S.Model<String, V>, proof: E.states(~String, ~Lookup.string_same, V, a, b)) -> E.states(~String, ~Lookup.string_same, V, b, a):
  symmetric(~String, ~Lookup.string_same, V, a, b, proof)

def string_transitive(-V: Data, a: S.Model<String, V>, b: S.Model<String, V>, c: S.Model<String, V>, first: E.states(~String, ~Lookup.string_same, V, a, b), second: E.states(~String, ~Lookup.string_same, V, b, c)) -> E.states(~String, ~Lookup.string_same, V, a, c):
  transitive(~String, ~Lookup.string_same, V, a, b, c, first, second)

# Configuration updates preserve the finite-map relation without assuming any
# agreement between the two binding-list enumeration orders.
def with_life(-K: Data, -V: Data, c: E.Canonical<K, V>, ns: T.Int64) -> E.Canonical<K, V>:
  E.Canon{cap, o, l, m, f, xs, x} = c
  E.Canon{cap, o, ns, m, f, xs, x}

def recency_length(-K: Data, -V: Data, c: E.Canonical<K, V>) -> Nat:
  E.Canon{cap, o, l, m, f, xs, x} = c
  List.length(&2, K, o)

def set_lifetime(~K: Data, ~same: K -> K -> Bool, -V: Data, a: S.Model<K, V>, b: S.Model<K, V>, +ns: T.Int64, proof: E.states(~K, ~same, V, a, b)) -> E.states(~K, ~same, V, S.set_lifetime(K, V, a, ns), S.set_lifetime(K, V, b, ns)):
  S.Abstract{+ac, +ab, +ao, +al, +am, +af} = a
  S.Abstract{+bc, +bb, +bo, +bl, +bm, +bf} = b
  Equal.cong(E.Canonical<K, V>, E.Canonical<K, V>, c => with_life(K, V, c, ns), E.canonical(~K, ~same, V, S.Abstract{ac, ab, ao, al, am, af}), E.canonical(~K, ~same, V, S.Abstract{bc, bb, bo, bl, bm, bf}), proof)

def length(~K: Data, ~same: K -> K -> Bool, -V: Data, a: S.Model<K, V>, b: S.Model<K, V>, proof: E.states(~K, ~same, V, a, b)) -> {S.length(K, V, a) == S.length(K, V, b) : Nat}:
  S.Abstract{+ac, +ab, +ao, +al, +am, +af} = a
  S.Abstract{+bc, +bb, +bo, +bl, +bm, +bf} = b
  Equal.cong(E.Canonical<K, V>, Nat, c => recency_length(K, V, c), E.canonical(~K, ~same, V, S.Abstract{ac, ab, ao, al, am, af}), E.canonical(~K, ~same, V, S.Abstract{bc, bb, bo, bl, bm, bf}), proof)

def string_set_lifetime(-V: Data, a: S.Model<String, V>, b: S.Model<String, V>, ns: T.Int64, proof: E.states(~String, ~Lookup.string_same, V, a, b)) -> E.states(~String, ~Lookup.string_same, V, S.set_lifetime(String, V, a, ns), S.set_lifetime(String, V, b, ns)):
  set_lifetime(~String, ~Lookup.string_same, V, a, b, ns, proof)

def string_length(-V: Data, a: S.Model<String, V>, b: S.Model<String, V>, proof: E.states(~String, ~Lookup.string_same, V, a, b)) -> {S.length(String, V, a) == S.length(String, V, b) : Nat}:
  length(~String, ~Lookup.string_same, V, a, b, proof)

def observation_reflexive(~K: Data, ~same: K -> K -> Bool, -V: Data, result: S.Observation<K, V>) -> E.observations(~K, ~same, V, result, result):
  S.Observed{s, item, flag, events} = result
  (reflexive(~K, ~same, V, s), {==}, {==}, {==})

def string_observation_reflexive(-V: Data, result: S.Observation<String, V>) -> E.observations(~String, ~Lookup.string_same, V, result, result):
  observation_reflexive(~String, ~Lookup.string_same, V, result)

def miss_counts(counts: T.Metrics, tracked: Bool) -> T.Metrics:
  T.Counts{i, e, r, h, m} = counts
  match tracked:
    case False{}: T.Counts{i, e, r, h, m}
    case True{}: T.Counts{i, e, r, h, Word.inc(64n, m)}

def with_counts(-K: Data, -V: Data, c: E.Canonical<K, V>, counts: T.Metrics) -> E.Canonical<K, V>:
  E.Canon{cap, o, l, m, f, xs, x} = c
  E.Canon{cap, o, l, counts, f, xs, x}

def counts_of(-K: Data, -V: Data, c: E.Canonical<K, V>) -> T.Metrics:
  E.Canon{cap, o, l, m, f, xs, x} = c
  m

def count_miss(~K: Data, ~same: K -> K -> Bool, -V: Data, a: S.Model<K, V>, b: S.Model<K, V>, +tracked: Bool, proof: E.states(~K, ~same, V, a, b)) -> E.states(~K, ~same, V, O.count_miss(K, V, a, tracked), O.count_miss(K, V, b, tracked)):
  S.Abstract{+ac, +ab, +ao, +al, T.Counts{+ai, +ae, +ar, +ah, +am}, +af} = a
  S.Abstract{+bc, +bb, +bo, +bl, T.Counts{+bi, +be, +br, +bh, +bm}, +bf} = b
  match tracked:
    case False{}: proof
    case True{}: Equal.cong(E.Canonical<K, V>, E.Canonical<K, V>, c => with_counts(K, V, c, miss_counts(counts_of(K, V, c), True{})), E.canonical(~K, ~same, V, S.Abstract{ac, ab, ao, al, T.Counts{ai, ae, ar, ah, am}, af}), E.canonical(~K, ~same, V, S.Abstract{bc, bb, bo, bl, T.Counts{bi, be, br, bh, bm}, bf}), proof)

def expired_result(~K: Data, ~same: K -> K -> Bool, -V: Data, a: S.Observation<K, V>, b: S.Observation<K, V>, tracked: Bool, proof: E.observations(~K, ~same, V, a, b)) -> E.observations(~K, ~same, V, O.expired_result(K, V, a, tracked), O.expired_result(K, V, b, tracked)):
  S.Observed{sa, ia, fa, ea} = a
  S.Observed{sb, ib, fb, eb} = b
  (states, items, flags, events) = proof
  (count_miss(~K, ~same, V, sa, sb, tracked, states), items, {==}, events)

def string_expired_result(-V: Data, a: S.Observation<String, V>, b: S.Observation<String, V>, tracked: Bool, proof: E.observations(~String, ~Lookup.string_same, V, a, b)) -> E.observations(~String, ~Lookup.string_same, V, O.expired_result(String, V, a, tracked), O.expired_result(String, V, b, tracked)):
  expired_result(~String, ~Lookup.string_same, V, a, b, tracked, proof)

def from_equal(~K: Data, ~same: K -> K -> Bool, -V: Data, +a: S.Observation<K, V>, b: S.Observation<K, V>, equal: {a == b : S.Observation<K, V>}) -> E.observations(~K, ~same, V, a, b):
  %equal : E.observations(~K, ~same, V, a, _)
  observation_reflexive(~K, ~same, V, a)

def observation_transitive(~K: Data, ~same: K -> K -> Bool, -V: Data, a: S.Observation<K, V>, b: S.Observation<K, V>, c: S.Observation<K, V>, first: E.observations(~K, ~same, V, a, b), second: E.observations(~K, ~same, V, b, c)) -> E.observations(~K, ~same, V, a, c):
  S.Observed{sa, ia, fa, ea} = a
  S.Observed{sb, ib, fb, eb} = b
  S.Observed{sc, ic, fc, ec} = c
  (states1, items1, flags1, events1) = first
  (states2, items2, flags2, events2) = second
  (transitive(~K, ~same, V, sa, sb, sc, states1, states2), Equal.trans(Maybe<&2, T.Entry<K, V>>, ia, ib, ic, items1, items2), Equal.trans(Bool, fa, fb, fc, flags1, flags2), Equal.trans(List<&2, T.LruEvent<K, V>>, ea, eb, ec, events1, events2))
