import Base
import ../spec/cache.bend as S
import ../spec/operations.bend as O
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./spec_lookup.bend as Lookup
import ./spec_write_lookup.bend as Write
import ./abstraction_bindings.bend as B
import ./store_lookup_refinement.bend as Store
import ./recency_unique.bend as Unique
import ./canonical.bend as Can
import ./canonical_string.bend as CS
import ./extensional_states.bend as Ext

def same(-V: Data, +a: S.Model<String, V>, +b: S.Model<String, V>, +key: String, +value: V, +deadline: T.Int64, +flag: Bool, +events: List<&2, T.Event<String, V>>) -> {Store.target(V, a, key, value, deadline, flag, events, key) == Store.target(V, b, key, value, deadline, flag, events, key) : Maybe<&2, T.Entry<String, V>>}:
  Equal.trans(Maybe<&2, T.Entry<String, V>>, Store.target(V, a, key, value, deadline, flag, events, key), Some{T.Item{key, value, deadline}}, Store.target(V, b, key, value, deadline, flag, events, key), Write.same(V, a, key, value, deadline, flag, events), Equal.sym(Maybe<&2, T.Entry<String, V>>, Store.target(V, b, key, value, deadline, flag, events, key), Some{T.Item{key, value, deadline}}, Write.same(V, b, key, value, deadline, flag, events)))

def other(-V: Data, +a: S.Model<String, V>, +b: S.Model<String, V>, +key: String, +value: V, +deadline: T.Int64, +flag: Bool, +events: List<&2, T.Event<String, V>>, +query: String, +different: {String.eq(key, query) == False{} : Bool}, equal: {S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, a), query) == S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, b), query) : Maybe<&2, T.Entry<String, V>>}) -> {Store.target(V, a, key, value, deadline, flag, events, query) == Store.target(V, b, key, value, deadline, flag, events, query) : Maybe<&2, T.Entry<String, V>>}:
  Equal.trans(Maybe<&2, T.Entry<String, V>>, Store.target(V, a, key, value, deadline, flag, events, query), S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, a), query), Store.target(V, b, key, value, deadline, flag, events, query), Write.other(V, a, key, value, deadline, flag, events, query, different), Equal.trans(Maybe<&2, T.Entry<String, V>>, S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, a), query), S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, b), query), Store.target(V, b, key, value, deadline, flag, events, query), equal, Equal.sym(Maybe<&2, T.Entry<String, V>>, Store.target(V, b, key, value, deadline, flag, events, query), S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, b), query), Write.other(V, b, key, value, deadline, flag, events, query, different))))

def decide(-V: Data, +a: S.Model<String, V>, +b: S.Model<String, V>, +key: String, +value: V, +deadline: T.Int64, +flag: Bool, +events: List<&2, T.Event<String, V>>, +query: String, equal: {S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, a), query) == S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, b), query) : Maybe<&2, T.Entry<String, V>>}, matched: Bool, checked: {String.eq(key, query) == matched : Bool}) -> {Store.target(V, a, key, value, deadline, flag, events, query) == Store.target(V, b, key, value, deadline, flag, events, query) : Maybe<&2, T.Entry<String, V>>}:
  match matched:
    case False{}: other(V, a, b, key, value, deadline, flag, events, query, checked, equal)
    case True{}:
      %Unique.equal_boolean(key, query, checked) : {Store.target(V, a, key, value, deadline, flag, events, _) == Store.target(V, b, key, value, deadline, flag, events, _) : Maybe<&2, T.Entry<String, V>>}
      same(V, a, b, key, value, deadline, flag, events)

def inserts(counts: T.Metrics) -> T.Metrics:
  T.Counts{i, e, r, h, m} = counts
  T.Counts{Word.inc(64n, i), e, r, h, m}

def written(-V: Data, +c: E.Canonical<String, V>, +key: String, value: V, deadline: T.Int64) -> E.Canonical<String, V>:
  Can.c_write(~String, ~Lookup.string_same, V, Ext.with_counts(String, V, c, inserts(Ext.counts_of(String, V, c))), key, value, deadline)

def observation(-V: Data, +a: S.Model<String, V>, +b: S.Model<String, V>, +key: String, +value: V, +deadline: T.Int64, +flag: Bool, +events: List<&2, T.Event<String, V>>, proof: E.states(~String, ~Lookup.string_same, V, a, b)) -> E.observations(~String, ~Lookup.string_same, V, O.write(~String, ~Lookup.string_same, V, a, key, value, deadline, flag, events), O.write(~String, ~Lookup.string_same, V, b, key, value, deadline, flag, events)):
  S.Abstract{+ac, +ab, +ao, +al, T.Counts{+ai, +ae, +ar, +ah, +am}, +af} = a
  S.Abstract{+bc, +bb, +bo, +bl, T.Counts{+bi, +be, +br, +bh, +bm}, +bf} = b
  (Equal.trans(E.Canonical<String, V>, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{ac, Con{T.Item{key, value, deadline}, S.erase(~String, ~Lookup.string_same, V, ab, key)}, Can.moved(~String, ~Lookup.string_same, ao, key), al, T.Counts{Word.inc(64n, ai), ae, ar, ah, am}, af}), written(V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{ac, ab, ao, al, T.Counts{ai, ae, ar, ah, am}, af}), key, value, deadline), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{bc, Con{T.Item{key, value, deadline}, S.erase(~String, ~Lookup.string_same, V, bb, key)}, Can.moved(~String, ~Lookup.string_same, bo, key), bl, T.Counts{Word.inc(64n, bi), be, br, bh, bm}, bf}), CS.write_transform(V, ac, ab, ao, al, T.Counts{Word.inc(64n, ai), ae, ar, ah, am}, af, key, value, deadline), Equal.trans(E.Canonical<String, V>, written(V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{ac, ab, ao, al, T.Counts{ai, ae, ar, ah, am}, af}), key, value, deadline), written(V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{bc, bb, bo, bl, T.Counts{bi, be, br, bh, bm}, bf}), key, value, deadline), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{bc, Con{T.Item{key, value, deadline}, S.erase(~String, ~Lookup.string_same, V, bb, key)}, Can.moved(~String, ~Lookup.string_same, bo, key), bl, T.Counts{Word.inc(64n, bi), be, br, bh, bm}, bf}), Equal.cong(E.Canonical<String, V>, E.Canonical<String, V>, c => written(V, c, key, value, deadline), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{ac, ab, ao, al, T.Counts{ai, ae, ar, ah, am}, af}), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{bc, bb, bo, bl, T.Counts{bi, be, br, bh, bm}, bf}), proof), Equal.sym(E.Canonical<String, V>, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{bc, Con{T.Item{key, value, deadline}, S.erase(~String, ~Lookup.string_same, V, bb, key)}, Can.moved(~String, ~Lookup.string_same, bo, key), bl, T.Counts{Word.inc(64n, bi), be, br, bh, bm}, bf}), written(V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{bc, bb, bo, bl, T.Counts{bi, be, br, bh, bm}, bf}), key, value, deadline), CS.write_transform(V, bc, bb, bo, bl, T.Counts{Word.inc(64n, bi), be, br, bh, bm}, bf, key, value, deadline)))), {==}, {==}, {==})
