import Base
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../src/codec.bend as Codec
import ../spec/cache.bend as S
import ../spec/operations.bend as O
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./abstraction_bindings.bend as B
import ./lookup_refinement.bend as L
import ./spec_lookup.bend as Lookup

def branch(~K: Data, ~same: K -> K -> Bool, -V: Data, c: C.Cache<K, V>, key: K, code: String, +now: T.Int64, +tracked: Bool) -> {F.observe(K, V, C.read_found(K, V, c, code, now, tracked, None{})) == O.read_found(~K, ~same, V, F.abstract(K, V, c), key, now, tracked, None{}) : S.Observation<K, V>}:
  C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb} = c
  match tracked:
    case False{}: {==}
    case True{}: {==}

def model_dispatch(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, +key: K, +now: T.Int64, +tracked: Bool, missing: {S.find(~K, ~same, V, B.model_bindings(K, V, s), key) == None{} : Maybe<&2, T.Entry<K, V>>}) -> {O.read(~K, ~same, V, s, key, now, tracked) == O.read_found(~K, ~same, V, s, key, now, tracked, None{}) : S.Observation<K, V>}:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  Equal.cong(Maybe<&2, T.Entry<K, V>>, S.Observation<K, V>, found => O.read_found(~K, ~same, V, S.Abstract{cap, bindings, order, life, counts, cb}, key, now, tracked, found), S.find(~K, ~same, V, bindings, key), None{}, missing)

# Arbitrary represented cache with an absent key, not merely an empty cache.
# Tracked Get increments Misses; untracked Peek/Contains do not. Both preserve
# all bindings, recency, lifetime and other counters, returning no entry/events.
def string_read(-V: Data, +c: C.Cache<String, V>, +key: String, +now: T.Int64, +tracked: Bool, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +missing: {S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), key) == None{} : Maybe<&2, T.Entry<String, V>>}) -> {F.observe(String, V, C.read_encoded(String, V, c, key, now, tracked)) == O.read(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, tracked) : S.Observation<String, V>}:
  native = Equal.trans(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, c, key), S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), key), None{}, L.string_lookup(V, c, key, valid), missing)
  Equal.trans(S.Observation<String, V>, F.observe(String, V, C.read_encoded(String, V, c, key, now, tracked)), F.observe(String, V, C.read_found(String, V, c, key, now, tracked, None{})), O.read(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, tracked), Equal.cong(Maybe<&2, T.Entry<String, V>>, S.Observation<String, V>, found => F.observe(String, V, C.read_found(String, V, c, key, now, tracked, found)), C.lookup(String, V, c, key), None{}, native), Equal.trans(S.Observation<String, V>, F.observe(String, V, C.read_found(String, V, c, key, now, tracked, None{})), O.read_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, tracked, None{}), O.read(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, tracked), branch(~String, ~Lookup.string_same, V, c, key, key, now, tracked), Equal.sym(S.Observation<String, V>, O.read(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, tracked), O.read_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, tracked, None{}), model_dispatch(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, tracked, missing))))

# The facade calls P.read rather than C.read_encoded. This equation connects
# its absent branch, including the no-removal signal, to the proved core branch.
def protocol_branch(-K: Data, -V: Data, c: C.Cache<K, V>, code: String, now: T.Int64, tracked: Bool) -> {P.read_found(K, V, c, code, now, tracked, None{}) == P.Reading{C.read_found(K, V, c, code, now, tracked, None{}), False{}} : P.Read<K, V>}:
  C.State{cap, table, order, life, counts, cb} = c
  {==}

def protocol_missing(-K: Data, -V: Data, +c: C.Cache<K, V>, +code: String, +now: T.Int64, +tracked: Bool, +missing: {C.lookup(K, V, c, code) == None{} : Maybe<&2, T.Entry<K, V>>}) -> {P.read(K, V, c, code, now, tracked) == P.Reading{C.read_encoded(K, V, c, code, now, tracked), False{}} : P.Read<K, V>}:
  %Equal.sym(Maybe<&2, T.Entry<K, V>>, C.lookup(K, V, c, code), None{}, missing) : {P.read_found(K, V, c, code, now, tracked, _) == P.Reading{C.read_found(K, V, c, code, now, tracked, _), False{}} : P.Read<K, V>}
  protocol_branch(K, V, c, code, now, tracked)
