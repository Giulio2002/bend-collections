import Base
import ../src/cache.bend as C
import ../src/time.bend as Time
import ../src/codec.bend as Codec
import ../spec/cache.bend as S
import ../spec/numeric.bend as N
import ../spec/operations.bend as O
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./abstraction_bindings.bend as B
import ./lookup_refinement.bend as L
import ./spec_lookup.bend as Lookup
import ./numeric.bend as Numeric

def entry_deadline(-K: Data, -V: Data, entry: T.Entry<K, V>) -> T.Int64:
  T.Item{key, value, d} = entry
  d

def live(~K: Data, ~same: K -> K -> Bool, -V: Data, c: C.Cache<K, V>, key: K, code: String, entry: T.Entry<K, V>) -> {F.observe(K, V, C.read_expiry(K, V, c, code, entry, False{}, False{})) == O.read_decide(~K, ~same, V, F.abstract(K, V, c), key, entry, False{}, False{}) : S.Observation<K, V>}:
  C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb} = c
  {==}

def found(~K: Data, ~same: K -> K -> Bool, -V: Data, +c: C.Cache<K, V>, +key: K, +code: String, +now: T.Int64, entry: T.Entry<K, V>, +alive: {N.expired(entry_deadline(K, V, entry), now) == False{} : Bool}) -> {F.observe(K, V, C.read_found(K, V, c, code, now, False{}, Some{entry})) == O.read_found(~K, ~same, V, F.abstract(K, V, c), key, now, False{}, Some{entry}) : S.Observation<K, V>}:
  T.Item{+original, +value, +expiry} = entry
  native = Equal.trans(Bool, Time.expired(expiry, now), N.expired(expiry, now), False{}, Numeric.expiration_refines(expiry, now), alive)
  Equal.trans(S.Observation<K, V>, F.observe(K, V, C.read_found(K, V, c, code, now, False{}, Some{T.Item{original, value, expiry}})), F.observe(K, V, C.read_expiry(K, V, c, code, T.Item{original, value, expiry}, False{}, False{})), O.read_found(~K, ~same, V, F.abstract(K, V, c), key, now, False{}, Some{T.Item{original, value, expiry}}), Equal.cong(Bool, S.Observation<K, V>, expired => F.observe(K, V, C.read_expiry(K, V, c, code, T.Item{original, value, expiry}, False{}, expired)), Time.expired(expiry, now), False{}, native), Equal.trans(S.Observation<K, V>, F.observe(K, V, C.read_expiry(K, V, c, code, T.Item{original, value, expiry}, False{}, False{})), O.read_decide(~K, ~same, V, F.abstract(K, V, c), key, T.Item{original, value, expiry}, False{}, False{}), O.read_found(~K, ~same, V, F.abstract(K, V, c), key, now, False{}, Some{T.Item{original, value, expiry}}), live(~K, ~same, V, c, key, code, T.Item{original, value, expiry}), Equal.cong(Bool, S.Observation<K, V>, expired => O.read_decide(~K, ~same, V, F.abstract(K, V, c), key, T.Item{original, value, expiry}, False{}, expired), False{}, N.expired(expiry, now), Equal.sym(Bool, N.expired(expiry, now), False{}, alive))))

def string_found(-V: Data, c: C.Cache<String, V>, +key: String, now: T.Int64, entry: T.Entry<String, V>, alive: {N.expired(entry_deadline(String, V, entry), now) == False{} : Bool}) -> {F.observe(String, V, C.read_found(String, V, c, key, now, False{}, Some{entry})) == O.read_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, False{}, Some{entry}) : S.Observation<String, V>}:
  found(~String, ~Lookup.string_same, V, c, key, key, now, entry, alive)

def model_dispatch(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, +key: K, now: T.Int64, entry: T.Entry<K, V>, present: {S.find(~K, ~same, V, B.model_bindings(K, V, s), key) == Some{entry} : Maybe<&2, T.Entry<K, V>>}) -> {O.read(~K, ~same, V, s, key, now, False{}) == O.read_found(~K, ~same, V, s, key, now, False{}, Some{entry}) : S.Observation<K, V>}:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  Equal.cong(Maybe<&2, T.Entry<K, V>>, S.Observation<K, V>, item => O.read_found(~K, ~same, V, S.Abstract{cap, bindings, order, life, counts, cb}, key, now, False{}, item), S.find(~K, ~same, V, bindings, key), Some{entry}, present)

# Actual encoded read, with lookup and expiration branch conditions discharged
# from the independent model. Host result projection remains a separate bridge.
def string_read(-V: Data, +c: C.Cache<String, V>, +key: String, +now: T.Int64, +entry: T.Entry<String, V>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +present: {S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), key) == Some{entry} : Maybe<&2, T.Entry<String, V>>}, alive: {N.expired(entry_deadline(String, V, entry), now) == False{} : Bool}) -> {F.observe(String, V, C.read_encoded(String, V, c, key, now, False{})) == O.read(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, False{}) : S.Observation<String, V>}:
  native = Equal.trans(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, c, key), S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), key), Some{entry}, L.string_lookup(V, c, key, valid), present)
  Equal.trans(S.Observation<String, V>, F.observe(String, V, C.read_encoded(String, V, c, key, now, False{})), F.observe(String, V, C.read_found(String, V, c, key, now, False{}, Some{entry})), O.read(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, False{}), Equal.cong(Maybe<&2, T.Entry<String, V>>, S.Observation<String, V>, item => F.observe(String, V, C.read_found(String, V, c, key, now, False{}, item)), C.lookup(String, V, c, key), Some{entry}, native), Equal.trans(S.Observation<String, V>, F.observe(String, V, C.read_found(String, V, c, key, now, False{}, Some{entry})), O.read_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, False{}, Some{entry}), O.read(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, False{}), string_found(V, c, key, now, entry, alive), Equal.sym(S.Observation<String, V>, O.read(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, False{}), O.read_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, False{}, Some{entry}), model_dispatch(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, entry, present))))
