import Base
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../src/time.bend as Time
import ../src/codec.bend as Codec
import ../types/model.bend as T
import ./cache_store_identities.bend as Store
import ./cache_key_identity.bend as Key
import ./refinement.bend as F
import ./abstraction_recency.bend as Recency

# Refresh stores the key/value of its successful prepared lookup and changes
# only the deadline. The code/key equation is derived from that lookup.
def refresh_at(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, +code: String, entry: T.Entry<K, V>, +lifetime: T.Int64, +now: T.Int64, valid: {F.storage_critbit(K, V, c) == True{} : Bool}, +identities: {Recency.cache_identities(~K, ~encode, V, c) == True{} : Bool}, found: {C.lookup(K, V, c, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}) -> {Recency.cache_identities(~K, ~encode, V, P.refresh_at(K, V, c, code, entry, lifetime, now)) == True{} : Bool}:
  C.State{+cap, +table, +order, +life, T.Counts{+i, +e, +r, +h, +m}, +cb} = c
  T.Item{+key, +value, +deadline} = entry
  Store.store(~K, ~encode, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, code, key, value, Time.deadline(now, lifetime), False{}, Nil{}, Key.lookup_code_identity(~K, ~encode, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, code, T.Item{key, value, deadline}, identities, found), valid, identities)

law string_refresh:
  for -V: Data
  for c: C.Cache<String, V>
  for code: String
  for entry: T.Entry<String, V>
  for lifetime: T.Int64
  for now: T.Int64
  for valid: {F.storage_critbit(String, V, c) == True{} : Bool}
  for identities: {Recency.cache_identities(~String, ~Codec.string_encode, V, c) == True{} : Bool}
  for found: {C.lookup(String, V, c, code) == Some{entry} : Maybe<&2, T.Entry<String, V>>}
  {Recency.cache_identities(~String, ~Codec.string_encode, V, P.refresh_at(String, V, c, code, entry, lifetime, now)) == True{} : Bool}
def string_refresh(V, c, code, entry, lifetime, now, valid, identities, found):
  refresh_at(~String, ~Codec.string_encode, V, c, code, entry, lifetime, now, valid, identities, found)

law integer_refresh:
  for -V: Data
  for c: C.Cache<T.Integer, V>
  for code: String
  for entry: T.Entry<T.Integer, V>
  for lifetime: T.Int64
  for now: T.Int64
  for valid: {F.storage_critbit(T.Integer, V, c) == True{} : Bool}
  for identities: {Recency.cache_identities(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}
  for found: {C.lookup(T.Integer, V, c, code) == Some{entry} : Maybe<&2, T.Entry<T.Integer, V>>}
  {Recency.cache_identities(~T.Integer, ~Codec.integer_encode, V, P.refresh_at(T.Integer, V, c, code, entry, lifetime, now)) == True{} : Bool}
def integer_refresh(V, c, code, entry, lifetime, now, valid, identities, found):
  refresh_at(~T.Integer, ~Codec.integer_encode, V, c, code, entry, lifetime, now, valid, identities, found)

law word64_refresh:
  for -V: Data
  for c: C.Cache<Word(64n), V>
  for code: String
  for entry: T.Entry<Word(64n), V>
  for lifetime: T.Int64
  for now: T.Int64
  for valid: {F.storage_critbit(Word(64n), V, c) == True{} : Bool}
  for identities: {Recency.cache_identities(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}
  for found: {C.lookup(Word(64n), V, c, code) == Some{entry} : Maybe<&2, T.Entry<Word(64n), V>>}
  {Recency.cache_identities(~Word(64n), ~Key.word64_encode, V, P.refresh_at(Word(64n), V, c, code, entry, lifetime, now)) == True{} : Bool}
def word64_refresh(V, c, code, entry, lifetime, now, valid, identities, found):
  refresh_at(~Word(64n), ~Key.word64_encode, V, c, code, entry, lifetime, now, valid, identities, found)

