import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./refinement.bend as F
import ./abstraction_identity.bend as Identity
import ./abstraction_recency.bend as Recency

# This contract is required only for custom encoders. The built-in encoders
# instantiate it below using their checked inverses, not a hash assumption.
def injective(~K: Data, ~encode: K -> String) -> Type:
  @a: K -> @b: K -> {encode(a) == encode(b) : String} -> {a == b : K}

def lookup_code_identity(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, +code: String, +entry: T.Entry<K, V>, identities: {Recency.cache_identities(~K, ~encode, V, c) == True{} : Bool}, found: {C.lookup(K, V, c, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}) -> {code == Identity.entry_code(~K, ~encode, V, entry) : String}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  Identity.listed_identity(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table), code, entry, identities, F.lookup_enumerated(K, V, cap, table, order, life, counts, cb, code, entry, found))

# A successful actual lookup at encode(key) retains exactly that original key.
# No capacity, expiry or returned-value refinement is claimed by this fact.
def lookup_original_key(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, +key: K, +original: K, value: V, deadline: T.Int64, contract: injective(~K, ~encode), identities: {Recency.cache_identities(~K, ~encode, V, c) == True{} : Bool}, found: {C.lookup(K, V, c, encode(key)) == Some{T.Item{original, value, deadline}} : Maybe<&2, T.Entry<K, V>>}) -> {key == original : K}:
  contract(key, original, lookup_code_identity(~K, ~encode, V, c, encode(key), T.Item{original, value, deadline}, identities, found))

law string_lookup_key:
  for -V: Data
  for c: C.Cache<String, V>
  for key: String
  for original: String
  for value: V
  for deadline: T.Int64
  for identities: {Recency.cache_identities(~String, ~Codec.string_encode, V, c) == True{} : Bool}
  for found: {C.lookup(String, V, c, Codec.string_encode(key)) == Some{T.Item{original, value, deadline}} : Maybe<&2, T.Entry<String, V>>}
  {key == original : String}
def string_lookup_key(V, c, key, original, value, deadline, identities, found):
  lookup_original_key(~String, ~Codec.string_encode, V, c, key, original, value, deadline, a => b => e => e, identities, found)

law integer_lookup_key:
  for -V: Data
  for c: C.Cache<T.Integer, V>
  for key: T.Integer
  for original: T.Integer
  for value: V
  for deadline: T.Int64
  for identities: {Recency.cache_identities(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}
  for found: {C.lookup(T.Integer, V, c, Codec.integer_encode(key)) == Some{T.Item{original, value, deadline}} : Maybe<&2, T.Entry<T.Integer, V>>}
  {key == original : T.Integer}
def integer_lookup_key(V, c, key, original, value, deadline, identities, found):
  lookup_original_key(~T.Integer, ~Codec.integer_encode, V, c, key, original, value, deadline, Codec.integer_injective, identities, found)

# This is the mathematical word encoder used by the host's signed/unsigned
# codecs. BigInt-to-Word and host String conversion remain separate obligations.
def word64_encode(w: Word(64n)) -> String:
  Codec.word_encode(64n, w)

law word64_lookup_key:
  for -V: Data
  for c: C.Cache<Word(64n), V>
  for key: Word(64n)
  for original: Word(64n)
  for value: V
  for deadline: T.Int64
  for identities: {Recency.cache_identities(~Word(64n), ~word64_encode, V, c) == True{} : Bool}
  for found: {C.lookup(Word(64n), V, c, word64_encode(key)) == Some{T.Item{original, value, deadline}} : Maybe<&2, T.Entry<Word(64n), V>>}
  {key == original : Word(64n)}
def word64_lookup_key(V, c, key, original, value, deadline, identities, found):
  lookup_original_key(~Word(64n), ~word64_encode, V, c, key, original, value, deadline, Codec.word_injective(64n), identities, found)
