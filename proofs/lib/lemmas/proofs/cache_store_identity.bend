import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../types/model.bend as T
import ./refinement.bend as F
import ./cache_key_identity.bend as Key
import ./abstraction_identity.bend as Identity
import ./abstraction_recency.bend as Recency
import ./recency_unique.bend as Unique

# Pointwise identity of every successful lookup after the actual store. This
# includes replacement and unrelated bindings; enumeration-wide preservation
# is a separate obligation.
def branch(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, +key: K, +value: V, +deadline: T.Int64, +flag: Bool, +events: List<&2, T.LruEvent<K, V>>, +query: String, +entry: T.Entry<K, V>, equal: Bool, decision: {String.eq(query, code) == equal : Bool}, fresh: {code == encode(key) : String}, valid: {F.storage_critbit(K, V, c) == True{} : Bool}, identities: {Recency.cache_identities(~K, ~encode, V, c) == True{} : Bool}, result: {C.lookup(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events)), query) == Some{entry} : Maybe<&2, T.Entry<K, V>>}) -> {query == Identity.entry_code(~K, ~encode, V, entry) : String}:
  match equal:
    case False{}:
      Key.lookup_code_identity(~K, ~encode, V, c, query, entry, identities, Equal.trans(Maybe<&2, T.Entry<K, V>>, C.lookup(K, V, c, query), C.lookup(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events)), query), Some{entry}, Equal.sym(Maybe<&2, T.Entry<K, V>>, C.lookup(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events)), query), C.lookup(K, V, c, query), F.store_other_lookup(K, V, c, code, key, value, deadline, flag, events, query, decision, valid)), result))
    case True{}:
      +same = Unique.equal_boolean(query, code, decision)
      payload = Equal.trans(Maybe<&2, T.Entry<K, V>>, Some{T.Item{key, value, deadline}}, C.lookup(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events)), code), Some{entry}, Equal.sym(Maybe<&2, T.Entry<K, V>>, C.lookup(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events)), code), Some{T.Item{key, value, deadline}}, F.store_lookup(K, V, c, code, key, value, deadline, flag, events)), %same : {C.lookup(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events)), _) == Some{entry} : Maybe<&2, T.Entry<K, V>>} result)
      Equal.trans(String, query, encode(key), Identity.entry_code(~K, ~encode, V, entry), Equal.trans(String, query, code, encode(key), same, fresh), Equal.cong(T.Entry<K, V>, String, e => Identity.entry_code(~K, ~encode, V, e), T.Item{key, value, deadline}, entry, Equal.cong(Maybe<&2, T.Entry<K, V>>, T.Entry<K, V>, e => Maybe.default(&2, T.Entry<K, V>, e, entry), Some{T.Item{key, value, deadline}}, Some{entry}, payload)))

def store(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, +key: K, +value: V, +deadline: T.Int64, +flag: Bool, +events: List<&2, T.LruEvent<K, V>>, +query: String, +entry: T.Entry<K, V>, fresh: {code == encode(key) : String}, valid: {F.storage_critbit(K, V, c) == True{} : Bool}, identities: {Recency.cache_identities(~K, ~encode, V, c) == True{} : Bool}, result: {C.lookup(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events)), query) == Some{entry} : Maybe<&2, T.Entry<K, V>>}) -> {query == Identity.entry_code(~K, ~encode, V, entry) : String}:
  branch(~K, ~encode, V, c, code, key, value, deadline, flag, events, query, entry, String.eq(query, code), {==}, fresh, valid, identities, result)

def string_store(-V: Data, +c: C.Cache<String, V>, +code: String, +key: String, +value: V, +deadline: T.Int64, +flag: Bool, +events: List<&2, T.LruEvent<String, V>>, +query: String, +entry: T.Entry<String, V>, fresh: {code == Codec.string_encode(key) : String}, valid: {F.storage_critbit(String, V, c) == True{} : Bool}, identities: {Recency.cache_identities(~String, ~Codec.string_encode, V, c) == True{} : Bool}, result: {C.lookup(String, V, C.step_cache(String, V, C.store(String, V, c, code, key, value, deadline, flag, events)), query) == Some{entry} : Maybe<&2, T.Entry<String, V>>}) -> {query == Identity.entry_code(~String, ~Codec.string_encode, V, entry) : String}:
  store(~String, ~Codec.string_encode, V, c, code, key, value, deadline, flag, events, query, entry, fresh, valid, identities, result)

def integer_store(-V: Data, +c: C.Cache<T.Integer, V>, +code: String, +key: T.Integer, +value: V, +deadline: T.Int64, +flag: Bool, +events: List<&2, T.LruEvent<T.Integer, V>>, +query: String, +entry: T.Entry<T.Integer, V>, fresh: {code == Codec.integer_encode(key) : String}, valid: {F.storage_critbit(T.Integer, V, c) == True{} : Bool}, identities: {Recency.cache_identities(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}, result: {C.lookup(T.Integer, V, C.step_cache(T.Integer, V, C.store(T.Integer, V, c, code, key, value, deadline, flag, events)), query) == Some{entry} : Maybe<&2, T.Entry<T.Integer, V>>}) -> {query == Identity.entry_code(~T.Integer, ~Codec.integer_encode, V, entry) : String}:
  store(~T.Integer, ~Codec.integer_encode, V, c, code, key, value, deadline, flag, events, query, entry, fresh, valid, identities, result)

def word64_store(-V: Data, +c: C.Cache<Word(64n), V>, +code: String, +key: Word(64n), +value: V, +deadline: T.Int64, +flag: Bool, +events: List<&2, T.LruEvent<Word(64n), V>>, +query: String, +entry: T.Entry<Word(64n), V>, fresh: {code == Key.word64_encode(key) : String}, valid: {F.storage_critbit(Word(64n), V, c) == True{} : Bool}, identities: {Recency.cache_identities(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}, result: {C.lookup(Word(64n), V, C.step_cache(Word(64n), V, C.store(Word(64n), V, c, code, key, value, deadline, flag, events)), query) == Some{entry} : Maybe<&2, T.Entry<Word(64n), V>>}) -> {query == Identity.entry_code(~Word(64n), ~Key.word64_encode, V, entry) : String}:
  store(~Word(64n), ~Key.word64_encode, V, c, code, key, value, deadline, flag, events, query, entry, fresh, valid, identities, result)

