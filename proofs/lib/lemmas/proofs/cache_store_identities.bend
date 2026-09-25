import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../types/model.bend as T
import ./cache_store_identity.bend as Point
import ./map_lookup.bend as L
import ./enumeration_suffix.bend as Suffix
import ./invariants.bend as Inv
import ./refinement.bend as F
import ./abstraction_recency.bend as Recency
import ./abstraction_size.bend as Size
import ./representation_parts.bend as Parts
import ./map_populated_inverse.bend as Inverse
import ./map_populated.bend as NativePop
import ./cache_populated.bend as Pop
import ./map_key_membership.bend as Keys
import ./map_routing.bend as R
import ./map_delete_prefix.bend as And
import ./cache_key_identity.bend as Key

# Structural induction over the actual native enumeration. The prefix equation
# ties every visited binding to the actual output map, rather than an oracle.
def suffix(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, +key: K, +value: V, +deadline: T.Int64, +flag: Bool, +events: List<&2, T.LruEvent<K, V>>, xs: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>, +prefix: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>, +fresh: {code == encode(key) : String}, +valid: {F.storage_critbit(K, V, c) == True{} : Bool}, +identities: {Recency.cache_identities(~K, ~encode, V, c) == True{} : Bool}, packed: {Size.packed(K, V, xs) == True{} : Bool}, +whole: {List.append(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, prefix, xs) == Suffix.entries(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events))) : List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>}) -> {Inv.identities(~K, ~encode, V, xs) == True{} : Bool}:
  match xs:
    case Nil{}: {==}
    case Con{Tuple{stored, None{}}, tail}:
      Empty.absurd({Inv.identities(~K, ~encode, V, Con{Tuple{stored, None{}}, tail}) == True{} : Bool}, R.false_true(packed))
    case Con{Tuple{+stored, Some{T.Item{+original, +old_value, +old_deadline}}}, +tail}:
      binding = Suffix.lookup(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events)), stored, T.Item{original, old_value, old_deadline}, F.store_preserves_storage_critbit(K, V, c, code, key, value, deadline, flag, events, valid), %whole : L.listed(T.Entry<K, V>, _, stored, T.Item{original, old_value, old_deadline}) Suffix.listed_prefix(T.Entry<K, V>, prefix, Con{Tuple{stored, Some{T.Item{original, old_value, old_deadline}}}, tail}, stored, T.Item{original, old_value, old_deadline}, Inl{({==}, {==})}))
      identity = Point.store(~K, ~encode, V, c, code, key, value, deadline, flag, events, stored, T.Item{original, old_value, old_deadline}, fresh, valid, identities, binding)
      And.conjunction(String.eq(stored, encode(original)), Inv.identities(~K, ~encode, V, tail), Keys.eq_true(stored, encode(original), identity), suffix(~K, ~encode, V, c, code, key, value, deadline, flag, events, tail, List.append(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, prefix, Con{Tuple{stored, Some{T.Item{original, old_value, old_deadline}}}, Nil{}}), fresh, valid, identities, packed, Equal.trans(List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>, List.append(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, List.append(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, prefix, Con{Tuple{stored, Some{T.Item{original, old_value, old_deadline}}}, Nil{}}), tail), List.append(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, prefix, Con{Tuple{stored, Some{T.Item{original, old_value, old_deadline}}}, tail}), Suffix.entries(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events))), Equal.sym(List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>, List.append(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, prefix, Con{Tuple{stored, Some{T.Item{original, old_value, old_deadline}}}, tail}), List.append(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, List.append(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, prefix, Con{Tuple{stored, Some{T.Item{original, old_value, old_deadline}}}, Nil{}}), tail), Suffix.append_cons(Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, prefix, Tuple{stored, Some{T.Item{original, old_value, old_deadline}}}, tail)), whole)))

def stored_packed(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, +code: String, +key: K, +value: V, +deadline: T.Int64, flag: Bool, events: List<&2, T.LruEvent<K, V>>, identities: {Recency.cache_identities(~K, ~encode, V, c) == True{} : Bool}) -> {Size.packed(K, V, Suffix.entries(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events)))) == True{} : Bool}:
  C.State{cap, +table, order, life, T.Counts{i, e, r, h, m}, cb} = c
  Size.enumerated_populated(K, V, Map.set(&2, Maybe<&2, T.Entry<K, V>>, table, code, Some{T.Item{key, value, deadline}}), Nil{}, NativePop.set_preserves_populated(T.Entry<K, V>, table, code, Some{T.Item{key, value, deadline}}, {==}, Inverse.packed_tree(K, V, table, Parts.identities_packed(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table), identities))), {==})

def finish(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, proof: {Inv.identities(~K, ~encode, V, Suffix.entries(K, V, c)) == True{} : Bool}) -> {Recency.cache_identities(~K, ~encode, V, c) == True{} : Bool}:
  C.State{cap, table, order, life, counts, cb} = c
  proof

def store(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, +key: K, +value: V, +deadline: T.Int64, +flag: Bool, +events: List<&2, T.LruEvent<K, V>>, +fresh: {code == encode(key) : String}, +valid: {F.storage_critbit(K, V, c) == True{} : Bool}, +identities: {Recency.cache_identities(~K, ~encode, V, c) == True{} : Bool}) -> {Recency.cache_identities(~K, ~encode, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events))) == True{} : Bool}:
  finish(~K, ~encode, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events)), suffix(~K, ~encode, V, c, code, key, value, deadline, flag, events, Suffix.entries(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events))), Nil{}, fresh, valid, identities, stored_packed(~K, ~encode, V, c, code, key, value, deadline, flag, events, identities), {==}))

def string_store(-V: Data, +c: C.Cache<String, V>, +code: String, +key: String, +value: V, +deadline: T.Int64, +flag: Bool, +events: List<&2, T.LruEvent<String, V>>, +fresh: {code == Codec.string_encode(key) : String}, +valid: {F.storage_critbit(String, V, c) == True{} : Bool}, +identities: {Recency.cache_identities(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {Recency.cache_identities(~String, ~Codec.string_encode, V, C.step_cache(String, V, C.store(String, V, c, code, key, value, deadline, flag, events))) == True{} : Bool}:
  store(~String, ~Codec.string_encode, V, c, code, key, value, deadline, flag, events, fresh, valid, identities)

def integer_store(-V: Data, +c: C.Cache<T.Integer, V>, +code: String, +key: T.Integer, +value: V, +deadline: T.Int64, +flag: Bool, +events: List<&2, T.LruEvent<T.Integer, V>>, +fresh: {code == Codec.integer_encode(key) : String}, +valid: {F.storage_critbit(T.Integer, V, c) == True{} : Bool}, +identities: {Recency.cache_identities(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}) -> {Recency.cache_identities(~T.Integer, ~Codec.integer_encode, V, C.step_cache(T.Integer, V, C.store(T.Integer, V, c, code, key, value, deadline, flag, events))) == True{} : Bool}:
  store(~T.Integer, ~Codec.integer_encode, V, c, code, key, value, deadline, flag, events, fresh, valid, identities)

def word64_store(-V: Data, +c: C.Cache<Word(64n), V>, +code: String, +key: Word(64n), +value: V, +deadline: T.Int64, +flag: Bool, +events: List<&2, T.LruEvent<Word(64n), V>>, +fresh: {code == Key.word64_encode(key) : String}, +valid: {F.storage_critbit(Word(64n), V, c) == True{} : Bool}, +identities: {Recency.cache_identities(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}) -> {Recency.cache_identities(~Word(64n), ~Key.word64_encode, V, C.step_cache(Word(64n), V, C.store(Word(64n), V, c, code, key, value, deadline, flag, events))) == True{} : Bool}:
  store(~Word(64n), ~Key.word64_encode, V, c, code, key, value, deadline, flag, events, fresh, valid, identities)

