import Base
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../src/codec.bend as Codec
import ../types/model.bend as T
import ./enumeration_suffix.bend as Suffix
import ./map_lookup.bend as L
import ./map_enumeration.bend as E
import ./map_delete_frame.bend as Delete
import ./map_delete_populated.bend as Pop
import ./invariants.bend as Inv
import ./abstraction_identity.bend as Identity
import ./abstraction_recency.bend as Recency
import ./abstraction_size.bend as Size
import ./representation_parts.bend as Parts
import ./map_populated_inverse.bend as Inverse
import ./map_key_membership.bend as Keys
import ./map_routing.bend as R
import ./map_delete_prefix.bend as And
import ./cache_key_identity.bend as Key

# Deletion can only retain original bindings. No validity or injectivity
# assumption is needed to preserve this value/key identity property.
def suffix(~K: Data, ~encode: K -> String, -V: Data, +tree: Map<&2, Maybe<&2, T.Entry<K, V>>>, +removed: String, xs: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>, +prefix: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>, +identities: {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, tree)) == True{} : Bool}, packed: {Size.packed(K, V, xs) == True{} : Bool}, +whole: {List.append(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, prefix, xs) == Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, Map.del(&2, Maybe<&2, T.Entry<K, V>>, tree, removed)) : List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>}) -> {Inv.identities(~K, ~encode, V, xs) == True{} : Bool}:
  match xs:
    case Nil{}: {==}
    case Con{Tuple{stored, None{}}, tail}:
      Empty.absurd({Inv.identities(~K, ~encode, V, Con{Tuple{stored, None{}}, tail}) == True{} : Bool}, R.false_true(packed))
    case Con{Tuple{+stored, Some{T.Item{+original, +value, +deadline}}}, +tail}:
      retained = Delete.no_new_binding(T.Entry<K, V>, tree, removed, stored, T.Item{original, value, deadline}, E.enumerated_is_leaf(T.Entry<K, V>, Map.del(&2, Maybe<&2, T.Entry<K, V>>, tree, removed), stored, T.Item{original, value, deadline}, %whole : L.listed(T.Entry<K, V>, _, stored, T.Item{original, value, deadline}) Suffix.listed_prefix(T.Entry<K, V>, prefix, Con{Tuple{stored, Some{T.Item{original, value, deadline}}}, tail}, stored, T.Item{original, value, deadline}, Inl{({==}, {==})})))
      identity = Identity.listed_identity(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, tree), stored, T.Item{original, value, deadline}, identities, L.leaf_enumerated(T.Entry<K, V>, tree, Nil{}, stored, T.Item{original, value, deadline}, retained))
      And.conjunction(String.eq(stored, encode(original)), Inv.identities(~K, ~encode, V, tail), Keys.eq_true(stored, encode(original), identity), suffix(~K, ~encode, V, tree, removed, tail, List.append(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, prefix, Con{Tuple{stored, Some{T.Item{original, value, deadline}}}, Nil{}}), identities, packed, Equal.trans(List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>, List.append(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, List.append(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, prefix, Con{Tuple{stored, Some{T.Item{original, value, deadline}}}, Nil{}}), tail), List.append(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, prefix, Con{Tuple{stored, Some{T.Item{original, value, deadline}}}, tail}), Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, Map.del(&2, Maybe<&2, T.Entry<K, V>>, tree, removed)), Equal.sym(List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>, List.append(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, prefix, Con{Tuple{stored, Some{T.Item{original, value, deadline}}}, tail}), List.append(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, List.append(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, prefix, Con{Tuple{stored, Some{T.Item{original, value, deadline}}}, Nil{}}), tail), Suffix.append_cons(Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, prefix, Tuple{stored, Some{T.Item{original, value, deadline}}}, tail)), whole)))

def delete(~K: Data, ~encode: K -> String, -V: Data, +tree: Map<&2, Maybe<&2, T.Entry<K, V>>>, +removed: String, +identities: {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, tree)) == True{} : Bool}) -> {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, Map.del(&2, Maybe<&2, T.Entry<K, V>>, tree, removed))) == True{} : Bool}:
  suffix(~K, ~encode, V, tree, removed, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, Map.del(&2, Maybe<&2, T.Entry<K, V>>, tree, removed)), Nil{}, identities, Size.enumerated_populated(K, V, Map.del(&2, Maybe<&2, T.Entry<K, V>>, tree, removed), Nil{}, Pop.preserves_populated(T.Entry<K, V>, tree, removed, Inverse.packed_tree(K, V, tree, Parts.identities_packed(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, tree), identities))), {==}), {==})

def remove_present(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, removed: String, evict: Bool, entry: T.Entry<K, V>, identities: {Recency.cache_identities(~K, ~encode, V, c) == True{} : Bool}) -> {Recency.cache_identities(~K, ~encode, V, C.step_cache(K, V, C.remove_present(K, V, c, removed, evict, entry))) == True{} : Bool}:
  C.State{cap, table, order, life, counts, cb} = c
  delete(~K, ~encode, V, table, removed, identities)

def detach_present(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, removed: String, entry: T.Entry<K, V>, identities: {Recency.cache_identities(~K, ~encode, V, c) == True{} : Bool}) -> {Recency.cache_identities(~K, ~encode, V, C.step_cache(K, V, P.detach_present(K, V, c, removed, entry))) == True{} : Bool}:
  C.State{cap, table, order, life, counts, cb} = c
  delete(~K, ~encode, V, table, removed, identities)

def string_delete(-V: Data, +tree: Map<&2, Maybe<&2, T.Entry<String, V>>>, +removed: String, identities: {Inv.identities(~String, ~Codec.string_encode, V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, tree)) == True{} : Bool}) -> {Inv.identities(~String, ~Codec.string_encode, V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, Map.del(&2, Maybe<&2, T.Entry<String, V>>, tree, removed))) == True{} : Bool}:
  delete(~String, ~Codec.string_encode, V, tree, removed, identities)

def string_remove_present(-V: Data, c: C.Cache<String, V>, removed: String, evict: Bool, entry: T.Entry<String, V>, identities: {Recency.cache_identities(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {Recency.cache_identities(~String, ~Codec.string_encode, V, C.step_cache(String, V, C.remove_present(String, V, c, removed, evict, entry))) == True{} : Bool}:
  remove_present(~String, ~Codec.string_encode, V, c, removed, evict, entry, identities)

def string_detach_present(-V: Data, c: C.Cache<String, V>, removed: String, entry: T.Entry<String, V>, identities: {Recency.cache_identities(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {Recency.cache_identities(~String, ~Codec.string_encode, V, C.step_cache(String, V, P.detach_present(String, V, c, removed, entry))) == True{} : Bool}:
  detach_present(~String, ~Codec.string_encode, V, c, removed, entry, identities)

def integer_delete(-V: Data, +tree: Map<&2, Maybe<&2, T.Entry<T.Integer, V>>>, +removed: String, identities: {Inv.identities(~T.Integer, ~Codec.integer_encode, V, Map.to_list(&2, Maybe<&2, T.Entry<T.Integer, V>>, tree)) == True{} : Bool}) -> {Inv.identities(~T.Integer, ~Codec.integer_encode, V, Map.to_list(&2, Maybe<&2, T.Entry<T.Integer, V>>, Map.del(&2, Maybe<&2, T.Entry<T.Integer, V>>, tree, removed))) == True{} : Bool}:
  delete(~T.Integer, ~Codec.integer_encode, V, tree, removed, identities)

def integer_remove_present(-V: Data, c: C.Cache<T.Integer, V>, removed: String, evict: Bool, entry: T.Entry<T.Integer, V>, identities: {Recency.cache_identities(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}) -> {Recency.cache_identities(~T.Integer, ~Codec.integer_encode, V, C.step_cache(T.Integer, V, C.remove_present(T.Integer, V, c, removed, evict, entry))) == True{} : Bool}:
  remove_present(~T.Integer, ~Codec.integer_encode, V, c, removed, evict, entry, identities)

def integer_detach_present(-V: Data, c: C.Cache<T.Integer, V>, removed: String, entry: T.Entry<T.Integer, V>, identities: {Recency.cache_identities(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}) -> {Recency.cache_identities(~T.Integer, ~Codec.integer_encode, V, C.step_cache(T.Integer, V, P.detach_present(T.Integer, V, c, removed, entry))) == True{} : Bool}:
  detach_present(~T.Integer, ~Codec.integer_encode, V, c, removed, entry, identities)

def word64_delete(-V: Data, +tree: Map<&2, Maybe<&2, T.Entry<Word(64n), V>>>, +removed: String, identities: {Inv.identities(~Word(64n), ~Key.word64_encode, V, Map.to_list(&2, Maybe<&2, T.Entry<Word(64n), V>>, tree)) == True{} : Bool}) -> {Inv.identities(~Word(64n), ~Key.word64_encode, V, Map.to_list(&2, Maybe<&2, T.Entry<Word(64n), V>>, Map.del(&2, Maybe<&2, T.Entry<Word(64n), V>>, tree, removed))) == True{} : Bool}:
  delete(~Word(64n), ~Key.word64_encode, V, tree, removed, identities)

def word64_remove_present(-V: Data, c: C.Cache<Word(64n), V>, removed: String, evict: Bool, entry: T.Entry<Word(64n), V>, identities: {Recency.cache_identities(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}) -> {Recency.cache_identities(~Word(64n), ~Key.word64_encode, V, C.step_cache(Word(64n), V, C.remove_present(Word(64n), V, c, removed, evict, entry))) == True{} : Bool}:
  remove_present(~Word(64n), ~Key.word64_encode, V, c, removed, evict, entry, identities)

def word64_detach_present(-V: Data, c: C.Cache<Word(64n), V>, removed: String, entry: T.Entry<Word(64n), V>, identities: {Recency.cache_identities(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}) -> {Recency.cache_identities(~Word(64n), ~Key.word64_encode, V, C.step_cache(Word(64n), V, P.detach_present(Word(64n), V, c, removed, entry))) == True{} : Bool}:
  detach_present(~Word(64n), ~Key.word64_encode, V, c, removed, entry, identities)

