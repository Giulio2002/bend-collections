import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../spec/cache.bend as S
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./abstraction_recency.bend as R
import ./representation_parts.bend as Parts
import ./spec_lookup.bend as Lookup

def identity(keys: List<&2, String>) -> {R.encode_keys(~String, ~Codec.string_encode, keys) == keys : List<&2, String>}:
  match keys:
    case Nil{}: {==}
    case Con{+key, +tail}:
      Equal.cong(List<&2, String>, List<&2, String>, xs => Con{key, xs}, R.encode_keys(~String, ~Codec.string_encode, tail), tail, identity(tail))

# String encoding is identity, including empty strings and embedded zero units.
# For represented caches the abstract original-key order is the exact native
# recency sequence, rather than merely a permutation or matching key set.
def faithful(-V: Data, +c: C.Cache<String, V>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {R.model_order(String, V, F.abstract(String, V, c)) == R.native_order(String, V, c) : List<&2, String>}:
  Equal.trans(List<&2, String>, R.model_order(String, V, F.abstract(String, V, c)), R.encode_keys(~String, ~Codec.string_encode, R.model_order(String, V, F.abstract(String, V, c))), R.native_order(String, V, c), Equal.sym(List<&2, String>, R.encode_keys(~String, ~Codec.string_encode, R.model_order(String, V, F.abstract(String, V, c))), R.model_order(String, V, F.abstract(String, V, c)), identity(R.model_order(String, V, F.abstract(String, V, c)))), Parts.recency_faithful(~String, ~Codec.string_encode, V, c, valid))

def omit(key: String, tail: List<&2, String>, equal: Bool) -> {C.without_keep(key, tail, equal) == S.omit_key(String, key, tail, equal) : List<&2, String>}:
  match equal:
    case False{}: {==}
    case True{}: {==}

def filter(order: List<&2, String>, +key: String) -> {C.without(order, key) == S.unlist(~String, ~Lookup.string_same, order, key) : List<&2, String>}:
  match order:
    case Nil{}: {==}
    case Con{+head, +tail}:
      Equal.trans(List<&2, String>, C.without_keep(head, C.without(tail, key), String.eq(head, key)), S.omit_key(String, head, C.without(tail, key), String.eq(head, key)), S.omit_key(String, head, S.unlist(~String, ~Lookup.string_same, tail, key), String.eq(head, key)), omit(head, C.without(tail, key), String.eq(head, key)), Equal.cong(List<&2, String>, List<&2, String>, xs => S.omit_key(String, head, xs, String.eq(head, key)), C.without(tail, key), S.unlist(~String, ~Lookup.string_same, tail, key), filter(tail, key)))

def normal(-V: Data, c: C.Cache<String, V>) -> S.Model<String, V>:
  C.State{cap, table, order, life, counts, cb} = c
  S.Abstract{cap, F.bindings(String, V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table)), order, life, counts, cb}

def normalize(-V: Data, c: C.Cache<String, V>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {F.abstract(String, V, c) == normal(V, c) : S.Model<String, V>}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  Equal.cong(List<&2, String>, S.Model<String, V>, xs => S.Abstract{cap, F.bindings(String, V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table)), xs, life, counts, cb}, R.model_order(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), order, faithful(V, C.State{cap, table, order, life, counts, cb}, valid))
