import Base
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../src/codec.bend as Codec
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./recency_unique.bend as Unique
import ./map_routing.bend as R
import ./map_key_membership.bend as Keys
import ./representation_access.bend as Access
import ./cache_oldest_available.bend as Oldest
import ./cache_storage_preservation.bend as Storage
import ./full_add.bend as Full

def absent(+order: List<&2, String>, +key: String, +missing: {Inv.member(order, key) == False{} : Bool}) -> {C.without(order, key) == order : List<&2, String>}:
  match order:
    case Nil{}: {==}
    case Con{+head, +tail}:
      %Equal.sym(Bool, String.eq(head, key), False{}, Unique.or_false_left(String.eq(head, key), Inv.member(tail, key), missing)) : {C.without_keep(head, C.without(tail, key), _) == Con{head, tail} : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, xs => Con{head, xs}, C.without(tail, key), tail, absent(tail, key, Unique.or_false_right(String.eq(head, key), Inv.member(tail, key), missing)))

# Unique recency makes actual filtering of its head exactly the original tail.
def head(+key: String, +tail: List<&2, String>, unique: {Inv.unique(Con{key, tail}) == True{} : Bool}) -> {C.without(Con{key, tail}, key) == tail : List<&2, String>}:
  %Equal.sym(Bool, String.eq(key, key), True{}, Keys.eq_true(key, key, {==})) : {C.without_keep(key, C.without(tail, key), _) == tail : List<&2, String>}
  absent(tail, key, Unique.not_true(Inv.member(tail, key), R.and_left(Bool.not(Inv.member(tail, key)), Inv.unique(tail), unique)))

def detach_present_length(-K: Data, -V: Data, cap: Nat, table: Map<&2, Maybe<&2, T.Entry<K, V>>>, +key: String, +tail: List<&2, String>, life: T.Int64, counts: T.Metrics, cb: Bool, entry: T.Entry<K, V>, unique: {Inv.unique(Con{key, tail}) == True{} : Bool}) -> {C.len(K, V, C.step_cache(K, V, P.detach_present(K, V, C.State{cap, table, Con{key, tail}, life, counts, cb}, key, entry))) == List.length(&2, String, tail) : Nat}:
  Equal.cong(List<&2, String>, Nat, xs => List.length(&2, String, xs), C.without(Con{key, tail}, key), tail, head(key, tail, unique))

def with_witness(-V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<String, V>>>, +key: String, +tail: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, unique: {Inv.unique(Con{key, tail}) == True{} : Bool}, witness: Oldest.available(String, V, C.State{cap, table, Con{key, tail}, life, counts, cb}, key)) -> {C.len(String, V, C.step_cache(String, V, P.detach_oldest(String, V, C.State{cap, table, Con{key, tail}, life, counts, cb}))) == List.length(&2, String, tail) : Nat}:
  (entry, found) = witness
  %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, C.State{cap, table, Con{key, tail}, life, counts, cb}, key), Some{entry}, found) : {C.len(String, V, C.step_cache(String, V, P.detach_found(String, V, C.State{cap, table, Con{key, tail}, life, counts, cb}, key, _))) == List.length(&2, String, tail) : Nat}
  detach_present_length(String, V, cap, table, key, tail, life, counts, cb, entry, unique)

# Exact decrement for the actual aggregate detach operation. The successful
# native lookup is derived, not assumed from a nonempty recency list alone.
def detach_oldest_length(-V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<String, V>>>, +key: String, +tail: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, +valid: {Inv.representation(~String, ~Codec.string_encode, V, C.State{cap, table, Con{key, tail}, life, counts, cb}) == True{} : Bool}) -> {C.len(String, V, C.step_cache(String, V, P.detach_oldest(String, V, C.State{cap, table, Con{key, tail}, life, counts, cb}))) == List.length(&2, String, tail) : Nat}:
  with_witness(V, cap, table, key, tail, life, counts, cb, Access.get_unique(~String, ~Codec.string_encode, V, C.State{cap, table, Con{key, tail}, life, counts, cb}, valid), Oldest.ordered_lookup(String, V, C.State{cap, table, Con{key, tail}, life, counts, cb}, key, Storage.valid(String, V, C.State{cap, table, Con{key, tail}, life, counts, cb}, Access.get_storage(~String, ~Codec.string_encode, V, C.State{cap, table, Con{key, tail}, life, counts, cb}, valid)), Storage.populated(String, V, C.State{cap, table, Con{key, tail}, life, counts, cb}, Access.get_storage(~String, ~Codec.string_encode, V, C.State{cap, table, Con{key, tail}, life, counts, cb}, valid)), Full.included(V, C.State{cap, table, Con{key, tail}, life, counts, cb}, valid), Oldest.head_member(key, tail)))
