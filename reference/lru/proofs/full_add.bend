import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../spec/cache.bend as S
import ../spec/operations.bend as O
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./disabled.bend as Disabled
import ./spec_lookup.bend as Lookup
import ./representation_access.bend as Access
import ./cache_storage_preservation.bend as Storage
import ./cache_oldest_available.bend as Oldest
import ./cache_order.bend as Order
import ./cache_key_identity.bend as Identity
import ./map_routing.bend as R
import ./full_add_head.bend as Head

def included(-V: Data, +c: C.Cache<String, V>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {Oldest.order_in_keys(String, V, c) == True{} : Bool}:
  R.and_left(Oldest.order_in_keys(String, V, c), Order.keys_in_order(String, V, c), Storage.membership(String, V, c, Access.get_storage(~String, ~Codec.string_encode, V, c, valid)))

def head(-V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<String, V>>>, +oldkey: String, +rest: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, +key: String, +value: V, +deadline: T.Int64, +valid: {Inv.representation(~String, ~Codec.string_encode, V, C.State{cap, table, Con{oldkey, rest}, life, counts, cb}) == True{} : Bool}, disabled: {cb == False{} : Bool}, full: {Nat.is_ge(1n+List.length(&2, String, rest), cap) == True{} : Bool}, witness: Oldest.available(String, V, C.State{cap, table, Con{oldkey, rest}, life, counts, cb}, oldkey)) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.add_room(String, V, C.State{cap, table, Con{oldkey, rest}, life, counts, cb}, key, key, value, deadline, True{})), O.absent_add(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, Con{oldkey, rest}, life, counts, cb}), key, value, deadline)):
  (entry, +found) = witness
  T.Item{+original, +oldvalue, +oldexpiry} = entry
  same = Identity.lookup_code_identity(~String, ~Codec.string_encode, V, C.State{cap, table, Con{oldkey, rest}, life, counts, cb}, oldkey, T.Item{original, oldvalue, oldexpiry}, Access.get_identities(~String, ~Codec.string_encode, V, C.State{cap, table, Con{oldkey, rest}, life, counts, cb}, valid), found)
  aligned = Equal.trans(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, C.State{cap, table, Con{oldkey, rest}, life, counts, cb}, oldkey), Some{T.Item{original, oldvalue, oldexpiry}}, Some{T.Item{oldkey, oldvalue, oldexpiry}}, found, Equal.cong(String, Maybe<&2, T.Entry<String, V>>, k => Some{T.Item{k, oldvalue, oldexpiry}}, original, oldkey, Equal.sym(String, oldkey, original, same)))
  Head.known(V, cap, table, oldkey, rest, life, counts, cb, key, value, deadline, oldvalue, oldexpiry, valid, disabled, full, aligned)

# Positive capacity and a full recency list exclude an empty state. Native
# membership/populated/critbit laws provide the actual oldest lookup witness.
def room(-V: Data, c: C.Cache<String, V>, +key: String, +value: V, +deadline: T.Int64, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}, full: {Nat.is_ge(C.len(String, V, c), C.capacity(String, V, c)) == True{} : Bool}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.add_room(String, V, c, key, key, value, deadline, True{})), O.absent_add(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, value, deadline)):
  C.State{cap, +table, order, +life, +counts, +cb} = c
  match cap order:
    case 0n xs:
      Empty.absurd(E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.add_room(String, V, C.State{0n, table, xs, life, counts, cb}, key, key, value, deadline, True{})), O.absent_add(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{0n, table, xs, life, counts, cb}), key, value, deadline)), R.false_true(Access.get_positive(~String, ~Codec.string_encode, V, C.State{0n, table, xs, life, counts, cb}, valid)))
    case 1n++n Nil{}:
      Empty.absurd(E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.add_room(String, V, C.State{1n+n, table, Nil{}, life, counts, cb}, key, key, value, deadline, True{})), O.absent_add(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{1n+n, table, Nil{}, life, counts, cb}), key, value, deadline)), R.false_true(full))
    case 1n++n Con{+oldkey, +rest}:
      head(V, 1n+n, table, oldkey, rest, life, counts, cb, key, value, deadline, valid, disabled, full, Oldest.ordered_lookup(String, V, C.State{1n+n, table, Con{oldkey, rest}, life, counts, cb}, oldkey, Storage.valid(String, V, C.State{1n+n, table, Con{oldkey, rest}, life, counts, cb}, Access.get_storage(~String, ~Codec.string_encode, V, C.State{1n+n, table, Con{oldkey, rest}, life, counts, cb}, valid)), Storage.populated(String, V, C.State{1n+n, table, Con{oldkey, rest}, life, counts, cb}, Access.get_storage(~String, ~Codec.string_encode, V, C.State{1n+n, table, Con{oldkey, rest}, life, counts, cb}, valid)), included(V, C.State{1n+n, table, Con{oldkey, rest}, life, counts, cb}, valid), Oldest.head_member(oldkey, rest)))

def branch(-V: Data, +c: C.Cache<String, V>, +key: String, +value: V, +deadline: T.Int64, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}, +full: {Nat.is_ge(C.len(String, V, c), C.capacity(String, V, c)) == True{} : Bool}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.add_found(String, V, c, key, key, value, deadline, None{})), O.add_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, value, deadline, None{})):
  %Equal.sym(Bool, Nat.is_ge(C.len(String, V, c), C.capacity(String, V, c)), True{}, full) : E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.add_room(String, V, c, key, key, value, deadline, _)), O.absent_add(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, value, deadline))
  room(V, c, key, value, deadline, valid, disabled, full)
