import Base
import ./invariants.bend as Inv
import ./map_lookup.bend as L
import ./map_insert.bend as I
import ./map_insert_membership.bend as Forward
import ./map_insert_inverse.bend as Inverse
import ./map_routing.bend as R

law absent_case:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +item: Maybe<&2, V>
  for +discriminator: Nat
  for +query: String
  for unequal: {String.eq(query, key) == False{} : Bool}
  for valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for absent: {I.lookup(Maybe<&2, V>, None{}, tree, query) == None{} : Maybe<&2, V>}
  for result: Maybe<&2, V>
  for result_eq: {I.lookup(Maybe<&2, V>, None{}, Map.ins(&2, Maybe<&2, V>, tree, key, item, discriminator), query) == result : Maybe<&2, V>}
  {I.lookup(Maybe<&2, V>, None{}, Map.ins(&2, Maybe<&2, V>, tree, key, item, discriminator), query) == None{} : Maybe<&2, V>}
def absent_case(V, tree, key, item, discriminator, query, unequal, valid, absent, result, result_eq):
  match result:
    case None{}: result_eq
    case Some{+value}:
      old = R.critbit_member_lookup(V, tree, query, value, valid, Inverse.no_new_other_binding(V, tree, key, item, discriminator, query, value, unequal, L.returned_value_is_stored(V, Map.ins(&2, Maybe<&2, V>, tree, key, item, discriminator), query, value, result_eq)))
      contradiction = Equal.trans(Maybe<&2, V>, None{}, I.lookup(Maybe<&2, V>, None{}, tree, query), Some{value}, Equal.sym(Maybe<&2, V>, I.lookup(Maybe<&2, V>, None{}, tree, query), None{}, absent), old)
      Empty.absurd({I.lookup(Maybe<&2, V>, None{}, Map.ins(&2, Maybe<&2, V>, tree, key, item, discriminator), query) == None{} : Maybe<&2, V>}, R.false_true(Equal.cong(Maybe<&2, V>, Bool, m => Maybe.is_some(&2, V, m), None{}, Some{value}, contradiction)))

law frame_case:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +stored: String
  for +item: Maybe<&2, V>
  for +query: String
  for unequal: {String.eq(query, key) == False{} : Bool}
  for fresh: {String.eq(key, stored) == False{} : Bool}
  for selected: {I.seek_found(Maybe<&2, V>, Map.seek(&2, Maybe<&2, V>, tree, key)) == Some{stored} : Maybe<&2, String>}
  for valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for result: Maybe<&2, V>
  for result_eq: {I.lookup(Maybe<&2, V>, None{}, tree, query) == result : Maybe<&2, V>}
  {I.lookup(Maybe<&2, V>, None{}, Map.ins(&2, Maybe<&2, V>, tree, key, item, Map.diff(key, stored)), query) == result : Maybe<&2, V>}
def frame_case(V, tree, key, stored, item, query, unequal, fresh, selected, valid, result, result_eq):
  match result:
    case None{}:
      absent_case(V, tree, key, item, Map.diff(key, stored), query, unequal, valid, result_eq, I.lookup(Maybe<&2, V>, None{}, Map.ins(&2, Maybe<&2, V>, tree, key, item, Map.diff(key, stored)), query), {==})
    case Some{value}:
      Forward.preserves_present_lookup(V, tree, key, stored, item, query, value, fresh, selected, valid, result_eq)

# General new-key insertion frame, including absent queries, across arbitrary
# existing valid trees. Seek and comparator inputs match the actual Map.set path.
law other_lookup_unchanged:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +stored: String
  for +item: Maybe<&2, V>
  for +query: String
  for unequal: {String.eq(query, key) == False{} : Bool}
  for fresh: {String.eq(key, stored) == False{} : Bool}
  for selected: {I.seek_found(Maybe<&2, V>, Map.seek(&2, Maybe<&2, V>, tree, key)) == Some{stored} : Maybe<&2, String>}
  for valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  {I.lookup(Maybe<&2, V>, None{}, Map.ins(&2, Maybe<&2, V>, tree, key, item, Map.diff(key, stored)), query) == I.lookup(Maybe<&2, V>, None{}, tree, query) : Maybe<&2, V>}
def other_lookup_unchanged(V, tree, key, stored, item, query, unequal, fresh, selected, valid):
  frame_case(V, tree, key, stored, item, query, unequal, fresh, selected, valid, I.lookup(Maybe<&2, V>, None{}, tree, query), {==})
