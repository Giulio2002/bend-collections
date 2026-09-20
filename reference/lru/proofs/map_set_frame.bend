import Base
import ./invariants.bend as Inv
import ./native_map.bend as N
import ./map_insert.bend as I
import ./map_insert_frame.bend as Insert
import ./map_put_frame.bend as Put
import ./map_seek_empty.bend as EmptySeek
import ./map_set_critbit.bend as Set

law comparison_case:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +stored: String
  for +item: Maybe<&2, V>
  for +query: String
  for c: Cmp
  for compared: {N.comparison_tag(String, String.cmp(key, stored)) == c : Cmp}
  for unequal: {String.eq(query, key) == False{} : Bool}
  for found: {I.seek_found(Maybe<&2, V>, Map.seek(&2, Maybe<&2, V>, tree, key)) == Some{stored} : Maybe<&2, String>}
  for valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  {I.lookup(Maybe<&2, V>, None{}, Map.set.fin.go(&2, Maybe<&2, V>, tree, key, item, ((key, stored), c)), query) == I.lookup(Maybe<&2, V>, None{}, tree, query) : Maybe<&2, V>}
def comparison_case(V, tree, key, stored, item, query, c, compared, unequal, found, valid):
  match c:
    case LT{}: Insert.other_lookup_unchanged(V, tree, key, stored, item, query, unequal, Set.comparison_boolean(key, stored, LT{}, compared), found, valid)
    case GT{}: Insert.other_lookup_unchanged(V, tree, key, stored, item, query, unequal, Set.comparison_boolean(key, stored, GT{}, compared), found, valid)
    case EQ{}:
      Put.other_lookup_unchanged(Maybe<&2, V>, tree, None{}, key, stored, item, query, %N.string_equal_from_comparison(key, stored, compared) : {String.eq(query, _) == False{} : Bool} unequal, found)

law found_case:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +stored: String
  for +item: Maybe<&2, V>
  for +query: String
  for unequal: {String.eq(query, key) == False{} : Bool}
  for found: {I.seek_found(Maybe<&2, V>, Map.seek(&2, Maybe<&2, V>, tree, key)) == Some{stored} : Maybe<&2, String>}
  for valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  {I.lookup(Maybe<&2, V>, None{}, Map.set.fin(&2, Maybe<&2, V>, tree, key, item, key, stored), query) == I.lookup(Maybe<&2, V>, None{}, tree, query) : Maybe<&2, V>}
def found_case(V, tree, key, stored, item, query, unequal, found, valid):
  %Equal.sym((String & String) & Cmp, String.cmp(key, stored), ((key, stored), N.comparison_tag(String, String.cmp(key, stored))), N.string_comparison_shape(key, stored)) : {I.lookup(Maybe<&2, V>, None{}, Map.set.fin.go(&2, Maybe<&2, V>, tree, key, item, _), query) == I.lookup(Maybe<&2, V>, None{}, tree, query) : Maybe<&2, V>}
  comparison_case(V, tree, key, stored, item, query, N.comparison_tag(String, String.cmp(key, stored)), {==}, unequal, found, valid)

law empty_case:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +item: Maybe<&2, V>
  for +query: String
  for unequal: {String.eq(query, key) == False{} : Bool}
  for valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for missing: {I.seek_found(Maybe<&2, V>, Map.seek(&2, Maybe<&2, V>, tree, key)) == None{} : Maybe<&2, String>}
  {I.lookup(Maybe<&2, V>, None{}, MLeaf{key, item}, query) == I.lookup(Maybe<&2, V>, None{}, tree, query) : Maybe<&2, V>}
def empty_case(V, tree, key, item, query, unequal, valid, missing):
  %Equal.sym(Map<&2, Maybe<&2, V>>, tree, MTip{}, EmptySeek.empty_seek_is_tip(Maybe<&2, V>, tree, key, valid, missing)) : {I.lookup(Maybe<&2, V>, None{}, MLeaf{key, item}, query) == I.lookup(Maybe<&2, V>, None{}, _, query) : Maybe<&2, V>}
  Put.leaf_miss(Maybe<&2, V>, None{}, query, key, item, unequal)

law seek_case:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +item: Maybe<&2, V>
  for +query: String
  for result: Maybe<&2, String>
  for selected: {I.seek_found(Maybe<&2, V>, Map.seek(&2, Maybe<&2, V>, tree, key)) == result : Maybe<&2, String>}
  for unequal: {String.eq(query, key) == False{} : Bool}
  for valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  {I.lookup(Maybe<&2, V>, None{}, Map.set.go(&2, Maybe<&2, V>, item, (tree, key, result)), query) == I.lookup(Maybe<&2, V>, None{}, tree, query) : Maybe<&2, V>}
def seek_case(V, tree, key, item, query, result, selected, unequal, valid):
  match result:
    case None{}: empty_case(V, tree, key, item, query, unequal, valid, selected)
    case Some{stored}: found_case(V, tree, key, stored, item, query, unequal, selected, valid)

# Complete actual native Map.set frame, including replacement and empty seek.
law other_lookup_unchanged:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +item: Maybe<&2, V>
  for +query: String
  for unequal: {String.eq(query, key) == False{} : Bool}
  for valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  {I.lookup(Maybe<&2, V>, None{}, Map.set(&2, Maybe<&2, V>, tree, key, item), query) == I.lookup(Maybe<&2, V>, None{}, tree, query) : Maybe<&2, V>}
def other_lookup_unchanged(V, tree, key, item, query, unequal, valid):
  %Equal.sym(Map<&2, Maybe<&2, V>> & String & Maybe<&2, String>, Map.seek(&2, Maybe<&2, V>, tree, key), (tree, key, I.seek_found(Maybe<&2, V>, Map.seek(&2, Maybe<&2, V>, tree, key))), I.seek_shape(Maybe<&2, V>, tree, key)) : {I.lookup(Maybe<&2, V>, None{}, Map.set.go(&2, Maybe<&2, V>, item, _), query) == I.lookup(Maybe<&2, V>, None{}, tree, query) : Maybe<&2, V>}
  seek_case(V, tree, key, item, query, I.seek_found(Maybe<&2, V>, Map.seek(&2, Maybe<&2, V>, tree, key)), {==}, unequal, valid)
