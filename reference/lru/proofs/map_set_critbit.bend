import Base
import ./invariants.bend as Inv
import ./native_map.bend as N
import ./map_insert.bend as I
import ./map_insert_critbit.bend as Insert
import ./map_shape.bend as Shape
import ./map_shape_invariants.bend as ShapeInv

law put_valid:
  for -V: Data
  for +tree: Map<&2, V>
  for +key: String
  for +stored: String
  for +value: V
  for found: {I.seek_found(V, Map.seek(&2, V, tree, key)) == Some{stored} : Maybe<&2, String>}
  for valid: {Inv.critbit(V, tree) == True{} : Bool}
  {Inv.critbit(V, Map.put(&2, V, tree, key, value)) == True{} : Bool}
def put_valid(V, tree, key, stored, value, found, valid):
  %ShapeInv.critbit(V, Map.put(&2, V, tree, key, value)) : {_ == True{} : Bool}
  %Equal.sym(Map<&2, Unit>, Shape.skeleton(V, Map.put(&2, V, tree, key, value)), Shape.skeleton(V, tree), Shape.put_found_shape(V, tree, key, value, stored, found)) : {Inv.critbit(Unit, _) == True{} : Bool}
  Equal.trans(Bool, Inv.critbit(Unit, Shape.skeleton(V, tree)), Inv.critbit(V, tree), True{}, ShapeInv.critbit(V, tree), valid)

law comparison_boolean:
  for +key: String
  for +stored: String
  for +c: Cmp
  for compared: {N.comparison_tag(String, String.cmp(key, stored)) == c : Cmp}
  {String.eq(key, stored) == Cmp.is_eq(c) : Bool}
def comparison_boolean(key, stored, c, compared):
  %Equal.sym((String & String) & Cmp, String.cmp(key, stored), ((key, stored), N.comparison_tag(String, String.cmp(key, stored))), N.string_comparison_shape(key, stored)) : {String.eq.fin(_) == Cmp.is_eq(c) : Bool}
  Equal.cong(Cmp, Bool, Cmp.is_eq, N.comparison_tag(String, String.cmp(key, stored)), c, compared)

law comparison_case:
  for -V: Data
  for +tree: Map<&2, V>
  for +key: String
  for +stored: String
  for +value: V
  for c: Cmp
  for compared: {N.comparison_tag(String, String.cmp(key, stored)) == c : Cmp}
  for found: {I.seek_found(V, Map.seek(&2, V, tree, key)) == Some{stored} : Maybe<&2, String>}
  for valid: {Inv.critbit(V, tree) == True{} : Bool}
  {Inv.critbit(V, Map.set.fin.go(&2, V, tree, key, value, ((key, stored), c))) == True{} : Bool}
def comparison_case(V, tree, key, stored, value, c, compared, found, valid):
  match c:
    case LT{}: Insert.insertion_at_seek(V, tree, key, stored, value, comparison_boolean(key, stored, LT{}, compared), found, valid)
    case EQ{}: put_valid(V, tree, key, stored, value, found, valid)
    case GT{}: Insert.insertion_at_seek(V, tree, key, stored, value, comparison_boolean(key, stored, GT{}, compared), found, valid)

law found_case:
  for -V: Data
  for +tree: Map<&2, V>
  for +key: String
  for +stored: String
  for +value: V
  for found: {I.seek_found(V, Map.seek(&2, V, tree, key)) == Some{stored} : Maybe<&2, String>}
  for valid: {Inv.critbit(V, tree) == True{} : Bool}
  {Inv.critbit(V, Map.set.fin(&2, V, tree, key, value, key, stored)) == True{} : Bool}
def found_case(V, tree, key, stored, value, found, valid):
  %Equal.sym((String & String) & Cmp, String.cmp(key, stored), ((key, stored), N.comparison_tag(String, String.cmp(key, stored))), N.string_comparison_shape(key, stored)) : {Inv.critbit(V, Map.set.fin.go(&2, V, tree, key, value, _)) == True{} : Bool}
  comparison_case(V, tree, key, stored, value, N.comparison_tag(String, String.cmp(key, stored)), {==}, found, valid)

law seek_case:
  for -V: Data
  for +tree: Map<&2, V>
  for +key: String
  for value: V
  for found: Maybe<&2, String>
  for selected: {I.seek_found(V, Map.seek(&2, V, tree, key)) == found : Maybe<&2, String>}
  for valid: {Inv.critbit(V, tree) == True{} : Bool}
  {Inv.critbit(V, Map.set.go(&2, V, value, (tree, key, found))) == True{} : Bool}
def seek_case(V, tree, key, value, found, selected, valid):
  match found:
    case None{}: {==}
    case Some{stored}: found_case(V, tree, key, stored, value, selected, valid)

# Universal native update validity. Every local insertion premise is discharged
# from actual seek/diff and the input tree invariant; no desired result assumed.
law preserves_critbit:
  for -V: Data
  for +tree: Map<&2, V>
  for +key: String
  for +value: V
  for valid: {Inv.critbit(V, tree) == True{} : Bool}
  {Inv.critbit(V, Map.set(&2, V, tree, key, value)) == True{} : Bool}
def preserves_critbit(V, tree, key, value, valid):
  %Equal.sym(Map<&2, V> & String & Maybe<&2, String>, Map.seek(&2, V, tree, key), (tree, key, I.seek_found(V, Map.seek(&2, V, tree, key))), I.seek_shape(V, tree, key)) : {Inv.critbit(V, Map.set.go(&2, V, value, _)) == True{} : Bool}
  seek_case(V, tree, key, value, I.seek_found(V, Map.seek(&2, V, tree, key)), {==}, valid)
