import Base
import ./invariants.bend as Inv
import ./map_insert.bend as I
import ./map_routing.bend as R

def selected_prefix(query: String, limit: Nat, found: Maybe<&2, String>) -> Bool:
  match found:
    case None{}: True{}
    case Some{stored}: Inv.same_prefix(query, stored, limit)

law branch:
  for -V: Data
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +p: Nat
  for +key: String
  for bit: Bool
  for route: {Map.bit(key, p) == (key, bit) : String & Bool}
  for +query: String
  for +limit: Nat
  for left: {selected_prefix(query, limit, I.seek_found(V, Map.seek(&2, V, lo, key))) == True{} : Bool}
  for right: {selected_prefix(query, limit, I.seek_found(V, Map.seek(&2, V, hi, key))) == True{} : Bool}
  {selected_prefix(query, limit, I.seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key))) == True{} : Bool}
def branch(V, lo, hi, p, key, bit, route, query, limit, left, right):
  match bit:
    case False{}:
      %Equal.sym(Maybe<&2, String>, I.seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key)), I.seek_found(V, Map.seek(&2, V, lo, key)), I.seek_left(V, lo, hi, p, key, route)) : {selected_prefix(query, limit, _) == True{} : Bool}
      left
    case True{}:
      %Equal.sym(Maybe<&2, String>, I.seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key)), I.seek_found(V, Map.seek(&2, V, hi, key)), I.seek_right(V, lo, hi, p, key, route)) : {selected_prefix(query, limit, _) == True{} : Bool}
      right

# The key returned by the actual native seek satisfies each prefix constraint
# imposed on the tree's leaves. No assumed membership certificate is supplied.
law selected_has_prefix:
  for -V: Data
  for tree: Map<&2, V>
  for +key: String
  for +query: String
  for +limit: Nat
  for +prefix: {Inv.prefix_against(V, query, tree, limit) == True{} : Bool}
  {selected_prefix(query, limit, I.seek_found(V, Map.seek(&2, V, tree, key))) == True{} : Bool}
def selected_has_prefix(V, tree, key, query, limit, prefix):
  match tree:
    case MTip{}: {==}
    case MLeaf{k, v}: prefix
    case MNode{+p, +lo, +hi}:
      branch(V, lo, hi, p, key, I.route_bit(Map.bit(key, p)), I.route_shape(key, p), query, limit,
        selected_has_prefix(V, lo, key, query, limit, R.and_left(Inv.prefix_against(V, query, lo, limit), Inv.prefix_against(V, query, hi, limit), prefix)),
        selected_has_prefix(V, hi, key, query, limit, R.and_right(Inv.prefix_against(V, query, lo, limit), Inv.prefix_against(V, query, hi, limit), prefix)))

law found_has_prefix:
  for -V: Data
  for +tree: Map<&2, V>
  for +key: String
  for +query: String
  for +limit: Nat
  for +stored: String
  for prefix: {Inv.prefix_against(V, query, tree, limit) == True{} : Bool}
  for found: {I.seek_found(V, Map.seek(&2, V, tree, key)) == Some{stored} : Maybe<&2, String>}
  {Inv.same_prefix(query, stored, limit) == True{} : Bool}
def found_has_prefix(V, tree, key, query, limit, stored, prefix, found):
  %found : {selected_prefix(query, limit, _) == True{} : Bool}
  selected_has_prefix(V, tree, key, query, limit, prefix)
