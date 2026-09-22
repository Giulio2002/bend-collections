import Base
import ./invariants.bend as Inv
import ./map_insert.bend as I
import ./map_seek_prefix.bend as Seek
import ./map_string_prefix.bend as Difference
import ./map_prefix_algebra.bend as A
import ./map_routing.bend as R
import ./map_delete_prefix.bend as P

# Extract a row for the actual native seek result from the all-pairs relation.
# The selected leaf is obtained by seek; no leaf-membership oracle is supplied.
law selected_row:
  for -V: Data
  for tree: Map<&2, V>
  for +whole: Map<&2, V>
  for +key: String
  for +stored: String
  for +limit: Nat
  for +common: {Inv.common_prefix(V, tree, whole, limit) == True{} : Bool}
  for +found: {I.seek_found(V, Map.seek(&2, V, whole, key)) == Some{stored} : Maybe<&2, String>}
  {Inv.prefix_against(V, stored, tree, limit) == True{} : Bool}
def selected_row(V, tree, whole, key, stored, limit, common, found):
  match tree:
    case MTip{}: {==}
    case MLeaf{+query, value}:
      A.symmetric(query, stored, limit, Seek.found_has_prefix(V, whole, key, query, limit, stored, common, found))
    case MNode{p, +lo, +hi}:
      P.conjunction(Inv.prefix_against(V, stored, lo, limit), Inv.prefix_against(V, stored, hi, limit),
        selected_row(V, lo, whole, key, stored, limit, R.and_left(Inv.common_prefix(V, lo, whole, limit), Inv.common_prefix(V, hi, whole, limit), common), found),
        selected_row(V, hi, whole, key, stored, limit, R.and_right(Inv.common_prefix(V, lo, whole, limit), Inv.common_prefix(V, hi, whole, limit), common), found))

# Discharge the fresh-key prefix premise at the actual native discriminator.
law fresh_difference_prefix:
  for -V: Data
  for +tree: Map<&2, V>
  for +key: String
  for +stored: String
  for common: {Inv.common_prefix(V, tree, tree, Map.diff(key, stored)) == True{} : Bool}
  for found: {I.seek_found(V, Map.seek(&2, V, tree, key)) == Some{stored} : Maybe<&2, String>}
  {Inv.prefix_against(V, key, tree, Map.diff(key, stored)) == True{} : Bool}
def fresh_difference_prefix(V, tree, key, stored, common, found):
  A.against_transitive(V, tree, key, stored, Map.diff(key, stored), Difference.native_prefix_invariant(key, stored), selected_row(V, tree, tree, key, stored, Map.diff(key, stored), common, found))
