import Base
import ./invariants.bend as Inv
import ./map_routing.bend as R
import ./map_delete_prefix.bend as P
import ./map_prefix_algebra.bend as A

law join_columns:
  for -V: Data
  for tree: Map<&2, V>
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +position: Nat
  for +limit: Nat
  for +left: {Inv.common_prefix(V, tree, lo, limit) == True{} : Bool}
  for +right: {Inv.common_prefix(V, tree, hi, limit) == True{} : Bool}
  {Inv.common_prefix(V, tree, MNode{position, lo, hi}, limit) == True{} : Bool}
def join_columns(V, tree, lo, hi, position, limit, left, right):
  match tree:
    case MTip{}: {==}
    case MLeaf{+key, value}:
      P.conjunction(Inv.prefix_against(V, key, lo, limit), Inv.prefix_against(V, key, hi, limit), left, right)
    case MNode{p, +a, +b}:
      P.conjunction(Inv.common_prefix(V, a, MNode{position, lo, hi}, limit), Inv.common_prefix(V, b, MNode{position, lo, hi}, limit),
        join_columns(V, a, lo, hi, position, limit, R.and_left(Inv.common_prefix(V, a, lo, limit), Inv.common_prefix(V, b, lo, limit), left), R.and_left(Inv.common_prefix(V, a, hi, limit), Inv.common_prefix(V, b, hi, limit), right)),
        join_columns(V, b, lo, hi, position, limit, R.and_right(Inv.common_prefix(V, a, lo, limit), Inv.common_prefix(V, b, lo, limit), left), R.and_right(Inv.common_prefix(V, a, hi, limit), Inv.common_prefix(V, b, hi, limit), right)))

law join_both:
  for -V: Data
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +position: Nat
  for +limit: Nat
  for ll: {Inv.common_prefix(V, lo, lo, limit) == True{} : Bool}
  for lh: {Inv.common_prefix(V, lo, hi, limit) == True{} : Bool}
  for hl: {Inv.common_prefix(V, hi, lo, limit) == True{} : Bool}
  for hh: {Inv.common_prefix(V, hi, hi, limit) == True{} : Bool}
  {Inv.common_prefix(V, MNode{position, lo, hi}, MNode{position, lo, hi}, limit) == True{} : Bool}
def join_both(V, lo, hi, position, limit, ll, lh, hl, hh):
  P.conjunction(Inv.common_prefix(V, lo, MNode{position, lo, hi}, limit), Inv.common_prefix(V, hi, MNode{position, lo, hi}, limit), join_columns(V, lo, lo, hi, position, limit, ll, lh), join_columns(V, hi, lo, hi, position, limit, hl, hh))

law fresh_left:
  for -V: Data
  for +key: String
  for +value: V
  for +rest: Map<&2, V>
  for +position: Nat
  for +limit: Nat
  for +fresh: {Inv.prefix_against(V, key, rest, limit) == True{} : Bool}
  for existing: {Inv.common_prefix(V, rest, rest, limit) == True{} : Bool}
  {Inv.common_prefix(V, MNode{position, MLeaf{key, value}, rest}, MNode{position, MLeaf{key, value}, rest}, limit) == True{} : Bool}
def fresh_left(V, key, value, rest, position, limit, fresh, existing):
  join_both(V, MLeaf{key, value}, rest, position, limit, A.reflexive(key, limit), fresh, A.against_column(V, rest, key, value, limit, fresh), existing)

law fresh_right:
  for -V: Data
  for +key: String
  for +value: V
  for +rest: Map<&2, V>
  for +position: Nat
  for +limit: Nat
  for +fresh: {Inv.prefix_against(V, key, rest, limit) == True{} : Bool}
  for existing: {Inv.common_prefix(V, rest, rest, limit) == True{} : Bool}
  {Inv.common_prefix(V, MNode{position, rest, MLeaf{key, value}}, MNode{position, rest, MLeaf{key, value}}, limit) == True{} : Bool}
def fresh_right(V, key, value, rest, position, limit, fresh, existing):
  join_both(V, rest, MLeaf{key, value}, position, limit, existing, A.against_column(V, rest, key, value, limit, fresh), fresh, A.reflexive(key, limit))
