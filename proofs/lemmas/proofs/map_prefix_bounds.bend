import Base
import ./invariants.bend as Inv
import ./map_routing.bend as R
import ./map_delete_prefix.bend as P
import ./map_difference_order.bend as O

law drop_suffix:
  for extra: Nat
  for +limit: Nat
  for +a: String
  for +b: String
  for prefix: {Inv.same_prefix(a, b, Nat.add(extra, limit)) == True{} : Bool}
  {Inv.same_prefix(a, b, limit) == True{} : Bool}
def drop_suffix(extra, limit, a, b, prefix):
  match extra:
    case 0n: prefix
    case 1n+ +rest:
      drop_suffix(rest, limit, a, b, R.and_right(Bool.not(Bool.xor(Inv.bit_value(Map.bit(a, Nat.add(rest, limit))), Inv.bit_value(Map.bit(b, Nat.add(rest, limit))))), Inv.same_prefix(a, b, Nat.add(rest, limit)), prefix))

law weaken:
  for +a: String
  for +b: String
  for +limit: Nat
  for +smaller: Nat
  for bound: {Nat.is_le(smaller, limit) == True{} : Bool}
  for prefix: {Inv.same_prefix(a, b, limit) == True{} : Bool}
  {Inv.same_prefix(a, b, smaller) == True{} : Bool}
def weaken(a, b, limit, smaller, bound, prefix):
  shape = Equal.trans(Nat, Nat.add(Nat.sub(limit, smaller), smaller), Nat.add(smaller, Nat.sub(limit, smaller)), limit, O.add_commute(Nat.sub(limit, smaller), smaller), O.add_complement(limit, smaller, bound))
  converted = Equal.cong(Nat, Bool, n => Inv.same_prefix(a, b, n), Nat.add(Nat.sub(limit, smaller), smaller), limit, shape)
  drop_suffix(Nat.sub(limit, smaller), smaller, a, b, Equal.trans(Bool, Inv.same_prefix(a, b, Nat.add(Nat.sub(limit, smaller), smaller)), Inv.same_prefix(a, b, limit), True{}, converted, prefix))

law against_weaken:
  for -V: Data
  for tree: Map<&2, V>
  for +key: String
  for +limit: Nat
  for +smaller: Nat
  for +bound: {Nat.is_le(smaller, limit) == True{} : Bool}
  for +prefix: {Inv.prefix_against(V, key, tree, limit) == True{} : Bool}
  {Inv.prefix_against(V, key, tree, smaller) == True{} : Bool}
def against_weaken(V, tree, key, limit, smaller, bound, prefix):
  match tree:
    case MTip{}: {==}
    case MLeaf{stored, value}: weaken(key, stored, limit, smaller, bound, prefix)
    case MNode{p, +lo, +hi}:
      P.conjunction(Inv.prefix_against(V, key, lo, smaller), Inv.prefix_against(V, key, hi, smaller), against_weaken(V, lo, key, limit, smaller, bound, R.and_left(Inv.prefix_against(V, key, lo, limit), Inv.prefix_against(V, key, hi, limit), prefix)), against_weaken(V, hi, key, limit, smaller, bound, R.and_right(Inv.prefix_against(V, key, lo, limit), Inv.prefix_against(V, key, hi, limit), prefix)))

law common_weaken:
  for -V: Data
  for tree: Map<&2, V>
  for +whole: Map<&2, V>
  for +limit: Nat
  for +smaller: Nat
  for +bound: {Nat.is_le(smaller, limit) == True{} : Bool}
  for +prefix: {Inv.common_prefix(V, tree, whole, limit) == True{} : Bool}
  {Inv.common_prefix(V, tree, whole, smaller) == True{} : Bool}
def common_weaken(V, tree, whole, limit, smaller, bound, prefix):
  match tree:
    case MTip{}: {==}
    case MLeaf{stored, value}: against_weaken(V, whole, stored, limit, smaller, bound, prefix)
    case MNode{p, +lo, +hi}:
      P.conjunction(Inv.common_prefix(V, lo, whole, smaller), Inv.common_prefix(V, hi, whole, smaller), common_weaken(V, lo, whole, limit, smaller, bound, R.and_left(Inv.common_prefix(V, lo, whole, limit), Inv.common_prefix(V, hi, whole, limit), prefix)), common_weaken(V, hi, whole, limit, smaller, bound, R.and_right(Inv.common_prefix(V, lo, whole, limit), Inv.common_prefix(V, hi, whole, limit), prefix)))
