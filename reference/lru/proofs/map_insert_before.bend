import Base
import ./invariants.bend as Inv
import ./map_critbit_parts.bend as Parts
import ./map_insert.bend as I
import ./map_difference.bend as D
import ./map_difference_order.bend as O
import ./map_prefix_bounds.bend as Bounds
import ./map_selected_prefix.bend as Selected
import ./map_prefix_routing.bend as Routing
import ./map_splice_critbit.bend as Splice
import ./map_routing.bend as R

law reverse_not_less:
  for a: Nat
  for b: Nat
  for earlier: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_lt(b, a) == False{} : Bool}
def reverse_not_less(a, b, earlier):
  match a b:
    case 0n 0n: {==}
    case 0n 1n+q: {==}
    case 1n+p 0n:
      Empty.absurd({True{} == False{} : Bool}, R.false_true(earlier))
    case 1n+p 1n+q: reverse_not_less(p, q, earlier)

def common_part(-V: Data, +position: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, parts: Parts.NodeFacts(V, position, lo, hi)) -> {Inv.common_prefix(V, MNode{position, lo, hi}, MNode{position, lo, hi}, position) == True{} : Bool}:
  (common, nl, nh, bl, bh, rl, rh, vl, vh) = parts
  common

# Native diff before the existing discriminator permits a splice above the
# whole node. All local prefix, routing, nonempty and ordering premises are
# derived here from actual seek, native diff, and the input critbit invariant.
law splice_before:
  for -V: Data
  for +key: String
  for +stored: String
  for +value: V
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +position: Nat
  for distinct: D.different(key, stored)
  for +found: {I.seek_found(V, Map.seek(&2, V, MNode{position, lo, hi}, key)) == Some{stored} : Maybe<&2, String>}
  for +earlier: {Nat.is_lt(Map.diff(key, stored), position) == True{} : Bool}
  for +valid: {Inv.critbit(V, MNode{position, lo, hi}) == True{} : Bool}
  {Inv.critbit(V, Map.ins.splice(&2, V, Map.diff(key, stored), key, value, MNode{position, lo, hi})) == True{} : Bool}
def splice_before(V, key, stored, value, lo, hi, position, distinct, found, earlier, valid):
  +common = common_part(V, position, lo, hi, Parts.node_parts(V, position, lo, hi, valid))
  +shorter = Bounds.common_weaken(V, MNode{position, lo, hi}, MNode{position, lo, hi}, position, Map.diff(key, stored), O.less_is_le(Map.diff(key, stored), position, earlier), common)
  Splice.preserves_critbit(V, key, value, MNode{position, lo, hi}, Map.diff(key, stored),
    Selected.fresh_difference_prefix(V, MNode{position, lo, hi}, key, stored, shorter, found), shorter, {==}, earlier,
    Routing.prefix_routing(V, MNode{position, lo, hi}, stored, position, Map.diff(key, stored), Bool.not(I.route_bit(Map.bit(key, Map.diff(key, stored)))), earlier, Selected.selected_row(V, MNode{position, lo, hi}, MNode{position, lo, hi}, key, stored, position, common, found), Splice.difference_leaf_route(V, key, stored, value, distinct)), valid)

law insertion_before:
  for -V: Data
  for +key: String
  for +stored: String
  for +value: V
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +position: Nat
  for distinct: D.different(key, stored)
  for found: {I.seek_found(V, Map.seek(&2, V, MNode{position, lo, hi}, key)) == Some{stored} : Maybe<&2, String>}
  for +earlier: {Nat.is_lt(Map.diff(key, stored), position) == True{} : Bool}
  for valid: {Inv.critbit(V, MNode{position, lo, hi}) == True{} : Bool}
  {Inv.critbit(V, Map.ins(&2, V, MNode{position, lo, hi}, key, value, Map.diff(key, stored))) == True{} : Bool}
def insertion_before(V, key, stored, value, lo, hi, position, distinct, found, earlier, valid):
  %Equal.sym(Bool, Nat.is_lt(position, Map.diff(key, stored)), False{}, reverse_not_less(Map.diff(key, stored), position, earlier)) : {Inv.critbit(V, Map.ins.if(&2, V, key, value, lo, hi, position, Map.diff(key, stored), _)) == True{} : Bool}
  splice_before(V, key, stored, value, lo, hi, position, distinct, found, earlier, valid)
