import Base
import ./invariants.bend as Inv
import ./map_insert.bend as I
import ./map_insert_common.bend as Common
import ./map_insert_nonempty.bend as Nonempty
import ./map_insert_below.bend as Below
import ./map_insert_routes.bend as Routes
import ./map_route_boolean.bend as Route
import ./map_critbit_parts.bend as Parts
import ./map_prefix_algebra.bend as Algebra
import ./map_prefix_bounds.bend as Bounds
import ./map_string_prefix.bend as Difference
import ./map_difference_order.bend as Order
import ./map_selected_prefix.bend as Selected

law deep_common:
  for -V: Data
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +position: Nat
  for +discriminator: Nat
  for +key: String
  for +value: V
  for descend: {Nat.is_lt(position, discriminator) == True{} : Bool}
  for fresh: {Inv.prefix_against(V, key, MNode{position, lo, hi}, position) == True{} : Bool}
  for common: {Inv.common_prefix(V, MNode{position, lo, hi}, MNode{position, lo, hi}, position) == True{} : Bool}
  {Inv.common_prefix(V, Map.ins.deep(&2, V, value, lo, hi, discriminator, position, Map.bit(key, position)), Map.ins.deep(&2, V, value, lo, hi, discriminator, position, Map.bit(key, position)), position) == True{} : Bool}
def deep_common(V, lo, hi, position, discriminator, key, value, descend, fresh, common):
  %descend : {Inv.common_prefix(V, Map.ins.if(&2, V, key, value, lo, hi, position, discriminator, _), Map.ins.if(&2, V, key, value, lo, hi, position, discriminator, _), position) == True{} : Bool}
  Common.preserves_common_prefix(V, MNode{position, lo, hi}, key, value, discriminator, position, fresh, common)

law common_bit:
  for -V: Data
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +position: Nat
  for +discriminator: Nat
  for +key: String
  for +value: V
  for +bit: Bool
  for route: {Map.bit(key, position) == (key, bit) : String & Bool}
  for all: {Inv.common_prefix(V, Map.ins.deep(&2, V, value, lo, hi, discriminator, position, Map.bit(key, position)), Map.ins.deep(&2, V, value, lo, hi, discriminator, position, Map.bit(key, position)), position) == True{} : Bool}
  {Inv.common_prefix(V, Map.ins.deep(&2, V, value, lo, hi, discriminator, position, (key, bit)), Map.ins.deep(&2, V, value, lo, hi, discriminator, position, (key, bit)), position) == True{} : Bool}
def common_bit(V, lo, hi, position, discriminator, key, value, bit, route, all):
  %route : {Inv.common_prefix(V, Map.ins.deep(&2, V, value, lo, hi, discriminator, position, _), Map.ins.deep(&2, V, value, lo, hi, discriminator, position, _), position) == True{} : Bool}
  all

law deep_bit_ready:
  for -V: Data
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +position: Nat
  for +key: String
  for +stored: String
  for +value: V
  for +bit: Bool
  for +route: {Map.bit(key, position) == (key, bit) : String & Bool}
  for found: {I.seek_found(V, Map.seek(&2, V, MNode{position, lo, hi}, key)) == Some{stored} : Maybe<&2, String>}
  for +descend: {Nat.is_lt(position, Map.diff(key, stored)) == True{} : Bool}
  for +common: {Inv.common_prefix(V, MNode{position, lo, hi}, MNode{position, lo, hi}, position) == True{} : Bool}
  for nl: {Inv.nonempty(V, lo) == True{} : Bool}
  for nh: {Inv.nonempty(V, hi) == True{} : Bool}
  for bl: {Inv.below(V, lo, position) == True{} : Bool}
  for bh: {Inv.below(V, hi, position) == True{} : Bool}
  for rl: {Inv.routed(V, lo, position, False{}) == True{} : Bool}
  for rh: {Inv.routed(V, hi, position, True{}) == True{} : Bool}
  for vl: {Inv.critbit(V, lo) == True{} : Bool}
  for vh: {Inv.critbit(V, hi) == True{} : Bool}
  for lp: {Inv.critbit(V, lo) == True{} : Bool} -> {I.seek_found(V, Map.seek(&2, V, lo, key)) == Some{stored} : Maybe<&2, String>} -> {Inv.critbit(V, Map.ins(&2, V, lo, key, value, Map.diff(key, stored))) == True{} : Bool}
  for hp: {Inv.critbit(V, hi) == True{} : Bool} -> {I.seek_found(V, Map.seek(&2, V, hi, key)) == Some{stored} : Maybe<&2, String>} -> {Inv.critbit(V, Map.ins(&2, V, hi, key, value, Map.diff(key, stored))) == True{} : Bool}
  for converted: {Inv.common_prefix(V, Map.ins.deep(&2, V, value, lo, hi, Map.diff(key, stored), position, (key, bit)), Map.ins.deep(&2, V, value, lo, hi, Map.diff(key, stored), position, (key, bit)), position) == True{} : Bool}
  {Inv.critbit(V, Map.ins.deep(&2, V, value, lo, hi, Map.diff(key, stored), position, (key, bit))) == True{} : Bool}
def deep_bit_ready(V, lo, hi, position, key, stored, value, bit, route, found, descend, common, nl, nh, bl, bh, rl, rh, vl, vh, lp, hp, converted):
  match bit:
    case False{}:
      child_found = Equal.trans(Maybe<&2, String>, I.seek_found(V, Map.seek(&2, V, lo, key)), I.seek_found(V, Map.seek(&2, V, MNode{position, lo, hi}, key)), Some{stored}, Equal.sym(Maybe<&2, String>, I.seek_found(V, Map.seek(&2, V, MNode{position, lo, hi}, key)), I.seek_found(V, Map.seek(&2, V, lo, key)), I.seek_left(V, lo, hi, position, key, route)), found)
      Parts.node_valid(V, position, Map.ins(&2, V, lo, key, value, Map.diff(key, stored)), hi, converted, Nonempty.insertion_nonempty(V, lo, key, value, Map.diff(key, stored)), nh, Below.preserves_below(V, lo, key, value, Map.diff(key, stored), position, descend, bl), bh, Routes.preserves_routing(V, lo, key, value, Map.diff(key, stored), position, False{}, Route.leaf_boolean(key, position, False{}, route), rl), rh, lp(vl, child_found), vh)
    case True{}:
      child_found = Equal.trans(Maybe<&2, String>, I.seek_found(V, Map.seek(&2, V, hi, key)), I.seek_found(V, Map.seek(&2, V, MNode{position, lo, hi}, key)), Some{stored}, Equal.sym(Maybe<&2, String>, I.seek_found(V, Map.seek(&2, V, MNode{position, lo, hi}, key)), I.seek_found(V, Map.seek(&2, V, hi, key)), I.seek_right(V, lo, hi, position, key, route)), found)
      Parts.node_valid(V, position, lo, Map.ins(&2, V, hi, key, value, Map.diff(key, stored)), converted, nl, Nonempty.insertion_nonempty(V, hi, key, value, Map.diff(key, stored)), bl, Below.preserves_below(V, hi, key, value, Map.diff(key, stored), position, descend, bh), rl, Routes.preserves_routing(V, hi, key, value, Map.diff(key, stored), position, True{}, Route.leaf_boolean(key, position, True{}, route), rh), vl, hp(vh, child_found))

law deep_bit:
  for -V: Data
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +position: Nat
  for +key: String
  for +stored: String
  for +value: V
  for +bit: Bool
  for +route: {Map.bit(key, position) == (key, bit) : String & Bool}
  for found: {I.seek_found(V, Map.seek(&2, V, MNode{position, lo, hi}, key)) == Some{stored} : Maybe<&2, String>}
  for +descend: {Nat.is_lt(position, Map.diff(key, stored)) == True{} : Bool}
  for +common: {Inv.common_prefix(V, MNode{position, lo, hi}, MNode{position, lo, hi}, position) == True{} : Bool}
  for nl: {Inv.nonempty(V, lo) == True{} : Bool}
  for nh: {Inv.nonempty(V, hi) == True{} : Bool}
  for bl: {Inv.below(V, lo, position) == True{} : Bool}
  for bh: {Inv.below(V, hi, position) == True{} : Bool}
  for rl: {Inv.routed(V, lo, position, False{}) == True{} : Bool}
  for rh: {Inv.routed(V, hi, position, True{}) == True{} : Bool}
  for vl: {Inv.critbit(V, lo) == True{} : Bool}
  for vh: {Inv.critbit(V, hi) == True{} : Bool}
  for lp: {Inv.critbit(V, lo) == True{} : Bool} -> {I.seek_found(V, Map.seek(&2, V, lo, key)) == Some{stored} : Maybe<&2, String>} -> {Inv.critbit(V, Map.ins(&2, V, lo, key, value, Map.diff(key, stored))) == True{} : Bool}
  for hp: {Inv.critbit(V, hi) == True{} : Bool} -> {I.seek_found(V, Map.seek(&2, V, hi, key)) == Some{stored} : Maybe<&2, String>} -> {Inv.critbit(V, Map.ins(&2, V, hi, key, value, Map.diff(key, stored))) == True{} : Bool}
  {Inv.critbit(V, Map.ins.deep(&2, V, value, lo, hi, Map.diff(key, stored), position, (key, bit))) == True{} : Bool}
def deep_bit(V, lo, hi, position, key, stored, value, bit, route, found, descend, common, nl, nh, bl, bh, rl, rh, vl, vh, lp, hp):
  +found_copy = found
  fresh = Algebra.against_transitive(V, MNode{position, lo, hi}, key, stored, position, Bounds.weaken(key, stored, Map.diff(key, stored), position, Order.less_is_le(position, Map.diff(key, stored), descend), Difference.native_prefix_invariant(key, stored)), Selected.selected_row(V, MNode{position, lo, hi}, MNode{position, lo, hi}, key, stored, position, common, found_copy))
  all = deep_common(V, lo, hi, position, Map.diff(key, stored), key, value, descend, fresh, common)
  converted = common_bit(V, lo, hi, position, Map.diff(key, stored), key, value, bit, route, all)
  deep_bit_ready(V, lo, hi, position, key, stored, value, bit, route, found_copy, descend, common, nl, nh, bl, bh, rl, rh, vl, vh, lp, hp, converted)

law from_parts:
  for -V: Data
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +position: Nat
  for +key: String
  for +stored: String
  for +value: V
  for found: {I.seek_found(V, Map.seek(&2, V, MNode{position, lo, hi}, key)) == Some{stored} : Maybe<&2, String>}
  for +descend: {Nat.is_lt(position, Map.diff(key, stored)) == True{} : Bool}
  for parts: Parts.NodeFacts(V, position, lo, hi)
  for lp: {Inv.critbit(V, lo) == True{} : Bool} -> {I.seek_found(V, Map.seek(&2, V, lo, key)) == Some{stored} : Maybe<&2, String>} -> {Inv.critbit(V, Map.ins(&2, V, lo, key, value, Map.diff(key, stored))) == True{} : Bool}
  for hp: {Inv.critbit(V, hi) == True{} : Bool} -> {I.seek_found(V, Map.seek(&2, V, hi, key)) == Some{stored} : Maybe<&2, String>} -> {Inv.critbit(V, Map.ins(&2, V, hi, key, value, Map.diff(key, stored))) == True{} : Bool}
  {Inv.critbit(V, Map.ins(&2, V, MNode{position, lo, hi}, key, value, Map.diff(key, stored))) == True{} : Bool}
def from_parts(V, lo, hi, position, key, stored, value, found, descend, parts, lp, hp):
  (common, nl, nh, bl, bh, rl, rh, vl, vh) = parts
  %Equal.sym(Bool, Nat.is_lt(position, Map.diff(key, stored)), True{}, descend) : {Inv.critbit(V, Map.ins.if(&2, V, key, value, lo, hi, position, Map.diff(key, stored), _)) == True{} : Bool}
  %Equal.sym(String & Bool, Map.bit(key, position), (key, I.route_bit(Map.bit(key, position))), I.route_shape(key, position)) : {Inv.critbit(V, Map.ins.deep(&2, V, value, lo, hi, Map.diff(key, stored), position, _)) == True{} : Bool}
  deep_bit(V, lo, hi, position, key, stored, value, I.route_bit(Map.bit(key, position)), I.route_shape(key, position), found, descend, common, nl, nh, bl, bh, rl, rh, vl, vh, lp, hp)
