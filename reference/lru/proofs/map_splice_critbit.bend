import Base
import ./map_difference.bend as D
import ./map_string_prefix.bend as Prefix
import ./map_prefix_algebra.bend as Algebra
import ./map_routing.bend as R
import ./invariants.bend as Inv
import ./map_insert.bend as I
import ./map_critbit_parts.bend as Parts
import ./map_prefix_join.bend as Join
import ./map_route_boolean.bend as Route

# Complete node obligations for an actual native insertion splice. The rest
# tree must be nonempty and routed opposite the fresh key at the new position.
# General Map.set correctness must derive these local input facts from seek/diff.
law splice_bit:
  for -V: Data
  for +key: String
  for +value: V
  for +rest: Map<&2, V>
  for +position: Nat
  for bit: Bool
  for route: {Map.bit(key, position) == (key, bit) : String & Bool}
  for fresh: {Inv.prefix_against(V, key, rest, position) == True{} : Bool}
  for common: {Inv.common_prefix(V, rest, rest, position) == True{} : Bool}
  for nonempty: {Inv.nonempty(V, rest) == True{} : Bool}
  for below: {Inv.below(V, rest, position) == True{} : Bool}
  for opposite: {Inv.routed(V, rest, position, Bool.not(bit)) == True{} : Bool}
  for valid: {Inv.critbit(V, rest) == True{} : Bool}
  {Inv.critbit(V, Map.ins.splice.bit(&2, V, value, rest, position, (key, bit))) == True{} : Bool}
def splice_bit(V, key, value, rest, position, bit, route, fresh, common, nonempty, below, opposite, valid):
  match bit:
    case False{}:
      Parts.node_valid(V, position, MLeaf{key, value}, rest, Join.fresh_left(V, key, value, rest, position, position, fresh, common), {==}, nonempty, {==}, below, Route.leaf_boolean(key, position, False{}, route), opposite, {==}, valid)
    case True{}:
      Parts.node_valid(V, position, rest, MLeaf{key, value}, Join.fresh_right(V, key, value, rest, position, position, fresh, common), nonempty, {==}, below, {==}, opposite, Route.leaf_boolean(key, position, True{}, route), valid, {==})

law preserves_critbit:
  for -V: Data
  for +key: String
  for +value: V
  for +rest: Map<&2, V>
  for +position: Nat
  for fresh: {Inv.prefix_against(V, key, rest, position) == True{} : Bool}
  for common: {Inv.common_prefix(V, rest, rest, position) == True{} : Bool}
  for nonempty: {Inv.nonempty(V, rest) == True{} : Bool}
  for below: {Inv.below(V, rest, position) == True{} : Bool}
  for opposite: {Inv.routed(V, rest, position, Bool.not(I.route_bit(Map.bit(key, position)))) == True{} : Bool}
  for valid: {Inv.critbit(V, rest) == True{} : Bool}
  {Inv.critbit(V, Map.ins.splice(&2, V, position, key, value, rest)) == True{} : Bool}
def preserves_critbit(V, key, value, rest, position, fresh, common, nonempty, below, opposite, valid):
  %Equal.sym(String & Bool, Map.bit(key, position), (key, I.route_bit(Map.bit(key, position))), I.route_shape(key, position)) : {Inv.critbit(V, Map.ins.splice.bit(&2, V, value, rest, position, _)) == True{} : Bool}
  splice_bit(V, key, value, rest, position, I.route_bit(Map.bit(key, position)), I.route_shape(key, position), fresh, common, nonempty, below, opposite, valid)

law xor_opposite:
  for a: Bool
  for b: Bool
  for different: {Bool.xor(a, b) == True{} : Bool}
  {Bool.not(Bool.xor(b, Bool.not(a))) == True{} : Bool}
def xor_opposite(a, b, different):
  match a b:
    case False{} False{}:
      Empty.absurd({False{} == True{} : Bool}, R.false_true(different))
    case False{} True{}: {==}
    case True{} False{}: {==}
    case True{} True{}:
      Empty.absurd({False{} == True{} : Bool}, R.false_true(different))

law difference_leaf_route:
  for -V: Data
  for +key: String
  for +stored: String
  for value: V
  for distinct: D.different(key, stored)
  {Inv.routed(V, MLeaf{stored, value}, Map.diff(key, stored), Bool.not(I.route_bit(Map.bit(key, Map.diff(key, stored))))) == True{} : Bool}
def difference_leaf_route(V, key, stored, value, distinct):
  %Equal.sym(Bool, Inv.bit_value(Map.bit(stored, Map.diff(key, stored))), I.route_bit(Map.bit(stored, Map.diff(key, stored))), Prefix.invariant_bit(Map.bit(stored, Map.diff(key, stored)))) : {Bool.not(Bool.xor(_, Bool.not(I.route_bit(Map.bit(key, Map.diff(key, stored)))))) == True{} : Bool}
  xor_opposite(I.route_bit(Map.bit(key, Map.diff(key, stored))), I.route_bit(Map.bit(stored, Map.diff(key, stored))), D.native_difference(key, stored, distinct))

# All local splice premises are discharged for a singleton, including arbitrary
# empty/embedded-zero Base String keys. This is the insertion induction base.
law singleton_insert_valid:
  for -V: Data
  for +key: String
  for +stored: String
  for +value: V
  for +old: V
  for distinct: D.different(key, stored)
  {Inv.critbit(V, Map.ins(&2, V, MLeaf{stored, old}, key, value, Map.diff(key, stored))) == True{} : Bool}
def singleton_insert_valid(V, key, stored, value, old, distinct):
  preserves_critbit(V, key, value, MLeaf{stored, old}, Map.diff(key, stored), Prefix.native_prefix_invariant(key, stored), Algebra.reflexive(stored, Map.diff(key, stored)), {==}, {==}, difference_leaf_route(V, key, stored, old, distinct), {==})
