import Base
import ./invariants.bend as Inv
import ./native_map.bend as N
import ./map_insert.bend as I
import ./map_critbit_parts.bend as Parts
import ./map_delete_below.bend as Below
import ./map_delete_common.bend as Common
import ./map_route_boolean.bend as Routes

law low:
  for -V: Data
  for +p: Nat
  for +hi: Map<&2, V>
  for r: Map<&2, V> & Maybe<&2, V>
  for prefix: {Inv.common_prefix(V, Map.del.fin(&2, V, Map.pop.lo(&2, V, p, hi, r)), Map.del.fin(&2, V, Map.pop.lo(&2, V, p, hi, r)), p) == True{} : Bool}
  for other_nonempty: {Inv.nonempty(V, hi) == True{} : Bool}
  for lb: {Inv.below(V, Map.del.fin(&2, V, r), p) == True{} : Bool}
  for hb: {Inv.below(V, hi, p) == True{} : Bool}
  for lr: {Inv.routed(V, Map.del.fin(&2, V, r), p, False{}) == True{} : Bool}
  for hr: {Inv.routed(V, hi, p, True{}) == True{} : Bool}
  for lv: {Inv.critbit(V, Map.del.fin(&2, V, r)) == True{} : Bool}
  for hv: {Inv.critbit(V, hi) == True{} : Bool}
  {Inv.critbit(V, Map.del.fin(&2, V, Map.pop.lo(&2, V, p, hi, r))) == True{} : Bool}
def low(V, p, hi, r, prefix, other_nonempty, lb, hb, lr, hr, lv, hv):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}: hv
        case MLeaf{+k, +v}:
          Parts.node_valid(V, p, MLeaf{k, v}, hi, prefix, {==}, other_nonempty, lb, hb, lr, hr, lv, hv)
        case MNode{+q, +a, +b}:
          Parts.node_valid(V, p, MNode{q, a, b}, hi, prefix, {==}, other_nonempty, lb, hb, lr, hr, lv, hv)

law high:
  for -V: Data
  for +p: Nat
  for +lo: Map<&2, V>
  for r: Map<&2, V> & Maybe<&2, V>
  for prefix: {Inv.common_prefix(V, Map.del.fin(&2, V, Map.pop.hi(&2, V, p, lo, r)), Map.del.fin(&2, V, Map.pop.hi(&2, V, p, lo, r)), p) == True{} : Bool}
  for other_nonempty: {Inv.nonempty(V, lo) == True{} : Bool}
  for lb: {Inv.below(V, lo, p) == True{} : Bool}
  for hb: {Inv.below(V, Map.del.fin(&2, V, r), p) == True{} : Bool}
  for lr: {Inv.routed(V, lo, p, False{}) == True{} : Bool}
  for hr: {Inv.routed(V, Map.del.fin(&2, V, r), p, True{}) == True{} : Bool}
  for lv: {Inv.critbit(V, lo) == True{} : Bool}
  for hv: {Inv.critbit(V, Map.del.fin(&2, V, r)) == True{} : Bool}
  {Inv.critbit(V, Map.del.fin(&2, V, Map.pop.hi(&2, V, p, lo, r))) == True{} : Bool}
def high(V, p, lo, r, prefix, other_nonempty, lb, hb, lr, hr, lv, hv):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}: lv
        case MLeaf{+k, +v}:
          Parts.node_valid(V, p, lo, MLeaf{k, v}, prefix, other_nonempty, {==}, lb, hb, lr, hr, lv, hv)
        case MNode{+q, +a, +b}:
          Parts.node_valid(V, p, lo, MNode{q, a, b}, prefix, other_nonempty, {==}, lb, hb, lr, hr, lv, hv)

law leaf:
  for -V: Data
  for value: V
  for key: String
  for stored: String
  for tag: Cmp
  {Inv.critbit(V, Map.del.fin(&2, V, Map.pop.leaf(&2, V, value, ((key, stored), tag)))) == True{} : Bool}
def leaf(V, value, key, stored, tag):
  match tag:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: {==}

law branch:
  for -V: Data
  for +p: Nat
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +key: String
  for bit: Bool
  for +route: {Map.bit(key, p) == (key, bit) : String & Bool}
  for parts: Parts.NodeFacts(V, p, lo, hi)
  for lp: {Inv.critbit(V, lo) == True{} : Bool} -> {Inv.critbit(V, Map.del(&2, V, lo, key)) == True{} : Bool}
  for hp: {Inv.critbit(V, hi) == True{} : Bool} -> {Inv.critbit(V, Map.del(&2, V, hi, key)) == True{} : Bool}
  {Inv.critbit(V, Map.del(&2, V, MNode{p, lo, hi}, key)) == True{} : Bool}
def branch(V, p, lo, hi, key, bit, route, parts, lp, hp):
  match bit:
    case False{}:
      (prefix, ln, hn, lb, hb, lr, hr, lv0, hv0) = parts
      +lv = {lv0 : {Inv.critbit(V, lo) == True{} : Bool}}
      +hv = {hv0 : {Inv.critbit(V, hi) == True{} : Bool}}
      %Equal.sym(String & Bool, Map.bit(key, p), (key, False{}), route) : {Inv.critbit(V, Map.del.fin(&2, V, Map.pop.bit(&2, V, lo, hi, p, _))) == True{} : Bool}
      low(V, p, hi, Map.pop(&2, V, lo, key),
        %route : {Inv.common_prefix(V, Map.del.fin(&2, V, Map.pop.bit(&2, V, lo, hi, p, _)), Map.del.fin(&2, V, Map.pop.bit(&2, V, lo, hi, p, _)), p) == True{} : Bool}
          Common.preserves_common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, key, p, prefix),
        hn, Below.preserves_below(V, lo, key, p, lv, lb), hb,
        Routes.deletion_preserves(V, lo, key, p, False{}, lr), hr, lp(lv), hv)
    case True{}:
      (prefix, ln, hn, lb, hb, lr, hr, lv0, hv0) = parts
      +lv = {lv0 : {Inv.critbit(V, lo) == True{} : Bool}}
      +hv = {hv0 : {Inv.critbit(V, hi) == True{} : Bool}}
      %Equal.sym(String & Bool, Map.bit(key, p), (key, True{}), route) : {Inv.critbit(V, Map.del.fin(&2, V, Map.pop.bit(&2, V, lo, hi, p, _))) == True{} : Bool}
      high(V, p, lo, Map.pop(&2, V, hi, key),
        %route : {Inv.common_prefix(V, Map.del.fin(&2, V, Map.pop.bit(&2, V, lo, hi, p, _)), Map.del.fin(&2, V, Map.pop.bit(&2, V, lo, hi, p, _)), p) == True{} : Bool}
          Common.preserves_common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, key, p, prefix),
        ln, lb, Below.preserves_below(V, hi, key, p, hv, hb),
        lr, Routes.deletion_preserves(V, hi, key, p, True{}, hr), lv, hp(hv))

# Full executable critbit preservation: prefix, ordering, routing, nonempty
# children and recursive validity, not only the weaker lookup-routing predicate.
law preserves_critbit:
  for -V: Data
  for tree: Map<&2, V>
  for +key: String
  for valid: {Inv.critbit(V, tree) == True{} : Bool}
  {Inv.critbit(V, Map.del(&2, V, tree, key)) == True{} : Bool}
def preserves_critbit(V, tree, key, valid):
  match tree:
    case MTip{}: {==}
    case MLeaf{+stored, +value}:
      %Equal.sym((String & String) & Cmp, String.cmp(key, stored), ((key, stored), N.comparison_tag(String, String.cmp(key, stored))), N.string_comparison_shape(key, stored)) : {Inv.critbit(V, Map.del.fin(&2, V, Map.pop.leaf(&2, V, value, _))) == True{} : Bool}
      leaf(V, value, key, stored, N.comparison_tag(String, String.cmp(key, stored)))
    case MNode{+p, +lo, +hi}:
      branch(V, p, lo, hi, key, I.route_bit(Map.bit(key, p)), I.route_shape(key, p), Parts.node_parts(V, p, lo, hi, valid), e => preserves_critbit(V, lo, key, e), e => preserves_critbit(V, hi, key, e))
