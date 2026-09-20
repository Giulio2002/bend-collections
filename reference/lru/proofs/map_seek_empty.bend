import Base
import ./invariants.bend as Inv
import ./map_insert.bend as I
import ./map_critbit_parts.bend as Parts
import ./map_routing.bend as R

law branch:
  for -V: Data
  for +p: Nat
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +key: String
  for bit: Bool
  for route: {Map.bit(key, p) == (key, bit) : String & Bool}
  for left: {Maybe.is_some(&2, String, I.seek_found(V, Map.seek(&2, V, lo, key))) == True{} : Bool}
  for right: {Maybe.is_some(&2, String, I.seek_found(V, Map.seek(&2, V, hi, key))) == True{} : Bool}
  {Maybe.is_some(&2, String, I.seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key))) == True{} : Bool}
def branch(V, p, lo, hi, key, bit, route, left, right):
  match bit:
    case False{}:
      %Equal.sym(Maybe<&2, String>, I.seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key)), I.seek_found(V, Map.seek(&2, V, lo, key)), I.seek_left(V, lo, hi, p, key, route)) : {Maybe.is_some(&2, String, _) == True{} : Bool}
      left
    case True{}:
      %Equal.sym(Maybe<&2, String>, I.seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key)), I.seek_found(V, Map.seek(&2, V, hi, key)), I.seek_right(V, lo, hi, p, key, route)) : {Maybe.is_some(&2, String, _) == True{} : Bool}
      right

law from_parts:
  for -V: Data
  for +p: Nat
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +key: String
  for facts: Parts.NodeFacts(V, p, lo, hi)
  for left: {Inv.critbit(V, lo) == True{} : Bool} -> {Inv.nonempty(V, lo) == True{} : Bool} -> {Maybe.is_some(&2, String, I.seek_found(V, Map.seek(&2, V, lo, key))) == True{} : Bool}
  for right: {Inv.critbit(V, hi) == True{} : Bool} -> {Inv.nonempty(V, hi) == True{} : Bool} -> {Maybe.is_some(&2, String, I.seek_found(V, Map.seek(&2, V, hi, key))) == True{} : Bool}
  {Maybe.is_some(&2, String, I.seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key))) == True{} : Bool}
def from_parts(V, p, lo, hi, key, facts, left, right):
  match facts:
    case (common, nl, nh, bl, bh, rl, rh, vl, vh):
      branch(V, p, lo, hi, key, I.route_bit(Map.bit(key, p)), I.route_shape(key, p), left(vl, nl), right(vh, nh))

# A valid nonempty native tree cannot seek into an empty child.
law nonempty_seek:
  for -V: Data
  for tree: Map<&2, V>
  for +key: String
  for valid: {Inv.critbit(V, tree) == True{} : Bool}
  for occupied: {Inv.nonempty(V, tree) == True{} : Bool}
  {Maybe.is_some(&2, String, I.seek_found(V, Map.seek(&2, V, tree, key))) == True{} : Bool}
def nonempty_seek(V, tree, key, valid, occupied):
  match tree:
    case MTip{}: Empty.absurd({Maybe.is_some(&2, String, I.seek_found(V, Map.seek(&2, V, MTip{}, key))) == True{} : Bool}, R.false_true(occupied))
    case MLeaf{stored, value}: {==}
    case MNode{+p, +lo, +hi}:
      from_parts(V, p, lo, hi, key, Parts.node_parts(V, p, lo, hi, valid), v => n => nonempty_seek(V, lo, key, v, n), v => n => nonempty_seek(V, hi, key, v, n))

law empty_seek_is_tip:
  for -V: Data
  for tree: Map<&2, V>
  for +key: String
  for valid: {Inv.critbit(V, tree) == True{} : Bool}
  for missing: {I.seek_found(V, Map.seek(&2, V, tree, key)) == None{} : Maybe<&2, String>}
  {tree == MTip{} : Map<&2, V>}
def empty_seek_is_tip(V, tree, key, valid, missing):
  match tree:
    case MTip{}: {==}
    case MLeaf{stored, value}:
      Empty.absurd({MLeaf{stored, value} == MTip{} : Map<&2, V>}, R.false_true(Equal.sym(Bool, True{}, False{}, Equal.cong(Maybe<&2, String>, Bool, m => Maybe.is_some(&2, String, m), Some{stored}, None{}, missing))))
    case MNode{+p, +lo, +hi}:
      present = nonempty_seek(V, MNode{p, lo, hi}, key, valid, {==})
      absent = Equal.cong(Maybe<&2, String>, Bool, m => Maybe.is_some(&2, String, m), I.seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key)), None{}, missing)
      Empty.absurd({MNode{p, lo, hi} == MTip{} : Map<&2, V>}, R.false_true(Equal.trans(Bool, False{}, Maybe.is_some(&2, String, I.seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key))), True{}, Equal.sym(Bool, Maybe.is_some(&2, String, I.seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key))), False{}, absent), present)))
