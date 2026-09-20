import Base
import ./map_insert.bend as I
import ./native_map.bend as N
import ./map_shape.bend as Shape

# Successful lookup and seek traverse the actual same native routing path.
def certificate(-V: Data, tree: Map<&2, Maybe<&2, V>>, key: String, found: Maybe<&2, V>) -> Type:
  match found:
    case None{}:
      Unit
    case Some{value}:
      {I.seek_found(Maybe<&2, V>, Map.seek(&2, Maybe<&2, V>, tree, key)) == Some{key} : Maybe<&2, String>}

law leaf_comparison:
  for -V: Data
  for +key: String
  for +stored: String
  for item: Maybe<&2, V>
  for cmp: Cmp
  for e: {N.comparison_tag(String, String.cmp(key, stored)) == cmp : Cmp}
  certificate(V, MLeaf{stored, item}, key, I.value(Maybe<&2, V>, Map.get.leaf(Maybe<&2, V>, None{}, item, ((key, stored), cmp))))
def leaf_comparison(V, key, stored, item, cmp, e):
  match item cmp:
    case None{} LT{}:
      Unit{}
    case None{} EQ{}:
      Unit{}
    case None{} GT{}:
      Unit{}
    case Some{value} LT{}:
      Unit{}
    case Some{value} GT{}:
      Unit{}
    case Some{value} EQ{}:
      Equal.cong(String, Maybe<&2, String>, k => Some{k}, stored, key, Equal.sym(String, key, stored, N.string_equal_from_comparison(key, stored, e)))

law leaf_lookup:
  for -V: Data
  for +key: String
  for +stored: String
  for +item: Maybe<&2, V>
  certificate(V, MLeaf{stored, item}, key, I.lookup(Maybe<&2, V>, None{}, MLeaf{stored, item}, key))
def leaf_lookup(V, key, stored, item):
  %Equal.sym((String & String) & Cmp, String.cmp(key, stored), ((key, stored), N.comparison_tag(String, String.cmp(key, stored))), N.string_comparison_shape(key, stored)) : certificate(V, MLeaf{stored, item}, key, I.value(Maybe<&2, V>, Map.get.leaf(Maybe<&2, V>, None{}, item, _)))
  leaf_comparison(V, key, stored, item, N.comparison_tag(String, String.cmp(key, stored)), {==})

law lift_left:
  for -V: Data
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +p: Nat
  for +key: String
  for found: Maybe<&2, V>
  for e: {Map.bit(key, p) == (key, False{}) : String & Bool}
  for cp: certificate(V, lo, key, found)
  certificate(V, MNode{p, lo, hi}, key, found)
def lift_left(V, lo, hi, p, key, found, e, cp):
  match found:
    case None{}:
      Unit{}
    case Some{value}:
      Equal.trans(Maybe<&2, String>, I.seek_found(Maybe<&2, V>, Map.seek(&2, Maybe<&2, V>, MNode{p, lo, hi}, key)), I.seek_found(Maybe<&2, V>, Map.seek(&2, Maybe<&2, V>, lo, key)), Some{key}, I.seek_left(Maybe<&2, V>, lo, hi, p, key, e), cp)

law lift_right:
  for -V: Data
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +p: Nat
  for +key: String
  for found: Maybe<&2, V>
  for e: {Map.bit(key, p) == (key, True{}) : String & Bool}
  for cp: certificate(V, hi, key, found)
  certificate(V, MNode{p, lo, hi}, key, found)
def lift_right(V, lo, hi, p, key, found, e, cp):
  match found:
    case None{}:
      Unit{}
    case Some{value}:
      Equal.trans(Maybe<&2, String>, I.seek_found(Maybe<&2, V>, Map.seek(&2, Maybe<&2, V>, MNode{p, lo, hi}, key)), I.seek_found(Maybe<&2, V>, Map.seek(&2, Maybe<&2, V>, hi, key)), Some{key}, I.seek_right(Maybe<&2, V>, lo, hi, p, key, e), cp)

law branch:
  for -V: Data
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +p: Nat
  for +key: String
  for bit: Bool
  for +e: {Map.bit(key, p) == (key, bit) : String & Bool}
  for lp: certificate(V, lo, key, I.lookup(Maybe<&2, V>, None{}, lo, key))
  for hp: certificate(V, hi, key, I.lookup(Maybe<&2, V>, None{}, hi, key))
  certificate(V, MNode{p, lo, hi}, key, I.lookup(Maybe<&2, V>, None{}, MNode{p, lo, hi}, key))
def branch(V, lo, hi, p, key, bit, e, lp, hp):
  match bit:
    case False{}:
      %Equal.sym(Maybe<&2, V>, I.lookup(Maybe<&2, V>, None{}, MNode{p, lo, hi}, key), I.lookup(Maybe<&2, V>, None{}, lo, key), I.node_left(Maybe<&2, V>, None{}, lo, hi, p, key, e)) : certificate(V, MNode{p, lo, hi}, key, _)
      lift_left(V, lo, hi, p, key, I.lookup(Maybe<&2, V>, None{}, lo, key), e, lp)
    case True{}:
      %Equal.sym(Maybe<&2, V>, I.lookup(Maybe<&2, V>, None{}, MNode{p, lo, hi}, key), I.lookup(Maybe<&2, V>, None{}, hi, key), I.node_right(Maybe<&2, V>, None{}, lo, hi, p, key, e)) : certificate(V, MNode{p, lo, hi}, key, _)
      lift_right(V, lo, hi, p, key, I.lookup(Maybe<&2, V>, None{}, hi, key), e, hp)

law lookup_certificate:
  for -V: Data
  for tree: Map<&2, Maybe<&2, V>>
  for +key: String
  certificate(V, tree, key, I.lookup(Maybe<&2, V>, None{}, tree, key))
def lookup_certificate(V, tree, key):
  match tree:
    case MTip{}:
      Unit{}
    case MLeaf{stored, item}:
      leaf_lookup(V, key, stored, item)
    case MNode{+p, +lo, +hi}:
      branch(V, lo, hi, p, key, I.route_bit(Map.bit(key, p)), I.route_shape(key, p), lookup_certificate(V, lo, key), lookup_certificate(V, hi, key))


law successful_lookup_seeks_key:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for value: V
  for found: {I.lookup(Maybe<&2, V>, None{}, tree, key) == Some{value} : Maybe<&2, V>}
  {I.seek_found(Maybe<&2, V>, Map.seek(&2, Maybe<&2, V>, tree, key)) == Some{key} : Maybe<&2, String>}
def successful_lookup_seeks_key(V, tree, key, value, found):
  %found : certificate(V, tree, key, _)
  lookup_certificate(V, tree, key)

# Discharges the previously explicit seek premise using actual lookup success.
law successful_replacement_preserves_keys:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for previous: V
  for item: Maybe<&2, V>
  for found: {I.lookup(Maybe<&2, V>, None{}, tree, key) == Some{previous} : Maybe<&2, V>}
  {Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, tree, key, item)) == Map.keys(&2, Maybe<&2, V>, tree) : List<&2, String>}
def successful_replacement_preserves_keys(V, tree, key, previous, item, found):
  Shape.set_existing_keys(Maybe<&2, V>, tree, key, item, successful_lookup_seeks_key(V, tree, key, previous, found))
