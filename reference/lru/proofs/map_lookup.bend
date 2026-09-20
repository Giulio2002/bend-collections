import Base
import ./map_insert.bend as I
import ./native_map.bend as N

# Structural membership names a real leaf and its exact value. No lookup
# algorithm or native-map axiom is hidden in this proposition.
def leaf(-V: Data, tree: Map<&2, Maybe<&2, V>>, key: String, value: V) -> Type:
  match tree:
    case MTip{}:
      Empty
    case MLeaf{stored, item}:
      {key == stored : String} & {Some{value} == item : Maybe<&2, V>}
    case MNode{p, lo, hi}:
      Either<&1, &1, leaf(V, lo, key, value), leaf(V, hi, key, value)>

def certificate(-V: Data, tree: Map<&2, Maybe<&2, V>>, key: String, found: Maybe<&2, V>) -> Type:
  match found:
    case None{}:
      Unit
    case Some{value}:
      leaf(V, tree, key, value)

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
      (N.string_equal_from_comparison(key, stored, e), {==})

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
  for lo: Map<&2, Maybe<&2, V>>
  for hi: Map<&2, Maybe<&2, V>>
  for p: Nat
  for key: String
  for found: Maybe<&2, V>
  for cp: certificate(V, lo, key, found)
  certificate(V, MNode{p, lo, hi}, key, found)
def lift_left(V, lo, hi, p, key, found, cp):
  match found:
    case None{}:
      Unit{}
    case Some{value}:
      Inl{cp}

law lift_right:
  for -V: Data
  for lo: Map<&2, Maybe<&2, V>>
  for hi: Map<&2, Maybe<&2, V>>
  for p: Nat
  for key: String
  for found: Maybe<&2, V>
  for cp: certificate(V, hi, key, found)
  certificate(V, MNode{p, lo, hi}, key, found)
def lift_right(V, lo, hi, p, key, found, cp):
  match found:
    case None{}:
      Unit{}
    case Some{value}:
      Inr{cp}

law branch:
  for -V: Data
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +p: Nat
  for +key: String
  for bit: Bool
  for e: {Map.bit(key, p) == (key, bit) : String & Bool}
  for lp: certificate(V, lo, key, I.lookup(Maybe<&2, V>, None{}, lo, key))
  for hp: certificate(V, hi, key, I.lookup(Maybe<&2, V>, None{}, hi, key))
  certificate(V, MNode{p, lo, hi}, key, I.lookup(Maybe<&2, V>, None{}, MNode{p, lo, hi}, key))
def branch(V, lo, hi, p, key, bit, e, lp, hp):
  match bit:
    case False{}:
      %Equal.sym(Maybe<&2, V>, I.lookup(Maybe<&2, V>, None{}, MNode{p, lo, hi}, key), I.lookup(Maybe<&2, V>, None{}, lo, key), I.node_left(Maybe<&2, V>, None{}, lo, hi, p, key, e)) : certificate(V, MNode{p, lo, hi}, key, _)
      lift_left(V, lo, hi, p, key, I.lookup(Maybe<&2, V>, None{}, lo, key), lp)
    case True{}:
      %Equal.sym(Maybe<&2, V>, I.lookup(Maybe<&2, V>, None{}, MNode{p, lo, hi}, key), I.lookup(Maybe<&2, V>, None{}, hi, key), I.node_right(Maybe<&2, V>, None{}, lo, hi, p, key, e)) : certificate(V, MNode{p, lo, hi}, key, _)
      lift_right(V, lo, hi, p, key, I.lookup(Maybe<&2, V>, None{}, hi, key), hp)

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

# No tree validity premise is needed for this direction. Converse membership
# implies successful lookup still needs routing/uniqueness invariants.
law returned_value_is_stored:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for value: V
  for found: {I.lookup(Maybe<&2, V>, None{}, tree, key) == Some{value} : Maybe<&2, V>}
  leaf(V, tree, key, value)
def returned_value_is_stored(V, tree, key, value, found):
  %found : certificate(V, tree, key, _)
  lookup_certificate(V, tree, key)

# Independent list membership for actual Map.to_list output.
def listed(-V: Data, entries: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, V>>>, key: String, value: V) -> Type:
  match entries:
    case Nil{}:
      Empty
    case Con{Tuple{stored, item}, tail}:
      Either<&1, &1, {key == stored : String} & {Some{value} == item : Maybe<&2, V>}, listed(V, tail, key, value)>

law accumulator_included:
  for -V: Data
  for tree: Map<&2, Maybe<&2, V>>
  for +acc: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, V>>>
  for +key: String
  for +value: V
  for member: listed(V, acc, key, value)
  listed(V, Map.to_list.go(&2, Maybe<&2, V>, tree, acc), key, value)
def accumulator_included(V, tree, acc, key, value, member):
  match tree:
    case MTip{}:
      member
    case MLeaf{stored, item}:
      Inr{member}
    case MNode{p, lo, +hi}:
      accumulator_included(V, lo, Map.to_list.go(&2, Maybe<&2, V>, hi, acc), key, value, accumulator_included(V, hi, acc, key, value, member))

law leaf_enumerated:
  for -V: Data
  for tree: Map<&2, Maybe<&2, V>>
  for +acc: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, V>>>
  for +key: String
  for +value: V
  for member: leaf(V, tree, key, value)
  listed(V, Map.to_list.go(&2, Maybe<&2, V>, tree, acc), key, value)
def leaf_enumerated(V, tree, acc, key, value, member):
  match tree:
    case MTip{}:
      Empty.absurd(listed(V, acc, key, value), member)
    case MLeaf{stored, item}:
      Inl{member}
    case MNode{p, +lo, +hi}:
      match member:
        case Inl{lp}:
          leaf_enumerated(V, lo, Map.to_list.go(&2, Maybe<&2, V>, hi, acc), key, value, lp)
        case Inr{hp}:
          accumulator_included(V, lo, Map.to_list.go(&2, Maybe<&2, V>, hi, acc), key, value, leaf_enumerated(V, hi, acc, key, value, hp))

law returned_value_enumerated:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +value: V
  for found: {I.lookup(Maybe<&2, V>, None{}, tree, key) == Some{value} : Maybe<&2, V>}
  listed(V, Map.to_list(&2, Maybe<&2, V>, tree), key, value)
def returned_value_enumerated(V, tree, key, value, found):
  leaf_enumerated(V, tree, Nil{}, key, value, returned_value_is_stored(V, tree, key, value, found))
