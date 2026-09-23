import Base
import ./native_map.bend as N
import ./map_insert.bend as I
import ./map_routing.bend as R
import ./map_delete_prefix.bend as P

# Every stored leaf has an actual value, including entries with zero deadlines.
def populated(-V: Data, tree: Map<&2, Maybe<&2, V>>) -> Bool:
  match tree:
    case MTip{}: True{}
    case MLeaf{key, item}: Maybe.is_some(&2, V, item)
    case MNode{p, lo, hi}: populated(V, lo) && populated(V, hi)

law splice_bit:
  for -V: Data
  for +key: String
  for value: Maybe<&2, V>
  for +rest: Map<&2, Maybe<&2, V>>
  for discriminator: Nat
  for bit: Bool
  for fresh: {populated(V, MLeaf{key, value}) == True{} : Bool}
  for existing: {populated(V, rest) == True{} : Bool}
  {populated(V, Map.ins.splice.bit(&2, Maybe<&2, V>, value, rest, discriminator, (key, bit))) == True{} : Bool}
def splice_bit(V, key, value, rest, discriminator, bit, fresh, existing):
  match bit:
    case False{}:
      P.conjunction(populated(V, MLeaf{key, value}), populated(V, rest), fresh, existing)
    case True{}:
      P.conjunction(populated(V, rest), populated(V, MLeaf{key, value}), existing, fresh)

law splice:
  for -V: Data
  for +key: String
  for +value: Maybe<&2, V>
  for +rest: Map<&2, Maybe<&2, V>>
  for +discriminator: Nat
  for fresh: {populated(V, MLeaf{key, value}) == True{} : Bool}
  for existing: {populated(V, rest) == True{} : Bool}
  {populated(V, Map.ins.splice(&2, Maybe<&2, V>, discriminator, key, value, rest)) == True{} : Bool}
def splice(V, key, value, rest, discriminator, fresh, existing):
  %Equal.sym(String & Bool, Map.bit(key, discriminator), (key, I.route_bit(Map.bit(key, discriminator))), I.route_shape(key, discriminator)) : {populated(V, Map.ins.splice.bit(&2, Maybe<&2, V>, value, rest, discriminator, _)) == True{} : Bool}
  splice_bit(V, key, value, rest, discriminator, I.route_bit(Map.bit(key, discriminator)), fresh, existing)

law deep_bit:
  for -V: Data
  for +key: String
  for +value: Maybe<&2, V>
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +discriminator: Nat
  for parent: Nat
  for bit: Bool
  for left: {populated(V, lo) == True{} : Bool}
  for right: {populated(V, hi) == True{} : Bool}
  for changed_left: {populated(V, Map.ins(&2, Maybe<&2, V>, lo, key, value, discriminator)) == True{} : Bool}
  for changed_right: {populated(V, Map.ins(&2, Maybe<&2, V>, hi, key, value, discriminator)) == True{} : Bool}
  {populated(V, Map.ins.deep(&2, Maybe<&2, V>, value, lo, hi, discriminator, parent, (key, bit))) == True{} : Bool}
def deep_bit(V, key, value, lo, hi, discriminator, parent, bit, left, right, changed_left, changed_right):
  match bit:
    case False{}:
      P.conjunction(populated(V, Map.ins(&2, Maybe<&2, V>, lo, key, value, discriminator)), populated(V, hi), changed_left, right)
    case True{}:
      P.conjunction(populated(V, lo), populated(V, Map.ins(&2, Maybe<&2, V>, hi, key, value, discriminator)), left, changed_right)

law branch:
  for -V: Data
  for +key: String
  for +value: Maybe<&2, V>
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +discriminator: Nat
  for +parent: Nat
  for descend: Bool
  for fresh: {populated(V, MLeaf{key, value}) == True{} : Bool}
  for left: {populated(V, lo) == True{} : Bool}
  for right: {populated(V, hi) == True{} : Bool}
  for changed_left: {populated(V, Map.ins(&2, Maybe<&2, V>, lo, key, value, discriminator)) == True{} : Bool}
  for changed_right: {populated(V, Map.ins(&2, Maybe<&2, V>, hi, key, value, discriminator)) == True{} : Bool}
  {populated(V, Map.ins.if(&2, Maybe<&2, V>, key, value, lo, hi, parent, discriminator, descend)) == True{} : Bool}
def branch(V, key, value, lo, hi, discriminator, parent, descend, fresh, left, right, changed_left, changed_right):
  match descend:
    case False{}:
      splice(V, key, value, MNode{parent, lo, hi}, discriminator, fresh, P.conjunction(populated(V, lo), populated(V, hi), left, right))
    case True{}:
      %Equal.sym(String & Bool, Map.bit(key, parent), (key, I.route_bit(Map.bit(key, parent))), I.route_shape(key, parent)) : {populated(V, Map.ins.deep(&2, Maybe<&2, V>, value, lo, hi, discriminator, parent, _)) == True{} : Bool}
      deep_bit(V, key, value, lo, hi, discriminator, parent, I.route_bit(Map.bit(key, parent)), left, right, changed_left, changed_right)

# Actual native insertion preserves populated leaves when the new value is present.
law insertion_preserves_populated:
  for -V: Data
  for tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +value: Maybe<&2, V>
  for +discriminator: Nat
  for +fresh: {populated(V, MLeaf{key, value}) == True{} : Bool}
  for +existing: {populated(V, tree) == True{} : Bool}
  {populated(V, Map.ins(&2, Maybe<&2, V>, tree, key, value, discriminator)) == True{} : Bool}
def insertion_preserves_populated(V, tree, key, value, discriminator, fresh, existing):
  match tree:
    case MTip{}: fresh
    case MLeaf{stored, old}:
      splice(V, key, value, MLeaf{stored, old}, discriminator, fresh, existing)
    case MNode{+parent, +lo, +hi}:
      +left = R.and_left(populated(V, lo), populated(V, hi), existing)
      +right = R.and_right(populated(V, lo), populated(V, hi), existing)
      branch(V, key, value, lo, hi, discriminator, parent, Nat.is_lt(parent, discriminator), fresh, left, right,
        insertion_preserves_populated(V, lo, key, value, discriminator, fresh, left),
        insertion_preserves_populated(V, hi, key, value, discriminator, fresh, right))

law put_branch:
  for -V: Data
  for +key: String
  for +value: Maybe<&2, V>
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for p: Nat
  for bit: Bool
  for left: {populated(V, lo) == True{} : Bool}
  for right: {populated(V, hi) == True{} : Bool}
  for changed_left: {populated(V, Map.put(&2, Maybe<&2, V>, lo, key, value)) == True{} : Bool}
  for changed_right: {populated(V, Map.put(&2, Maybe<&2, V>, hi, key, value)) == True{} : Bool}
  {populated(V, Map.put.bit(&2, Maybe<&2, V>, value, p, lo, hi, (key, bit))) == True{} : Bool}
def put_branch(V, key, value, lo, hi, p, bit, left, right, changed_left, changed_right):
  match bit:
    case False{}: P.conjunction(populated(V, Map.put(&2, Maybe<&2, V>, lo, key, value)), populated(V, hi), changed_left, right)
    case True{}: P.conjunction(populated(V, lo), populated(V, Map.put(&2, Maybe<&2, V>, hi, key, value)), left, changed_right)

law put_preserves_populated:
  for -V: Data
  for tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +value: Maybe<&2, V>
  for +fresh: {Maybe.is_some(&2, V, value) == True{} : Bool}
  for +existing: {populated(V, tree) == True{} : Bool}
  {populated(V, Map.put(&2, Maybe<&2, V>, tree, key, value)) == True{} : Bool}
def put_preserves_populated(V, tree, key, value, fresh, existing):
  match tree:
    case MTip{}: fresh
    case MLeaf{stored, old}: fresh
    case MNode{+p, +lo, +hi}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, I.route_bit(Map.bit(key, p))), I.route_shape(key, p)) : {populated(V, Map.put.bit(&2, Maybe<&2, V>, value, p, lo, hi, _)) == True{} : Bool}
      put_branch(V, key, value, lo, hi, p, I.route_bit(Map.bit(key, p)), R.and_left(populated(V, lo), populated(V, hi), existing), R.and_right(populated(V, lo), populated(V, hi), existing), put_preserves_populated(V, lo, key, value, fresh, R.and_left(populated(V, lo), populated(V, hi), existing)), put_preserves_populated(V, hi, key, value, fresh, R.and_right(populated(V, lo), populated(V, hi), existing)))

law comparison_case:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +stored: String
  for +value: Maybe<&2, V>
  for c: Cmp
  for compared: {N.comparison_tag(String, String.cmp(key, stored)) == c : Cmp}
  for found: {I.seek_found(Maybe<&2, V>, Map.seek(&2, Maybe<&2, V>, tree, key)) == Some{stored} : Maybe<&2, String>}
  for +fresh: {Maybe.is_some(&2, V, value) == True{} : Bool}
  for valid: {populated(V, tree) == True{} : Bool}
  {populated(V, Map.set.fin.go(&2, Maybe<&2, V>, tree, key, value, ((key, stored), c))) == True{} : Bool}
def comparison_case(V, tree, key, stored, value, c, compared, found, fresh, valid):
  match c:
    case LT{}: insertion_preserves_populated(V, tree, key, value, Map.diff(key, stored), fresh, valid)
    case EQ{}: put_preserves_populated(V, tree, key, value, fresh, valid)
    case GT{}: insertion_preserves_populated(V, tree, key, value, Map.diff(key, stored), fresh, valid)

law found_case:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +stored: String
  for +value: Maybe<&2, V>
  for found: {I.seek_found(Maybe<&2, V>, Map.seek(&2, Maybe<&2, V>, tree, key)) == Some{stored} : Maybe<&2, String>}
  for +fresh: {Maybe.is_some(&2, V, value) == True{} : Bool}
  for valid: {populated(V, tree) == True{} : Bool}
  {populated(V, Map.set.fin(&2, Maybe<&2, V>, tree, key, value, key, stored)) == True{} : Bool}
def found_case(V, tree, key, stored, value, found, fresh, valid):
  %Equal.sym((String & String) & Cmp, String.cmp(key, stored), ((key, stored), N.comparison_tag(String, String.cmp(key, stored))), N.string_comparison_shape(key, stored)) : {populated(V, Map.set.fin.go(&2, Maybe<&2, V>, tree, key, value, _)) == True{} : Bool}
  comparison_case(V, tree, key, stored, value, N.comparison_tag(String, String.cmp(key, stored)), {==}, found, fresh, valid)

law seek_case:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for value: Maybe<&2, V>
  for found: Maybe<&2, String>
  for selected: {I.seek_found(Maybe<&2, V>, Map.seek(&2, Maybe<&2, V>, tree, key)) == found : Maybe<&2, String>}
  for +fresh: {Maybe.is_some(&2, V, value) == True{} : Bool}
  for valid: {populated(V, tree) == True{} : Bool}
  {populated(V, Map.set.go(&2, Maybe<&2, V>, value, (tree, key, found))) == True{} : Bool}
def seek_case(V, tree, key, value, found, selected, fresh, valid):
  match found:
    case None{}: fresh
    case Some{stored}: found_case(V, tree, key, stored, value, selected, fresh, valid)

# Native set never stores None when the input leaves and new payload are populated.
law set_preserves_populated:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +value: Maybe<&2, V>
  for +fresh: {Maybe.is_some(&2, V, value) == True{} : Bool}
  for valid: {populated(V, tree) == True{} : Bool}
  {populated(V, Map.set(&2, Maybe<&2, V>, tree, key, value)) == True{} : Bool}
def set_preserves_populated(V, tree, key, value, fresh, valid):
  %Equal.sym(Map<&2, Maybe<&2, V>> & String & Maybe<&2, String>, Map.seek(&2, Maybe<&2, V>, tree, key), (tree, key, I.seek_found(Maybe<&2, V>, Map.seek(&2, Maybe<&2, V>, tree, key))), I.seek_shape(Maybe<&2, V>, tree, key)) : {populated(V, Map.set.go(&2, Maybe<&2, V>, value, _)) == True{} : Bool}
  seek_case(V, tree, key, value, I.seek_found(Maybe<&2, V>, Map.seek(&2, Maybe<&2, V>, tree, key)), {==}, fresh, valid)
