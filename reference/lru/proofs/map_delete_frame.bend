import Base
import ./native_map.bend as N
import ./map_insert.bend as I
import ./map_lookup.bend as L
import ./map_routing.bend as R
import ./map_delete_routes.bend as D

# Actual pop only removes the selected matching leaf. Every other binding
# survives, even in malformed trees; lookup observability additionally needs R.valid.
def different(a: String, b: String) -> Type:
  {a == b : String} -> Empty

law collapse_low:
  for -V: Data
  for p: Nat
  for hi: Map<&2, Maybe<&2, V>>
  for r: Map<&2, Maybe<&2, V>> & Maybe<&2, Maybe<&2, V>>
  for key: String
  for value: V
  for member: L.leaf(V, MNode{p, Map.del.fin(&2, Maybe<&2, V>, r), hi}, key, value)
  L.leaf(V, Map.del.fin(&2, Maybe<&2, V>, Map.pop.lo(&2, Maybe<&2, V>, p, hi, r)), key, value)
def collapse_low(V, p, hi, r, key, value, member):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}:
          match member:
            case Inl{impossible}:
              Empty.absurd(L.leaf(V, hi, key, value), impossible)
            case Inr{present}:
              present
        case MLeaf{k, v}:
          member
        case MNode{q, lo, other}:
          member

law collapse_high:
  for -V: Data
  for p: Nat
  for lo: Map<&2, Maybe<&2, V>>
  for r: Map<&2, Maybe<&2, V>> & Maybe<&2, Maybe<&2, V>>
  for key: String
  for value: V
  for member: L.leaf(V, MNode{p, lo, Map.del.fin(&2, Maybe<&2, V>, r)}, key, value)
  L.leaf(V, Map.del.fin(&2, Maybe<&2, V>, Map.pop.hi(&2, Maybe<&2, V>, p, lo, r)), key, value)
def collapse_high(V, p, lo, r, key, value, member):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}:
          match member:
            case Inl{present}:
              present
            case Inr{impossible}:
              Empty.absurd(L.leaf(V, lo, key, value), impossible)
        case MLeaf{k, v}:
          member
        case MNode{q, other, hi}:
          member

law leaf_case:
  for -V: Data
  for item: Maybe<&2, V>
  for +removed: String
  for +stored: String
  for c: Cmp
  for comparison: {N.comparison_tag(String, String.cmp(removed, stored)) == c : Cmp}
  for +key: String
  for value: V
  for distinct: different(key, removed)
  for member: L.leaf(V, MLeaf{stored, item}, key, value)
  L.leaf(V, Map.del.fin(&2, Maybe<&2, V>, Map.pop.leaf(&2, Maybe<&2, V>, item, ((removed, stored), c))), key, value)
def leaf_case(V, item, removed, stored, c, comparison, key, value, distinct, member):
  match c:
    case LT{}:
      member
    case GT{}:
      member
    case EQ{}:
      (same_key, same_value) = member
      distinct(Equal.trans(String, key, stored, removed, same_key, Equal.sym(String, removed, stored, N.string_equal_from_comparison(removed, stored, comparison))))

law selected_low:
  for -V: Data
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +p: Nat
  for +removed: String
  for +key: String
  for +value: V
  for distinct: different(key, removed)
  for recurse: different(key, removed) -> L.leaf(V, lo, key, value) -> L.leaf(V, Map.del(&2, Maybe<&2, V>, lo, removed), key, value)
  for member: L.leaf(V, MNode{p, lo, hi}, key, value)
  L.leaf(V, Map.del.fin(&2, Maybe<&2, V>, Map.pop.lo(&2, Maybe<&2, V>, p, hi, Map.pop(&2, Maybe<&2, V>, lo, removed))), key, value)
def selected_low(V, lo, hi, p, removed, key, value, distinct, recurse, member):
  match member:
    case Inl{present}:
      collapse_low(V, p, hi, Map.pop(&2, Maybe<&2, V>, lo, removed), key, value, Inl{recurse(distinct)(present)})
    case Inr{present}:
      collapse_low(V, p, hi, Map.pop(&2, Maybe<&2, V>, lo, removed), key, value, Inr{present})

law selected_high:
  for -V: Data
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +p: Nat
  for +removed: String
  for +key: String
  for +value: V
  for distinct: different(key, removed)
  for recurse: different(key, removed) -> L.leaf(V, hi, key, value) -> L.leaf(V, Map.del(&2, Maybe<&2, V>, hi, removed), key, value)
  for member: L.leaf(V, MNode{p, lo, hi}, key, value)
  L.leaf(V, Map.del.fin(&2, Maybe<&2, V>, Map.pop.hi(&2, Maybe<&2, V>, p, lo, Map.pop(&2, Maybe<&2, V>, hi, removed))), key, value)
def selected_high(V, lo, hi, p, removed, key, value, distinct, recurse, member):
  match member:
    case Inl{present}:
      collapse_high(V, p, lo, Map.pop(&2, Maybe<&2, V>, hi, removed), key, value, Inl{present})
    case Inr{present}:
      collapse_high(V, p, lo, Map.pop(&2, Maybe<&2, V>, hi, removed), key, value, Inr{recurse(distinct)(present)})

law branch:
  for -V: Data
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +p: Nat
  for +removed: String
  for bit: Bool
  for e: {Map.bit(removed, p) == (removed, bit) : String & Bool}
  for +key: String
  for +value: V
  for distinct: different(key, removed)
  for lp: different(key, removed) -> L.leaf(V, lo, key, value) -> L.leaf(V, Map.del(&2, Maybe<&2, V>, lo, removed), key, value)
  for hp: different(key, removed) -> L.leaf(V, hi, key, value) -> L.leaf(V, Map.del(&2, Maybe<&2, V>, hi, removed), key, value)
  for member: L.leaf(V, MNode{p, lo, hi}, key, value)
  L.leaf(V, Map.del(&2, Maybe<&2, V>, MNode{p, lo, hi}, removed), key, value)
def branch(V, lo, hi, p, removed, bit, e, key, value, distinct, lp, hp, member):
  match bit:
    case False{}:
      %Equal.sym(String & Bool, Map.bit(removed, p), (removed, False{}), e) : L.leaf(V, Map.del.fin(&2, Maybe<&2, V>, Map.pop.bit(&2, Maybe<&2, V>, lo, hi, p, _)), key, value)
      selected_low(V, lo, hi, p, removed, key, value, distinct, lp, member)
    case True{}:
      %Equal.sym(String & Bool, Map.bit(removed, p), (removed, True{}), e) : L.leaf(V, Map.del.fin(&2, Maybe<&2, V>, Map.pop.bit(&2, Maybe<&2, V>, lo, hi, p, _)), key, value)
      selected_high(V, lo, hi, p, removed, key, value, distinct, hp, member)

law other_binding_survives:
  for -V: Data
  for tree: Map<&2, Maybe<&2, V>>
  for +removed: String
  for +key: String
  for +value: V
  for distinct: different(key, removed)
  for member: L.leaf(V, tree, key, value)
  L.leaf(V, Map.del(&2, Maybe<&2, V>, tree, removed), key, value)
def other_binding_survives(V, tree, removed, key, value, distinct, member):
  match tree:
    case MTip{}:
      member
    case MLeaf{+stored, +item}:
      %Equal.sym((String & String) & Cmp, String.cmp(removed, stored), ((removed, stored), N.comparison_tag(String, String.cmp(removed, stored))), N.string_comparison_shape(removed, stored)) : L.leaf(V, Map.del.fin(&2, Maybe<&2, V>, Map.pop.leaf(&2, Maybe<&2, V>, item, _)), key, value)
      leaf_case(V, item, removed, stored, N.comparison_tag(String, String.cmp(removed, stored)), {==}, key, value, distinct, member)
    case MNode{+p, +lo, +hi}:
      branch(V, lo, hi, p, removed, I.route_bit(Map.bit(removed, p)), I.route_shape(removed, p), key, value, distinct, d => m => other_binding_survives(V, lo, removed, key, value, d, m), d => m => other_binding_survives(V, hi, removed, key, value, d, m), member)

law other_present_lookup:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +removed: String
  for +key: String
  for +value: V
  for valid: R.valid(Maybe<&2, V>, tree)
  for distinct: different(key, removed)
  for found: {I.lookup(Maybe<&2, V>, None{}, tree, key) == Some{value} : Maybe<&2, V>}
  {I.lookup(Maybe<&2, V>, None{}, Map.del(&2, Maybe<&2, V>, tree, removed), key) == Some{value} : Maybe<&2, V>}
def other_present_lookup(V, tree, removed, key, value, valid, distinct, found):
  R.member_lookup(V, Map.del(&2, Maybe<&2, V>, tree, removed), key, value, D.preserves_valid(Maybe<&2, V>, tree, removed, valid), other_binding_survives(V, tree, removed, key, value, distinct, L.returned_value_is_stored(V, tree, key, value, found)))

law uncollapse_low:
  for -V: Data
  for p: Nat
  for hi: Map<&2, Maybe<&2, V>>
  for r: Map<&2, Maybe<&2, V>> & Maybe<&2, Maybe<&2, V>>
  for key: String
  for value: V
  for member: L.leaf(V, Map.del.fin(&2, Maybe<&2, V>, Map.pop.lo(&2, Maybe<&2, V>, p, hi, r)), key, value)
  L.leaf(V, MNode{p, Map.del.fin(&2, Maybe<&2, V>, r), hi}, key, value)
def uncollapse_low(V, p, hi, r, key, value, member):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}:
          Inr{member}
        case MLeaf{k, v}:
          member
        case MNode{q, a, b}:
          member

law restore_low:
  for -V: Data
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +p: Nat
  for +removed: String
  for +key: String
  for +value: V
  for recurse: L.leaf(V, Map.del(&2, Maybe<&2, V>, lo, removed), key, value) -> L.leaf(V, lo, key, value)
  for member: L.leaf(V, MNode{p, Map.del(&2, Maybe<&2, V>, lo, removed), hi}, key, value)
  L.leaf(V, MNode{p, lo, hi}, key, value)
def restore_low(V, lo, hi, p, removed, key, value, recurse, member):
  match member:
    case Inl{present}:
      Inl{recurse(present)}
    case Inr{present}:
      Inr{present}

law uncollapse_high:
  for -V: Data
  for p: Nat
  for lo: Map<&2, Maybe<&2, V>>
  for r: Map<&2, Maybe<&2, V>> & Maybe<&2, Maybe<&2, V>>
  for key: String
  for value: V
  for member: L.leaf(V, Map.del.fin(&2, Maybe<&2, V>, Map.pop.hi(&2, Maybe<&2, V>, p, lo, r)), key, value)
  L.leaf(V, MNode{p, lo, Map.del.fin(&2, Maybe<&2, V>, r)}, key, value)
def uncollapse_high(V, p, lo, r, key, value, member):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}:
          Inl{member}
        case MLeaf{k, v}:
          member
        case MNode{q, a, b}:
          member

law restore_high:
  for -V: Data
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +p: Nat
  for +removed: String
  for +key: String
  for +value: V
  for recurse: L.leaf(V, Map.del(&2, Maybe<&2, V>, hi, removed), key, value) -> L.leaf(V, hi, key, value)
  for member: L.leaf(V, MNode{p, lo, Map.del(&2, Maybe<&2, V>, hi, removed)}, key, value)
  L.leaf(V, MNode{p, lo, hi}, key, value)
def restore_high(V, lo, hi, p, removed, key, value, recurse, member):
  match member:
    case Inl{present}:
      Inl{present}
    case Inr{present}:
      Inr{recurse(present)}

law leaf_original:
  for -V: Data
  for item: Maybe<&2, V>
  for removed: String
  for stored: String
  for c: Cmp
  for key: String
  for value: V
  for member: L.leaf(V, Map.del.fin(&2, Maybe<&2, V>, Map.pop.leaf(&2, Maybe<&2, V>, item, ((removed, stored), c))), key, value)
  L.leaf(V, MLeaf{stored, item}, key, value)
def leaf_original(V, item, removed, stored, c, key, value, member):
  match c:
    case LT{}:
      member
    case GT{}:
      member
    case EQ{}:
      Empty.absurd(L.leaf(V, MLeaf{stored, item}, key, value), member)

law original_branch:
  for -V: Data
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +p: Nat
  for +removed: String
  for bit: Bool
  for e: {Map.bit(removed, p) == (removed, bit) : String & Bool}
  for +key: String
  for +value: V
  for lp: L.leaf(V, Map.del(&2, Maybe<&2, V>, lo, removed), key, value) -> L.leaf(V, lo, key, value)
  for hp: L.leaf(V, Map.del(&2, Maybe<&2, V>, hi, removed), key, value) -> L.leaf(V, hi, key, value)
  for member: L.leaf(V, Map.del(&2, Maybe<&2, V>, MNode{p, lo, hi}, removed), key, value)
  L.leaf(V, MNode{p, lo, hi}, key, value)
def original_branch(V, lo, hi, p, removed, bit, e, key, value, lp, hp, member):
  match bit:
    case False{}:
      restore_low(V, lo, hi, p, removed, key, value, lp, uncollapse_low(V, p, hi, Map.pop(&2, Maybe<&2, V>, lo, removed), key, value, %e : L.leaf(V, Map.del.fin(&2, Maybe<&2, V>, Map.pop.bit(&2, Maybe<&2, V>, lo, hi, p, _)), key, value) member))
    case True{}:
      restore_high(V, lo, hi, p, removed, key, value, hp, uncollapse_high(V, p, lo, Map.pop(&2, Maybe<&2, V>, hi, removed), key, value, %e : L.leaf(V, Map.del.fin(&2, Maybe<&2, V>, Map.pop.bit(&2, Maybe<&2, V>, lo, hi, p, _)), key, value) member))

law no_new_binding:
  for -V: Data
  for tree: Map<&2, Maybe<&2, V>>
  for +removed: String
  for +key: String
  for +value: V
  for member: L.leaf(V, Map.del(&2, Maybe<&2, V>, tree, removed), key, value)
  L.leaf(V, tree, key, value)
def no_new_binding(V, tree, removed, key, value, member):
  match tree:
    case MTip{}:
      member
    case MLeaf{+stored, +item}:
      leaf_original(V, item, removed, stored, N.comparison_tag(String, String.cmp(removed, stored)), key, value, %N.string_comparison_shape(removed, stored) : L.leaf(V, Map.del.fin(&2, Maybe<&2, V>, Map.pop.leaf(&2, Maybe<&2, V>, item, _)), key, value) member)
    case MNode{+p, +lo, +hi}:
      original_branch(V, lo, hi, p, removed, I.route_bit(Map.bit(removed, p)), I.route_shape(removed, p), key, value, m => no_new_binding(V, lo, removed, key, value, m), m => no_new_binding(V, hi, removed, key, value, m), member)

def present(-V: Data, x: Maybe<&2, V>) -> Bool:
  match x:
    case None{}:
      False{}
    case Some{v}:
      True{}

law absent_case:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +removed: String
  for +key: String
  for valid: R.valid(Maybe<&2, V>, tree)
  for absent: {I.lookup(Maybe<&2, V>, None{}, tree, key) == None{} : Maybe<&2, V>}
  for result: Maybe<&2, V>
  for result_eq: {I.lookup(Maybe<&2, V>, None{}, Map.del(&2, Maybe<&2, V>, tree, removed), key) == result : Maybe<&2, V>}
  {I.lookup(Maybe<&2, V>, None{}, Map.del(&2, Maybe<&2, V>, tree, removed), key) == None{} : Maybe<&2, V>}
def absent_case(V, tree, removed, key, valid, absent, result, result_eq):
  match result:
    case None{}:
      result_eq
    case Some{+value}:
      Empty.absurd({I.lookup(Maybe<&2, V>, None{}, Map.del(&2, Maybe<&2, V>, tree, removed), key) == None{} : Maybe<&2, V>}, R.false_true(Equal.cong(Maybe<&2, V>, Bool, x => present(V, x), None{}, Some{value}, Equal.trans(Maybe<&2, V>, None{}, I.lookup(Maybe<&2, V>, None{}, tree, key), Some{value}, Equal.sym(Maybe<&2, V>, I.lookup(Maybe<&2, V>, None{}, tree, key), None{}, absent), R.member_lookup(V, tree, key, value, valid, no_new_binding(V, tree, removed, key, value, L.returned_value_is_stored(V, Map.del(&2, Maybe<&2, V>, tree, removed), key, value, result_eq)))))))

law absent_stays_absent:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +removed: String
  for +key: String
  for valid: R.valid(Maybe<&2, V>, tree)
  for absent: {I.lookup(Maybe<&2, V>, None{}, tree, key) == None{} : Maybe<&2, V>}
  {I.lookup(Maybe<&2, V>, None{}, Map.del(&2, Maybe<&2, V>, tree, removed), key) == None{} : Maybe<&2, V>}
def absent_stays_absent(V, tree, removed, key, valid, absent):
  absent_case(V, tree, removed, key, valid, absent, I.lookup(Maybe<&2, V>, None{}, Map.del(&2, Maybe<&2, V>, tree, removed), key), {==})

law frame_case:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +removed: String
  for +key: String
  for valid: R.valid(Maybe<&2, V>, tree)
  for distinct: different(key, removed)
  for result: Maybe<&2, V>
  for e: {I.lookup(Maybe<&2, V>, None{}, tree, key) == result : Maybe<&2, V>}
  {I.lookup(Maybe<&2, V>, None{}, Map.del(&2, Maybe<&2, V>, tree, removed), key) == result : Maybe<&2, V>}
def frame_case(V, tree, removed, key, valid, distinct, result, e):
  match result:
    case None{}:
      absent_stays_absent(V, tree, removed, key, valid, e)
    case Some{value}:
      other_present_lookup(V, tree, removed, key, value, valid, distinct, e)

law other_lookup_unchanged:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +removed: String
  for +key: String
  for valid: R.valid(Maybe<&2, V>, tree)
  for distinct: different(key, removed)
  {I.lookup(Maybe<&2, V>, None{}, Map.del(&2, Maybe<&2, V>, tree, removed), key) == I.lookup(Maybe<&2, V>, None{}, tree, key) : Maybe<&2, V>}
def other_lookup_unchanged(V, tree, removed, key, valid, distinct):
  frame_case(V, tree, removed, key, valid, distinct, I.lookup(Maybe<&2, V>, None{}, tree, key), {==})
