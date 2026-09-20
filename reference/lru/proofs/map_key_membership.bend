import Base
import ./invariants.bend as Inv
import ./map_lookup.bend as L
import ./native_map.bend as N
import ./map_routing.bend as R
import ./recency_unique.bend as U

law eq_true:
  for +a: String
  for +b: String
  for same: {a == b : String}
  {String.eq(a, b) == True{} : Bool}
def eq_true(a, b, same):
  %Equal.sym((String & String) & Cmp, String.cmp(a, b), ((a, b), EQ{}), N.string_equal_comparison(a, b, same)) : {String.eq.fin(_) == True{} : Bool}
  {==}

law or_true:
  for b: Bool
  {b || True{} == True{} : Bool}
def or_true(b):
  match b:
    case False{}: {==}
    case True{}: {==}

law member_cons:
  for +head: String
  for +tail: List<&2, String>
  for +key: String
  for member: {Inv.member(tail, key) == True{} : Bool}
  {Inv.member(Con{head, tail}, key) == True{} : Bool}
def member_cons(head, tail, key, member):
  %Equal.sym(Bool, Inv.member(tail, key), True{}, member) : {String.eq(head, key) || _ == True{} : Bool}
  or_true(String.eq(head, key))

law accumulator_member:
  for -V: Data
  for tree: Map<&2, V>
  for +acc: List<&2, String>
  for +key: String
  for member: {Inv.member(acc, key) == True{} : Bool}
  {Inv.member(Map.keys.go(&2, V, tree, acc), key) == True{} : Bool}
def accumulator_member(V, tree, acc, key, member):
  match tree:
    case MTip{}: member
    case MLeaf{stored, item}: member_cons(stored, acc, key, member)
    case MNode{p, +lo, +hi}:
      accumulator_member(V, lo, Map.keys.go(&2, V, hi, acc), key, accumulator_member(V, hi, acc, key, member))

law leaf_member:
  for -V: Data
  for tree: Map<&2, Maybe<&2, V>>
  for +acc: List<&2, String>
  for +key: String
  for +value: V
  for leaf: L.leaf(V, tree, key, value)
  {Inv.member(Map.keys.go(&2, Maybe<&2, V>, tree, acc), key) == True{} : Bool}
def leaf_member(V, tree, acc, key, value, leaf):
  match tree:
    case MTip{}: Empty.absurd({Inv.member(acc, key) == True{} : Bool}, leaf)
    case MLeaf{+stored, item}:
      (same, item_eq) = leaf
      %Equal.sym(Bool, String.eq(stored, key), True{}, eq_true(stored, key, Equal.sym(String, key, stored, same))) : {_ || Inv.member(acc, key) == True{} : Bool}
      {==}
    case MNode{p, +lo, +hi}:
      match leaf:
        case Inl{left}: leaf_member(V, lo, Map.keys.go(&2, Maybe<&2, V>, hi, acc), key, value, left)
        case Inr{right}: accumulator_member(Maybe<&2, V>, lo, Map.keys.go(&2, Maybe<&2, V>, hi, acc), key, leaf_member(V, hi, acc, key, value, right))

law included_branch:
  for +head: String
  for +tail: List<&2, String>
  for +ys: List<&2, String>
  for +key: String
  for same: Bool
  for decision: {String.eq(head, key) == same : Bool}
  for member: {same || Inv.member(tail, key) == True{} : Bool}
  for head_in: {Inv.member(ys, head) == True{} : Bool}
  for recurse: {Inv.member(tail, key) == True{} : Bool} -> {Inv.member(ys, key) == True{} : Bool}
  {Inv.member(ys, key) == True{} : Bool}
def included_branch(head, tail, ys, key, same, decision, member, head_in, recurse):
  match same:
    case False{}: recurse(member)
    case True{}:
      %U.equal_boolean(head, key, decision) : {Inv.member(ys, _) == True{} : Bool}
      head_in

law included_member:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  for +key: String
  for +included: {Inv.included(xs, ys) == True{} : Bool}
  for member: {Inv.member(xs, key) == True{} : Bool}
  {Inv.member(ys, key) == True{} : Bool}
def included_member(xs, ys, key, included, member):
  match xs:
    case Nil{}: Empty.absurd({Inv.member(ys, key) == True{} : Bool}, R.false_true(member))
    case Con{+head, +tail}:
      included_branch(head, tail, ys, key, String.eq(head, key), {==}, member, R.and_left(Inv.member(ys, head), Inv.included(tail, ys), included), m => included_member(tail, ys, key, R.and_right(Inv.member(ys, head), Inv.included(tail, ys), included), m))
