import Base
import ./invariants.bend as Inv
import ./map_routing.bend as R
import ./map_delete_prefix.bend as And
import ./map_key_disjoint.bend as D
import ./map_key_membership.bend as Keys
import ./cache_delete_membership.bend as Lists
import ./map_populated.bend as Pop
import ./map_critbit_parts.bend as Parts

def apart(xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  match xs:
    case Nil{}: True{}
    case Con{head, tail}: Bool.not(Inv.member(ys, head)) && apart(tail, ys)

law or_assoc:
  for a: Bool
  for b: Bool
  for c: Bool
  {a || (b || c) == (a || b) || c : Bool}
def or_assoc(a, b, c):
  match a:
    case False{}: {==}
    case True{}: {==}

law member_append:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  for +key: String
  {Inv.member(List.append(&2, String, xs, ys), key) == Inv.member(xs, key) || Inv.member(ys, key) : Bool}
def member_append(xs, ys, key):
  match xs:
    case Nil{}: {==}
    case Con{+head, +tail}:
      Equal.trans(Bool, String.eq(head, key) || Inv.member(List.append(&2, String, tail, ys), key), String.eq(head, key) || (Inv.member(tail, key) || Inv.member(ys, key)), (String.eq(head, key) || Inv.member(tail, key)) || Inv.member(ys, key),
        Equal.cong(Bool, Bool, b => String.eq(head, key) || b, Inv.member(List.append(&2, String, tail, ys), key), Inv.member(tail, key) || Inv.member(ys, key), member_append(tail, ys, key)),
        or_assoc(String.eq(head, key), Inv.member(tail, key), Inv.member(ys, key)))

law not_or:
  for a: Bool
  for b: Bool
  for left: {Bool.not(a) == True{} : Bool}
  for right: {Bool.not(b) == True{} : Bool}
  {Bool.not(a || b) == True{} : Bool}
def not_or(a, b, left, right):
  match a:
    case False{}: right
    case True{}: left

law unique_append:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  for +ux: {Inv.unique(xs) == True{} : Bool}
  for +uy: {Inv.unique(ys) == True{} : Bool}
  for +separate: {apart(xs, ys) == True{} : Bool}
  {Inv.unique(List.append(&2, String, xs, ys)) == True{} : Bool}
def unique_append(xs, ys, ux, uy, separate):
  match xs:
    case Nil{}: uy
    case Con{+head, +tail}:
      And.conjunction(Bool.not(Inv.member(List.append(&2, String, tail, ys), head)), Inv.unique(List.append(&2, String, tail, ys)),
        Equal.trans(Bool, Bool.not(Inv.member(List.append(&2, String, tail, ys), head)), Bool.not(Inv.member(tail, head) || Inv.member(ys, head)), True{},
          Equal.cong(Bool, Bool, Bool.not, Inv.member(List.append(&2, String, tail, ys), head), Inv.member(tail, head) || Inv.member(ys, head), member_append(tail, ys, head)),
          not_or(Inv.member(tail, head), Inv.member(ys, head), R.and_left(Bool.not(Inv.member(tail, head)), Inv.unique(tail), ux), R.and_left(Bool.not(Inv.member(ys, head)), apart(tail, ys), separate))),
        unique_append(tail, ys, R.and_right(Bool.not(Inv.member(tail, head)), Inv.unique(tail), ux), uy, R.and_right(Bool.not(Inv.member(ys, head)), apart(tail, ys), separate)))

law keys_go_append:
  for -V: Data
  for tree: Map<&2, V>
  for +acc: List<&2, String>
  for +extra: List<&2, String>
  {Map.keys.go(&2, V, tree, List.append(&2, String, acc, extra)) == List.append(&2, String, Map.keys.go(&2, V, tree, acc), extra) : List<&2, String>}
def keys_go_append(V, tree, acc, extra):
  match tree:
    case MTip{}: {==}
    case MLeaf{key, value}: {==}
    case MNode{position, +lo, +hi}:
      Equal.trans(List<&2, String>, Map.keys.go(&2, V, lo, Map.keys.go(&2, V, hi, List.append(&2, String, acc, extra))), Map.keys.go(&2, V, lo, List.append(&2, String, Map.keys.go(&2, V, hi, acc), extra)), List.append(&2, String, Map.keys.go(&2, V, lo, Map.keys.go(&2, V, hi, acc)), extra),
        Equal.cong(List<&2, String>, List<&2, String>, xs => Map.keys.go(&2, V, lo, xs), Map.keys.go(&2, V, hi, List.append(&2, String, acc, extra)), List.append(&2, String, Map.keys.go(&2, V, hi, acc), extra), keys_go_append(V, hi, acc, extra)),
        keys_go_append(V, lo, Map.keys.go(&2, V, hi, acc), extra))

law routed_apart:
  for -V: Data
  for xs: List<&2, String>
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +position: Nat
  for +left_route: {Inv.routed(Maybe<&2, V>, lo, position, False{}) == True{} : Bool}
  for +right_route: {Inv.routed(Maybe<&2, V>, hi, position, True{}) == True{} : Bool}
  for +left_populated: {Pop.populated(V, lo) == True{} : Bool}
  for +right_populated: {Pop.populated(V, hi) == True{} : Bool}
  for +included: {Inv.included(xs, Map.keys(&2, Maybe<&2, V>, lo)) == True{} : Bool}
  {apart(xs, Map.keys(&2, Maybe<&2, V>, hi)) == True{} : Bool}
def routed_apart(V, xs, lo, hi, position, left_route, right_route, left_populated, right_populated, included):
  match xs:
    case Nil{}: {==}
    case Con{+head, +tail}:
      And.conjunction(Bool.not(Inv.member(Map.keys(&2, Maybe<&2, V>, hi), head)), apart(tail, Map.keys(&2, Maybe<&2, V>, hi)),
        Equal.cong(Bool, Bool, Bool.not, Inv.member(Map.keys(&2, Maybe<&2, V>, hi), head), False{}, D.opposite(V, lo, hi, head, position, left_route, right_route, left_populated, right_populated, R.and_left(Inv.member(Map.keys(&2, Maybe<&2, V>, lo), head), Inv.included(tail, Map.keys(&2, Maybe<&2, V>, lo)), included))),
        routed_apart(V, tail, lo, hi, position, left_route, right_route, left_populated, right_populated, R.and_right(Inv.member(Map.keys(&2, Maybe<&2, V>, lo), head), Inv.included(tail, Map.keys(&2, Maybe<&2, V>, lo)), included)))

law join:
  for -V: Data
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +position: Nat
  for left_route: {Inv.routed(Maybe<&2, V>, lo, position, False{}) == True{} : Bool}
  for right_route: {Inv.routed(Maybe<&2, V>, hi, position, True{}) == True{} : Bool}
  for left_populated: {Pop.populated(V, lo) == True{} : Bool}
  for right_populated: {Pop.populated(V, hi) == True{} : Bool}
  for left_unique: {Inv.unique(Map.keys(&2, Maybe<&2, V>, lo)) == True{} : Bool}
  for right_unique: {Inv.unique(Map.keys(&2, Maybe<&2, V>, hi)) == True{} : Bool}
  {Inv.unique(Map.keys(&2, Maybe<&2, V>, MNode{position, lo, hi})) == True{} : Bool}
def join(V, lo, hi, position, left_route, right_route, left_populated, right_populated, left_unique, right_unique):
  %Equal.sym(List<&2, String>, Map.keys.go(&2, Maybe<&2, V>, lo, Map.keys(&2, Maybe<&2, V>, hi)), List.append(&2, String, Map.keys(&2, Maybe<&2, V>, lo), Map.keys(&2, Maybe<&2, V>, hi)), keys_go_append(Maybe<&2, V>, lo, Nil{}, Map.keys(&2, Maybe<&2, V>, hi))) : {Inv.unique(_) == True{} : Bool}
  unique_append(Map.keys(&2, Maybe<&2, V>, lo), Map.keys(&2, Maybe<&2, V>, hi), left_unique, right_unique,
    routed_apart(V, Map.keys(&2, Maybe<&2, V>, lo), lo, hi, position, left_route, right_route, left_populated, right_populated, Lists.included_self(Map.keys(&2, Maybe<&2, V>, lo))))

law node_step:
  for -V: Data
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +position: Nat
  for facts: Parts.NodeFacts(Maybe<&2, V>, position, lo, hi)
  for +packed: {Pop.populated(V, MNode{position, lo, hi}) == True{} : Bool}
  for left: {Inv.critbit(Maybe<&2, V>, lo) == True{} : Bool} -> {Pop.populated(V, lo) == True{} : Bool} -> {Inv.unique(Map.keys(&2, Maybe<&2, V>, lo)) == True{} : Bool}
  for right: {Inv.critbit(Maybe<&2, V>, hi) == True{} : Bool} -> {Pop.populated(V, hi) == True{} : Bool} -> {Inv.unique(Map.keys(&2, Maybe<&2, V>, hi)) == True{} : Bool}
  {Inv.unique(Map.keys(&2, Maybe<&2, V>, MNode{position, lo, hi})) == True{} : Bool}
def node_step(V, lo, hi, position, facts, packed, left, right):
  (prefix, ln, rn, lb, rb, lr, rr, lv, rv) = facts
  +lp = R.and_left(Pop.populated(V, lo), Pop.populated(V, hi), packed)
  +rp = R.and_right(Pop.populated(V, lo), Pop.populated(V, hi), packed)
  join(V, lo, hi, position, lr, rr, lp, rp, left(lv, lp), right(rv, rp))

# Actual native enumeration is unique for every populated critbit tree.
law unique_keys:
  for -V: Data
  for tree: Map<&2, Maybe<&2, V>>
  for valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for packed: {Pop.populated(V, tree) == True{} : Bool}
  {Inv.unique(Map.keys(&2, Maybe<&2, V>, tree)) == True{} : Bool}
def unique_keys(V, tree, valid, packed):
  match tree:
    case MTip{}: {==}
    case MLeaf{key, value}: {==}
    case MNode{+position, +lo, +hi}:
      node_step(V, lo, hi, position, Parts.node_parts(Maybe<&2, V>, position, lo, hi, valid), packed,
        v => p => unique_keys(V, lo, v, p),
        v => p => unique_keys(V, hi, v, p))
