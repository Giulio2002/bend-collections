import Base
import ./invariants.bend as Inv
import ./map_lookup.bend as L
import ./map_insert.bend as I
import ./map_routing.bend as R
import ./map_populated.bend as P
import ./recency_unique.bend as U

# A key enumerated by the native map has a populated leaf, or came from
# the enumeration accumulator. This is an inverse of leaf_member.
def witness(-V: Data, tree: Map<&2, Maybe<&2, V>>, key: String) -> Type:
  Sigma<&2, &1, V, value => L.leaf(V, tree, key, value)>

def partition(-V: Data, tree: Map<&2, Maybe<&2, V>>, acc: List<&2, String>, key: String) -> Type:
  Either<&1, &1, witness(V, tree, key), {Inv.member(acc, key) == True{} : Bool}>

law leaf_branch:
  for -V: Data
  for +stored: String
  for item: Maybe<&2, V>
  for +acc: List<&2, String>
  for +key: String
  for same: Bool
  for decision: {String.eq(stored, key) == same : Bool}
  for populated: {Maybe.is_some(&2, V, item) == True{} : Bool}
  for member: {same || Inv.member(acc, key) == True{} : Bool}
  partition(V, MLeaf{stored, item}, acc, key)
def leaf_branch(V, stored, item, acc, key, same, decision, populated, member):
  match item:
    case None{}: Empty.absurd(partition(V, MLeaf{stored, None{}}, acc, key), R.false_true(populated))
    case Some{value}:
      match same:
        case False{}: Inr{member}
        case True{}: Inl{(value, (Equal.sym(String, stored, key, U.equal_boolean(stored, key, decision)), {==}))}

law lift_high:
  for -V: Data
  for lo: Map<&2, Maybe<&2, V>>
  for hi: Map<&2, Maybe<&2, V>>
  for p: Nat
  for acc: List<&2, String>
  for key: String
  for proof: partition(V, hi, acc, key)
  partition(V, MNode{p, lo, hi}, acc, key)
def lift_high(V, lo, hi, p, acc, key, proof):
  match proof:
    case Inl{w}:
      (value, leaf) = w
      Inl{(value, Inr{leaf})}
    case Inr{member}: Inr{member}

law lift_node:
  for -V: Data
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for p: Nat
  for acc: List<&2, String>
  for key: String
  for high: {Inv.member(Map.keys.go(&2, Maybe<&2, V>, hi, acc), key) == True{} : Bool} -> partition(V, hi, acc, key)
  for proof: partition(V, lo, Map.keys.go(&2, Maybe<&2, V>, hi, acc), key)
  partition(V, MNode{p, lo, hi}, acc, key)
def lift_node(V, lo, hi, p, acc, key, high, proof):
  match proof:
    case Inl{w}:
      (value, leaf) = w
      Inl{(value, Inl{leaf})}
    case Inr{member}: lift_high(V, lo, hi, p, acc, key, high(member))

law keys_partition:
  for -V: Data
  for tree: Map<&2, Maybe<&2, V>>
  for +acc: List<&2, String>
  for +key: String
  for +populated: {P.populated(V, tree) == True{} : Bool}
  for member: {Inv.member(Map.keys.go(&2, Maybe<&2, V>, tree, acc), key) == True{} : Bool}
  partition(V, tree, acc, key)
def keys_partition(V, tree, acc, key, populated, member):
  match tree:
    case MTip{}: Inr{member}
    case MLeaf{+stored, item}: leaf_branch(V, stored, item, acc, key, String.eq(stored, key), {==}, populated, member)
    case MNode{p, +lo, +hi}:
      lift_node(V, lo, hi, p, acc, key,
        m => keys_partition(V, hi, acc, key, R.and_right(P.populated(V, lo), P.populated(V, hi), populated), m),
        keys_partition(V, lo, Map.keys.go(&2, Maybe<&2, V>, hi, acc), key, R.and_left(P.populated(V, lo), P.populated(V, hi), populated), member))

law empty_accumulator:
  for -V: Data
  for tree: Map<&2, Maybe<&2, V>>
  for key: String
  for proof: partition(V, tree, Nil{}, key)
  witness(V, tree, key)
def empty_accumulator(V, tree, key, proof):
  match proof:
    case Inl{w}: w
    case Inr{member}: Empty.absurd(witness(V, tree, key), R.false_true(member))

law key_has_leaf:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for populated: {P.populated(V, tree) == True{} : Bool}
  for member: {Inv.member(Map.keys(&2, Maybe<&2, V>, tree), key) == True{} : Bool}
  witness(V, tree, key)
def key_has_leaf(V, tree, key, populated, member):
  empty_accumulator(V, tree, key, keys_partition(V, tree, Nil{}, key, populated, member))

law leaf_lookup:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for w: witness(V, tree, key)
  Sigma<&2, &1, V, value => {I.lookup(Maybe<&2, V>, None{}, tree, key) == Some{value} : Maybe<&2, V>}>
def leaf_lookup(V, tree, key, valid, w):
  (+value, leaf) = w
  (value, R.critbit_member_lookup(V, tree, key, value, valid, leaf))

law key_lookup:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for populated: {P.populated(V, tree) == True{} : Bool}
  for member: {Inv.member(Map.keys(&2, Maybe<&2, V>, tree), key) == True{} : Bool}
  Sigma<&2, &1, V, value => {I.lookup(Maybe<&2, V>, None{}, tree, key) == Some{value} : Maybe<&2, V>}>
def key_lookup(V, tree, key, valid, populated, member):
  leaf_lookup(V, tree, key, valid, key_has_leaf(V, tree, key, populated, member))
