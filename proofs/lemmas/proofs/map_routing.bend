import Base
import ./map_insert.bend as I
import ./map_lookup.bend as L
import ./invariants.bend as R

# Logical forms of the existing executable routing predicates.
def truth(b: Bool) -> Type:
  match b:
    case False{}:
      Empty
    case True{}:
      Unit

law false_true:
  for e: {False{} == True{} : Bool}
  Empty
def false_true(e):
  %Equal.sym(Bool, False{}, True{}, e) : truth(_)
  Unit{}

law and_left:
  for a: Bool
  for b: Bool
  for e: {a && b == True{} : Bool}
  {a == True{} : Bool}
def and_left(a, b, e):
  match a:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_true(e))
    case True{}:
      {==}

law and_right:
  for a: Bool
  for b: Bool
  for e: {a && b == True{} : Bool}
  {b == True{} : Bool}
def and_right(a, b, e):
  match a:
    case False{}:
      Empty.absurd({b == True{} : Bool}, false_true(e))
    case True{}:
      e

law equal_bit:
  for bit: Bool
  for side: Bool
  for e: {Bool.not(Bool.xor(bit, side)) == True{} : Bool}
  {bit == side : Bool}
def equal_bit(bit, side, e):
  match bit side:
    case False{} False{}:
      {==}
    case True{} True{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, false_true(e))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, false_true(e))

def routed(-V: Data, tree: Map<&2, V>, pos: Nat, side: Bool) -> Type:
  match tree:
    case MTip{}:
      Unit
    case MLeaf{key, value}:
      {Map.bit(key, pos) == (key, side) : String & Bool}
    case MNode{p, lo, hi}:
      routed(V, lo, pos, side) & routed(V, hi, pos, side)

law route_projection:
  for r: String & Bool
  {R.bit_value(r) == I.route_bit(r) : Bool}
def route_projection(r):
  match r:
    case Tuple{key, bit}:
      {==}

law routed_certificate:
  for -V: Data
  for tree: Map<&2, V>
  for +pos: Nat
  for +side: Bool
  for +e: {R.routed(V, tree, pos, side) == True{} : Bool}
  routed(V, tree, pos, side)
def routed_certificate(V, tree, pos, side, e):
  match tree:
    case MTip{}:
      Unit{}
    case MLeaf{+key, value}:
      Equal.trans(String & Bool, Map.bit(key, pos), (key, I.route_bit(Map.bit(key, pos))), (key, side), I.route_shape(key, pos), Equal.cong(Bool, String & Bool, b => (key, b), I.route_bit(Map.bit(key, pos)), side, Equal.trans(Bool, I.route_bit(Map.bit(key, pos)), R.bit_value(Map.bit(key, pos)), side, Equal.sym(Bool, R.bit_value(Map.bit(key, pos)), I.route_bit(Map.bit(key, pos)), route_projection(Map.bit(key, pos))), equal_bit(R.bit_value(Map.bit(key, pos)), side, e))))
    case MNode{p, +lo, +hi}:
      (routed_certificate(V, lo, pos, side, and_left(R.routed(V, lo, pos, side), R.routed(V, hi, pos, side), e)), routed_certificate(V, hi, pos, side, and_right(R.routed(V, lo, pos, side), R.routed(V, hi, pos, side), e)))

# This weaker property is precisely the part of critbit needed for lookup. The
# full discriminator/prefix property remains required for insertion preservation.
def valid(-V: Data, tree: Map<&2, V>) -> Type:
  match tree:
    case MTip{}:
      Unit
    case MLeaf{k, v}:
      Unit
    case MNode{p, lo, hi}:
      routed(V, lo, p, False{}) & routed(V, hi, p, True{}) & valid(V, lo) & valid(V, hi)

law member_routed:
  for -V: Data
  for tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +value: V
  for +pos: Nat
  for +side: Bool
  for routes: routed(Maybe<&2, V>, tree, pos, side)
  for member: L.leaf(V, tree, key, value)
  {Map.bit(key, pos) == (key, side) : String & Bool}
def member_routed(V, tree, key, value, pos, side, routes, member):
  match tree:
    case MTip{}:
      Empty.absurd({Map.bit(key, pos) == (key, side) : String & Bool}, member)
    case MLeaf{stored, item}:
      (same, val) = member
      %Equal.sym(String, key, stored, same) : {Map.bit(_, pos) == (_, side) : String & Bool}
      routes
    case MNode{p, +lo, +hi}:
      (lp, hp) = routes
      match member:
        case Inl{lm}:
          member_routed(V, lo, key, value, pos, side, lp, lm)
        case Inr{hm}:
          member_routed(V, hi, key, value, pos, side, hp, hm)

def copies_left(-A: Type, -B: Type, pair: A & A) -> Either<&1, &1, A, B> & Either<&1, &1, A, B>:
  (a, b) = pair
  (Inl{a}, Inl{b})

def copies_right(-A: Type, -B: Type, pair: B & B) -> Either<&1, &1, A, B> & Either<&1, &1, A, B>:
  (a, b) = pair
  (Inr{a}, Inr{b})

# Structural duplication of a membership witness; no unrestricted Type cast.
law duplicate_member:
  for -V: Data
  for tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +value: V
  for member: L.leaf(V, tree, key, value)
  L.leaf(V, tree, key, value) & L.leaf(V, tree, key, value)
def duplicate_member(V, tree, key, value, member):
  match tree:
    case MTip{}:
      Empty.absurd(Empty & Empty, member)
    case MLeaf{stored, item}:
      Tuple{+same, +val} = member
      ((same, val), (same, val))
    case MNode{p, lo, hi}:
      match member:
        case Inl{lm}:
          copies_left(L.leaf(V, lo, key, value), L.leaf(V, hi, key, value), duplicate_member(V, lo, key, value, lm))
        case Inr{hm}:
          copies_right(L.leaf(V, lo, key, value), L.leaf(V, hi, key, value), duplicate_member(V, hi, key, value, hm))

# Converse of native lookup soundness. The routing premise is structural and is
# separately derived from the actual executable critbit predicate below.
law lookup_left:
  for -V: Data
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +p: Nat
  for +key: String
  for +value: V
  for routes: routed(Maybe<&2, V>, lo, p, False{})
  for induction: @member: L.leaf(V, lo, key, value) -> {I.lookup(Maybe<&2, V>, None{}, lo, key) == Some{value} : Maybe<&2, V>}
  for copies: L.leaf(V, lo, key, value) & L.leaf(V, lo, key, value)
  {I.lookup(Maybe<&2, V>, None{}, MNode{p, lo, hi}, key) == Some{value} : Maybe<&2, V>}
def lookup_left(V, lo, hi, p, key, value, routes, induction, copies):
  (route_member, lookup_member) = copies
  Equal.trans(Maybe<&2, V>, I.lookup(Maybe<&2, V>, None{}, MNode{p, lo, hi}, key), I.lookup(Maybe<&2, V>, None{}, lo, key), Some{value}, I.node_left(Maybe<&2, V>, None{}, lo, hi, p, key, member_routed(V, lo, key, value, p, False{}, routes, route_member)), induction(lookup_member))

law lookup_right:
  for -V: Data
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +p: Nat
  for +key: String
  for +value: V
  for routes: routed(Maybe<&2, V>, hi, p, True{})
  for induction: @member: L.leaf(V, hi, key, value) -> {I.lookup(Maybe<&2, V>, None{}, hi, key) == Some{value} : Maybe<&2, V>}
  for copies: L.leaf(V, hi, key, value) & L.leaf(V, hi, key, value)
  {I.lookup(Maybe<&2, V>, None{}, MNode{p, lo, hi}, key) == Some{value} : Maybe<&2, V>}
def lookup_right(V, lo, hi, p, key, value, routes, induction, copies):
  (route_member, lookup_member) = copies
  Equal.trans(Maybe<&2, V>, I.lookup(Maybe<&2, V>, None{}, MNode{p, lo, hi}, key), I.lookup(Maybe<&2, V>, None{}, hi, key), Some{value}, I.node_right(Maybe<&2, V>, None{}, lo, hi, p, key, member_routed(V, hi, key, value, p, True{}, routes, route_member)), induction(lookup_member))

law member_lookup:
  for -V: Data
  for tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +value: V
  for invariant: valid(Maybe<&2, V>, tree)
  for member: L.leaf(V, tree, key, value)
  {I.lookup(Maybe<&2, V>, None{}, tree, key) == Some{value} : Maybe<&2, V>}
def member_lookup(V, tree, key, value, invariant, member):
  match tree:
    case MTip{}:
      Empty.absurd({I.lookup(Maybe<&2, V>, None{}, MTip{}, key) == Some{value} : Maybe<&2, V>}, member)
    case MLeaf{stored, item}:
      (same, val) = member
      %same : {I.lookup(Maybe<&2, V>, None{}, MLeaf{_, item}, key) == Some{value} : Maybe<&2, V>}
      %val : {I.lookup(Maybe<&2, V>, None{}, MLeaf{key, _}, key) == Some{value} : Maybe<&2, V>}
      I.leaf_same(Maybe<&2, V>, None{}, key, Some{value})
    case MNode{+p, +lo, +hi}:
      (lr, hr, lv, hv) = invariant
      match member:
        case Inl{lm}:
          lookup_left(V, lo, hi, p, key, value, lr, m => member_lookup(V, lo, key, value, lv, m), duplicate_member(V, lo, key, value, lm))
        case Inr{hm}:
          lookup_right(V, lo, hi, p, key, value, hr, m => member_lookup(V, hi, key, value, hv, m), duplicate_member(V, hi, key, value, hm))

law critbit_certificate:
  for -V: Data
  for tree: Map<&2, V>
  for +e: {R.critbit(V, tree) == True{} : Bool}
  valid(V, tree)
def critbit_certificate(V, tree, e):
  match tree:
    case MTip{}:
      Unit{}
    case MLeaf{k, v}:
      Unit{}
    case MNode{+p, +lo, +hi}:
      +base = R.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && R.nonempty(V, lo) && R.nonempty(V, hi) && R.below(V, lo, p) && R.below(V, hi, p)
      +lr = R.routed(V, lo, p, False{})
      +hr = R.routed(V, hi, p, True{})
      +lv = R.critbit(V, lo)
      +hv = R.critbit(V, hi)
      +e1 = and_left(base && lr && hr && lv, hv, e)
      +e2 = and_left(base && lr && hr, lv, e1)
      +e3 = and_left(base && lr, hr, e2)
      (routed_certificate(V, lo, p, False{}, and_right(base, lr, e3)), routed_certificate(V, hi, p, True{}, and_right(base && lr, hr, e2)), critbit_certificate(V, lo, and_right(base && lr && hr, lv, e1)), critbit_certificate(V, hi, and_right(base && lr && hr && lv, hv, e)))

law critbit_member_lookup:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for key: String
  for value: V
  for invariant: {R.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for member: L.leaf(V, tree, key, value)
  {I.lookup(Maybe<&2, V>, None{}, tree, key) == Some{value} : Maybe<&2, V>}
def critbit_member_lookup(V, tree, key, value, invariant, member):
  member_lookup(V, tree, key, value, critbit_certificate(Maybe<&2, V>, tree, invariant), member)
