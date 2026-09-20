import Base
import ./native_map.bend as N
import ./invariants.bend as Inv
import ./map_insert.bend as I
import ./map_difference.bend as D
import ./map_splice_critbit.bend as Splice
import ./map_insert_before.bend as Before
import ./map_insert_descent.bend as Descent
import ./map_seek_discriminator.bend as Discriminator
import ./map_critbit_parts.bend as Parts
import ./map_routing.bend as R

# Constructive total ordering; neither an order oracle nor a public premise.
def Order(+a: Nat, +b: Nat) -> Type:
  Either<&1, &1, {Nat.is_lt(a, b) == True{} : Bool}, Either<&1, &1, {a == b : Nat}, {Nat.is_lt(b, a) == True{} : Bool}>>

law order_lift:
  for +a: Nat
  for +b: Nat
  for order: Order(a, b)
  Order(1n+a, 1n+b)
def order_lift(a, b, order):
  match order:
    case Inl{e}: Inl{e}
    case Inr{Inl{e}}: Inr{Inl{Equal.cong(Nat, Nat, n => 1n+n, a, b, e)}}
    case Inr{Inr{e}}: Inr{Inr{e}}

law total_order:
  for a: Nat
  for b: Nat
  Order(a, b)
def total_order(a, b):
  match a b:
    case 0n 0n: Inr{Inl{{==}}}
    case 0n 1n+p: Inl{{==}}
    case 1n+p 0n: Inr{Inr{{==}}}
    case 1n+ +a 1n+ +b: order_lift(a, b, total_order(a, b))

law equal_impossible:
  for -V: Data
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +position: Nat
  for +key: String
  for +stored: String
  for distinct: D.different(key, stored)
  for found: {I.seek_found(V, Map.seek(&2, V, MNode{position, lo, hi}, key)) == Some{stored} : Maybe<&2, String>}
  for equal: {Map.diff(key, stored) == position : Nat}
  for parts: Parts.NodeFacts(V, position, lo, hi)
  Empty
def equal_impossible(V, lo, hi, position, key, stored, distinct, found, equal, parts):
  (common, nl, nh, bl, bh, rl, rh, vl, vh) = parts
  Discriminator.difference_not_root(V, lo, hi, position, key, stored, distinct, found, rl, rh, equal)

law node_case:
  for -V: Data
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +position: Nat
  for +key: String
  for +stored: String
  for +value: V
  for order: Order(Map.diff(key, stored), position)
  for distinct: D.different(key, stored)
  for found: {I.seek_found(V, Map.seek(&2, V, MNode{position, lo, hi}, key)) == Some{stored} : Maybe<&2, String>}
  for valid: {Inv.critbit(V, MNode{position, lo, hi}) == True{} : Bool}
  for lp: {Inv.critbit(V, lo) == True{} : Bool} -> {I.seek_found(V, Map.seek(&2, V, lo, key)) == Some{stored} : Maybe<&2, String>} -> {Inv.critbit(V, Map.ins(&2, V, lo, key, value, Map.diff(key, stored))) == True{} : Bool}
  for hp: {Inv.critbit(V, hi) == True{} : Bool} -> {I.seek_found(V, Map.seek(&2, V, hi, key)) == Some{stored} : Maybe<&2, String>} -> {Inv.critbit(V, Map.ins(&2, V, hi, key, value, Map.diff(key, stored))) == True{} : Bool}
  {Inv.critbit(V, Map.ins(&2, V, MNode{position, lo, hi}, key, value, Map.diff(key, stored))) == True{} : Bool}
def node_case(V, lo, hi, position, key, stored, value, order, distinct, found, valid, lp, hp):
  match order:
    case Inl{earlier}:
      Before.insertion_before(V, key, stored, value, lo, hi, position, distinct, found, earlier, valid)
    case Inr{Inl{equal}}:
      Empty.absurd({Inv.critbit(V, Map.ins(&2, V, MNode{position, lo, hi}, key, value, Map.diff(key, stored))) == True{} : Bool}, equal_impossible(V, lo, hi, position, key, stored, distinct, found, equal, Parts.node_parts(V, position, lo, hi, valid)))
    case Inr{Inr{descend}}:
      Descent.from_parts(V, lo, hi, position, key, stored, value, found, descend, Parts.node_parts(V, position, lo, hi, valid), lp, hp)

law leaf:
  for -V: Data
  for +key: String
  for +stored: String
  for +actual: String
  for value: V
  for old: V
  for distinct: D.different(key, stored)
  for found: {Some{actual} == Some{stored} : Maybe<&2, String>}
  {Inv.critbit(V, Map.ins(&2, V, MLeaf{actual, old}, key, value, Map.diff(key, stored))) == True{} : Bool}
def leaf(V, key, stored, actual, value, old, distinct, found):
  eq = Equal.cong(Maybe<&2, String>, String, m => Maybe.default(&2, String, m, ""), Some{actual}, Some{stored}, found)
  %Equal.sym(String, actual, stored, eq) : {Inv.critbit(V, Map.ins(&2, V, MLeaf{_, old}, key, value, Map.diff(key, stored))) == True{} : Bool}
  Splice.singleton_insert_valid(V, key, stored, value, old, distinct)

law unequal_distinct:
  for +key: String
  for +stored: String
  for unequal: {String.eq(key, stored) == False{} : Bool}
  D.different(key, stored)
def unequal_distinct(key, stored, unequal):
  e => R.false_true(Equal.trans(Bool, False{}, String.eq(key, stored), True{}, Equal.sym(Bool, String.eq(key, stored), False{}, unequal), Equal.cong((String & String) & Cmp, Bool, String.eq.fin, String.cmp(key, stored), ((key, stored), EQ{}), N.string_equal_comparison(key, stored, e))))

# Full insertion critbit preservation at the leaf selected by actual seek.
# The public Map.set bridge must additionally handle replacement and empty seek.
law insertion_at_seek:
  for -V: Data
  for tree: Map<&2, V>
  for +key: String
  for +stored: String
  for +value: V
  for +unequal: {String.eq(key, stored) == False{} : Bool}
  for found: {I.seek_found(V, Map.seek(&2, V, tree, key)) == Some{stored} : Maybe<&2, String>}
  for valid: {Inv.critbit(V, tree) == True{} : Bool}
  {Inv.critbit(V, Map.ins(&2, V, tree, key, value, Map.diff(key, stored))) == True{} : Bool}
def insertion_at_seek(V, tree, key, stored, value, unequal, found, valid):
  match tree:
    case MTip{}:
      Empty.absurd({Inv.critbit(V, Map.ins(&2, V, MTip{}, key, value, Map.diff(key, stored))) == True{} : Bool}, R.false_true(Equal.cong(Maybe<&2, String>, Bool, m => Maybe.is_some(&2, String, m), None{}, Some{stored}, found)))
    case MLeaf{actual, old}: leaf(V, key, stored, actual, value, old, unequal_distinct(key, stored, unequal), found)
    case MNode{+position, +lo, +hi}:
      node_case(V, lo, hi, position, key, stored, value, total_order(Map.diff(key, stored), position), unequal_distinct(key, stored, unequal), found, valid,
        v => f => insertion_at_seek(V, lo, key, stored, value, unequal, f, v),
        v => f => insertion_at_seek(V, hi, key, stored, value, unequal, f, v))
