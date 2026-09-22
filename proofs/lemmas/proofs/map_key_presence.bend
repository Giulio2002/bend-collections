import Base
import ./invariants.bend as Inv
import ./map_populated.bend as Pop
import ./map_key_lookup.bend as M
import ./map_key_membership.bend as Keys
import ./map_insert.bend as I
import ./map_lookup.bend as L
import ./map_routing.bend as R

law available_present:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for w: Sigma<&2, &1, V, value => {I.lookup(Maybe<&2, V>, None{}, tree, key) == Some{value} : Maybe<&2, V>}>
  {Maybe.is_some(&2, V, I.lookup(Maybe<&2, V>, None{}, tree, key)) == True{} : Bool}
def available_present(V, tree, key, w):
  (value, found) = w
  Equal.cong(Maybe<&2, V>, Bool, m => Maybe.is_some(&2, V, m), I.lookup(Maybe<&2, V>, None{}, tree, key), Some{value}, found)

law missing_member:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for bit: Bool
  for decision: {Inv.member(Map.keys(&2, Maybe<&2, V>, tree), key) == bit : Bool}
  for valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for populated: {Pop.populated(V, tree) == True{} : Bool}
  for absent: {I.lookup(Maybe<&2, V>, None{}, tree, key) == None{} : Maybe<&2, V>}
  {False{} == bit : Bool}
def missing_member(V, tree, key, bit, decision, valid, populated, absent):
  match bit:
    case False{}: {==}
    case True{}:
      Equal.trans(Bool, False{}, Maybe.is_some(&2, V, I.lookup(Maybe<&2, V>, None{}, tree, key)), True{}, Equal.sym(Bool, Maybe.is_some(&2, V, I.lookup(Maybe<&2, V>, None{}, tree, key)), False{}, Equal.cong(Maybe<&2, V>, Bool, m => Maybe.is_some(&2, V, m), I.lookup(Maybe<&2, V>, None{}, tree, key), None{}, absent)), available_present(V, tree, key, M.key_lookup(V, tree, key, valid, populated, decision)))

law lookup_case:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for result: Maybe<&2, V>
  for decision: {I.lookup(Maybe<&2, V>, None{}, tree, key) == result : Maybe<&2, V>}
  for valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for populated: {Pop.populated(V, tree) == True{} : Bool}
  {Maybe.is_some(&2, V, result) == Inv.member(Map.keys(&2, Maybe<&2, V>, tree), key) : Bool}
def lookup_case(V, tree, key, result, decision, valid, populated):
  match result:
    case None{}: missing_member(V, tree, key, Inv.member(Map.keys(&2, Maybe<&2, V>, tree), key), {==}, valid, populated, decision)
    case Some{+value}:
      Equal.sym(Bool, Inv.member(Map.keys(&2, Maybe<&2, V>, tree), key), True{}, Keys.leaf_member(V, tree, Nil{}, key, value, L.returned_value_is_stored(V, tree, key, value, decision)))

# Full Boolean equivalence, including absent keys, against actual Map.get/keys.
law lookup_presence:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for populated: {Pop.populated(V, tree) == True{} : Bool}
  {Maybe.is_some(&2, V, I.lookup(Maybe<&2, V>, None{}, tree, key)) == Inv.member(Map.keys(&2, Maybe<&2, V>, tree), key) : Bool}
def lookup_presence(V, tree, key, valid, populated):
  lookup_case(V, tree, key, I.lookup(Maybe<&2, V>, None{}, tree, key), {==}, valid, populated)
