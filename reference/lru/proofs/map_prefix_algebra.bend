import Base
import ./invariants.bend as Inv
import ./map_routing.bend as R
import ./map_delete_prefix.bend as P

law bit_self:
  for bit: Bool
  {Bool.not(Bool.xor(bit, bit)) == True{} : Bool}
def bit_self(bit):
  match bit:
    case False{}: {==}
    case True{}: {==}

law bit_symmetric:
  for a: Bool
  for b: Bool
  {Bool.not(Bool.xor(a, b)) == Bool.not(Bool.xor(b, a)) : Bool}
def bit_symmetric(a, b):
  match a b:
    case False{} False{}: {==}
    case False{} True{}: {==}
    case True{} False{}: {==}
    case True{} True{}: {==}

law reflexive:
  for +key: String
  for limit: Nat
  {Inv.same_prefix(key, key, limit) == True{} : Bool}
def reflexive(key, limit):
  match limit:
    case 0n: {==}
    case 1n+ +p:
      P.conjunction(Bool.not(Bool.xor(Inv.bit_value(Map.bit(key, p)), Inv.bit_value(Map.bit(key, p)))), Inv.same_prefix(key, key, p), bit_self(Inv.bit_value(Map.bit(key, p))), reflexive(key, p))

law symmetric:
  for +a: String
  for +b: String
  for limit: Nat
  for +prefix: {Inv.same_prefix(a, b, limit) == True{} : Bool}
  {Inv.same_prefix(b, a, limit) == True{} : Bool}
def symmetric(a, b, limit, prefix):
  match limit:
    case 0n: {==}
    case 1n+ +p:
      bit = R.and_left(Bool.not(Bool.xor(Inv.bit_value(Map.bit(a, p)), Inv.bit_value(Map.bit(b, p)))), Inv.same_prefix(a, b, p), prefix)
      tail = R.and_right(Bool.not(Bool.xor(Inv.bit_value(Map.bit(a, p)), Inv.bit_value(Map.bit(b, p)))), Inv.same_prefix(a, b, p), prefix)
      P.conjunction(Bool.not(Bool.xor(Inv.bit_value(Map.bit(b, p)), Inv.bit_value(Map.bit(a, p)))), Inv.same_prefix(b, a, p), Equal.trans(Bool, Bool.not(Bool.xor(Inv.bit_value(Map.bit(b, p)), Inv.bit_value(Map.bit(a, p)))), Bool.not(Bool.xor(Inv.bit_value(Map.bit(a, p)), Inv.bit_value(Map.bit(b, p)))), True{}, bit_symmetric(Inv.bit_value(Map.bit(b, p)), Inv.bit_value(Map.bit(a, p))), bit), symmetric(a, b, p, tail))

# Reverse each row of a prefix-against constraint, without assuming symmetry.
law against_column:
  for -V: Data
  for tree: Map<&2, V>
  for +key: String
  for +value: V
  for +limit: Nat
  for +prefix: {Inv.prefix_against(V, key, tree, limit) == True{} : Bool}
  {Inv.common_prefix(V, tree, MLeaf{key, value}, limit) == True{} : Bool}
def against_column(V, tree, key, value, limit, prefix):
  match tree:
    case MTip{}: {==}
    case MLeaf{stored, old}: symmetric(key, stored, limit, prefix)
    case MNode{p, +lo, +hi}:
      P.conjunction(Inv.common_prefix(V, lo, MLeaf{key, value}, limit), Inv.common_prefix(V, hi, MLeaf{key, value}, limit), against_column(V, lo, key, value, limit, R.and_left(Inv.prefix_against(V, key, lo, limit), Inv.prefix_against(V, key, hi, limit), prefix)), against_column(V, hi, key, value, limit, R.and_right(Inv.prefix_against(V, key, lo, limit), Inv.prefix_against(V, key, hi, limit), prefix)))

law bit_transitive:
  for +a: Bool
  for +b: Bool
  for c: Bool
  for ab: {Bool.not(Bool.xor(a, b)) == True{} : Bool}
  for bc: {Bool.not(Bool.xor(b, c)) == True{} : Bool}
  {Bool.not(Bool.xor(a, c)) == True{} : Bool}
def bit_transitive(a, b, c, ab, bc):
  %Equal.sym(Bool, a, b, R.equal_bit(a, b, ab)) : {Bool.not(Bool.xor(_, c)) == True{} : Bool}
  bc

law transitive:
  for +a: String
  for +b: String
  for +c: String
  for limit: Nat
  for +ab: {Inv.same_prefix(a, b, limit) == True{} : Bool}
  for +bc: {Inv.same_prefix(b, c, limit) == True{} : Bool}
  {Inv.same_prefix(a, c, limit) == True{} : Bool}
def transitive(a, b, c, limit, ab, bc):
  match limit:
    case 0n: {==}
    case 1n+ +p:
      P.conjunction(Bool.not(Bool.xor(Inv.bit_value(Map.bit(a, p)), Inv.bit_value(Map.bit(c, p)))), Inv.same_prefix(a, c, p),
        bit_transitive(Inv.bit_value(Map.bit(a, p)), Inv.bit_value(Map.bit(b, p)), Inv.bit_value(Map.bit(c, p)), R.and_left(Bool.not(Bool.xor(Inv.bit_value(Map.bit(a, p)), Inv.bit_value(Map.bit(b, p)))), Inv.same_prefix(a, b, p), ab), R.and_left(Bool.not(Bool.xor(Inv.bit_value(Map.bit(b, p)), Inv.bit_value(Map.bit(c, p)))), Inv.same_prefix(b, c, p), bc)),
        transitive(a, b, c, p, R.and_right(Bool.not(Bool.xor(Inv.bit_value(Map.bit(a, p)), Inv.bit_value(Map.bit(b, p)))), Inv.same_prefix(a, b, p), ab), R.and_right(Bool.not(Bool.xor(Inv.bit_value(Map.bit(b, p)), Inv.bit_value(Map.bit(c, p)))), Inv.same_prefix(b, c, p), bc)))

law against_transitive:
  for -V: Data
  for tree: Map<&2, V>
  for +a: String
  for +b: String
  for +limit: Nat
  for +ab: {Inv.same_prefix(a, b, limit) == True{} : Bool}
  for +bc: {Inv.prefix_against(V, b, tree, limit) == True{} : Bool}
  {Inv.prefix_against(V, a, tree, limit) == True{} : Bool}
def against_transitive(V, tree, a, b, limit, ab, bc):
  match tree:
    case MTip{}: {==}
    case MLeaf{stored, old}: transitive(a, b, stored, limit, ab, bc)
    case MNode{p, +lo, +hi}:
      P.conjunction(Inv.prefix_against(V, a, lo, limit), Inv.prefix_against(V, a, hi, limit), against_transitive(V, lo, a, b, limit, ab, R.and_left(Inv.prefix_against(V, b, lo, limit), Inv.prefix_against(V, b, hi, limit), bc)), against_transitive(V, hi, a, b, limit, ab, R.and_right(Inv.prefix_against(V, b, lo, limit), Inv.prefix_against(V, b, hi, limit), bc)))
