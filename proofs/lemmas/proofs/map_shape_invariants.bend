import Base
import ./map_shape.bend as S
import ./invariants.bend as R
import ./map_insert.bend as I
import ./map_seek.bend as Seek

# The erased tree is a proof observation. The executable cache keeps Base Map.
law nonempty:
  for -V: Data
  for tree: Map<&2, V>
  {R.nonempty(Unit, S.skeleton(V, tree)) == R.nonempty(V, tree) : Bool}
def nonempty(V, tree):
  match tree:
    case MTip{}: {==}
    case MLeaf{k, v}: {==}
    case MNode{p, lo, hi}: {==}

law below:
  for -V: Data
  for tree: Map<&2, V>
  for parent: Nat
  {R.below(Unit, S.skeleton(V, tree), parent) == R.below(V, tree, parent) : Bool}
def below(V, tree, parent):
  match tree:
    case MTip{}: {==}
    case MLeaf{k, v}: {==}
    case MNode{p, lo, hi}: {==}

law routed:
  for -V: Data
  for tree: Map<&2, V>
  for +position: Nat
  for +side: Bool
  {R.routed(Unit, S.skeleton(V, tree), position, side) == R.routed(V, tree, position, side) : Bool}
def routed(V, tree, position, side):
  match tree:
    case MTip{}: {==}
    case MLeaf{k, v}: {==}
    case MNode{p, +lo, +hi}:
      %routed(V, lo, position, side) : {R.routed(Unit, S.skeleton(V, lo), position, side) && R.routed(Unit, S.skeleton(V, hi), position, side) == _ && R.routed(V, hi, position, side) : Bool}
      Equal.cong(Bool, Bool, b => R.routed(Unit, S.skeleton(V, lo), position, side) && b, R.routed(Unit, S.skeleton(V, hi), position, side), R.routed(V, hi, position, side), routed(V, hi, position, side))

law prefix_against:
  for -V: Data
  for +key: String
  for tree: Map<&2, V>
  for +limit: Nat
  {R.prefix_against(Unit, key, S.skeleton(V, tree), limit) == R.prefix_against(V, key, tree, limit) : Bool}
def prefix_against(V, key, tree, limit):
  match tree:
    case MTip{}: {==}
    case MLeaf{k, v}: {==}
    case MNode{p, +lo, +hi}:
      %prefix_against(V, key, lo, limit) : {R.prefix_against(Unit, key, S.skeleton(V, lo), limit) && R.prefix_against(Unit, key, S.skeleton(V, hi), limit) == _ && R.prefix_against(V, key, hi, limit) : Bool}
      Equal.cong(Bool, Bool, b => R.prefix_against(Unit, key, S.skeleton(V, lo), limit) && b, R.prefix_against(Unit, key, S.skeleton(V, hi), limit), R.prefix_against(V, key, hi, limit), prefix_against(V, key, hi, limit))

law common_prefix:
  for -V: Data
  for tree: Map<&2, V>
  for +whole: Map<&2, V>
  for +limit: Nat
  {R.common_prefix(Unit, S.skeleton(V, tree), S.skeleton(V, whole), limit) == R.common_prefix(V, tree, whole, limit) : Bool}
def common_prefix(V, tree, whole, limit):
  match tree:
    case MTip{}: {==}
    case MLeaf{k, v}:
      prefix_against(V, k, whole, limit)
    case MNode{p, +lo, +hi}:
      %common_prefix(V, lo, whole, limit) : {R.common_prefix(Unit, S.skeleton(V, lo), S.skeleton(V, whole), limit) && R.common_prefix(Unit, S.skeleton(V, hi), S.skeleton(V, whole), limit) == _ && R.common_prefix(V, hi, whole, limit) : Bool}
      Equal.cong(Bool, Bool, b => R.common_prefix(Unit, S.skeleton(V, lo), S.skeleton(V, whole), limit) && b, R.common_prefix(Unit, S.skeleton(V, hi), S.skeleton(V, whole), limit), R.common_prefix(V, hi, whole, limit), common_prefix(V, hi, whole, limit))

law critbit:
  for -V: Data
  for tree: Map<&2, V>
  {R.critbit(Unit, S.skeleton(V, tree)) == R.critbit(V, tree) : Bool}
def critbit(V, tree):
  match tree:
    case MTip{}: {==}
    case MLeaf{k, v}: {==}
    case MNode{+p, +lo, +hi}:
      %Equal.sym(Bool, R.common_prefix(Unit, S.skeleton(V, MNode{p, lo, hi}), S.skeleton(V, MNode{p, lo, hi}), p), R.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p), common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p)) : {_ && R.nonempty(Unit, S.skeleton(V, lo)) && R.nonempty(Unit, S.skeleton(V, hi)) && R.below(Unit, S.skeleton(V, lo), p) && R.below(Unit, S.skeleton(V, hi), p) && R.routed(Unit, S.skeleton(V, lo), p, False{}) && R.routed(Unit, S.skeleton(V, hi), p, True{}) && R.critbit(Unit, S.skeleton(V, lo)) && R.critbit(Unit, S.skeleton(V, hi)) == R.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && R.nonempty(V, lo) && R.nonempty(V, hi) && R.below(V, lo, p) && R.below(V, hi, p) && R.routed(V, lo, p, False{}) && R.routed(V, hi, p, True{}) && R.critbit(V, lo) && R.critbit(V, hi) : Bool}
      %Equal.sym(Bool, R.nonempty(Unit, S.skeleton(V, lo)), R.nonempty(V, lo), nonempty(V, lo)) : {R.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && _ && R.nonempty(Unit, S.skeleton(V, hi)) && R.below(Unit, S.skeleton(V, lo), p) && R.below(Unit, S.skeleton(V, hi), p) && R.routed(Unit, S.skeleton(V, lo), p, False{}) && R.routed(Unit, S.skeleton(V, hi), p, True{}) && R.critbit(Unit, S.skeleton(V, lo)) && R.critbit(Unit, S.skeleton(V, hi)) == R.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && R.nonempty(V, lo) && R.nonempty(V, hi) && R.below(V, lo, p) && R.below(V, hi, p) && R.routed(V, lo, p, False{}) && R.routed(V, hi, p, True{}) && R.critbit(V, lo) && R.critbit(V, hi) : Bool}
      %Equal.sym(Bool, R.nonempty(Unit, S.skeleton(V, hi)), R.nonempty(V, hi), nonempty(V, hi)) : {R.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && R.nonempty(V, lo) && _ && R.below(Unit, S.skeleton(V, lo), p) && R.below(Unit, S.skeleton(V, hi), p) && R.routed(Unit, S.skeleton(V, lo), p, False{}) && R.routed(Unit, S.skeleton(V, hi), p, True{}) && R.critbit(Unit, S.skeleton(V, lo)) && R.critbit(Unit, S.skeleton(V, hi)) == R.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && R.nonempty(V, lo) && R.nonempty(V, hi) && R.below(V, lo, p) && R.below(V, hi, p) && R.routed(V, lo, p, False{}) && R.routed(V, hi, p, True{}) && R.critbit(V, lo) && R.critbit(V, hi) : Bool}
      %Equal.sym(Bool, R.below(Unit, S.skeleton(V, lo), p), R.below(V, lo, p), below(V, lo, p)) : {R.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && R.nonempty(V, lo) && R.nonempty(V, hi) && _ && R.below(Unit, S.skeleton(V, hi), p) && R.routed(Unit, S.skeleton(V, lo), p, False{}) && R.routed(Unit, S.skeleton(V, hi), p, True{}) && R.critbit(Unit, S.skeleton(V, lo)) && R.critbit(Unit, S.skeleton(V, hi)) == R.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && R.nonempty(V, lo) && R.nonempty(V, hi) && R.below(V, lo, p) && R.below(V, hi, p) && R.routed(V, lo, p, False{}) && R.routed(V, hi, p, True{}) && R.critbit(V, lo) && R.critbit(V, hi) : Bool}
      %Equal.sym(Bool, R.below(Unit, S.skeleton(V, hi), p), R.below(V, hi, p), below(V, hi, p)) : {R.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && R.nonempty(V, lo) && R.nonempty(V, hi) && R.below(V, lo, p) && _ && R.routed(Unit, S.skeleton(V, lo), p, False{}) && R.routed(Unit, S.skeleton(V, hi), p, True{}) && R.critbit(Unit, S.skeleton(V, lo)) && R.critbit(Unit, S.skeleton(V, hi)) == R.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && R.nonempty(V, lo) && R.nonempty(V, hi) && R.below(V, lo, p) && R.below(V, hi, p) && R.routed(V, lo, p, False{}) && R.routed(V, hi, p, True{}) && R.critbit(V, lo) && R.critbit(V, hi) : Bool}
      %Equal.sym(Bool, R.routed(Unit, S.skeleton(V, lo), p, False{}), R.routed(V, lo, p, False{}), routed(V, lo, p, False{})) : {R.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && R.nonempty(V, lo) && R.nonempty(V, hi) && R.below(V, lo, p) && R.below(V, hi, p) && _ && R.routed(Unit, S.skeleton(V, hi), p, True{}) && R.critbit(Unit, S.skeleton(V, lo)) && R.critbit(Unit, S.skeleton(V, hi)) == R.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && R.nonempty(V, lo) && R.nonempty(V, hi) && R.below(V, lo, p) && R.below(V, hi, p) && R.routed(V, lo, p, False{}) && R.routed(V, hi, p, True{}) && R.critbit(V, lo) && R.critbit(V, hi) : Bool}
      %Equal.sym(Bool, R.routed(Unit, S.skeleton(V, hi), p, True{}), R.routed(V, hi, p, True{}), routed(V, hi, p, True{})) : {R.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && R.nonempty(V, lo) && R.nonempty(V, hi) && R.below(V, lo, p) && R.below(V, hi, p) && R.routed(V, lo, p, False{}) && _ && R.critbit(Unit, S.skeleton(V, lo)) && R.critbit(Unit, S.skeleton(V, hi)) == R.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && R.nonempty(V, lo) && R.nonempty(V, hi) && R.below(V, lo, p) && R.below(V, hi, p) && R.routed(V, lo, p, False{}) && R.routed(V, hi, p, True{}) && R.critbit(V, lo) && R.critbit(V, hi) : Bool}
      %Equal.sym(Bool, R.critbit(Unit, S.skeleton(V, lo)), R.critbit(V, lo), critbit(V, lo)) : {R.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && R.nonempty(V, lo) && R.nonempty(V, hi) && R.below(V, lo, p) && R.below(V, hi, p) && R.routed(V, lo, p, False{}) && R.routed(V, hi, p, True{}) && _ && R.critbit(Unit, S.skeleton(V, hi)) == R.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && R.nonempty(V, lo) && R.nonempty(V, hi) && R.below(V, lo, p) && R.below(V, hi, p) && R.routed(V, lo, p, False{}) && R.routed(V, hi, p, True{}) && R.critbit(V, lo) && R.critbit(V, hi) : Bool}
      %Equal.sym(Bool, R.critbit(Unit, S.skeleton(V, hi)), R.critbit(V, hi), critbit(V, hi)) : {R.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && R.nonempty(V, lo) && R.nonempty(V, hi) && R.below(V, lo, p) && R.below(V, hi, p) && R.routed(V, lo, p, False{}) && R.routed(V, hi, p, True{}) && R.critbit(V, lo) && _ == R.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && R.nonempty(V, lo) && R.nonempty(V, hi) && R.below(V, lo, p) && R.below(V, hi, p) && R.routed(V, lo, p, False{}) && R.routed(V, hi, p, True{}) && R.critbit(V, lo) && R.critbit(V, hi) : Bool}
      {==}

law replacement_preserves_critbit:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +old: V
  for +value: Maybe<&2, V>
  for found: {I.lookup(Maybe<&2, V>, None{}, tree, key) == Some{old} : Maybe<&2, V>}
  {R.critbit(Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, tree, key, value)) == R.critbit(Maybe<&2, V>, tree) : Bool}
def replacement_preserves_critbit(V, tree, key, old, value, found):
  %critbit(Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, tree, key, value)) : {_ == R.critbit(Maybe<&2, V>, tree) : Bool}
  %Equal.sym(Map<&2, Unit>, S.skeleton(Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, tree, key, value)), S.skeleton(Maybe<&2, V>, tree), S.set_existing_shape(Maybe<&2, V>, tree, key, value, Seek.successful_lookup_seeks_key(V, tree, key, old, found))) : {R.critbit(Unit, _) == R.critbit(Maybe<&2, V>, tree) : Bool}
  critbit(Maybe<&2, V>, tree)
