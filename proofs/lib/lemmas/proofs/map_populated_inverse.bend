import Base
import ../types/model.bend as T
import ./map_populated.bend as Pop
import ./abstraction_size.bend as Size
import ./map_routing.bend as R
import ./map_delete_prefix.bend as And

# Native enumeration cannot hide a None leaf, including behind a nonempty
# accumulator. Return both tree and accumulator facts for structural induction.
law join_right:
  for -K: Data
  for -V: Data
  for +lo: Map<&2, Maybe<&2, T.Entry<K, V>>>
  for +hi: Map<&2, Maybe<&2, T.Entry<K, V>>>
  for acc: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>
  for left: {Pop.populated(T.Entry<K, V>, lo) == True{} : Bool}
  for pair: {Pop.populated(T.Entry<K, V>, hi) == True{} : Bool} & {Size.packed(K, V, acc) == True{} : Bool}
  {Pop.populated(T.Entry<K, V>, lo) && Pop.populated(T.Entry<K, V>, hi) == True{} : Bool} & {Size.packed(K, V, acc) == True{} : Bool}
def join_right(K, V, lo, hi, acc, left, pair):
  (right, tail) = pair
  (And.conjunction(Pop.populated(T.Entry<K, V>, lo), Pop.populated(T.Entry<K, V>, hi), left, right), tail)

law join_left:
  for -K: Data
  for -V: Data
  for +lo: Map<&2, Maybe<&2, T.Entry<K, V>>>
  for +hi: Map<&2, Maybe<&2, T.Entry<K, V>>>
  for +acc: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>
  for recurse: {Size.packed(K, V, Map.to_list.go(&2, Maybe<&2, T.Entry<K, V>>, hi, acc)) == True{} : Bool} -> {Pop.populated(T.Entry<K, V>, hi) == True{} : Bool} & {Size.packed(K, V, acc) == True{} : Bool}
  for pair: {Pop.populated(T.Entry<K, V>, lo) == True{} : Bool} & {Size.packed(K, V, Map.to_list.go(&2, Maybe<&2, T.Entry<K, V>>, hi, acc)) == True{} : Bool}
  {Pop.populated(T.Entry<K, V>, lo) && Pop.populated(T.Entry<K, V>, hi) == True{} : Bool} & {Size.packed(K, V, acc) == True{} : Bool}
def join_left(K, V, lo, hi, acc, recurse, pair):
  (left, remainder) = pair
  join_right(K, V, lo, hi, acc, left, recurse(remainder))

law packed_partition:
  for -K: Data
  for -V: Data
  for tree: Map<&2, Maybe<&2, T.Entry<K, V>>>
  for +acc: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>
  for packed: {Size.packed(K, V, Map.to_list.go(&2, Maybe<&2, T.Entry<K, V>>, tree, acc)) == True{} : Bool}
  {Pop.populated(T.Entry<K, V>, tree) == True{} : Bool} & {Size.packed(K, V, acc) == True{} : Bool}
def packed_partition(K, V, tree, acc, packed):
  match tree:
    case MTip{}: ({==}, packed)
    case MLeaf{code, None{}}:
      Empty.absurd({False{} == True{} : Bool} & {Size.packed(K, V, acc) == True{} : Bool}, R.false_true(packed))
    case MLeaf{code, Some{entry}}: ({==}, packed)
    case MNode{p, +lo, +hi}:
      join_left(K, V, lo, hi, acc, r => packed_partition(K, V, hi, acc, r), packed_partition(K, V, lo, Map.to_list.go(&2, Maybe<&2, T.Entry<K, V>>, hi, acc), packed))

law take_tree:
  for -K: Data
  for -V: Data
  for tree: Map<&2, Maybe<&2, T.Entry<K, V>>>
  for pair: {Pop.populated(T.Entry<K, V>, tree) == True{} : Bool} & {Size.packed(K, V, Nil{}) == True{} : Bool}
  {Pop.populated(T.Entry<K, V>, tree) == True{} : Bool}
def take_tree(K, V, tree, pair):
  (populated, tail) = pair
  populated

law packed_tree:
  for -K: Data
  for -V: Data
  for +tree: Map<&2, Maybe<&2, T.Entry<K, V>>>
  for packed: {Size.packed(K, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, tree)) == True{} : Bool}
  {Pop.populated(T.Entry<K, V>, tree) == True{} : Bool}
def packed_tree(K, V, tree, packed):
  take_tree(K, V, tree, packed_partition(K, V, tree, Nil{}, packed))
