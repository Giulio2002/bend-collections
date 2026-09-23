import Base
import ./abstraction_bindings.bend as A
import ./refinement.bend as F
import ./map_populated.bend as P
import ./cache_populated.bend as CPop
import ./native_map.bend as Native
import ./map_routing.bend as R
import ../src/cache.bend as C
import ../types/model.bend as T

def packed(-K: Data, -V: Data, xs: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>) -> Bool:
  match xs:
    case Nil{}: True{}
    case Con{Tuple{code, item}, tail}:
      Maybe.is_some(&2, T.Entry<K, V>, item) && packed(K, V, tail)

law enumerated_populated:
  for -K: Data
  for -V: Data
  for tree: Map<&2, Maybe<&2, T.Entry<K, V>>>
  for +acc: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>
  for +valid: {P.populated(T.Entry<K, V>, tree) == True{} : Bool}
  for packed_acc: {packed(K, V, acc) == True{} : Bool}
  {packed(K, V, Map.to_list.go(&2, Maybe<&2, T.Entry<K, V>>, tree, acc)) == True{} : Bool}
def enumerated_populated(K, V, tree, acc, valid, packed_acc):
  match tree:
    case MTip{}: packed_acc
    case MLeaf{key, None{}}:
      Empty.absurd({packed(K, V, Con{Tuple{key, None{}}, acc}) == True{} : Bool}, R.false_true(valid))
    case MLeaf{key, Some{entry}}: packed_acc
    case MNode{p, +lo, +hi}:
      enumerated_populated(K, V, lo, Map.to_list.go(&2, Maybe<&2, T.Entry<K, V>>, hi, acc), R.and_left(P.populated(T.Entry<K, V>, lo), P.populated(T.Entry<K, V>, hi), valid), enumerated_populated(K, V, hi, acc, R.and_right(P.populated(T.Entry<K, V>, lo), P.populated(T.Entry<K, V>, hi), valid), packed_acc))

law bindings_length:
  for -K: Data
  for -V: Data
  for xs: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>
  for valid: {packed(K, V, xs) == True{} : Bool}
  {List.length(&2, T.Entry<K, V>, F.bindings(K, V, xs)) == List.length(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, xs) : Nat}
def bindings_length(K, V, xs, valid):
  match xs:
    case Nil{}: {==}
    case Con{Tuple{code, None{}}, tail}:
      Empty.absurd({List.length(&2, T.Entry<K, V>, F.bindings(K, V, tail)) == 1n+List.length(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, tail) : Nat}, R.false_true(valid))
    case Con{Tuple{code, Some{entry}}, +tail}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, T.Entry<K, V>, F.bindings(K, V, tail)), List.length(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, tail), bindings_length(K, V, tail, valid))

# No stored binding is discarded by bindings when there are no stored None.
# The premise is a representation component, not full cache reachability.
law abstraction_size:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for valid: {CPop.storage_populated(K, V, c) == True{} : Bool}
  {List.length(&2, T.Entry<K, V>, A.model_bindings(K, V, F.abstract(K, V, c))) == C.map_size(K, V, c) : Nat}
def abstraction_size(K, V, c, valid):
  match c:
    case C.State{cap, +table, order, life, counts, cb}:
      Equal.trans(Nat, List.length(&2, T.Entry<K, V>, F.bindings(K, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table))), List.length(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)), Map.size(&2, Maybe<&2, T.Entry<K, V>>, table), bindings_length(K, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table), enumerated_populated(K, V, table, Nil{}, valid, {==})), Native.entries_size(Maybe<&2, T.Entry<K, V>>, table))
