import Base
import ../../src/balanced_search_tree.bend as B
import ../../types/balanced_search_tree.bend as E

# Universal equivalence to the existing insertion and lookup algorithms.
# No sortedness/order premise is needed: the same comparator decisions and
# balancing calls are made even on an arbitrary tree.
def descent(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +t: B.Tree<K, V>, +k: K, +v: V, +a: Cmp) -> {B.ins_found(~K, ~cmp, V, t, k, v, a) == (B.ins(~K, ~cmp, V, t, k, v, a), B.find(~K, ~cmp, V, t, k, a)) : B.Tree<K, V> & Maybe<&2, V>}:
  match t a:
    case B.Leaf{} _:
      {==}
    case B.Node{c, +l, e, r} LT{}:
      Equal.cong(B.Tree<K, V> & Maybe<&2, V>, B.Tree<K, V> & Maybe<&2, V>, q => B.ins_left(K, V, c, e, r, q),
        B.ins_found(~K, ~cmp, V, l, k, v, B.c1(~K, ~cmp, V, k, l)),
        (B.ins(~K, ~cmp, V, l, k, v, B.c1(~K, ~cmp, V, k, l)), B.find(~K, ~cmp, V, l, k, B.c1(~K, ~cmp, V, k, l))),
        descent(~K, ~cmp, V, l, k, v, B.c1(~K, ~cmp, V, k, l)))
    case B.Node{c, l, e, r} EQ{}:
      {==}
    case B.Node{c, l, e, +r} GT{}:
      Equal.cong(B.Tree<K, V> & Maybe<&2, V>, B.Tree<K, V> & Maybe<&2, V>, q => B.ins_right(K, V, c, l, e, q),
        B.ins_found(~K, ~cmp, V, r, k, v, B.c1(~K, ~cmp, V, k, r)),
        (B.ins(~K, ~cmp, V, r, k, v, B.c1(~K, ~cmp, V, k, r)), B.find(~K, ~cmp, V, r, k, B.c1(~K, ~cmp, V, k, r))),
        descent(~K, ~cmp, V, r, k, v, B.c1(~K, ~cmp, V, k, r)))

def same(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +n: Nat, +t: B.Tree<K, V>, +k: K, +v: V) -> {B.insert(~K, ~cmp, V, B.BST{n, t}, k, v) == B.BST{B.grow(V, B.lookup_tree(~K, ~cmp, V, t, k), n), B.insert_tree(~K, ~cmp, V, t, k, v)} : B.OrdMap<K, V>}:
  Equal.cong(B.Tree<K, V> & Maybe<&2, V>, B.OrdMap<K, V>, q => B.insert_finish(K, V, n, q),
    B.ins_found(~K, ~cmp, V, t, k, v, B.c1(~K, ~cmp, V, k, t)),
    (B.ins(~K, ~cmp, V, t, k, v, B.c1(~K, ~cmp, V, k, t)), B.find(~K, ~cmp, V, t, k, B.c1(~K, ~cmp, V, k, t))),
    descent(~K, ~cmp, V, t, k, v, B.c1(~K, ~cmp, V, k, t)))

def same_u32(+n: Nat, +t: B.Tree<U32, U32>, +k: U32, +v: U32) -> {B.insert(~U32, ~U32.cmp, U32, B.BST{n, t}, k, v) == B.BST{B.grow(U32, B.lookup_tree(~U32, ~U32.cmp, U32, t, k), n), B.insert_tree(~U32, ~U32.cmp, U32, t, k, v)} : B.OrdMap<U32, U32>}:
  same(~U32, ~U32.cmp, U32, n, t, k, v)

def same_string(+n: Nat, +t: B.Tree<String, String>, +k: String, +v: String) -> {B.insert(~String, ~String.order, String, B.BST{n, t}, k, v) == B.BST{B.grow(String, B.lookup_tree(~String, ~String.order, String, t, k), n), B.insert_tree(~String, ~String.order, String, t, k, v)} : B.OrdMap<String, String>}:
  same(~String, ~String.order, String, n, t, k, v)
