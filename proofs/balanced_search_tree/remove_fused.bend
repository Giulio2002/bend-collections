import Base
import ../lib/logic.bend as L
import ../../reference/legacy_balanced_search_tree.bend as B
import ../../types/balanced_search_tree.bend as E

# Deletion and the returned old binding follow precisely the same search.
def descent(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +t: B.Tree<K, V>, +k: K, +a: Cmp) -> {B.del_found(~K, ~cmp, V, t, k, a) == (B.del(~K, ~cmp, V, t, k, a), B.find(~K, ~cmp, V, t, k, a)) : B.UpD<K, V> & Maybe<&2, V>}:
  match t a:
    case B.Leaf{} _:
      {==}
    case B.Node{c, +l, e, r} LT{}:
      Equal.cong(B.UpD<K, V> & Maybe<&2, V>, B.UpD<K, V> & Maybe<&2, V>, q => B.del_left_found(K, V, r, c, e, q),
        B.del_found(~K, ~cmp, V, l, k, B.c1(~K, ~cmp, V, k, l)),
        (B.del(~K, ~cmp, V, l, k, B.c1(~K, ~cmp, V, k, l)), B.find(~K, ~cmp, V, l, k, B.c1(~K, ~cmp, V, k, l))),
        descent(~K, ~cmp, V, l, k, B.c1(~K, ~cmp, V, k, l)))
    case B.Node{c, l, e, r} EQ{}:
      {==}
    case B.Node{c, l, e, +r} GT{}:
      Equal.cong(B.UpD<K, V> & Maybe<&2, V>, B.UpD<K, V> & Maybe<&2, V>, q => B.del_right_found(K, V, l, c, e, q),
        B.del_found(~K, ~cmp, V, r, k, B.c1(~K, ~cmp, V, k, r)),
        (B.del(~K, ~cmp, V, r, k, B.c1(~K, ~cmp, V, k, r)), B.find(~K, ~cmp, V, r, k, B.c1(~K, ~cmp, V, k, r))),
        descent(~K, ~cmp, V, r, k, B.c1(~K, ~cmp, V, k, r)))

# A miss preserves the exact tree, including colours. This needs no balancing
# invariant and prevents a failed removal from blackening an arbitrary root.
def absent(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +t: B.Tree<K, V>, +k: K, +a: Cmp, h: {B.find(~K, ~cmp, V, t, k, a) == None{} : Maybe<&2, V>}) -> {B.del(~K, ~cmp, V, t, k, a) == B.TD{t} : B.UpD<K, V>}:
  match t a:
    case B.Leaf{} _:
      {==}
    case B.Node{c, +l, e, r} LT{}:
      Equal.cong(B.UpD<K, V>, B.UpD<K, V>, u => B.fix_left(K, V, r, c, u, e), B.del(~K, ~cmp, V, l, k, B.c1(~K, ~cmp, V, k, l)), B.TD{l}, absent(~K, ~cmp, V, l, k, B.c1(~K, ~cmp, V, k, l), h))
    case B.Node{c, l, e, r} EQ{}:
      Empty.absurd({B.del_here(K, V, c, l, r) == B.TD{B.Node{c, l, e, r}} : B.UpD<K, V>}, L.none_some(V, E.val(K, V, e), Equal.sym(Maybe<&2, V>, Some{E.val(K, V, e)}, None{}, h)))
    case B.Node{c, l, e, +r} GT{}:
      Equal.cong(B.UpD<K, V>, B.UpD<K, V>, u => B.fix_right(K, V, l, c, e, u), B.del(~K, ~cmp, V, r, k, B.c1(~K, ~cmp, V, k, r)), B.TD{r}, absent(~K, ~cmp, V, r, k, B.c1(~K, ~cmp, V, k, r), h))

def finish_same(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +n: Nat, +t: B.Tree<K, V>, +k: K, +m: Maybe<&2, V>, h: {B.lookup_tree(~K, ~cmp, V, t, k) == m : Maybe<&2, V>}) -> {B.remove_finish(K, V, n, (B.del(~K, ~cmp, V, t, k, B.c1(~K, ~cmp, V, k, t)), m)) == B.remove_at(~K, ~cmp, V, m, n, t, k) : B.OrdMap<K, V> & Result<&2, &2, E.Error, V>}:
  match m:
    case None{}:
      Equal.cong(B.UpD<K, V>, B.OrdMap<K, V> & Result<&2, &2, E.Error, V>, u => B.remove_finish(K, V, n, (u, None{})), B.del(~K, ~cmp, V, t, k, B.c1(~K, ~cmp, V, k, t)), B.TD{t}, absent(~K, ~cmp, V, t, k, B.c1(~K, ~cmp, V, k, t), h))
    case Some{v}:
      {==}

def same(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +n: Nat, +t: B.Tree<K, V>, +k: K) -> {B.remove(~K, ~cmp, V, B.BST{n, t}, k) == B.remove_at(~K, ~cmp, V, B.lookup_tree(~K, ~cmp, V, t, k), n, t, k) : B.OrdMap<K, V> & Result<&2, &2, E.Error, V>}:
  Equal.trans(B.OrdMap<K, V> & Result<&2, &2, E.Error, V>, B.remove(~K, ~cmp, V, B.BST{n, t}, k), B.remove_finish(K, V, n, (B.del(~K, ~cmp, V, t, k, B.c1(~K, ~cmp, V, k, t)), B.lookup_tree(~K, ~cmp, V, t, k))), B.remove_at(~K, ~cmp, V, B.lookup_tree(~K, ~cmp, V, t, k), n, t, k),
    Equal.cong(B.UpD<K, V> & Maybe<&2, V>, B.OrdMap<K, V> & Result<&2, &2, E.Error, V>, q => B.remove_finish(K, V, n, q), B.del_found(~K, ~cmp, V, t, k, B.c1(~K, ~cmp, V, k, t)), (B.del(~K, ~cmp, V, t, k, B.c1(~K, ~cmp, V, k, t)), B.lookup_tree(~K, ~cmp, V, t, k)), descent(~K, ~cmp, V, t, k, B.c1(~K, ~cmp, V, k, t))),
    finish_same(~K, ~cmp, V, n, t, k, B.lookup_tree(~K, ~cmp, V, t, k), {==}))

def same_u32(+n: Nat, +t: B.Tree<U32, U32>, +k: U32) -> {B.remove(~U32, ~U32.cmp, U32, B.BST{n, t}, k) == B.remove_at(~U32, ~U32.cmp, U32, B.lookup_tree(~U32, ~U32.cmp, U32, t, k), n, t, k) : B.OrdMap<U32, U32> & Result<&2, &2, E.Error, U32>}:
  same(~U32, ~U32.cmp, U32, n, t, k)

def same_string(+n: Nat, +t: B.Tree<String, String>, +k: String) -> {B.remove(~String, ~String.order, String, B.BST{n, t}, k) == B.remove_at(~String, ~String.order, String, B.lookup_tree(~String, ~String.order, String, t, k), n, t, k) : B.OrdMap<String, String> & Result<&2, &2, E.Error, String>}:
  same(~String, ~String.order, String, n, t, k)
