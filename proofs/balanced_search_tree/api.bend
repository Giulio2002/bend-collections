import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../../spec/common.bend as SC
import ../../spec/balanced_search_tree.bend as S
import ../../reference/legacy_balanced_search_tree.bend as B
import ../../types/balanced_search_tree.bend as E
import ./sorted.bend as SO
import ./specops.bend as SP
import ./tree.bend as T
import ./query.bend as Q
import ./steps.bend as ST

# The ordered map's public operations as used by client structures
# (src/graph.bend): each is characterised on the abstraction ST.abs under
# the invariant ST.inv, which each state-changing operation preserves.

# Deleting an absent key changes nothing.
def del_absent_c(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +t: List<&2, E.Entry<K, V>>, +k: K, c: Cmp, +ec: {cmp(k, E.key(K, V, e)) == c : Cmp}, +f: {S.find(~K, ~cmp, V, k, Con{e, t}) == None{} : Maybe<&2, V>}, ih: @+f2: {S.find(~K, ~cmp, V, k, t) == None{} : Maybe<&2, V>} -> {S.del(~K, ~cmp, V, k, t) == t : List<&2, E.Entry<K, V>>}) -> {S.del(~K, ~cmp, V, k, Con{e, t}) == Con{e, t} : List<&2, E.Entry<K, V>>}:
  match c:
    case EQ{}:
      Empty.absurd({S.del(~K, ~cmp, V, k, Con{e, t}) == Con{e, t} : List<&2, E.Entry<K, V>>}, L.none_some(V, E.val(K, V, e), Equal.trans(Maybe<&2, V>, None{}, S.find(~K, ~cmp, V, k, Con{e, t}), Some{E.val(K, V, e)}, Equal.sym(Maybe<&2, V>, S.find(~K, ~cmp, V, k, Con{e, t}), None{}, f), SP.find_eq(~K, ~cmp, V, e, t, k, ec))))
    case LT{}:
      Equal.trans(List<&2, E.Entry<K, V>>, S.del(~K, ~cmp, V, k, Con{e, t}), Con{e, S.del(~K, ~cmp, V, k, t)}, Con{e, t},
        SP.del_lt(~K, ~cmp, V, e, t, k, ec),
        LL.cons_cong(E.Entry<K, V>, e, S.del(~K, ~cmp, V, k, t), t, ih(Equal.trans(Maybe<&2, V>, S.find(~K, ~cmp, V, k, t), S.find(~K, ~cmp, V, k, Con{e, t}), None{}, Equal.sym(Maybe<&2, V>, S.find(~K, ~cmp, V, k, Con{e, t}), S.find(~K, ~cmp, V, k, t), SP.find_lt(~K, ~cmp, V, e, t, k, ec)), f))))
    case GT{}:
      Equal.trans(List<&2, E.Entry<K, V>>, S.del(~K, ~cmp, V, k, Con{e, t}), Con{e, S.del(~K, ~cmp, V, k, t)}, Con{e, t},
        SP.del_gt(~K, ~cmp, V, e, t, k, ec),
        LL.cons_cong(E.Entry<K, V>, e, S.del(~K, ~cmp, V, k, t), t, ih(Equal.trans(Maybe<&2, V>, S.find(~K, ~cmp, V, k, t), S.find(~K, ~cmp, V, k, Con{e, t}), None{}, Equal.sym(Maybe<&2, V>, S.find(~K, ~cmp, V, k, Con{e, t}), S.find(~K, ~cmp, V, k, t), SP.find_gt(~K, ~cmp, V, e, t, k, ec)), f))))

def del_absent(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +xs: List<&2, E.Entry<K, V>>, +k: K, +f: {S.find(~K, ~cmp, V, k, xs) == None{} : Maybe<&2, V>}) -> {S.del(~K, ~cmp, V, k, xs) == xs : List<&2, E.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      del_absent_c(~K, ~cmp, V, e, t, k, cmp(k, E.key(K, V, e)), {==}, f, f2 => del_absent(~K, ~cmp, V, t, k, f2))

def new_abs(~K: Data, ~cmp: K -> K -> Cmp, -V: Data) -> {ST.abs(~K, ~cmp, V, B.new(K, V)) == Nil{} : List<&2, E.Entry<K, V>>}:
  {==}

def new_inv(~K: Data, ~cmp: K -> K -> Cmp, -V: Data) -> {ST.inv(~K, ~cmp, V, B.new(K, V)) == True{} : Bool}:
  {==}

def get_ok(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +s: B.OrdMap<K, V>, +k: K, +g: {ST.inv(~K, ~cmp, V, s) == True{} : Bool}) -> {B.get(~K, ~cmp, V, s, k) == S.find(~K, ~cmp, V, k, ST.abs(~K, ~cmp, V, s)) : Maybe<&2, V>}:
  match s:
    case B.BST{+n, +t}:
      ST.lookup_ok(~K, ~cmp, ~o, V, t, k, ST.inv_s(~K, ~cmp, V, n, t, g))

def contains_ok(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +s: B.OrdMap<K, V>, +k: K, +g: {ST.inv(~K, ~cmp, V, s) == True{} : Bool}) -> {B.contains(~K, ~cmp, V, s, k) == S.is_some(V, S.find(~K, ~cmp, V, k, ST.abs(~K, ~cmp, V, s))) : Bool}:
  match s:
    case B.BST{+n, +t}:
      Equal.trans(Bool, B.present(V, B.lookup_tree(~K, ~cmp, V, t, k)), S.is_some(V, B.lookup_tree(~K, ~cmp, V, t, k)), S.is_some(V, S.find(~K, ~cmp, V, k, T.io(K, V, t))),
        ST.present_some(V, B.lookup_tree(~K, ~cmp, V, t, k)),
        Equal.cong(Maybe<&2, V>, Bool, z => S.is_some(V, z), B.lookup_tree(~K, ~cmp, V, t, k), S.find(~K, ~cmp, V, k, T.io(K, V, t)), ST.lookup_ok(~K, ~cmp, ~o, V, t, k, ST.inv_s(~K, ~cmp, V, n, t, g))))

def insert_abs(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +s: B.OrdMap<K, V>, +k: K, +v: V, +g: {ST.inv(~K, ~cmp, V, s) == True{} : Bool}) -> {ST.abs(~K, ~cmp, V, B.insert(~K, ~cmp, V, s, k, v)) == S.ins(~K, ~cmp, V, k, v, ST.abs(~K, ~cmp, V, s)) : List<&2, E.Entry<K, V>>}:
  match s:
    case B.BST{+n, +t}:
      T.insert_io(~K, ~cmp, ~o, V, t, k, v, ST.inv_s(~K, ~cmp, V, n, t, g))

def insert_inv(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +s: B.OrdMap<K, V>, +k: K, +v: V, +g: {ST.inv(~K, ~cmp, V, s) == True{} : Bool}) -> {ST.inv(~K, ~cmp, V, B.insert(~K, ~cmp, V, s, k, v)) == True{} : Bool}:
  match s:
    case B.BST{+n, +t}:
      ST.insert_inv(~K, ~cmp, ~o, V, n, t, k, v, g)

def RemOK(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, s: B.OrdMap<K, V>, k: K) -> Type:
  {ST.abs(~K, ~cmp, V, Pair.fst(B.OrdMap<K, V>, Result<&2, &2, E.Error, V>, B.remove(~K, ~cmp, V, s, k))) == S.del(~K, ~cmp, V, k, ST.abs(~K, ~cmp, V, s)) : List<&2, E.Entry<K, V>>} & {ST.inv(~K, ~cmp, V, Pair.fst(B.OrdMap<K, V>, Result<&2, &2, E.Error, V>, B.remove(~K, ~cmp, V, s, k))) == True{} : Bool}

def remove_at_ok(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +n: Nat, +t: B.Tree<K, V>, +k: K, m: Maybe<&2, V>, +em: {B.lookup_tree(~K, ~cmp, V, t, k) == m : Maybe<&2, V>}, +g: {ST.inv(~K, ~cmp, V, B.BST{n, t}) == True{} : Bool}) -> RemOK(~K, ~cmp, V, B.BST{n, t}, k):
  match m:
    case None{}:
      -EE = E.Entry<K, V>
      +s = ST.inv_s(~K, ~cmp, V, n, t, g)
      +ef = Equal.trans(Maybe<&2, V>, S.find(~K, ~cmp, V, k, T.io(K, V, t)), B.lookup_tree(~K, ~cmp, V, t, k), None{}, Equal.sym(Maybe<&2, V>, B.lookup_tree(~K, ~cmp, V, t, k), S.find(~K, ~cmp, V, k, T.io(K, V, t)), ST.lookup_ok(~K, ~cmp, ~o, V, t, k, s)), em)
      %Equal.sym(Maybe<&2, V>, B.lookup_tree(~K, ~cmp, V, t, k), None{}, em) : {ST.abs(~K, ~cmp, V, Pair.fst(B.OrdMap<K, V>, Result<&2, &2, E.Error, V>, B.remove_at(~K, ~cmp, V, _, n, t, k))) == S.del(~K, ~cmp, V, k, T.io(K, V, t)) : List<&2, EE>} & {ST.inv(~K, ~cmp, V, Pair.fst(B.OrdMap<K, V>, Result<&2, &2, E.Error, V>, B.remove_at(~K, ~cmp, V, _, n, t, k))) == True{} : Bool}
      (Equal.sym(List<&2, EE>, S.del(~K, ~cmp, V, k, T.io(K, V, t)), T.io(K, V, t), del_absent(~K, ~cmp, V, T.io(K, V, t), k, ef)), g)
    case Some{+w}:
      -EE = E.Entry<K, V>
      +s = ST.inv_s(~K, ~cmp, V, n, t, g)
      +ef = Equal.trans(Maybe<&2, V>, S.find(~K, ~cmp, V, k, T.io(K, V, t)), B.lookup_tree(~K, ~cmp, V, t, k), Some{w}, Equal.sym(Maybe<&2, V>, B.lookup_tree(~K, ~cmp, V, t, k), S.find(~K, ~cmp, V, k, T.io(K, V, t)), ST.lookup_ok(~K, ~cmp, ~o, V, t, k, s)), em)
      +t1 = B.remove_tree(~K, ~cmp, V, t, k)
      +er = T.remove_io(~K, ~cmp, ~o, V, t, k, s)
      +ld = SP.len_del(~K, ~cmp, ~o, V, T.io(K, V, t), k, w, s, ef)
      %Equal.sym(Maybe<&2, V>, B.lookup_tree(~K, ~cmp, V, t, k), Some{w}, em) : {ST.abs(~K, ~cmp, V, Pair.fst(B.OrdMap<K, V>, Result<&2, &2, E.Error, V>, B.remove_at(~K, ~cmp, V, _, n, t, k))) == S.del(~K, ~cmp, V, k, T.io(K, V, t)) : List<&2, EE>} & {ST.inv(~K, ~cmp, V, Pair.fst(B.OrdMap<K, V>, Result<&2, &2, E.Error, V>, B.remove_at(~K, ~cmp, V, _, n, t, k))) == True{} : Bool}
      (er,
       ST.inv_mk(~K, ~cmp, V, Nat.sub(n, 1n), t1,
         L.subst(List<&2, EE>, xs => {SO.sorted(~K, ~cmp, V, xs) == True{} : Bool}, S.del(~K, ~cmp, V, k, T.io(K, V, t)), T.io(K, V, t1), Equal.sym(List<&2, EE>, T.io(K, V, t1), S.del(~K, ~cmp, V, k, T.io(K, V, t)), er), SP.sorted_del(~K, ~cmp, V, T.io(K, V, t), k, s)),
         T.remove_bal(~K, ~cmp, V, t, k, ST.inv_b(~K, ~cmp, V, n, t, g)),
         Equal.trans(Nat, Nat.sub(n, 1n), Nat.sub(1n+SC.length(EE, S.del(~K, ~cmp, V, k, T.io(K, V, t))), 1n), SC.length(EE, T.io(K, V, t1)),
           Equal.cong(Nat, Nat, x => Nat.sub(x, 1n), n, 1n+SC.length(EE, S.del(~K, ~cmp, V, k, T.io(K, V, t))), Equal.trans(Nat, n, SC.length(EE, T.io(K, V, t)), 1n+SC.length(EE, S.del(~K, ~cmp, V, k, T.io(K, V, t))), ST.inv_n(~K, ~cmp, V, n, t, g), Equal.sym(Nat, 1n+SC.length(EE, S.del(~K, ~cmp, V, k, T.io(K, V, t))), SC.length(EE, T.io(K, V, t)), ld))),
           Equal.trans(Nat, Nat.sub(1n+SC.length(EE, S.del(~K, ~cmp, V, k, T.io(K, V, t))), 1n), SC.length(EE, S.del(~K, ~cmp, V, k, T.io(K, V, t))), SC.length(EE, T.io(K, V, t1)),
             N.sub_zero(SC.length(EE, S.del(~K, ~cmp, V, k, T.io(K, V, t)))),
             Equal.cong(List<&2, EE>, Nat, xs => SC.length(EE, xs), S.del(~K, ~cmp, V, k, T.io(K, V, t)), T.io(K, V, t1), Equal.sym(List<&2, EE>, T.io(K, V, t1), S.del(~K, ~cmp, V, k, T.io(K, V, t)), er))))))

def remove_ok(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +s: B.OrdMap<K, V>, +k: K, +g: {ST.inv(~K, ~cmp, V, s) == True{} : Bool}) -> RemOK(~K, ~cmp, V, s, k):
  match s:
    case B.BST{+n, +t}:
      remove_at_ok(~K, ~cmp, ~o, V, n, t, k, B.lookup_tree(~K, ~cmp, V, t, k), {==}, g)

def to_list_ok(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +s: B.OrdMap<K, V>) -> {B.to_list(K, V, s) == ST.abs(~K, ~cmp, V, s) : List<&2, E.Entry<K, V>>}:
  match s:
    case B.BST{n, +t}:
      Equal.trans(List<&2, E.Entry<K, V>>, B.entries(K, V, t, Nil{}), SC.append(E.Entry<K, V>, T.io(K, V, t), Nil{}), T.io(K, V, t), Q.entries_ok(K, V, t, Nil{}), LL.append_nil(E.Entry<K, V>, T.io(K, V, t)))
