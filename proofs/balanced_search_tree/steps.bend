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
import ./insert_fused.bend as F
import ./remove_fused.bend as RF

# Ordered-map state: abstraction, invariant and every public operation.

def abs(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, s: B.OrdMap<K, V>) -> List<&2, E.Entry<K, V>>:
  match s:
    case B.BST{n, t}:
      T.io(K, V, t)

# Invariant: in-order keys strictly increasing, the red-black invariant
# (black root, no red-red parent/child edge, equal black height on every
# root-to-leaf path: `T.bal`), and the cached size is the entry count.
def inv(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, s: B.OrdMap<K, V>) -> Bool:
  match s:
    case B.BST{+n, +t}:
      Bool.and(SO.sorted(~K, ~cmp, V, T.io(K, V, t)), Bool.and(T.bal(K, V, t), Nat.is_eq(n, SC.length(E.Entry<K, V>, T.io(K, V, t)))))

def view1(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, r: B.OrdMap<K, V> & E.Obs<K, V>) -> List<&2, E.Entry<K, V>> & E.Obs<K, V>:
  match r:
    case Tuple{s, o}:
      (abs(~K, ~cmp, V, s), o)

def StepOK(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, s: B.OrdMap<K, V>, op: E.Op<K, V>) -> Type:
  {view1(~K, ~cmp, V, B.step(~K, ~cmp, V, s, op)) == S.step(~K, ~cmp, V, abs(~K, ~cmp, V, s), op) : List<&2, E.Entry<K, V>> & E.Obs<K, V>} & {inv(~K, ~cmp, V, Pair.fst(B.OrdMap<K, V>, E.Obs<K, V>, B.step(~K, ~cmp, V, s, op))) == True{} : Bool}

def inv_s(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +n: Nat, +t: B.Tree<K, V>, +g: {inv(~K, ~cmp, V, B.BST{n, t}) == True{} : Bool}) -> {SO.sorted(~K, ~cmp, V, T.io(K, V, t)) == True{} : Bool}:
  L.and_left(SO.sorted(~K, ~cmp, V, T.io(K, V, t)), Bool.and(T.bal(K, V, t), Nat.is_eq(n, SC.length(E.Entry<K, V>, T.io(K, V, t)))), g)

def inv_b(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +n: Nat, +t: B.Tree<K, V>, +g: {inv(~K, ~cmp, V, B.BST{n, t}) == True{} : Bool}) -> {T.bal(K, V, t) == True{} : Bool}:
  L.and_left(T.bal(K, V, t), Nat.is_eq(n, SC.length(E.Entry<K, V>, T.io(K, V, t))), L.and_right(SO.sorted(~K, ~cmp, V, T.io(K, V, t)), Bool.and(T.bal(K, V, t), Nat.is_eq(n, SC.length(E.Entry<K, V>, T.io(K, V, t)))), g))

def inv_n(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +n: Nat, +t: B.Tree<K, V>, +g: {inv(~K, ~cmp, V, B.BST{n, t}) == True{} : Bool}) -> {n == SC.length(E.Entry<K, V>, T.io(K, V, t)) : Nat}:
  N.eq_from_is_eq(n, SC.length(E.Entry<K, V>, T.io(K, V, t)), L.and_right(T.bal(K, V, t), Nat.is_eq(n, SC.length(E.Entry<K, V>, T.io(K, V, t))), L.and_right(SO.sorted(~K, ~cmp, V, T.io(K, V, t)), Bool.and(T.bal(K, V, t), Nat.is_eq(n, SC.length(E.Entry<K, V>, T.io(K, V, t)))), g)))

def inv_mk(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +n: Nat, +t: B.Tree<K, V>, +s: {SO.sorted(~K, ~cmp, V, T.io(K, V, t)) == True{} : Bool}, +b: {T.bal(K, V, t) == True{} : Bool}, +en: {n == SC.length(E.Entry<K, V>, T.io(K, V, t)) : Nat}) -> {inv(~K, ~cmp, V, B.BST{n, t}) == True{} : Bool}:
  L.and_intro(SO.sorted(~K, ~cmp, V, T.io(K, V, t)), Bool.and(T.bal(K, V, t), Nat.is_eq(n, SC.length(E.Entry<K, V>, T.io(K, V, t)))), s,
    L.and_intro(T.bal(K, V, t), Nat.is_eq(n, SC.length(E.Entry<K, V>, T.io(K, V, t))), b, L.subst(Nat, x => {Nat.is_eq(n, x) == True{} : Bool}, n, SC.length(E.Entry<K, V>, T.io(K, V, t)), en, N.is_eq_refl(n))))

# ---- result wrappers: src and spec define the same conversions ----

def result_value(-V: Data, +m: Maybe<&2, V>) -> {B.result(V, m) == S.value(V, m) : Result<&2, &2, E.Error, V>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

def present_some(-V: Data, +m: Maybe<&2, V>) -> {B.present(V, m) == S.is_some(V, m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

def entry_eq(-K: Data, -V: Data, +m: Maybe<&2, E.Entry<K, V>>, +err: E.Error) -> {B.entry(K, V, m, err) == S.entry(K, V, m, err) : Result<&2, &2, E.Error, E.Entry<K, V>>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

# ---- insert / remove ----

def lookup_ok(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +t: B.Tree<K, V>, +k: K, +s: {SO.sorted(~K, ~cmp, V, T.io(K, V, t)) == True{} : Bool}) -> {B.lookup_tree(~K, ~cmp, V, t, k) == S.find(~K, ~cmp, V, k, T.io(K, V, t)) : Maybe<&2, V>}:
  Q.find_ok(~K, ~cmp, ~o, V, t, k, B.c1(~K, ~cmp, V, k, t), {==}, s)

def insert_inv(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +n: Nat, +t: B.Tree<K, V>, +k: K, +v: V, +g: {inv(~K, ~cmp, V, B.BST{n, t}) == True{} : Bool}) -> {inv(~K, ~cmp, V, B.insert(~K, ~cmp, V, B.BST{n, t}, k, v)) == True{} : Bool}:
  %Equal.sym(B.OrdMap<K, V>, B.insert(~K, ~cmp, V, B.BST{n, t}, k, v), B.BST{B.grow(V, B.lookup_tree(~K, ~cmp, V, t, k), n), B.insert_tree(~K, ~cmp, V, t, k, v)}, F.same(~K, ~cmp, V, n, t, k, v)) : {inv(~K, ~cmp, V, _) == True{} : Bool}
  -EE = E.Entry<K, V>
  +s = inv_s(~K, ~cmp, V, n, t, g)
  +t1 = B.insert_tree(~K, ~cmp, V, t, k, v)
  +ei = T.insert_io(~K, ~cmp, ~o, V, t, k, v, s)
  inv_mk(~K, ~cmp, V, B.grow(V, B.lookup_tree(~K, ~cmp, V, t, k), n), t1,
    L.subst(List<&2, EE>, xs => {SO.sorted(~K, ~cmp, V, xs) == True{} : Bool}, S.ins(~K, ~cmp, V, k, v, T.io(K, V, t)), T.io(K, V, t1), Equal.sym(List<&2, EE>, T.io(K, V, t1), S.ins(~K, ~cmp, V, k, v, T.io(K, V, t)), ei), SP.sorted_ins(~K, ~cmp, ~o, V, T.io(K, V, t), k, v, s)),
    T.insert_bal(~K, ~cmp, V, t, k, v, inv_b(~K, ~cmp, V, n, t, g)),
    Equal.trans(Nat, B.grow(V, B.lookup_tree(~K, ~cmp, V, t, k), n), B.grow(V, S.find(~K, ~cmp, V, k, T.io(K, V, t)), SC.length(EE, T.io(K, V, t))), SC.length(EE, T.io(K, V, t1)),
      Equal.trans(Nat, B.grow(V, B.lookup_tree(~K, ~cmp, V, t, k), n), B.grow(V, S.find(~K, ~cmp, V, k, T.io(K, V, t)), n), B.grow(V, S.find(~K, ~cmp, V, k, T.io(K, V, t)), SC.length(EE, T.io(K, V, t))),
        Equal.cong(Maybe<&2, V>, Nat, m => B.grow(V, m, n), B.lookup_tree(~K, ~cmp, V, t, k), S.find(~K, ~cmp, V, k, T.io(K, V, t)), lookup_ok(~K, ~cmp, ~o, V, t, k, s)),
        Equal.cong(Nat, Nat, x => B.grow(V, S.find(~K, ~cmp, V, k, T.io(K, V, t)), x), n, SC.length(EE, T.io(K, V, t)), inv_n(~K, ~cmp, V, n, t, g))),
      Equal.sym(Nat, SC.length(EE, T.io(K, V, t1)), B.grow(V, S.find(~K, ~cmp, V, k, T.io(K, V, t)), SC.length(EE, T.io(K, V, t))),
        Equal.trans(Nat, SC.length(EE, T.io(K, V, t1)), SC.length(EE, S.ins(~K, ~cmp, V, k, v, T.io(K, V, t))), B.grow(V, S.find(~K, ~cmp, V, k, T.io(K, V, t)), SC.length(EE, T.io(K, V, t))),
          Equal.cong(List<&2, EE>, Nat, xs => SC.length(EE, xs), T.io(K, V, t1), S.ins(~K, ~cmp, V, k, v, T.io(K, V, t)), ei),
          SP.len_ins(~K, ~cmp, ~o, V, T.io(K, V, t), k, v, s)))))

def remove_ok(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +n: Nat, +t: B.Tree<K, V>, +k: K, m: Maybe<&2, V>, +em: {B.lookup_tree(~K, ~cmp, V, t, k) == m : Maybe<&2, V>}, +g: {inv(~K, ~cmp, V, B.BST{n, t}) == True{} : Bool}) -> StepOK(~K, ~cmp, V, B.BST{n, t}, E.Remove{k}):
  match m:
    case None{}:
      %Equal.sym(B.OrdMap<K, V> & Result<&2, &2, E.Error, V>, B.remove(~K, ~cmp, V, B.BST{n, t}, k), B.remove_at(~K, ~cmp, V, B.lookup_tree(~K, ~cmp, V, t, k), n, t, k), RF.same(~K, ~cmp, V, n, t, k)) : {view1(~K, ~cmp, V, B.obs_val(K, V, _)) == S.step(~K, ~cmp, V, T.io(K, V, t), E.Remove{k}) : List<&2, E.Entry<K, V>> & E.Obs<K, V>} & {inv(~K, ~cmp, V, Pair.fst(B.OrdMap<K, V>, E.Obs<K, V>, B.obs_val(K, V, _))) == True{} : Bool}
      -EE = E.Entry<K, V>
      +s = inv_s(~K, ~cmp, V, n, t, g)
      +ef = Equal.trans(Maybe<&2, V>, S.find(~K, ~cmp, V, k, T.io(K, V, t)), B.lookup_tree(~K, ~cmp, V, t, k), None{}, Equal.sym(Maybe<&2, V>, B.lookup_tree(~K, ~cmp, V, t, k), S.find(~K, ~cmp, V, k, T.io(K, V, t)), lookup_ok(~K, ~cmp, ~o, V, t, k, s)), em)
      %Equal.sym(Maybe<&2, V>, B.lookup_tree(~K, ~cmp, V, t, k), None{}, em) : {view1(~K, ~cmp, V, B.obs_val(K, V, B.remove_at(~K, ~cmp, V, _, n, t, k))) == S.remove_at(~K, ~cmp, V, S.find(~K, ~cmp, V, k, T.io(K, V, t)), k, T.io(K, V, t)) : List<&2, EE> & E.Obs<K, V>} & {inv(~K, ~cmp, V, Pair.fst(B.OrdMap<K, V>, E.Obs<K, V>, B.obs_val(K, V, B.remove_at(~K, ~cmp, V, _, n, t, k)))) == True{} : Bool}
      %Equal.sym(Maybe<&2, V>, S.find(~K, ~cmp, V, k, T.io(K, V, t)), None{}, ef) : {view1(~K, ~cmp, V, B.obs_val(K, V, B.remove_at(~K, ~cmp, V, None{}, n, t, k))) == S.remove_at(~K, ~cmp, V, _, k, T.io(K, V, t)) : List<&2, EE> & E.Obs<K, V>} & {inv(~K, ~cmp, V, Pair.fst(B.OrdMap<K, V>, E.Obs<K, V>, B.obs_val(K, V, B.remove_at(~K, ~cmp, V, None{}, n, t, k)))) == True{} : Bool}
      ({==}, g)
    case Some{+w}:
      %Equal.sym(B.OrdMap<K, V> & Result<&2, &2, E.Error, V>, B.remove(~K, ~cmp, V, B.BST{n, t}, k), B.remove_at(~K, ~cmp, V, B.lookup_tree(~K, ~cmp, V, t, k), n, t, k), RF.same(~K, ~cmp, V, n, t, k)) : {view1(~K, ~cmp, V, B.obs_val(K, V, _)) == S.step(~K, ~cmp, V, T.io(K, V, t), E.Remove{k}) : List<&2, E.Entry<K, V>> & E.Obs<K, V>} & {inv(~K, ~cmp, V, Pair.fst(B.OrdMap<K, V>, E.Obs<K, V>, B.obs_val(K, V, _))) == True{} : Bool}
      -EE = E.Entry<K, V>
      +s = inv_s(~K, ~cmp, V, n, t, g)
      +ef = Equal.trans(Maybe<&2, V>, S.find(~K, ~cmp, V, k, T.io(K, V, t)), B.lookup_tree(~K, ~cmp, V, t, k), Some{w}, Equal.sym(Maybe<&2, V>, B.lookup_tree(~K, ~cmp, V, t, k), S.find(~K, ~cmp, V, k, T.io(K, V, t)), lookup_ok(~K, ~cmp, ~o, V, t, k, s)), em)
      +t1 = B.remove_tree(~K, ~cmp, V, t, k)
      +er = T.remove_io(~K, ~cmp, ~o, V, t, k, s)
      +ld = SP.len_del(~K, ~cmp, ~o, V, T.io(K, V, t), k, w, s, ef)
      %Equal.sym(Maybe<&2, V>, B.lookup_tree(~K, ~cmp, V, t, k), Some{w}, em) : {view1(~K, ~cmp, V, B.obs_val(K, V, B.remove_at(~K, ~cmp, V, _, n, t, k))) == S.remove_at(~K, ~cmp, V, S.find(~K, ~cmp, V, k, T.io(K, V, t)), k, T.io(K, V, t)) : List<&2, EE> & E.Obs<K, V>} & {inv(~K, ~cmp, V, Pair.fst(B.OrdMap<K, V>, E.Obs<K, V>, B.obs_val(K, V, B.remove_at(~K, ~cmp, V, _, n, t, k)))) == True{} : Bool}
      %Equal.sym(Maybe<&2, V>, S.find(~K, ~cmp, V, k, T.io(K, V, t)), Some{w}, ef) : {view1(~K, ~cmp, V, B.obs_val(K, V, B.remove_at(~K, ~cmp, V, Some{w}, n, t, k))) == S.remove_at(~K, ~cmp, V, _, k, T.io(K, V, t)) : List<&2, EE> & E.Obs<K, V>} & {inv(~K, ~cmp, V, Pair.fst(B.OrdMap<K, V>, E.Obs<K, V>, B.obs_val(K, V, B.remove_at(~K, ~cmp, V, Some{w}, n, t, k)))) == True{} : Bool}
      (Equal.cong(List<&2, EE>, List<&2, EE> & E.Obs<K, V>, xs => (xs, E.OVal{Done{w}}), T.io(K, V, t1), S.del(~K, ~cmp, V, k, T.io(K, V, t)), er),
       inv_mk(~K, ~cmp, V, Nat.sub(n, 1n), t1,
         L.subst(List<&2, EE>, xs => {SO.sorted(~K, ~cmp, V, xs) == True{} : Bool}, S.del(~K, ~cmp, V, k, T.io(K, V, t)), T.io(K, V, t1), Equal.sym(List<&2, EE>, T.io(K, V, t1), S.del(~K, ~cmp, V, k, T.io(K, V, t)), er), SP.sorted_del(~K, ~cmp, V, T.io(K, V, t), k, s)),
         T.remove_bal(~K, ~cmp, V, t, k, inv_b(~K, ~cmp, V, n, t, g)),
         Equal.trans(Nat, Nat.sub(n, 1n), Nat.sub(1n+SC.length(EE, S.del(~K, ~cmp, V, k, T.io(K, V, t))), 1n), SC.length(EE, T.io(K, V, t1)),
           Equal.cong(Nat, Nat, x => Nat.sub(x, 1n), n, 1n+SC.length(EE, S.del(~K, ~cmp, V, k, T.io(K, V, t))), Equal.trans(Nat, n, SC.length(EE, T.io(K, V, t)), 1n+SC.length(EE, S.del(~K, ~cmp, V, k, T.io(K, V, t))), inv_n(~K, ~cmp, V, n, t, g), Equal.sym(Nat, 1n+SC.length(EE, S.del(~K, ~cmp, V, k, T.io(K, V, t))), SC.length(EE, T.io(K, V, t)), ld))),
           Equal.trans(Nat, Nat.sub(1n+SC.length(EE, S.del(~K, ~cmp, V, k, T.io(K, V, t))), 1n), SC.length(EE, S.del(~K, ~cmp, V, k, T.io(K, V, t))), SC.length(EE, T.io(K, V, t1)),
             N.sub_zero(SC.length(EE, S.del(~K, ~cmp, V, k, T.io(K, V, t)))),
             Equal.cong(List<&2, EE>, Nat, xs => SC.length(EE, xs), S.del(~K, ~cmp, V, k, T.io(K, V, t)), T.io(K, V, t1), Equal.sym(List<&2, EE>, T.io(K, V, t1), S.del(~K, ~cmp, V, k, T.io(K, V, t)), er))))))

# ---- every operation ----

def step_ok(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +s: B.OrdMap<K, V>, +op: E.Op<K, V>, +g: {inv(~K, ~cmp, V, s) == True{} : Bool}) -> StepOK(~K, ~cmp, V, s, op):
  match s op:
    case B.BST{+n, +t} E.Length{}:
      (%inv_n(~K, ~cmp, V, n, t, g) : {(T.io(K, V, t), E.ONat{n}) == (T.io(K, V, t), E.ONat{_}) : List<&2, E.Entry<K, V>> & E.Obs<K, V>}
       {==}, g)
    case B.BST{+n, +t} E.Insert{+k, +v}:
      (%Equal.sym(B.OrdMap<K, V>, B.insert(~K, ~cmp, V, B.BST{n, t}, k, v), B.BST{B.grow(V, B.lookup_tree(~K, ~cmp, V, t, k), n), B.insert_tree(~K, ~cmp, V, t, k, v)}, F.same(~K, ~cmp, V, n, t, k, v)) : {(abs(~K, ~cmp, V, _), E.OUnit{}) == S.step(~K, ~cmp, V, T.io(K, V, t), E.Insert{k, v}) : List<&2, E.Entry<K, V>> & E.Obs<K, V>}
       Equal.cong(List<&2, E.Entry<K, V>>, List<&2, E.Entry<K, V>> & E.Obs<K, V>, xs => (xs, E.OUnit{}), T.io(K, V, B.insert_tree(~K, ~cmp, V, t, k, v)), S.ins(~K, ~cmp, V, k, v, T.io(K, V, t)), T.insert_io(~K, ~cmp, ~o, V, t, k, v, inv_s(~K, ~cmp, V, n, t, g))),
       insert_inv(~K, ~cmp, ~o, V, n, t, k, v, g))
    case B.BST{+n, +t} E.Remove{+k}:
      remove_ok(~K, ~cmp, ~o, V, n, t, k, B.lookup_tree(~K, ~cmp, V, t, k), {==}, g)
    case B.BST{+n, +t} E.Lookup{+k}:
      (Equal.cong(Result<&2, &2, E.Error, V>, List<&2, E.Entry<K, V>> & E.Obs<K, V>, x => (T.io(K, V, t), E.OVal{x}), B.result(V, B.lookup_tree(~K, ~cmp, V, t, k)), S.value(V, S.find(~K, ~cmp, V, k, T.io(K, V, t))),
         Equal.trans(Result<&2, &2, E.Error, V>, B.result(V, B.lookup_tree(~K, ~cmp, V, t, k)), S.value(V, B.lookup_tree(~K, ~cmp, V, t, k)), S.value(V, S.find(~K, ~cmp, V, k, T.io(K, V, t))),
           result_value(V, B.lookup_tree(~K, ~cmp, V, t, k)),
           Equal.cong(Maybe<&2, V>, Result<&2, &2, E.Error, V>, z => S.value(V, z), B.lookup_tree(~K, ~cmp, V, t, k), S.find(~K, ~cmp, V, k, T.io(K, V, t)), lookup_ok(~K, ~cmp, ~o, V, t, k, inv_s(~K, ~cmp, V, n, t, g))))),
       g)
    case B.BST{+n, +t} E.Contains{+k}:
      (Equal.cong(Bool, List<&2, E.Entry<K, V>> & E.Obs<K, V>, x => (T.io(K, V, t), E.OBool{x}), B.present(V, B.lookup_tree(~K, ~cmp, V, t, k)), S.is_some(V, S.find(~K, ~cmp, V, k, T.io(K, V, t))),
         Equal.trans(Bool, B.present(V, B.lookup_tree(~K, ~cmp, V, t, k)), S.is_some(V, B.lookup_tree(~K, ~cmp, V, t, k)), S.is_some(V, S.find(~K, ~cmp, V, k, T.io(K, V, t))),
           present_some(V, B.lookup_tree(~K, ~cmp, V, t, k)),
           Equal.cong(Maybe<&2, V>, Bool, z => S.is_some(V, z), B.lookup_tree(~K, ~cmp, V, t, k), S.find(~K, ~cmp, V, k, T.io(K, V, t)), lookup_ok(~K, ~cmp, ~o, V, t, k, inv_s(~K, ~cmp, V, n, t, g))))),
       g)
    case B.BST{+n, +t} E.Min{}:
      -R = Result<&2, &2, E.Error, E.Entry<K, V>>
      (Equal.cong(R, List<&2, E.Entry<K, V>> & E.Obs<K, V>, x => (T.io(K, V, t), E.OEntry{x}), B.entry(K, V, B.min_go(K, V, t), E.EmptyTree{}), S.entry(K, V, SC.head(E.Entry<K, V>, T.io(K, V, t)), E.EmptyTree{}),
         Equal.trans(R, B.entry(K, V, B.min_go(K, V, t), E.EmptyTree{}), S.entry(K, V, B.min_go(K, V, t), E.EmptyTree{}), S.entry(K, V, SC.head(E.Entry<K, V>, T.io(K, V, t)), E.EmptyTree{}),
           entry_eq(K, V, B.min_go(K, V, t), E.EmptyTree{}),
           Equal.cong(Maybe<&2, E.Entry<K, V>>, R, z => S.entry(K, V, z, E.EmptyTree{}), B.min_go(K, V, t), SC.head(E.Entry<K, V>, T.io(K, V, t)), Q.min_ok(K, V, t)))),
       g)
    case B.BST{+n, +t} E.Max{}:
      -R = Result<&2, &2, E.Error, E.Entry<K, V>>
      (Equal.cong(R, List<&2, E.Entry<K, V>> & E.Obs<K, V>, x => (T.io(K, V, t), E.OEntry{x}), B.entry(K, V, B.max_go(K, V, t), E.EmptyTree{}), S.entry(K, V, SC.last(E.Entry<K, V>, T.io(K, V, t)), E.EmptyTree{}),
         Equal.trans(R, B.entry(K, V, B.max_go(K, V, t), E.EmptyTree{}), S.entry(K, V, B.max_go(K, V, t), E.EmptyTree{}), S.entry(K, V, SC.last(E.Entry<K, V>, T.io(K, V, t)), E.EmptyTree{}),
           entry_eq(K, V, B.max_go(K, V, t), E.EmptyTree{}),
           Equal.cong(Maybe<&2, E.Entry<K, V>>, R, z => S.entry(K, V, z, E.EmptyTree{}), B.max_go(K, V, t), SC.last(E.Entry<K, V>, T.io(K, V, t)), Q.max_ok(K, V, t)))),
       g)
    case B.BST{+n, +t} E.LowerBound{+k}:
      -R = Result<&2, &2, E.Error, E.Entry<K, V>>
      (Equal.cong(R, List<&2, E.Entry<K, V>> & E.Obs<K, V>, x => (T.io(K, V, t), E.OEntry{x}), B.entry(K, V, B.lower_tree(~K, ~cmp, V, t, k), E.KeyNotFound{}), S.entry(K, V, S.lower(~K, ~cmp, V, k, T.io(K, V, t)), E.KeyNotFound{}),
         Equal.trans(R, B.entry(K, V, B.lower_tree(~K, ~cmp, V, t, k), E.KeyNotFound{}), S.entry(K, V, B.lower_tree(~K, ~cmp, V, t, k), E.KeyNotFound{}), S.entry(K, V, S.lower(~K, ~cmp, V, k, T.io(K, V, t)), E.KeyNotFound{}),
           entry_eq(K, V, B.lower_tree(~K, ~cmp, V, t, k), E.KeyNotFound{}),
           Equal.cong(Maybe<&2, E.Entry<K, V>>, R, z => S.entry(K, V, z, E.KeyNotFound{}), B.lower_tree(~K, ~cmp, V, t, k), S.lower(~K, ~cmp, V, k, T.io(K, V, t)), Q.lb_ok(~K, ~cmp, ~o, V, t, k, B.d1(~K, ~cmp, V, k, t), {==}, inv_s(~K, ~cmp, V, n, t, g))))),
       g)
    case B.BST{+n, +t} E.Range{+lo, +hi}:
      (Equal.cong(List<&2, E.Entry<K, V>>, List<&2, E.Entry<K, V>> & E.Obs<K, V>, x => (T.io(K, V, t), E.OList{x}), B.rng(~K, ~cmp, V, t, lo, hi, Nil{}, True{}), S.range(~K, ~cmp, V, lo, hi, T.io(K, V, t)), Q.range_ok(~K, ~cmp, ~o, V, t, lo, hi, inv_s(~K, ~cmp, V, n, t, g))),
       g)
    case B.BST{+n, +t} E.ToList{}:
      (Equal.cong(List<&2, E.Entry<K, V>>, List<&2, E.Entry<K, V>> & E.Obs<K, V>, x => (T.io(K, V, t), E.OList{x}), B.entries(K, V, t, Nil{}), T.io(K, V, t),
         Equal.trans(List<&2, E.Entry<K, V>>, B.entries(K, V, t, Nil{}), SC.append(E.Entry<K, V>, T.io(K, V, t), Nil{}), T.io(K, V, t), Q.entries_ok(K, V, t, Nil{}), LL.append_nil(E.Entry<K, V>, T.io(K, V, t)))),
       g)
