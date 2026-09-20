import Base
import ../lib/logic.bend as L
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../../spec/common.bend as SC
import ../../spec/binary_heap.bend as S
import ../../src/binary_heap.bend as H
import ./multiset.bend as M

# Heap trees: abstraction (the sorted multiset of all node values), heap
# order, and element bounds. Templates over (~A, ~cmp, ~o).

# Insert every node value into acc (pre-order).
def ab(~A: Data, ~cmp: A -> A -> Cmp, t: H.Tree<A>, acc: List<&2, A>) -> List<&2, A>:
  match t:
    case H.Leaf{}:
      acc
    case H.Node{x, l, r}:
      S.ins(~A, ~cmp, x, ab(~A, ~cmp, l, ab(~A, ~cmp, r, acc)))

# Every element of t is >= z.
def allt(~A: Data, ~cmp: A -> A -> Cmp, +z: A, t: H.Tree<A>) -> Bool:
  match t:
    case H.Leaf{}:
      True{}
    case H.Node{x, l, r}:
      Bool.and(S.le(~A, ~cmp, z, x), Bool.and(allt(~A, ~cmp, z, l), allt(~A, ~cmp, z, r)))

# Heap order: every node is <= every element below it.
def ho(~A: Data, ~cmp: A -> A -> Cmp, t: H.Tree<A>) -> Bool:
  match t:
    case H.Leaf{}:
      True{}
    case H.Node{+x, +l, +r}:
      Bool.and(allt(~A, ~cmp, x, l), Bool.and(allt(~A, ~cmp, x, r), Bool.and(ho(~A, ~cmp, l), ho(~A, ~cmp, r))))

# ---- Bool reshuffles ----

def and_assoc4(+a: Bool, +b: Bool, +c: Bool, +d: Bool) -> {Bool.and(Bool.and(a, Bool.and(b, c)), d) == Bool.and(a, Bool.and(b, Bool.and(c, d))) : Bool}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} _:
      {==}
    case False{} _ _:
      {==}

def and_true_r(+a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# ---- abstraction algebra ----

def ab_ins(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +t: H.Tree<A>, +x: A, +s: List<&2, A>) -> {ab(~A, ~cmp, t, S.ins(~A, ~cmp, x, s)) == S.ins(~A, ~cmp, x, ab(~A, ~cmp, t, s)) : List<&2, A>}:
  match t:
    case H.Leaf{}:
      {==}
    case H.Node{+y, +l, +r}:
      %Equal.sym(List<&2, A>, ab(~A, ~cmp, r, S.ins(~A, ~cmp, x, s)), S.ins(~A, ~cmp, x, ab(~A, ~cmp, r, s)), ab_ins(~A, ~cmp, ~o, r, x, s)) : {S.ins(~A, ~cmp, y, ab(~A, ~cmp, l, _)) == S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, ab(~A, ~cmp, l, ab(~A, ~cmp, r, s)))) : List<&2, A>}
      %Equal.sym(List<&2, A>, ab(~A, ~cmp, l, S.ins(~A, ~cmp, x, ab(~A, ~cmp, r, s))), S.ins(~A, ~cmp, x, ab(~A, ~cmp, l, ab(~A, ~cmp, r, s))), ab_ins(~A, ~cmp, ~o, l, x, ab(~A, ~cmp, r, s))) : {S.ins(~A, ~cmp, y, _) == S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, ab(~A, ~cmp, l, ab(~A, ~cmp, r, s)))) : List<&2, A>}
      M.ins_comm(~A, ~cmp, ~o, y, x, ab(~A, ~cmp, l, ab(~A, ~cmp, r, s)))

def ab_comm(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +t1: H.Tree<A>, +t2: H.Tree<A>, +s: List<&2, A>) -> {ab(~A, ~cmp, t1, ab(~A, ~cmp, t2, s)) == ab(~A, ~cmp, t2, ab(~A, ~cmp, t1, s)) : List<&2, A>}:
  match t1:
    case H.Leaf{}:
      {==}
    case H.Node{+x, +l, +r}:
      %Equal.sym(List<&2, A>, ab(~A, ~cmp, r, ab(~A, ~cmp, t2, s)), ab(~A, ~cmp, t2, ab(~A, ~cmp, r, s)), ab_comm(~A, ~cmp, ~o, r, t2, s)) : {S.ins(~A, ~cmp, x, ab(~A, ~cmp, l, _)) == ab(~A, ~cmp, t2, S.ins(~A, ~cmp, x, ab(~A, ~cmp, l, ab(~A, ~cmp, r, s)))) : List<&2, A>}
      %Equal.sym(List<&2, A>, ab(~A, ~cmp, l, ab(~A, ~cmp, t2, ab(~A, ~cmp, r, s))), ab(~A, ~cmp, t2, ab(~A, ~cmp, l, ab(~A, ~cmp, r, s))), ab_comm(~A, ~cmp, ~o, l, t2, ab(~A, ~cmp, r, s))) : {S.ins(~A, ~cmp, x, _) == ab(~A, ~cmp, t2, S.ins(~A, ~cmp, x, ab(~A, ~cmp, l, ab(~A, ~cmp, r, s)))) : List<&2, A>}
      Equal.sym(List<&2, A>, ab(~A, ~cmp, t2, S.ins(~A, ~cmp, x, ab(~A, ~cmp, l, ab(~A, ~cmp, r, s)))), S.ins(~A, ~cmp, x, ab(~A, ~cmp, t2, ab(~A, ~cmp, l, ab(~A, ~cmp, r, s)))), ab_ins(~A, ~cmp, ~o, t2, x, ab(~A, ~cmp, l, ab(~A, ~cmp, r, s))))

# Elements of ab(t, acc) are those of t and of acc.
def all_ge_ab(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +z: A, +t: H.Tree<A>, +acc: List<&2, A>) -> {M.all_ge(~A, ~cmp, z, ab(~A, ~cmp, t, acc)) == Bool.and(allt(~A, ~cmp, z, t), M.all_ge(~A, ~cmp, z, acc)) : Bool}:
  match t:
    case H.Leaf{}:
      {==}
    case H.Node{+x, +l, +r}:
      %Equal.sym(Bool, M.all_ge(~A, ~cmp, z, S.ins(~A, ~cmp, x, ab(~A, ~cmp, l, ab(~A, ~cmp, r, acc)))), Bool.and(S.le(~A, ~cmp, z, x), M.all_ge(~A, ~cmp, z, ab(~A, ~cmp, l, ab(~A, ~cmp, r, acc)))), M.all_ge_ins(~A, ~cmp, ~o, z, x, ab(~A, ~cmp, l, ab(~A, ~cmp, r, acc)))) : {_ == Bool.and(Bool.and(S.le(~A, ~cmp, z, x), Bool.and(allt(~A, ~cmp, z, l), allt(~A, ~cmp, z, r))), M.all_ge(~A, ~cmp, z, acc)) : Bool}
      %Equal.sym(Bool, M.all_ge(~A, ~cmp, z, ab(~A, ~cmp, l, ab(~A, ~cmp, r, acc))), Bool.and(allt(~A, ~cmp, z, l), M.all_ge(~A, ~cmp, z, ab(~A, ~cmp, r, acc))), all_ge_ab(~A, ~cmp, ~o, z, l, ab(~A, ~cmp, r, acc))) : {Bool.and(S.le(~A, ~cmp, z, x), _) == Bool.and(Bool.and(S.le(~A, ~cmp, z, x), Bool.and(allt(~A, ~cmp, z, l), allt(~A, ~cmp, z, r))), M.all_ge(~A, ~cmp, z, acc)) : Bool}
      %Equal.sym(Bool, M.all_ge(~A, ~cmp, z, ab(~A, ~cmp, r, acc)), Bool.and(allt(~A, ~cmp, z, r), M.all_ge(~A, ~cmp, z, acc)), all_ge_ab(~A, ~cmp, ~o, z, r, acc)) : {Bool.and(S.le(~A, ~cmp, z, x), Bool.and(allt(~A, ~cmp, z, l), _)) == Bool.and(Bool.and(S.le(~A, ~cmp, z, x), Bool.and(allt(~A, ~cmp, z, l), allt(~A, ~cmp, z, r))), M.all_ge(~A, ~cmp, z, acc)) : Bool}
      Equal.sym(Bool, Bool.and(Bool.and(S.le(~A, ~cmp, z, x), Bool.and(allt(~A, ~cmp, z, l), allt(~A, ~cmp, z, r))), M.all_ge(~A, ~cmp, z, acc)), Bool.and(S.le(~A, ~cmp, z, x), Bool.and(allt(~A, ~cmp, z, l), Bool.and(allt(~A, ~cmp, z, r), M.all_ge(~A, ~cmp, z, acc)))), and_assoc4(S.le(~A, ~cmp, z, x), allt(~A, ~cmp, z, l), allt(~A, ~cmp, z, r), M.all_ge(~A, ~cmp, z, acc)))

# allt through the abstraction.
def allt_ab(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +z: A, +t: H.Tree<A>) -> {allt(~A, ~cmp, z, t) == M.all_ge(~A, ~cmp, z, ab(~A, ~cmp, t, Nil{})) : Bool}:
  Equal.sym(Bool, M.all_ge(~A, ~cmp, z, ab(~A, ~cmp, t, Nil{})), allt(~A, ~cmp, z, t), Equal.trans(Bool, M.all_ge(~A, ~cmp, z, ab(~A, ~cmp, t, Nil{})), Bool.and(allt(~A, ~cmp, z, t), True{}), allt(~A, ~cmp, z, t), all_ge_ab(~A, ~cmp, ~o, z, t, Nil{}), and_true_r(allt(~A, ~cmp, z, t))))

def allt_mono(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +a: A, +b: A, +t: H.Tree<A>, +hab: {S.le(~A, ~cmp, a, b) == True{} : Bool}, +hb: {allt(~A, ~cmp, b, t) == True{} : Bool}) -> {allt(~A, ~cmp, a, t) == True{} : Bool}:
  match t:
    case H.Leaf{}:
      {==}
    case H.Node{+x, +l, +r}:
      L.and_intro(S.le(~A, ~cmp, a, x), Bool.and(allt(~A, ~cmp, a, l), allt(~A, ~cmp, a, r)),
        O.trans(~A, ~cmp, o, a, b, x, hab, L.and_left(S.le(~A, ~cmp, b, x), Bool.and(allt(~A, ~cmp, b, l), allt(~A, ~cmp, b, r)), hb)),
        L.and_intro(allt(~A, ~cmp, a, l), allt(~A, ~cmp, a, r),
          allt_mono(~A, ~cmp, ~o, a, b, l, hab, L.and_left(allt(~A, ~cmp, b, l), allt(~A, ~cmp, b, r), L.and_right(S.le(~A, ~cmp, b, x), Bool.and(allt(~A, ~cmp, b, l), allt(~A, ~cmp, b, r)), hb))),
          allt_mono(~A, ~cmp, ~o, a, b, r, hab, L.and_right(allt(~A, ~cmp, b, l), allt(~A, ~cmp, b, r), L.and_right(S.le(~A, ~cmp, b, x), Bool.and(allt(~A, ~cmp, b, l), allt(~A, ~cmp, b, r)), hb)))))

# ---- projections of ho ----

def ho_l(~A: Data, ~cmp: A -> A -> Cmp, +x: A, +l: H.Tree<A>, +r: H.Tree<A>, +h: {ho(~A, ~cmp, H.Node{x, l, r}) == True{} : Bool}) -> {allt(~A, ~cmp, x, l) == True{} : Bool}:
  L.and_left(allt(~A, ~cmp, x, l), Bool.and(allt(~A, ~cmp, x, r), Bool.and(ho(~A, ~cmp, l), ho(~A, ~cmp, r))), h)

def ho_rest(~A: Data, ~cmp: A -> A -> Cmp, +x: A, +l: H.Tree<A>, +r: H.Tree<A>, +h: {ho(~A, ~cmp, H.Node{x, l, r}) == True{} : Bool}) -> {Bool.and(allt(~A, ~cmp, x, r), Bool.and(ho(~A, ~cmp, l), ho(~A, ~cmp, r))) == True{} : Bool}:
  L.and_right(allt(~A, ~cmp, x, l), Bool.and(allt(~A, ~cmp, x, r), Bool.and(ho(~A, ~cmp, l), ho(~A, ~cmp, r))), h)

def ho_r(~A: Data, ~cmp: A -> A -> Cmp, +x: A, +l: H.Tree<A>, +r: H.Tree<A>, +h: {ho(~A, ~cmp, H.Node{x, l, r}) == True{} : Bool}) -> {allt(~A, ~cmp, x, r) == True{} : Bool}:
  L.and_left(allt(~A, ~cmp, x, r), Bool.and(ho(~A, ~cmp, l), ho(~A, ~cmp, r)), ho_rest(~A, ~cmp, x, l, r, h))

def ho_hl(~A: Data, ~cmp: A -> A -> Cmp, +x: A, +l: H.Tree<A>, +r: H.Tree<A>, +h: {ho(~A, ~cmp, H.Node{x, l, r}) == True{} : Bool}) -> {ho(~A, ~cmp, l) == True{} : Bool}:
  L.and_left(ho(~A, ~cmp, l), ho(~A, ~cmp, r), L.and_right(allt(~A, ~cmp, x, r), Bool.and(ho(~A, ~cmp, l), ho(~A, ~cmp, r)), ho_rest(~A, ~cmp, x, l, r, h)))

def ho_hr(~A: Data, ~cmp: A -> A -> Cmp, +x: A, +l: H.Tree<A>, +r: H.Tree<A>, +h: {ho(~A, ~cmp, H.Node{x, l, r}) == True{} : Bool}) -> {ho(~A, ~cmp, r) == True{} : Bool}:
  L.and_right(ho(~A, ~cmp, l), ho(~A, ~cmp, r), L.and_right(allt(~A, ~cmp, x, r), Bool.and(ho(~A, ~cmp, l), ho(~A, ~cmp, r)), ho_rest(~A, ~cmp, x, l, r, h)))

def ho_mk(~A: Data, ~cmp: A -> A -> Cmp, +x: A, +l: H.Tree<A>, +r: H.Tree<A>, +a: {allt(~A, ~cmp, x, l) == True{} : Bool}, +b: {allt(~A, ~cmp, x, r) == True{} : Bool}, +c: {ho(~A, ~cmp, l) == True{} : Bool}, +d: {ho(~A, ~cmp, r) == True{} : Bool}) -> {ho(~A, ~cmp, H.Node{x, l, r}) == True{} : Bool}:
  L.and_intro(allt(~A, ~cmp, x, l), Bool.and(allt(~A, ~cmp, x, r), Bool.and(ho(~A, ~cmp, l), ho(~A, ~cmp, r))), a,
    L.and_intro(allt(~A, ~cmp, x, r), Bool.and(ho(~A, ~cmp, l), ho(~A, ~cmp, r)), b, L.and_intro(ho(~A, ~cmp, l), ho(~A, ~cmp, r), c, d)))

# A heap-ordered node is >= its root: the root bounds the whole node.
def ho_self(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +x: A, +l: H.Tree<A>, +r: H.Tree<A>, +h: {ho(~A, ~cmp, H.Node{x, l, r}) == True{} : Bool}) -> {allt(~A, ~cmp, x, H.Node{x, l, r}) == True{} : Bool}:
  L.and_intro(S.le(~A, ~cmp, x, x), Bool.and(allt(~A, ~cmp, x, l), allt(~A, ~cmp, x, r)), O.le_refl(~A, ~cmp, ~o, x), L.and_intro(allt(~A, ~cmp, x, l), allt(~A, ~cmp, x, r), ho_l(~A, ~cmp, x, l, r, h), ho_r(~A, ~cmp, x, l, r, h)))
