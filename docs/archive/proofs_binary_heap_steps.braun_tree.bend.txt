import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../../spec/common.bend as SC
import ../../spec/binary_heap.bend as S
import ../../src/binary_heap.bend as H
import ../../types/binary_heap.bend as E
import ./multiset.bend as M
import ./tree.bend as TR
import ./ops.bend as OP

# Heap state: abstraction, invariant and every public operation.

def abs(~A: Data, ~cmp: A -> A -> Cmp, h: H.Heap<A>) -> List<&2, A>:
  match h:
    case H.BH{n, t}:
      TR.ab(~A, ~cmp, t, Nil{})

# Invariant: the cached size is the element count, and the tree is heap-ordered.
def inv(~A: Data, ~cmp: A -> A -> Cmp, h: H.Heap<A>) -> Bool:
  match h:
    case H.BH{+n, +t}:
      Bool.and(Nat.is_eq(n, SC.length(A, TR.ab(~A, ~cmp, t, Nil{}))), TR.ho(~A, ~cmp, t))

def view1(~A: Data, ~cmp: A -> A -> Cmp, r: H.Heap<A> & E.Obs<A>) -> List<&2, A> & E.Obs<A>:
  match r:
    case Tuple{h, o}:
      (abs(~A, ~cmp, h), o)

def StepOK(~A: Data, ~cmp: A -> A -> Cmp, h: H.Heap<A>, op: E.Op<A>) -> Type:
  {view1(~A, ~cmp, H.step(~A, ~cmp, h, op)) == S.step(~A, ~cmp, abs(~A, ~cmp, h), op) : List<&2, A> & E.Obs<A>} & {inv(~A, ~cmp, Pair.fst(H.Heap<A>, E.Obs<A>, H.step(~A, ~cmp, h, op))) == True{} : Bool}

def inv_n(~A: Data, ~cmp: A -> A -> Cmp, +n: Nat, +t: H.Tree<A>, +g: {inv(~A, ~cmp, H.BH{n, t}) == True{} : Bool}) -> {n == SC.length(A, TR.ab(~A, ~cmp, t, Nil{})) : Nat}:
  N.eq_from_is_eq(n, SC.length(A, TR.ab(~A, ~cmp, t, Nil{})), L.and_left(Nat.is_eq(n, SC.length(A, TR.ab(~A, ~cmp, t, Nil{}))), TR.ho(~A, ~cmp, t), g))

def inv_ho(~A: Data, ~cmp: A -> A -> Cmp, +n: Nat, +t: H.Tree<A>, +g: {inv(~A, ~cmp, H.BH{n, t}) == True{} : Bool}) -> {TR.ho(~A, ~cmp, t) == True{} : Bool}:
  L.and_right(Nat.is_eq(n, SC.length(A, TR.ab(~A, ~cmp, t, Nil{}))), TR.ho(~A, ~cmp, t), g)

def inv_mk(~A: Data, ~cmp: A -> A -> Cmp, +n: Nat, +t: H.Tree<A>, +en: {n == SC.length(A, TR.ab(~A, ~cmp, t, Nil{})) : Nat}, +h: {TR.ho(~A, ~cmp, t) == True{} : Bool}) -> {inv(~A, ~cmp, H.BH{n, t}) == True{} : Bool}:
  L.and_intro(Nat.is_eq(n, SC.length(A, TR.ab(~A, ~cmp, t, Nil{}))), TR.ho(~A, ~cmp, t), L.subst(Nat, k => {Nat.is_eq(n, k) == True{} : Bool}, n, SC.length(A, TR.ab(~A, ~cmp, t, Nil{})), en, N.is_eq_refl(n)), h)

def length_ins_c(~A: Data, ~cmp: A -> A -> Cmp, +x: A, +h: A, +t: List<&2, A>, +b: Bool, +e: {S.le(~A, ~cmp, x, h) == b : Bool}, +ih: {SC.length(A, S.ins(~A, ~cmp, x, t)) == 1n+SC.length(A, t) : Nat}) -> {SC.length(A, S.ins(~A, ~cmp, x, Con{h, t})) == 2n+SC.length(A, t) : Nat}:
  match b:
    case True{}:
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{h, t}), Con{x, Con{h, t}}, M.ins_cons(~A, ~cmp, x, h, t, True{}, e)) : {SC.length(A, _) == 2n+SC.length(A, t) : Nat}
      {==}
    case False{}:
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{h, t}), Con{h, S.ins(~A, ~cmp, x, t)}, M.ins_cons(~A, ~cmp, x, h, t, False{}, e)) : {SC.length(A, _) == 2n+SC.length(A, t) : Nat}
      N.succ_cong(SC.length(A, S.ins(~A, ~cmp, x, t)), 1n+SC.length(A, t), ih)

def length_ins(~A: Data, ~cmp: A -> A -> Cmp, +x: A, +xs: List<&2, A>) -> {SC.length(A, S.ins(~A, ~cmp, x, xs)) == 1n+SC.length(A, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      length_ins_c(~A, ~cmp, x, h, t, S.le(~A, ~cmp, x, h), {==}, length_ins(~A, ~cmp, x, t))

# The root of a heap-ordered tree comes first in its sorted multiset.
def heap_top(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +x: A, +l: H.Tree<A>, +r: H.Tree<A>, +h: {TR.ho(~A, ~cmp, H.Node{x, l, r}) == True{} : Bool}) -> {TR.ab(~A, ~cmp, H.Node{x, l, r}, Nil{}) == Con{x, TR.ab(~A, ~cmp, l, TR.ab(~A, ~cmp, r, Nil{}))} : List<&2, A>}:
  +s = TR.ab(~A, ~cmp, l, TR.ab(~A, ~cmp, r, Nil{}))
  M.ins_min(~A, ~cmp, ~o, x, s,
    L.subst(Bool, c => {c == True{} : Bool}, Bool.and(TR.allt(~A, ~cmp, x, l), M.all_ge(~A, ~cmp, x, TR.ab(~A, ~cmp, r, Nil{}))), M.all_ge(~A, ~cmp, x, s), Equal.sym(Bool, M.all_ge(~A, ~cmp, x, s), Bool.and(TR.allt(~A, ~cmp, x, l), M.all_ge(~A, ~cmp, x, TR.ab(~A, ~cmp, r, Nil{}))), TR.all_ge_ab(~A, ~cmp, ~o, x, l, TR.ab(~A, ~cmp, r, Nil{}))),
      L.and_intro(TR.allt(~A, ~cmp, x, l), M.all_ge(~A, ~cmp, x, TR.ab(~A, ~cmp, r, Nil{})), TR.ho_l(~A, ~cmp, x, l, r, h),
        L.subst(Bool, c => {c == True{} : Bool}, TR.allt(~A, ~cmp, x, r), M.all_ge(~A, ~cmp, x, TR.ab(~A, ~cmp, r, Nil{})), TR.allt_ab(~A, ~cmp, ~o, x, r), TR.ho_r(~A, ~cmp, x, l, r, h)))))

# ---- push (also used by from_list) ----

def push_abs(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +h: H.Heap<A>, +x: A) -> {abs(~A, ~cmp, H.push(~A, ~cmp, h, x)) == S.ins(~A, ~cmp, x, abs(~A, ~cmp, h)) : List<&2, A>}:
  match h:
    case H.BH{+n, +t}:
      OP.hins_ab(~A, ~cmp, ~o, t, x, Nil{})

def push_inv(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +h: H.Heap<A>, +x: A, +g: {inv(~A, ~cmp, h) == True{} : Bool}) -> {inv(~A, ~cmp, H.push(~A, ~cmp, h, x)) == True{} : Bool}:
  match h:
    case H.BH{+n, +t}:
      inv_mk(~A, ~cmp, 1n+n, H.ins(~A, ~cmp, t, x),
        Equal.trans(Nat, 1n+n, 1n+SC.length(A, TR.ab(~A, ~cmp, t, Nil{})), SC.length(A, TR.ab(~A, ~cmp, H.ins(~A, ~cmp, t, x), Nil{})),
          N.succ_cong(n, SC.length(A, TR.ab(~A, ~cmp, t, Nil{})), inv_n(~A, ~cmp, n, t, g)),
          Equal.sym(Nat, SC.length(A, TR.ab(~A, ~cmp, H.ins(~A, ~cmp, t, x), Nil{})), 1n+SC.length(A, TR.ab(~A, ~cmp, t, Nil{})),
            %Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, H.ins(~A, ~cmp, t, x), Nil{}), S.ins(~A, ~cmp, x, TR.ab(~A, ~cmp, t, Nil{})), OP.hins_ab(~A, ~cmp, ~o, t, x, Nil{})) : {SC.length(A, _) == 1n+SC.length(A, TR.ab(~A, ~cmp, t, Nil{})) : Nat}
            length_ins(~A, ~cmp, x, TR.ab(~A, ~cmp, t, Nil{})))),
        OP.hins_ho(~A, ~cmp, ~o, t, x, inv_ho(~A, ~cmp, n, t, g)))

def from_list_ok(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ys: List<&2, A>, +h: H.Heap<A>, +g: {inv(~A, ~cmp, h) == True{} : Bool}) -> {abs(~A, ~cmp, H.from_list_go(~A, ~cmp, ys, h)) == S.from_list(~A, ~cmp, ys, abs(~A, ~cmp, h)) : List<&2, A>} & {inv(~A, ~cmp, H.from_list_go(~A, ~cmp, ys, h)) == True{} : Bool}:
  match ys:
    case Nil{}:
      ({==}, g)
    case Con{+y, +rest}:
      +h1 = H.push(~A, ~cmp, h, y)
      -P = {abs(~A, ~cmp, H.from_list_go(~A, ~cmp, rest, h1)) == S.from_list(~A, ~cmp, rest, abs(~A, ~cmp, h1)) : List<&2, A>}
      -Q = {inv(~A, ~cmp, H.from_list_go(~A, ~cmp, rest, h1)) == True{} : Bool}
      (%push_abs(~A, ~cmp, ~o, h, y) : {abs(~A, ~cmp, H.from_list_go(~A, ~cmp, rest, h1)) == S.from_list(~A, ~cmp, rest, _) : List<&2, A>}
       Pair.fst(P, Q, from_list_ok(~A, ~cmp, ~o, rest, h1, push_inv(~A, ~cmp, ~o, h, y, g))),
       Pair.snd(P, Q, from_list_ok(~A, ~cmp, ~o, rest, h1, push_inv(~A, ~cmp, ~o, h, y, g))))

# ---- to_sorted_list: draining returns the sorted multiset ----

def drain_ok(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +n: Nat, +t: H.Tree<A>, +en: {n == SC.length(A, TR.ab(~A, ~cmp, t, Nil{})) : Nat}, +h: {TR.ho(~A, ~cmp, t) == True{} : Bool}) -> {H.drain(~A, ~cmp, n, t) == TR.ab(~A, ~cmp, t, Nil{}) : List<&2, A>}:
  match n t:
    case 0n _:
      Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, t, Nil{}), Nil{}, LL.length_zero_nil(A, TR.ab(~A, ~cmp, t, Nil{}), Equal.sym(Nat, 0n, SC.length(A, TR.ab(~A, ~cmp, t, Nil{})), en)))
    case 1n+m H.Leaf{}:
      Empty.absurd({Nil{} == Nil{} : List<&2, A>}, N.succ_zero(m, en))
    case 1n+ +m H.Node{+x, +l, +r}:
      +s = TR.ab(~A, ~cmp, l, TR.ab(~A, ~cmp, r, Nil{}))
      +ht = heap_top(~A, ~cmp, ~o, x, l, r, h)
      +em = N.succ_inj(m, SC.length(A, s), Equal.trans(Nat, 1n+m, SC.length(A, TR.ab(~A, ~cmp, H.Node{x, l, r}, Nil{})), 1n+SC.length(A, s), en, Equal.cong(List<&2, A>, Nat, ys => SC.length(A, ys), TR.ab(~A, ~cmp, H.Node{x, l, r}, Nil{}), Con{x, s}, ht)))
      +ed = OP.del_ab(~A, ~cmp, ~o, l, r, Nil{})
      %Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, H.Node{x, l, r}, Nil{}), Con{x, s}, ht) : {Con{x, H.drain(~A, ~cmp, m, H.del_root(~A, ~cmp, l, r))} == _ : List<&2, A>}
      LL.cons_cong(A, x, H.drain(~A, ~cmp, m, H.del_root(~A, ~cmp, l, r)), s,
        Equal.trans(List<&2, A>, H.drain(~A, ~cmp, m, H.del_root(~A, ~cmp, l, r)), TR.ab(~A, ~cmp, H.del_root(~A, ~cmp, l, r), Nil{}), s,
          drain_ok(~A, ~cmp, ~o, m, H.del_root(~A, ~cmp, l, r),
            Equal.trans(Nat, m, SC.length(A, s), SC.length(A, TR.ab(~A, ~cmp, H.del_root(~A, ~cmp, l, r), Nil{})), em, Equal.cong(List<&2, A>, Nat, ys => SC.length(A, ys), s, TR.ab(~A, ~cmp, H.del_root(~A, ~cmp, l, r), Nil{}), Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, H.del_root(~A, ~cmp, l, r), Nil{}), s, ed))),
            OP.del_ho(~A, ~cmp, ~o, l, r, TR.ho_hl(~A, ~cmp, x, l, r, h), TR.ho_hr(~A, ~cmp, x, l, r, h))),
          ed))

# ---- every operation ----

def step_ok(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +h: H.Heap<A>, +op: E.Op<A>, +g: {inv(~A, ~cmp, h) == True{} : Bool}) -> StepOK(~A, ~cmp, h, op):
  match h op:
    case H.BH{+n, +t} E.Length{}:
      (%inv_n(~A, ~cmp, n, t, g) : {(TR.ab(~A, ~cmp, t, Nil{}), E.ONat{n}) == (TR.ab(~A, ~cmp, t, Nil{}), E.ONat{_}) : List<&2, A> & E.Obs<A>}
       {==}, g)
    case H.BH{+n, +t} E.Push{+x}:
      (Equal.cong(List<&2, A>, List<&2, A> & E.Obs<A>, xs => (xs, E.OUnit{}), TR.ab(~A, ~cmp, H.ins(~A, ~cmp, t, x), Nil{}), S.ins(~A, ~cmp, x, TR.ab(~A, ~cmp, t, Nil{})), OP.hins_ab(~A, ~cmp, ~o, t, x, Nil{})),
       push_inv(~A, ~cmp, ~o, H.BH{n, t}, x, g))
    case H.BH{+n, H.Leaf{}} E.Peek{}:
      ({==}, g)
    case H.BH{+n, H.Node{+x, +l, +r}} E.Peek{}:
      +nd = {H.Node{x, l, r} : H.Tree<A>}
      +s = TR.ab(~A, ~cmp, l, TR.ab(~A, ~cmp, r, Nil{}))
      (%Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, nd, Nil{}), Con{x, s}, heap_top(~A, ~cmp, ~o, x, l, r, inv_ho(~A, ~cmp, n, nd, g))) : {(TR.ab(~A, ~cmp, nd, Nil{}), E.OItem{Done{x}}) == (TR.ab(~A, ~cmp, nd, Nil{}), E.OItem{S.item(A, SC.head(A, _))}) : List<&2, A> & E.Obs<A>}
       {==}, g)
    case H.BH{+n, H.Leaf{}} E.Pop{}:
      ({==}, g)
    case H.BH{+n, H.Node{+x, +l, +r}} E.Pop{}:
      +nd = {H.Node{x, l, r} : H.Tree<A>}
      +s = TR.ab(~A, ~cmp, l, TR.ab(~A, ~cmp, r, Nil{}))
      +hn = inv_ho(~A, ~cmp, n, nd, g)
      +ht = heap_top(~A, ~cmp, ~o, x, l, r, hn)
      +ed = OP.del_ab(~A, ~cmp, ~o, l, r, Nil{})
      +en = Equal.trans(Nat, n, SC.length(A, TR.ab(~A, ~cmp, nd, Nil{})), 1n+SC.length(A, s), inv_n(~A, ~cmp, n, nd, g), Equal.cong(List<&2, A>, Nat, ys => SC.length(A, ys), TR.ab(~A, ~cmp, nd, Nil{}), Con{x, s}, ht))
      (%Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, nd, Nil{}), Con{x, s}, ht) : {(TR.ab(~A, ~cmp, H.del_root(~A, ~cmp, l, r), Nil{}), E.OItem{Done{x}}) == S.pop(A, _) : List<&2, A> & E.Obs<A>}
       %Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, H.del_root(~A, ~cmp, l, r), Nil{}), s, ed) : {(_, E.OItem{Done{x}}) == (s, E.OItem{Done{x}}) : List<&2, A> & E.Obs<A>}
       {==},
       inv_mk(~A, ~cmp, Nat.sub(n, 1n), H.del_root(~A, ~cmp, l, r),
         Equal.trans(Nat, Nat.sub(n, 1n), SC.length(A, s), SC.length(A, TR.ab(~A, ~cmp, H.del_root(~A, ~cmp, l, r), Nil{})),
           Equal.trans(Nat, Nat.sub(n, 1n), Nat.sub(1n+SC.length(A, s), 1n), SC.length(A, s), Equal.cong(Nat, Nat, k => Nat.sub(k, 1n), n, 1n+SC.length(A, s), en), N.sub_zero(SC.length(A, s))),
           Equal.cong(List<&2, A>, Nat, ys => SC.length(A, ys), s, TR.ab(~A, ~cmp, H.del_root(~A, ~cmp, l, r), Nil{}), Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, H.del_root(~A, ~cmp, l, r), Nil{}), s, ed))),
         OP.del_ho(~A, ~cmp, ~o, l, r, TR.ho_hl(~A, ~cmp, x, l, r, hn), TR.ho_hr(~A, ~cmp, x, l, r, hn))))
    case H.BH{+n, +t} E.FromList{+ys}:
      -P = {abs(~A, ~cmp, H.from_list_go(~A, ~cmp, ys, H.new(A))) == S.from_list(~A, ~cmp, ys, Nil{}) : List<&2, A>}
      -Q = {inv(~A, ~cmp, H.from_list_go(~A, ~cmp, ys, H.new(A))) == True{} : Bool}
      (Equal.cong(List<&2, A>, List<&2, A> & E.Obs<A>, xs => (xs, E.OUnit{}), abs(~A, ~cmp, H.from_list_go(~A, ~cmp, ys, H.new(A))), S.from_list(~A, ~cmp, ys, Nil{}), Pair.fst(P, Q, from_list_ok(~A, ~cmp, ~o, ys, H.new(A), {==}))),
       Pair.snd(P, Q, from_list_ok(~A, ~cmp, ~o, ys, H.new(A), {==})))
    case H.BH{+n, +t} E.ToSortedList{}:
      (%Equal.sym(List<&2, A>, H.drain(~A, ~cmp, n, t), TR.ab(~A, ~cmp, t, Nil{}), drain_ok(~A, ~cmp, ~o, n, t, inv_n(~A, ~cmp, n, t, g), inv_ho(~A, ~cmp, n, t, g))) : {(TR.ab(~A, ~cmp, t, Nil{}), E.OList{_}) == (TR.ab(~A, ~cmp, t, Nil{}), E.OList{TR.ab(~A, ~cmp, t, Nil{})}) : List<&2, A> & E.Obs<A>}
       {==}, g)
