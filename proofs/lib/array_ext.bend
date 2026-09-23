import Base
import ./logic.bend as L
import ./nat.bend as N
import ./list.bend as LL
import ./array.bend as AR
import ./spec_common.bend as SC

# Two perfect mirror trees of the same depth with the same slot lists are
# the same tree (the slots determine a perfect tree).

def take_len(-A: Data, +xs: List<&2, A>) -> {SC.take(A, xs, SC.length(A, xs)) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      LL.cons_cong(A, h, SC.take(A, t, SC.length(A, t)), t, take_len(A, t))

def drop_zero(-A: Data, +xs: List<&2, A>) -> {SC.drop(A, xs, 0n) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def take_app_len(-A: Data, +xs: List<&2, A>, +ys: List<&2, A>) -> {SC.take(A, SC.append(A, xs, ys), SC.length(A, xs)) == xs : List<&2, A>}:
  Equal.trans(List<&2, A>, SC.take(A, SC.append(A, xs, ys), SC.length(A, xs)), SC.take(A, xs, SC.length(A, xs)), xs, LL.sc_take_append_left(A, xs, ys, SC.length(A, xs), N.le_refl(SC.length(A, xs))), take_len(A, xs))

def drop_app_len(-A: Data, +xs: List<&2, A>, +ys: List<&2, A>) -> {SC.drop(A, SC.append(A, xs, ys), SC.length(A, xs)) == ys : List<&2, A>}:
  match xs:
    case Nil{}:
      drop_zero(A, ys)
    case Con{+h, +t}:
      drop_app_len(A, t, ys)

def split_eq(-A: Data, +a1: List<&2, A>, +b1: List<&2, A>, +a2: List<&2, A>, +b2: List<&2, A>, +el: {SC.length(A, a1) == SC.length(A, a2) : Nat}, +e: {SC.append(A, a1, b1) == SC.append(A, a2, b2) : List<&2, A>}) -> {a1 == a2 : List<&2, A>}:
  +t1 = Equal.trans(List<&2, A>, a1, SC.take(A, SC.append(A, a1, b1), SC.length(A, a1)), SC.take(A, SC.append(A, a2, b2), SC.length(A, a1)), Equal.sym(List<&2, A>, SC.take(A, SC.append(A, a1, b1), SC.length(A, a1)), a1, take_app_len(A, a1, b1)), Equal.cong(List<&2, A>, List<&2, A>, z => SC.take(A, z, SC.length(A, a1)), SC.append(A, a1, b1), SC.append(A, a2, b2), e))
  Equal.trans(List<&2, A>, a1, SC.take(A, SC.append(A, a2, b2), SC.length(A, a1)), a2, t1, L.subst(Nat, z => {SC.take(A, SC.append(A, a2, b2), z) == a2 : List<&2, A>}, SC.length(A, a2), SC.length(A, a1), Equal.sym(Nat, SC.length(A, a1), SC.length(A, a2), el), take_app_len(A, a2, b2)))

def split_eq_r(-A: Data, +a1: List<&2, A>, +b1: List<&2, A>, +a2: List<&2, A>, +b2: List<&2, A>, +el: {SC.length(A, a1) == SC.length(A, a2) : Nat}, +e: {SC.append(A, a1, b1) == SC.append(A, a2, b2) : List<&2, A>}) -> {b1 == b2 : List<&2, A>}:
  +t1 = Equal.trans(List<&2, A>, b1, SC.drop(A, SC.append(A, a1, b1), SC.length(A, a1)), SC.drop(A, SC.append(A, a2, b2), SC.length(A, a1)), Equal.sym(List<&2, A>, SC.drop(A, SC.append(A, a1, b1), SC.length(A, a1)), b1, drop_app_len(A, a1, b1)), Equal.cong(List<&2, A>, List<&2, A>, z => SC.drop(A, z, SC.length(A, a1)), SC.append(A, a1, b1), SC.append(A, a2, b2), e))
  Equal.trans(List<&2, A>, b1, SC.drop(A, SC.append(A, a2, b2), SC.length(A, a1)), b2, t1, L.subst(Nat, z => {SC.drop(A, SC.append(A, a2, b2), z) == b2 : List<&2, A>}, SC.length(A, a2), SC.length(A, a1), Equal.sym(Nat, SC.length(A, a1), SC.length(A, a2), el), drop_app_len(A, a2, b2)))

def head_of(-A: Data, xs: List<&2, A>, +d: A) -> A:
  match xs:
    case Nil{}:
      d
    case Con{h, t}:
      h

def tree_ext(-A: Data, +d: Nat, +u: AR.Tree<A>, +v: AR.Tree<A>, +pu: {AR.perfect(A, d, u) == True{} : Bool}, +pv: {AR.perfect(A, d, v) == True{} : Bool}, +e: {AR.slots(A, u) == AR.slots(A, v) : List<&2, A>}) -> {u == v : AR.Tree<A>}:
  match d u v:
    case 0n AR.TLeaf{+x} AR.TLeaf{+y}:
      Equal.cong(A, AR.Tree<A>, z => AR.TLeaf{z}, x, y, Equal.cong(List<&2, A>, A, z => head_of(A, z, x), Con{x, Nil{}}, Con{y, Nil{}}, e))
    case 0n AR.TLeaf{x} AR.TNode{l, r}:
      Empty.absurd({AR.TLeaf{x} == AR.TNode{l, r} : AR.Tree<A>}, L.false_true(pv))
    case 0n AR.TNode{l, r} _:
      Empty.absurd({AR.TNode{l, r} == v : AR.Tree<A>}, L.false_true(pu))
    case 1n+p AR.TLeaf{x} _:
      Empty.absurd({AR.TLeaf{x} == v : AR.Tree<A>}, L.false_true(pu))
    case 1n+p AR.TNode{l, r} AR.TLeaf{y}:
      Empty.absurd({AR.TNode{l, r} == AR.TLeaf{y} : AR.Tree<A>}, L.false_true(pv))
    case 1n+ +p AR.TNode{+l1, +r1} AR.TNode{+l2, +r2}:
      +pl1 = AR.pf_left(A, p, l1, r1, pu)
      +pr1 = AR.pf_right(A, p, l1, r1, pu)
      +pl2 = AR.pf_left(A, p, l2, r2, pv)
      +pr2 = AR.pf_right(A, p, l2, r2, pv)
      +el = Equal.trans(Nat, SC.length(A, AR.slots(A, l1)), SC.pow2(p), SC.length(A, AR.slots(A, l2)), AR.slots_length(A, p, l1, pl1), Equal.sym(Nat, SC.length(A, AR.slots(A, l2)), SC.pow2(p), AR.slots_length(A, p, l2, pl2)))
      +el2 = tree_ext(A, p, l1, l2, pl1, pl2, split_eq(A, AR.slots(A, l1), AR.slots(A, r1), AR.slots(A, l2), AR.slots(A, r2), el, e))
      +er2 = tree_ext(A, p, r1, r2, pr1, pr2, split_eq_r(A, AR.slots(A, l1), AR.slots(A, r1), AR.slots(A, l2), AR.slots(A, r2), el, e))
      %Equal.sym(AR.Tree<A>, l1, l2, el2) : {AR.TNode{_, r1} == AR.TNode{l2, r2} : AR.Tree<A>}
      %Equal.sym(AR.Tree<A>, r1, r2, er2) : {AR.TNode{l2, _} == AR.TNode{l2, r2} : AR.Tree<A>}
      {==}
