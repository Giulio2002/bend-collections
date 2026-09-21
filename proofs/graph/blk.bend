import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../lib/array2.bend as A2
import ../../spec/common.bend as SC

# Tree-update identities used when an operation takes a block out of the
# adjacency array (Array.swap with a placeholder) and puts it back.

# Writing the value that is already stored changes nothing.
def tupd_self(-T: Data, +d: Nat, +t: AR.Tree<T>, +j: Nat, +x: T, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(T, d, t) == True{} : Bool}, +hx: {SC.nth(T, AR.slots(T, t), j) == Some{x} : Maybe<&2, T>}, +b: Bool, +eb: {AR.ndec(d, j) == b : Bool}) -> {AR.tupd(T, d, t, j, x, b) == t : AR.Tree<T>}:
  match d t b:
    case 0n AR.TLeaf{+y} _:
      Equal.cong(T, AR.Tree<T>, z => AR.TLeaf{z}, x, y, Equal.sym(T, y, x, AR.leaf_value(T, y, j, x, hj, hx)))
    case 0n AR.TNode{l, r} _:
      Empty.absurd({AR.tupd(T, 0n, AR.TNode{l, r}, j, x, b) == AR.TNode{l, r} : AR.Tree<T>}, L.false_true(pf))
    case 1n+p AR.TLeaf{y} _:
      Empty.absurd({AR.tupd(T, 1n+p, AR.TLeaf{y}, j, x, b) == AR.TLeaf{y} : AR.Tree<T>}, L.false_true(pf))
    case 1n+ +p AR.TNode{+l, +r} True{}:
      +pl = AR.pf_left(T, p, l, r, pf)
      +hjl = eb
      +hxl = Equal.trans(Maybe<&2, T>, SC.nth(T, AR.slots(T, l), j), SC.nth(T, SC.append(T, AR.slots(T, l), AR.slots(T, r)), j), Some{x},
        Equal.sym(Maybe<&2, T>, SC.nth(T, SC.append(T, AR.slots(T, l), AR.slots(T, r)), j), SC.nth(T, AR.slots(T, l), j), LL.nth_append_left(T, AR.slots(T, l), AR.slots(T, r), j, AR.len_lt(T, p, l, j, pl, hjl))), hx)
      %Equal.sym(AR.Tree<T>, AR.tupd(T, p, l, j, x, AR.ndec(p, j)), l, tupd_self(T, p, l, j, x, hjl, pl, hxl, AR.ndec(p, j), {==})) : {AR.TNode{_, r} == AR.TNode{l, r} : AR.Tree<T>}
      {==}
    case 1n+ +p AR.TNode{+l, +r} False{}:
      +pl = AR.pf_left(T, p, l, r, pf)
      +pr = AR.pf_right(T, p, l, r, pf)
      +le = N.not_lt_le(j, SC.pow2(p), eb)
      +k = Nat.sub(j, SC.pow2(p))
      +hjr = AR.upper_lt(j, p, hj, le)
      +hxr = Equal.trans(Maybe<&2, T>, SC.nth(T, AR.slots(T, r), k), SC.nth(T, SC.append(T, AR.slots(T, l), AR.slots(T, r)), j), Some{x},
        Equal.sym(Maybe<&2, T>, SC.nth(T, SC.append(T, AR.slots(T, l), AR.slots(T, r)), j), SC.nth(T, AR.slots(T, r), k), AR.right_nth(T, p, l, r, j, pl, le)), hx)
      %Equal.sym(AR.Tree<T>, AR.tupd(T, p, r, k, x, AR.ndec(p, k)), r, tupd_self(T, p, r, k, x, hjr, pr, hxr, AR.ndec(p, k), {==})) : {AR.TNode{l, _} == AR.TNode{l, r} : AR.Tree<T>}
      {==}

# Two writes at the same index: the second wins.
def tupd_tupd(-T: Data, +d: Nat, +t: AR.Tree<T>, +j: Nat, +a: T, +x: T, +b: Bool) -> {AR.tupd(T, d, AR.tupd(T, d, t, j, a, b), j, x, b) == AR.tupd(T, d, t, j, x, b) : AR.Tree<T>}:
  match d t b:
    case 0n AR.TLeaf{y} _:
      {==}
    case 0n AR.TNode{l, r} _:
      {==}
    case 1n+p AR.TLeaf{y} _:
      {==}
    case 1n+ +p AR.TNode{+l, +r} True{}:
      %Equal.sym(AR.Tree<T>, AR.tupd(T, p, AR.tupd(T, p, l, j, a, AR.ndec(p, j)), j, x, AR.ndec(p, j)), AR.tupd(T, p, l, j, x, AR.ndec(p, j)), tupd_tupd(T, p, l, j, a, x, AR.ndec(p, j))) : {AR.TNode{_, r} == AR.TNode{AR.tupd(T, p, l, j, x, AR.ndec(p, j)), r} : AR.Tree<T>}
      {==}
    case 1n+ +p AR.TNode{+l, +r} False{}:
      +k = Nat.sub(j, SC.pow2(p))
      %Equal.sym(AR.Tree<T>, AR.tupd(T, p, AR.tupd(T, p, r, k, a, AR.ndec(p, k)), k, x, AR.ndec(p, k)), AR.tupd(T, p, r, k, x, AR.ndec(p, k)), tupd_tupd(T, p, r, k, a, x, AR.ndec(p, k))) : {AR.TNode{l, _} == AR.TNode{l, AR.tupd(T, p, r, k, x, AR.ndec(p, k))} : AR.Tree<T>}
      {==}

# Take the value out (replacing it by `a`) and put the same value back.
def upd_back(-T: Data, +d: Nat, +t: AR.Tree<T>, +j: Nat, +a: T, +x: T, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(T, d, t) == True{} : Bool}, +hx: {SC.nth(T, AR.slots(T, t), j) == Some{x} : Maybe<&2, T>}) -> {AR.upd(T, d, AR.upd(T, d, t, j, a), j, x) == t : AR.Tree<T>}:
  Equal.trans(AR.Tree<T>, AR.tupd(T, d, AR.tupd(T, d, t, j, a, AR.ndec(d, j)), j, x, AR.ndec(d, j)), AR.tupd(T, d, t, j, x, AR.ndec(d, j)), t,
    tupd_tupd(T, d, t, j, a, x, AR.ndec(d, j)),
    tupd_self(T, d, t, j, x, hj, pf, hx, AR.ndec(d, j), {==}))
