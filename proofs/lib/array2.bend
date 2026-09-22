import Base
import ./logic.bend as L
import ./nat.bend as N
import ./u32.bend as U
import ./list.bend as LL
import ./array.bend as AR
import ../spec/common.bend as SC

# Functional correctness of the installed Base.Array swap/set algorithms at a
# NESTED element type: `Array<Array<U32>>`, the block of adjacency blocks the
# graph uses.
#
# proofs/lib/array.bend states its laws about `AR.thaw(T, t)` for a Data
# mirror `T`. That does not cover this case, because the element type here is
# `Array<U32>`, which is linear (not `Data`), so `Array.get` is not even
# applicable and `AR.thaw` cannot produce the outer array. The MIRROR,
# however, is still Data: `AR.Tree<AR.Tree<U32>>`. So every mirror-level
# lemma of proofs/lib/array.bend (perfect, slots, upd, nth) is reused as is at
# `T = AR.Tree<U32>`, and only the realization function and the two Base
# algorithms that touch it (`Array.swap`, and `Array.set` on top of it) are
# proved again here, by the same induction.

def thaw2(t: AR.Tree<AR.Tree<U32>>) -> Array<Array<U32>>:
  match t:
    case AR.TLeaf{b}:
      ALeaf{AR.thaw(U32, b)}
    case AR.TNode{l, r}:
      ANode{thaw2(l), thaw2(r)}

def size_thaw2(+d: Nat, +t: AR.Tree<AR.Tree<U32>>, +pf: {AR.perfect(AR.Tree<U32>, d, t) == True{} : Bool}) -> {Array.size(Array<U32>, thaw2(t)) == (thaw2(t), U.pow2u(d)) : Array<Array<U32>> & U32}:
  match d t:
    case 0n AR.TLeaf{b}:
      {==}
    case 0n AR.TNode{l, r}:
      Empty.absurd({Array.size(Array<U32>, thaw2(AR.TNode{l, r})) == (thaw2(AR.TNode{l, r}), 1) : Array<Array<U32>> & U32}, L.false_true(pf))
    case 1n+p AR.TLeaf{b}:
      Empty.absurd({Array.size(Array<U32>, ALeaf{AR.thaw(U32, b)}) == (ALeaf{AR.thaw(U32, b)}, U.pow2u(1n+p)) : Array<Array<U32>> & U32}, L.false_true(pf))
    case 1n+ +p AR.TNode{+l, +r}:
      %Equal.sym(Array<Array<U32>> & U32, Array.size(Array<U32>, thaw2(l)), (thaw2(l), U.pow2u(p)), size_thaw2(p, l, AR.pf_left(AR.Tree<U32>, p, l, r, pf))) : {Array.size.node(Array<U32>, thaw2(r), _) == (ANode{thaw2(l), thaw2(r)}, U32.shl(U.pow2u(p))) : Array<Array<U32>> & U32}
      {==}

def swap_go2(+d: Nat, +t: AR.Tree<AR.Tree<U32>>, +i: U32, +vt: AR.Tree<U32>, +xt: AR.Tree<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}, +hx: {SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, t), U32.to_nat(i)) == Some{xt} : Maybe<&2, AR.Tree<U32>>}, +b: Bool, +eb: {U32.is_lt(i, U.pow2u(N.pred(d))) == b : Bool}, +pf: {AR.perfect(AR.Tree<U32>, d, t) == True{} : Bool}) -> {Array.swap.go(Array<U32>, thaw2(t), U.pow2u(d), i, AR.thaw(U32, vt)) == (thaw2(AR.upd(AR.Tree<U32>, d, t, U32.to_nat(i), vt)), AR.thaw(U32, xt)) : Array<Array<U32>> & Array<U32>}:
  match d t b:
    case 0n AR.TLeaf{+y} _:
      %AR.leaf_value(AR.Tree<U32>, y, U32.to_nat(i), xt, hi, hx) : {(ALeaf{AR.thaw(U32, vt)}, AR.thaw(U32, y)) == (ALeaf{AR.thaw(U32, vt)}, AR.thaw(U32, _)) : Array<Array<U32>> & Array<U32>}
      {==}
    case 0n AR.TNode{l, r} _:
      Empty.absurd({Array.swap.go(Array<U32>, thaw2(AR.TNode{l, r}), 1, i, AR.thaw(U32, vt)) == (thaw2(AR.upd(AR.Tree<U32>, 0n, AR.TNode{l, r}, U32.to_nat(i), vt)), AR.thaw(U32, xt)) : Array<Array<U32>> & Array<U32>}, L.false_true(pf))
    case 1n+p AR.TLeaf{y} _:
      Empty.absurd({Array.swap.go(Array<U32>, ALeaf{AR.thaw(U32, y)}, U.pow2u(1n+p), i, AR.thaw(U32, vt)) == (thaw2(AR.upd(AR.Tree<U32>, 1n+p, AR.TLeaf{y}, U32.to_nat(i), vt)), AR.thaw(U32, xt)) : Array<Array<U32>> & Array<U32>}, L.false_true(pf))
    case 1n+ +p AR.TNode{+l, +r} True{}:
      +hp = N.lt_trans(p, 1n+p, 32n, N.lt_succ(p), hd)
      +pl = AR.pf_left(AR.Tree<U32>, p, l, r, pf)
      +hil = AR.lt_bridge(i, p, hp, True{}, eb)
      +ti = U32.to_nat(i)
      %Equal.sym(U32, U32.shr(U.pow2u(1n+p)), U.pow2u(p), U.shr_pow2u(p, hd)) : {Array.swap.if(Array<U32>, thaw2(l), thaw2(r), _, i, AR.thaw(U32, vt), U32.is_lt(i, _)) == (thaw2(AR.upd(AR.Tree<U32>, 1n+p, AR.TNode{l, r}, ti, vt)), AR.thaw(U32, xt)) : Array<Array<U32>> & Array<U32>}
      %Equal.sym(Bool, U32.is_lt(i, U.pow2u(p)), True{}, eb) : {Array.swap.if(Array<U32>, thaw2(l), thaw2(r), U.pow2u(p), i, AR.thaw(U32, vt), _) == (thaw2(AR.upd(AR.Tree<U32>, 1n+p, AR.TNode{l, r}, ti, vt)), AR.thaw(U32, xt)) : Array<Array<U32>> & Array<U32>}
      %Equal.sym(Bool, Nat.is_lt(ti, SC.pow2(p)), True{}, hil) : {Array.swap.lo(Array<U32>, thaw2(r), Array.swap.go(Array<U32>, thaw2(l), U.pow2u(p), i, AR.thaw(U32, vt))) == (thaw2(AR.tupd(AR.Tree<U32>, 1n+p, AR.TNode{l, r}, ti, vt, _)), AR.thaw(U32, xt)) : Array<Array<U32>> & Array<U32>}
      %Equal.sym(Array<Array<U32>> & Array<U32>, Array.swap.go(Array<U32>, thaw2(l), U.pow2u(p), i, AR.thaw(U32, vt)), (thaw2(AR.upd(AR.Tree<U32>, p, l, ti, vt)), AR.thaw(U32, xt)), swap_go2(p, l, i, vt, xt, hp, hil, Equal.trans(Maybe<&2, AR.Tree<U32>>, SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, l), ti), SC.nth(AR.Tree<U32>, SC.append(AR.Tree<U32>, AR.slots(AR.Tree<U32>, l), AR.slots(AR.Tree<U32>, r)), ti), Some{xt}, Equal.sym(Maybe<&2, AR.Tree<U32>>, SC.nth(AR.Tree<U32>, SC.append(AR.Tree<U32>, AR.slots(AR.Tree<U32>, l), AR.slots(AR.Tree<U32>, r)), ti), SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, l), ti), LL.nth_append_left(AR.Tree<U32>, AR.slots(AR.Tree<U32>, l), AR.slots(AR.Tree<U32>, r), ti, AR.len_lt(AR.Tree<U32>, p, l, ti, pl, hil))), hx), U32.is_lt(i, U.pow2u(N.pred(p))), {==}, pl)) : {Array.swap.lo(Array<U32>, thaw2(r), _) == (thaw2(AR.TNode{AR.tupd(AR.Tree<U32>, p, l, ti, vt, AR.ndec(p, ti)), r}), AR.thaw(U32, xt)) : Array<Array<U32>> & Array<U32>}
      {==}
    case 1n+ +p AR.TNode{+l, +r} False{}:
      +hp = N.lt_trans(p, 1n+p, 32n, N.lt_succ(p), hd)
      +pl = AR.pf_left(AR.Tree<U32>, p, l, r, pf)
      +ti = U32.to_nat(i)
      +nb = AR.lt_bridge(i, p, hp, False{}, eb)
      +le = N.not_lt_le(ti, SC.pow2(p), nb)
      +j = U32.sub(i, U.pow2u(p))
      +k = Nat.sub(ti, SC.pow2(p))
      +ej = AR.sub_bridge(i, p, hp, le)
      +hir = L.subst(Nat, n => {Nat.is_lt(n, SC.pow2(p)) == True{} : Bool}, k, U32.to_nat(j), Equal.sym(Nat, U32.to_nat(j), k, ej), AR.upper_lt(ti, p, hi, le))
      +hxr = L.subst(Nat, n => {SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, r), n) == Some{xt} : Maybe<&2, AR.Tree<U32>>}, k, U32.to_nat(j), Equal.sym(Nat, U32.to_nat(j), k, ej), Equal.trans(Maybe<&2, AR.Tree<U32>>, SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, r), k), SC.nth(AR.Tree<U32>, SC.append(AR.Tree<U32>, AR.slots(AR.Tree<U32>, l), AR.slots(AR.Tree<U32>, r)), ti), Some{xt}, Equal.sym(Maybe<&2, AR.Tree<U32>>, SC.nth(AR.Tree<U32>, SC.append(AR.Tree<U32>, AR.slots(AR.Tree<U32>, l), AR.slots(AR.Tree<U32>, r)), ti), SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, r), k), AR.right_nth(AR.Tree<U32>, p, l, r, ti, pl, le)), hx))
      +ih = swap_go2(p, r, j, vt, xt, hp, hir, hxr, U32.is_lt(j, U.pow2u(N.pred(p))), {==}, AR.pf_right(AR.Tree<U32>, p, l, r, pf))
      +ih2 = L.subst(Nat, n => {Array.swap.go(Array<U32>, thaw2(r), U.pow2u(p), j, AR.thaw(U32, vt)) == (thaw2(AR.upd(AR.Tree<U32>, p, r, n, vt)), AR.thaw(U32, xt)) : Array<Array<U32>> & Array<U32>}, U32.to_nat(j), k, ej, ih)
      %Equal.sym(U32, U32.shr(U.pow2u(1n+p)), U.pow2u(p), U.shr_pow2u(p, hd)) : {Array.swap.if(Array<U32>, thaw2(l), thaw2(r), _, i, AR.thaw(U32, vt), U32.is_lt(i, _)) == (thaw2(AR.upd(AR.Tree<U32>, 1n+p, AR.TNode{l, r}, ti, vt)), AR.thaw(U32, xt)) : Array<Array<U32>> & Array<U32>}
      %Equal.sym(Bool, U32.is_lt(i, U.pow2u(p)), False{}, eb) : {Array.swap.if(Array<U32>, thaw2(l), thaw2(r), U.pow2u(p), i, AR.thaw(U32, vt), _) == (thaw2(AR.upd(AR.Tree<U32>, 1n+p, AR.TNode{l, r}, ti, vt)), AR.thaw(U32, xt)) : Array<Array<U32>> & Array<U32>}
      %Equal.sym(Bool, Nat.is_lt(ti, SC.pow2(p)), False{}, nb) : {Array.swap.hi(Array<U32>, thaw2(l), Array.swap.go(Array<U32>, thaw2(r), U.pow2u(p), j, AR.thaw(U32, vt))) == (thaw2(AR.tupd(AR.Tree<U32>, 1n+p, AR.TNode{l, r}, ti, vt, _)), AR.thaw(U32, xt)) : Array<Array<U32>> & Array<U32>}
      %Equal.sym(Array<Array<U32>> & Array<U32>, Array.swap.go(Array<U32>, thaw2(r), U.pow2u(p), j, AR.thaw(U32, vt)), (thaw2(AR.upd(AR.Tree<U32>, p, r, k, vt)), AR.thaw(U32, xt)), ih2) : {Array.swap.hi(Array<U32>, thaw2(l), _) == (thaw2(AR.TNode{l, AR.tupd(AR.Tree<U32>, p, r, k, vt, AR.ndec(p, k))}), AR.thaw(U32, xt)) : Array<Array<U32>> & Array<U32>}
      {==}

# Public Base entry points at the nested element type.
def swap2(+d: Nat, +t: AR.Tree<AR.Tree<U32>>, +i: U32, +vt: AR.Tree<U32>, +xt: AR.Tree<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}, +hx: {SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, t), U32.to_nat(i)) == Some{xt} : Maybe<&2, AR.Tree<U32>>}, +pf: {AR.perfect(AR.Tree<U32>, d, t) == True{} : Bool}) -> {Array.swap(Array<U32>, thaw2(t), i, AR.thaw(U32, vt)) == (thaw2(AR.upd(AR.Tree<U32>, d, t, U32.to_nat(i), vt)), AR.thaw(U32, xt)) : Array<Array<U32>> & Array<U32>}:
  %Equal.sym(Array<Array<U32>> & U32, Array.size(Array<U32>, thaw2(t)), (thaw2(t), U.pow2u(d)), size_thaw2(d, t, pf)) : {Array.swap.at(Array<U32>, i, AR.thaw(U32, vt), _) == (thaw2(AR.upd(AR.Tree<U32>, d, t, U32.to_nat(i), vt)), AR.thaw(U32, xt)) : Array<Array<U32>> & Array<U32>}
  %Equal.sym(U32, U32.and(i, U32.sub(U.pow2u(d), 1)), i, U.mask_pow2u(i, d, hd, hi)) : {Array.swap.go(Array<U32>, thaw2(t), U.pow2u(d), _, AR.thaw(U32, vt)) == (thaw2(AR.upd(AR.Tree<U32>, d, t, U32.to_nat(i), vt)), AR.thaw(U32, xt)) : Array<Array<U32>> & Array<U32>}
  swap_go2(d, t, i, vt, xt, hd, hi, hx, U32.is_lt(i, U.pow2u(N.pred(d))), {==}, pf)

def set2(+d: Nat, +t: AR.Tree<AR.Tree<U32>>, +i: U32, +vt: AR.Tree<U32>, +xt: AR.Tree<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}, +hx: {SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, t), U32.to_nat(i)) == Some{xt} : Maybe<&2, AR.Tree<U32>>}, +pf: {AR.perfect(AR.Tree<U32>, d, t) == True{} : Bool}) -> {Array.set(Array<U32>, thaw2(t), i, AR.thaw(U32, vt)) == thaw2(AR.upd(AR.Tree<U32>, d, t, U32.to_nat(i), vt)) : Array<Array<U32>>}:
  %Equal.sym(Array<Array<U32>> & Array<U32>, Array.swap(Array<U32>, thaw2(t), i, AR.thaw(U32, vt)), (thaw2(AR.upd(AR.Tree<U32>, d, t, U32.to_nat(i), vt)), AR.thaw(U32, xt)), swap2(d, t, i, vt, xt, hd, hi, hx, pf)) : {Array.set.fin(Array<U32>, _) == thaw2(AR.upd(AR.Tree<U32>, d, t, U32.to_nat(i), vt)) : Array<Array<U32>>}
  {==}

# Doubling on either side, as the vertex table grows.
def node_lo(+lt: AR.Tree<AR.Tree<U32>>, +rt: AR.Tree<AR.Tree<U32>>) -> {ANode{thaw2(lt), thaw2(rt)} == thaw2(AR.TNode{lt, rt}) : Array<Array<U32>>}:
  {==}
