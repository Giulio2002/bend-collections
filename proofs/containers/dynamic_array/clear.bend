import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../lib/array.bend as AR
import ../../lib/spec_common.bend as SC
import ../../../src/containers/dynamic_array.bend as DA
import ./layout.bend as LY
import ./state.bend as ST
import ./steps.bend as SP
import ../../lib/array_ext.bend as AX

# The executable clear (src/dynamic_array.bend clear_at) resets the occupied
# slots [0, n) to None, top down, in the block it already has; the parametric
# clear allocates a fresh all-None block of the same depth. On a good state
# the two agree: each reset is the in-place write pop makes (and keeps the
# layout good with one fewer element), and a good layout of length 0 is the
# all-None tree itself.

# A list of Nones is the replication of None to its length.
def nones_rep_eq(-T: Data, +xs: List<&2, Maybe<&2, T>>, +h: {LY.nones(T, xs) == True{} : Bool}) -> {xs == SC.replicate(Maybe<&2, T>, SC.length(Maybe<&2, T>, xs), None{}) : List<&2, Maybe<&2, T>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{None{}, +r}:
      LL.cons_cong(Maybe<&2, T>, None{}, r, SC.replicate(Maybe<&2, T>, SC.length(Maybe<&2, T>, r), None{}), nones_rep_eq(T, r, h))
    case Con{Some{x}, r}:
      Empty.absurd({Con{Some{x}, r} == SC.replicate(Maybe<&2, T>, SC.length(Maybe<&2, T>, Con{Some{x}, r}), None{}) : List<&2, Maybe<&2, T>>}, L.false_true(h))

# A layout of length 0 holds only Nones.
def lay0_nones(-T: Data, +xs: List<&2, Maybe<&2, T>>, +h: {LY.lay(T, xs, 0n) == True{} : Bool}) -> {LY.nones(T, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{None{}, r}:
      h
    case Con{Some{x}, r}:
      Empty.absurd({LY.nones(T, Con{Some{x}, r}) == True{} : Bool}, L.false_true(h))

# The slots of a good empty shadow are those of the all-None tree.
def empty_slots_eq(-T: Data, +d: Nat, +t: AR.Tree<Maybe<&2, T>>, +pf: {AR.perfect(Maybe<&2, T>, d, t) == True{} : Bool}, +h: {LY.lay(T, AR.slots(Maybe<&2, T>, t), 0n) == True{} : Bool}) -> {AR.slots(Maybe<&2, T>, t) == AR.slots(Maybe<&2, T>, AR.trep(Maybe<&2, T>, d, None{})) : List<&2, Maybe<&2, T>>}:
  +ss = AR.slots(Maybe<&2, T>, t)
  %Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, AR.trep(Maybe<&2, T>, d, None{})), SC.replicate(Maybe<&2, T>, SC.pow2(d), None{}), AR.trep_slots(Maybe<&2, T>, d, None{})) : {ss == _ : List<&2, Maybe<&2, T>>}
  %AR.slots_length(Maybe<&2, T>, d, t, pf) : {ss == SC.replicate(Maybe<&2, T>, _, None{}) : List<&2, Maybe<&2, T>>}
  nones_rep_eq(T, ss, lay0_nones(T, ss, h))

# Resetting the k occupied slots of a good shadow gives the all-None block.
def clear_go_eq(~T: Data, +l: Nat, +d: Nat, +k: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{l, d, k, t}) == True{} : Bool}) -> {DA.clear_go_at(~T, k, AR.thaw(Maybe<&2, T>, t)) == DA.empty_slots(T, d) : Array<Maybe<&2, T>>}:
  match k:
    case 0n:
      +pf = ST.g_perfect(T, l, d, 0n, t, g)
      +te = AX.tree_ext(Maybe<&2, T>, d, t, AR.trep(Maybe<&2, T>, d, None{}), pf, AR.trep_perfect(Maybe<&2, T>, d, None{}), empty_slots_eq(T, d, t, pf, ST.g_lay(T, l, d, 0n, t, g)))
      %Equal.sym(Array<Maybe<&2, T>>, DA.empty_slots(T, d), AR.thaw(Maybe<&2, T>, AR.trep(Maybe<&2, T>, d, None{})), ST.empty_eq(T, d)) : {AR.thaw(Maybe<&2, T>, t) == _ : Array<Maybe<&2, T>>}
      %te : {AR.thaw(Maybe<&2, T>, t) == AR.thaw(Maybe<&2, T>, _) : Array<Maybe<&2, T>>}
      {==}
    case 1n+ +m:
      +ss = AR.slots(Maybe<&2, T>, t)
      +x = SC.nth(T, LY.somes(T, ss), m)
      +hlay = ST.g_lay(T, l, d, 1n+m, t, g)
      +hm = N.lt_succ(m)
      +hi = N.lt_le_trans(m, 1n+m, SC.pow2(d), hm, SP.n_le_cap(T, l, d, 1n+m, t, g))
      +t2 = AR.upd(Maybe<&2, T>, d, t, m, None{})
      +hs = SP.upd_slots(T, l, d, 1n+m, t, m, None{}, g, hi)
      +g2 = ST.good_intro(T, l, d, m, t2, ST.g_limit(T, l, d, 1n+m, t, g), ST.g_depth(T, l, d, 1n+m, t, g), AR.upd_perfect(Maybe<&2, T>, d, t, m, None{}, ST.g_perfect(T, l, d, 1n+m, t, g)),
        L.subst(List<&2, Maybe<&2, T>>, ys => {LY.lay(T, ys, m) == True{} : Bool}, SC.update(Maybe<&2, T>, ss, m, None{}), AR.slots(Maybe<&2, T>, t2), Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t2), SC.update(Maybe<&2, T>, ss, m, None{}), hs), LY.lay_pop(T, ss, m, hlay)))
      %Equal.sym(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.swap(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(m), None{}), (AR.thaw(Maybe<&2, T>, t2), x), SP.swap_arr(T, l, d, 1n+m, t, m, None{}, x, g, hi, LY.lay_nth(T, ss, 1n+m, m, hlay, hm))) : {DA.clear_go_at(~T, m, Array.set.fin(Maybe<&2, T>, _)) == DA.empty_slots(T, d) : Array<Maybe<&2, T>>}
      clear_go_eq(~T, l, d, m, t2, g2)

def clear_eq(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}) -> {DA.clear_at(~T, ST.real(T, ST.Sh{l, d, n, t})) == DA.clear(T, ST.real(T, ST.Sh{l, d, n, t})) : DA.DynArray<&2, T>}:
  Equal.cong(Array<Maybe<&2, T>>, DA.DynArray<&2, T>, z => DA.DA{l, d, SC.pow2(d), 0n, z}, DA.clear_go_at(~T, n, AR.thaw(Maybe<&2, T>, t)), DA.empty_slots(T, d), clear_go_eq(~T, l, d, n, t, g))
