import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../spec/binary_heap.bend as S
import ../../src/binary_heap.bend as H
import ./idx.bend as IX
import ./slots.bend as SL
import ./vals.bend as V
import ./root.bend as RT

# Doubling the block: the old block becomes the lower half of a block one
# level deeper, so every element keeps its index and nothing about the heap
# changes except the capacity. These are the lemmas that say so.

def slots_grown(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>) -> {AR.slots(Maybe<&2, A>, AR.TNode{t, AR.trep(Maybe<&2, A>, d, None{})}) == SC.append(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), SC.replicate(Maybe<&2, A>, SC.pow2(d), None{})) : List<&2, Maybe<&2, A>>}:
  %Equal.sym(List<&2, Maybe<&2, A>>, AR.slots(Maybe<&2, A>, AR.trep(Maybe<&2, A>, d, None{})), SC.replicate(Maybe<&2, A>, SC.pow2(d), None{}), AR.trep_slots(Maybe<&2, A>, d, None{})) : {SC.append(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), _) == SC.append(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), SC.replicate(Maybe<&2, A>, SC.pow2(d), None{})) : List<&2, Maybe<&2, A>>}
  {==}

# A slot inside the old block reads the same through the appended one.
def slot_left(~A: Data, +ss: List<&2, Maybe<&2, A>>, +ys: List<&2, Maybe<&2, A>>, +j: Nat, +h: {Nat.is_lt(j, SC.length(Maybe<&2, A>, ss)) == True{} : Bool}) -> {SL.slot(~A, SC.append(Maybe<&2, A>, ss, ys), j) == SL.slot(~A, ss, j) : Maybe<&2, A>}:
  Equal.cong(Maybe<&2, Maybe<&2, A>>, Maybe<&2, A>, m => SL.unwrap(~A, m), SC.nth(Maybe<&2, A>, SC.append(Maybe<&2, A>, ss, ys), j), SC.nth(Maybe<&2, A>, ss, j), LL.nth_append_left(Maybe<&2, A>, ss, ys, j, h))

def lay_grow(~A: Data, +ss: List<&2, Maybe<&2, A>>, +ys: List<&2, Maybe<&2, A>>, k: Nat, +hk: {Nat.is_le(k, SC.length(Maybe<&2, A>, ss)) == True{} : Bool}, +h: {SL.lay(~A, ss, k) == True{} : Bool}) -> {SL.lay(~A, SC.append(Maybe<&2, A>, ss, ys), k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +m:
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, SC.append(Maybe<&2, A>, ss, ys), m), SL.slot(~A, ss, m), slot_left(~A, ss, ys, m, N.succ_le_lt(m, SC.length(Maybe<&2, A>, ss), hk))) : {Bool.and(Maybe.is_some(&2, A, _), SL.lay(~A, SC.append(Maybe<&2, A>, ss, ys), m)) == True{} : Bool}
      L.and_intro(Maybe.is_some(&2, A, SL.slot(~A, ss, m)), SL.lay(~A, SC.append(Maybe<&2, A>, ss, ys), m),
        L.and_left(Maybe.is_some(&2, A, SL.slot(~A, ss, m)), SL.lay(~A, ss, m), h),
        lay_grow(~A, ss, ys, m, N.le_trans(m, 1n+m, SC.length(Maybe<&2, A>, ss), N.le_succ(m), hk), L.and_right(Maybe.is_some(&2, A, SL.slot(~A, ss, m)), SL.lay(~A, ss, m), h)))

# one heap-order pair, read through the appended block
def pair_grow(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +ys: List<&2, Maybe<&2, A>>, m: Nat, +hm: {Nat.is_lt(m, SC.length(Maybe<&2, A>, ss)) == True{} : Bool}, +h: {SL.pair_ok(~A, ~cmp, ss, m) == True{} : Bool}) -> {SL.pair_ok(~A, ~cmp, SC.append(Maybe<&2, A>, ss, ys), m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+ +p:
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, SC.append(Maybe<&2, A>, ss, ys), 1n+p), SL.slot(~A, ss, 1n+p), slot_left(~A, ss, ys, 1n+p, hm)) : {SL.mle(~A, ~cmp, SL.slot(~A, SC.append(Maybe<&2, A>, ss, ys), IX.par(1n+p)), _) == True{} : Bool}
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, SC.append(Maybe<&2, A>, ss, ys), IX.par(1n+p)), SL.slot(~A, ss, IX.par(1n+p)), slot_left(~A, ss, ys, IX.par(1n+p), N.lt_trans(IX.par(1n+p), 1n+p, SC.length(Maybe<&2, A>, ss), IX.par_lt(1n+p, {==}), hm))) : {SL.mle(~A, ~cmp, _, SL.slot(~A, ss, 1n+p)) == True{} : Bool}
      h

def ho_grow(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +ys: List<&2, Maybe<&2, A>>, k: Nat, +hk: {Nat.is_le(k, SC.length(Maybe<&2, A>, ss)) == True{} : Bool}, +h: {SL.ho_upto(~A, ~cmp, ss, k) == True{} : Bool}) -> {SL.ho_upto(~A, ~cmp, SC.append(Maybe<&2, A>, ss, ys), k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +m:
      L.and_intro(SL.pair_ok(~A, ~cmp, SC.append(Maybe<&2, A>, ss, ys), m), SL.ho_upto(~A, ~cmp, SC.append(Maybe<&2, A>, ss, ys), m),
        pair_grow(~A, ~cmp, ss, ys, m, N.succ_le_lt(m, SC.length(Maybe<&2, A>, ss), hk), L.and_left(SL.pair_ok(~A, ~cmp, ss, m), SL.ho_upto(~A, ~cmp, ss, m), h)),
        ho_grow(~A, ~cmp, ss, ys, m, N.le_trans(m, 1n+m, SC.length(Maybe<&2, A>, ss), N.le_succ(m), hk), L.and_right(SL.pair_ok(~A, ~cmp, ss, m), SL.ho_upto(~A, ~cmp, ss, m), h)))

def vals_grow(~A: Data, +ss: List<&2, Maybe<&2, A>>, +ys: List<&2, Maybe<&2, A>>, k: Nat, +hk: {Nat.is_le(k, SC.length(Maybe<&2, A>, ss)) == True{} : Bool}) -> {V.vals(~A, SC.append(Maybe<&2, A>, ss, ys), k) == V.vals(~A, ss, k) : List<&2, A>}:
  match k:
    case 0n:
      {==}
    case 1n+ +m:
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, SC.append(Maybe<&2, A>, ss, ys), m), SL.slot(~A, ss, m), slot_left(~A, ss, ys, m, N.succ_le_lt(m, SC.length(Maybe<&2, A>, ss), hk))) : {V.cons_slot(~A, _, V.vals(~A, SC.append(Maybe<&2, A>, ss, ys), m)) == V.vals(~A, ss, 1n+m) : List<&2, A>}
      Equal.cong(List<&2, A>, List<&2, A>, zs => V.cons_slot(~A, SL.slot(~A, ss, m), zs), V.vals(~A, SC.append(Maybe<&2, A>, ss, ys), m), V.vals(~A, ss, m), vals_grow(~A, ss, ys, m, N.le_trans(m, 1n+m, SC.length(Maybe<&2, A>, ss), N.le_succ(m), hk)))

# ---- the grown block, as a tree ----

def gtree(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>) -> AR.Tree<Maybe<&2, A>>:
  AR.TNode{t, AR.trep(Maybe<&2, A>, d, None{})}

def gtree_perfect(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {AR.perfect(Maybe<&2, A>, 1n+d, gtree(~A, d, t)) == True{} : Bool}:
  L.and_intro(AR.perfect(Maybe<&2, A>, d, t), AR.perfect(Maybe<&2, A>, d, AR.trep(Maybe<&2, A>, d, None{})), pf, AR.trep_perfect(Maybe<&2, A>, d, None{}))

def gtree_real(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>) -> {H.grown(~A, d, AR.thaw(Maybe<&2, A>, t)) == AR.thaw(Maybe<&2, A>, gtree(~A, d, t)) : Array<Maybe<&2, A>>}:
  Equal.cong(Array<Maybe<&2, A>>, Array<Maybe<&2, A>>, a => ANode{AR.thaw(Maybe<&2, A>, t), a}, H.empty_slots(~A, d), AR.thaw(Maybe<&2, A>, AR.trep(Maybe<&2, A>, d, None{})), AR.new(Maybe<&2, A>, d, None{}))

def gtree_lay(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +k: Nat, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hk: {Nat.is_le(k, SC.pow2(d)) == True{} : Bool}, +h: {SL.lay(~A, AR.slots(Maybe<&2, A>, t), k) == True{} : Bool}) -> {SL.lay(~A, AR.slots(Maybe<&2, A>, gtree(~A, d, t)), k) == True{} : Bool}:
  %Equal.sym(List<&2, Maybe<&2, A>>, AR.slots(Maybe<&2, A>, gtree(~A, d, t)), SC.append(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), SC.replicate(Maybe<&2, A>, SC.pow2(d), None{})), slots_grown(~A, d, t)) : {SL.lay(~A, _, k) == True{} : Bool}
  lay_grow(~A, AR.slots(Maybe<&2, A>, t), SC.replicate(Maybe<&2, A>, SC.pow2(d), None{}), k,
    L.subst(Nat, z => {Nat.is_le(k, z) == True{} : Bool}, SC.pow2(d), SC.length(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t)), Equal.sym(Nat, SC.length(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t)), SC.pow2(d), AR.slots_length(Maybe<&2, A>, d, t, pf)), hk), h)

def gtree_ho(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +k: Nat, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hk: {Nat.is_le(k, SC.pow2(d)) == True{} : Bool}, +h: {SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), k) == True{} : Bool}) -> {SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, gtree(~A, d, t)), k) == True{} : Bool}:
  %Equal.sym(List<&2, Maybe<&2, A>>, AR.slots(Maybe<&2, A>, gtree(~A, d, t)), SC.append(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), SC.replicate(Maybe<&2, A>, SC.pow2(d), None{})), slots_grown(~A, d, t)) : {SL.ho_upto(~A, ~cmp, _, k) == True{} : Bool}
  ho_grow(~A, ~cmp, AR.slots(Maybe<&2, A>, t), SC.replicate(Maybe<&2, A>, SC.pow2(d), None{}), k,
    L.subst(Nat, z => {Nat.is_le(k, z) == True{} : Bool}, SC.pow2(d), SC.length(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t)), Equal.sym(Nat, SC.length(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t)), SC.pow2(d), AR.slots_length(Maybe<&2, A>, d, t, pf)), hk), h)

def gtree_vals(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +k: Nat, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hk: {Nat.is_le(k, SC.pow2(d)) == True{} : Bool}) -> {V.vals(~A, AR.slots(Maybe<&2, A>, gtree(~A, d, t)), k) == V.vals(~A, AR.slots(Maybe<&2, A>, t), k) : List<&2, A>}:
  %Equal.sym(List<&2, Maybe<&2, A>>, AR.slots(Maybe<&2, A>, gtree(~A, d, t)), SC.append(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), SC.replicate(Maybe<&2, A>, SC.pow2(d), None{})), slots_grown(~A, d, t)) : {V.vals(~A, _, k) == V.vals(~A, AR.slots(Maybe<&2, A>, t), k) : List<&2, A>}
  vals_grow(~A, AR.slots(Maybe<&2, A>, t), SC.replicate(Maybe<&2, A>, SC.pow2(d), None{}), k,
    L.subst(Nat, z => {Nat.is_le(k, z) == True{} : Bool}, SC.pow2(d), SC.length(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t)), Equal.sym(Nat, SC.length(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t)), SC.pow2(d), AR.slots_length(Maybe<&2, A>, d, t, pf)), hk))
