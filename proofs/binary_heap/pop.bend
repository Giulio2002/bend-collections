import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../spec/common.bend as SC
import ../spec/binary_heap.bend as S
import ../../src/containers/binary_heap.bend as H
import ../../src/containers/types/binary_heap.bend as E
import ./idx.bend as IX
import ./u32idx.bend as UX
import ./slots.bend as SL
import ./vals.bend as V
import ./multiset.bend as M
import ./root.bend as RT
import ./up.bend as UPS
import ./down.bend as DN
import ./state.bend as ST

# pop: the root is taken out, the last element is lifted into the hole at the
# root and sifted down. `hole` is the logical block the sift-down works on:
# the last slot emptied, the root slot holding the lifted value.

# ---- small arithmetic the pop needs ----

def scale_double(f: Nat, +m: Nat) -> {IX.scale(f, Nat.double(m)) == Nat.double(IX.scale(f, m)) : Nat}:
  match f:
    case 0n:
      {==}
    case 1n+ +g:
      scale_double(g, Nat.double(m))

def scale_one(d: Nat) -> {IX.scale(d, 1n) == SC.pow2(d) : Nat}:
  match d:
    case 0n:
      {==}
    case 1n+ +g:
      Equal.trans(Nat, IX.scale(g, Nat.double(1n)), Nat.double(IX.scale(g, 1n)), Nat.double(SC.pow2(g)),
        scale_double(g, 1n),
        Equal.cong(Nat, Nat, z => Nat.double(z), IX.scale(g, 1n), SC.pow2(g), scale_one(g)))

def half_ge1(k: Nat, +h: {Nat.is_le(2n, k) == True{} : Bool}) -> {Nat.is_le(1n, IX.half(k)) == True{} : Bool}:
  match k:
    case 0n:
      Empty.absurd({Nat.is_le(1n, IX.half(0n)) == True{} : Bool}, L.true_not_false(Nat.is_le(2n, 0n), h, {==}))
    case 1n+0n:
      Empty.absurd({Nat.is_le(1n, IX.half(1n)) == True{} : Bool}, L.true_not_false(Nat.is_le(2n, 1n), h, {==}))
    case 1n+1n+ +r:
      N.zero_le(IX.half_go(r, False{}))

# not a child of the root and positive => the parent is positive too
def par_pos(j: Nat, +hj: {Nat.is_le(1n, j) == True{} : Bool}, +hkf: {SL.kid_of(j, 0n) == False{} : Bool}) -> {Nat.is_le(1n, IX.par(j)) == True{} : Bool}:
  match j:
    case 0n:
      Empty.absurd({Nat.is_le(1n, IX.par(0n)) == True{} : Bool}, L.true_not_false(Nat.is_le(1n, 0n), hj, {==}))
    case 1n+0n:
      Empty.absurd({Nat.is_le(1n, IX.par(1n)) == True{} : Bool}, L.true_not_false(SL.kid_of(1n, 0n), {==}, hkf))
    case 1n+1n+0n:
      Empty.absurd({Nat.is_le(1n, IX.par(2n)) == True{} : Bool}, L.true_not_false(SL.kid_of(2n, 0n), {==}, hkf))
    case 1n+1n+1n+ +r:
      half_ge1(2n+r, N.zero_le(r))

# ---- the logical block the sift-down starts from ----

def hole(~A: Data, +ss: List<&2, Maybe<&2, A>>, +m: Nat, +last: A) -> List<&2, Maybe<&2, A>>:
  SC.update(Maybe<&2, A>, ss, 0n, Some{last})

def hole_at0(~A: Data, +ss: List<&2, Maybe<&2, A>>, +m: Nat, +last: A, +hlen: {Nat.is_lt(0n, SC.length(Maybe<&2, A>, ss)) == True{} : Bool}) -> {SL.slot(~A, hole(~A, ss, m, last), 0n) == Some{last} : Maybe<&2, A>}:
  SL.slot_same(~A, ss, 0n, Some{last}, hlen)

def hole_off(~A: Data, +ss: List<&2, Maybe<&2, A>>, +m: Nat, +last: A, +j: Nat, +hj0: {Nat.is_eq(0n, j) == False{} : Bool}) -> {SL.slot(~A, hole(~A, ss, m, last), j) == SL.slot(~A, ss, j) : Maybe<&2, A>}:
  SL.slot_other(~A, ss, 0n, j, Some{last}, hj0)

# ---- every pair except the two below the root still holds ----

def pop_pair(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +m: Nat, +last: A, j: Nat, +hjm: {Nat.is_lt(j, m) == True{} : Bool}, +hkf: {SL.kid_of(j, 0n) == False{} : Bool}, +hho: {SL.ho_upto(~A, ~cmp, ss, 1n+m) == True{} : Bool}) -> {SL.pair_ok(~A, ~cmp, hole(~A, ss, m, last), j) == True{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+ +p:
      +hpp = par_pos(1n+p, N.zero_le(p), hkf)
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, hole(~A, ss, m, last), 1n+p), SL.slot(~A, ss, 1n+p), hole_off(~A, ss, m, last, 1n+p, {==})) : {SL.mle(~A, ~cmp, SL.slot(~A, hole(~A, ss, m, last), IX.par(1n+p)), _) == True{} : Bool}
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, hole(~A, ss, m, last), IX.par(1n+p)), SL.slot(~A, ss, IX.par(1n+p)), hole_off(~A, ss, m, last, IX.par(1n+p), N.is_eq_lt(0n, IX.par(1n+p), N.succ_le_lt(0n, IX.par(1n+p), hpp)))) : {SL.mle(~A, ~cmp, _, SL.slot(~A, ss, 1n+p)) == True{} : Bool}
      SL.ho_at(~A, ~cmp, ss, 1n+m, 1n+p, hho, N.lt_trans(1n+p, m, 1n+m, hjm, N.lt_succ(m)))

def pop_skip(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +m: Nat, +last: A, +j: Nat, +hjm: {Nat.is_lt(j, m) == True{} : Bool}, +hho: {SL.ho_upto(~A, ~cmp, ss, 1n+m) == True{} : Bool}, b: Bool, +eb: {SL.kid_of(j, 0n) == b : Bool}) -> {SL.pair_skip2(~A, ~cmp, hole(~A, ss, m, last), j, 0n) == True{} : Bool}:
  match b:
    case True{}:
      SL.skip2_eq(~A, ~cmp, hole(~A, ss, m, last), j, 0n, eb)
    case False{}:
      SL.skip2_ne(~A, ~cmp, hole(~A, ss, m, last), j, 0n, eb, pop_pair(~A, ~cmp, ss, m, last, j, hjm, eb, hho))

def pop_exc(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +m: Nat, +last: A, k: Nat, +hk: {Nat.is_le(k, m) == True{} : Bool}, +hho: {SL.ho_upto(~A, ~cmp, ss, 1n+m) == True{} : Bool}) -> {SL.ho_exc2(~A, ~cmp, hole(~A, ss, m, last), k, 0n) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      L.and_intro(SL.pair_skip2(~A, ~cmp, hole(~A, ss, m, last), p, 0n), SL.ho_exc2(~A, ~cmp, hole(~A, ss, m, last), p, 0n),
        pop_skip(~A, ~cmp, ss, m, last, p, N.succ_le_lt(p, m, hk), hho, SL.kid_of(p, 0n), {==}),
        pop_exc(~A, ~cmp, ss, m, last, p, N.le_trans(p, 1n+p, m, N.le_succ(p), hk), hho))

# ---- the slots below m are still occupied ----

def pop_some(~A: Data, +ss: List<&2, Maybe<&2, A>>, +m: Nat, +last: A, j: Nat, +hjm: {Nat.is_lt(j, m) == True{} : Bool}, +hlay: {SL.lay(~A, ss, 1n+m) == True{} : Bool}, +hlen: {Nat.is_lt(0n, SC.length(Maybe<&2, A>, ss)) == True{} : Bool}) -> {Maybe.is_some(&2, A, SL.slot(~A, hole(~A, ss, m, last), j)) == True{} : Bool}:
  match j:
    case 0n:
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, hole(~A, ss, m, last), 0n), Some{last}, hole_at0(~A, ss, m, last, hlen)) : {Maybe.is_some(&2, A, _) == True{} : Bool}
      {==}
    case 1n+ +p:
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, hole(~A, ss, m, last), 1n+p), SL.slot(~A, ss, 1n+p), hole_off(~A, ss, m, last, 1n+p, {==})) : {Maybe.is_some(&2, A, _) == True{} : Bool}
      SL.lay_at(~A, ss, 1n+m, 1n+p, hlay, N.lt_trans(1n+p, m, 1n+m, hjm, N.lt_succ(m)))

def pop_lay(~A: Data, +ss: List<&2, Maybe<&2, A>>, +m: Nat, +last: A, k: Nat, +hk: {Nat.is_le(k, m) == True{} : Bool}, +hlay: {SL.lay(~A, ss, 1n+m) == True{} : Bool}, +hlen: {Nat.is_lt(0n, SC.length(Maybe<&2, A>, ss)) == True{} : Bool}) -> {SL.lay(~A, hole(~A, ss, m, last), k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      L.and_intro(Maybe.is_some(&2, A, SL.slot(~A, hole(~A, ss, m, last), p)), SL.lay(~A, hole(~A, ss, m, last), p),
        pop_some(~A, ss, m, last, p, N.succ_le_lt(p, m, hk), hlay, hlen),
        pop_lay(~A, ss, m, last, p, N.le_trans(p, 1n+p, m, N.le_succ(p), hk), hlay, hlen))

# ---- the old root is still below the two slots the sift-down compares ----

def pop_kid(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ss: List<&2, Maybe<&2, A>>, +m: Nat, +root: A, +c: Nat, +hm: {Nat.is_lt(0n, m) == True{} : Bool}, +hho: {SL.ho_upto(~A, ~cmp, ss, 1n+m) == True{} : Bool}, +hlay: {SL.lay(~A, ss, 1n+m) == True{} : Bool}, +h0: {SL.slot(~A, ss, 0n) == Some{root} : Maybe<&2, A>}, b: Bool, +eb: {Nat.is_lt(c, m) == b : Bool}) -> {SL.kid_le(~A, ~cmp, ss, m, 0n, c) == True{} : Bool}:
  match b:
    case True{}:
      SL.kid_le_in(~A, ~cmp, ss, m, 0n, c, eb,
        %Equal.sym(Maybe<&2, A>, SL.slot(~A, ss, 0n), Some{root}, h0) : {SL.mle(~A, ~cmp, _, SL.slot(~A, ss, c)) == True{} : Bool}
        RT.root_le(~A, ~cmp, ~o, ss, 1n+m, c, root, c, N.lt_trans(c, m, 1n+m, eb, N.lt_succ(m)), N.le_refl(c), hho, hlay, h0))
    case False{}:
      SL.kid_le_out(~A, ~cmp, ss, m, 0n, c, eb)

def pop_kids(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ss: List<&2, Maybe<&2, A>>, +m: Nat, +root: A, +hm: {Nat.is_lt(0n, m) == True{} : Bool}, +hho: {SL.ho_upto(~A, ~cmp, ss, 1n+m) == True{} : Bool}, +hlay: {SL.lay(~A, ss, 1n+m) == True{} : Bool}, +h0: {SL.slot(~A, ss, 0n) == Some{root} : Maybe<&2, A>}) -> {SL.kids_le(~A, ~cmp, ss, m, IX.par(0n), 0n) == True{} : Bool}:
  L.and_intro(SL.kid_le(~A, ~cmp, ss, m, 0n, IX.kidl(0n)), SL.kid_le(~A, ~cmp, ss, m, 0n, IX.kidr(0n)),
    pop_kid(~A, ~cmp, ~o, ss, m, root, IX.kidl(0n), hm, hho, hlay, h0, Nat.is_lt(IX.kidl(0n), m), {==}),
    pop_kid(~A, ~cmp, ~o, ss, m, root, IX.kidr(0n), hm, hho, hlay, h0, Nat.is_lt(IX.kidr(0n), m), {==}))

# ---- the multiset loses exactly the root ----

def pop_ms(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ss: List<&2, Maybe<&2, A>>, +m: Nat, +root: A, +last: A, +hm: {Nat.is_lt(0n, m) == True{} : Bool}, +h0: {SL.slot(~A, ss, 0n) == Some{root} : Maybe<&2, A>}, +hlast: {SL.slot(~A, ss, m) == Some{last} : Maybe<&2, A>}) -> {V.msort(~A, ~cmp, V.vals(~A, ss, 1n+m)) == S.ins(~A, ~cmp, root, V.msort(~A, ~cmp, V.vals(~A, hole(~A, ss, m, last), m))) : List<&2, A>}:
  Equal.trans(List<&2, A>, V.msort(~A, ~cmp, V.vals(~A, ss, 1n+m)), S.ins(~A, ~cmp, last, V.msort(~A, ~cmp, V.vals(~A, ss, m))), S.ins(~A, ~cmp, root, V.msort(~A, ~cmp, V.vals(~A, hole(~A, ss, m, last), m))),
    Equal.cong(Maybe<&2, A>, List<&2, A>, ms => V.msort(~A, ~cmp, V.cons_slot(~A, ms, V.vals(~A, ss, m))), SL.slot(~A, ss, m), Some{last}, hlast),
    Equal.sym(List<&2, A>, S.ins(~A, ~cmp, root, V.msort(~A, ~cmp, V.vals(~A, hole(~A, ss, m, last), m))), S.ins(~A, ~cmp, last, V.msort(~A, ~cmp, V.vals(~A, ss, m))),
      V.ins_set(~A, ~cmp, ~o, ss, m, 0n, root, last, hm, h0, Nat.is_eq(0n, N.pred(m)), {==})))

# ---- the old root is still the minimum of what is left ----

def pop_low_at(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ss: List<&2, Maybe<&2, A>>, +m: Nat, +root: A, +last: A, j: Nat, +hjm: {Nat.is_lt(j, m) == True{} : Bool}, +hho: {SL.ho_upto(~A, ~cmp, ss, 1n+m) == True{} : Bool}, +hlay: {SL.lay(~A, ss, 1n+m) == True{} : Bool}, +h0: {SL.slot(~A, ss, 0n) == Some{root} : Maybe<&2, A>}, +hlast: {SL.slot(~A, ss, m) == Some{last} : Maybe<&2, A>}, +hlen: {Nat.is_lt(0n, SC.length(Maybe<&2, A>, ss)) == True{} : Bool}) -> {SL.mle(~A, ~cmp, Some{root}, SL.slot(~A, hole(~A, ss, m, last), j)) == True{} : Bool}:
  match j:
    case 0n:
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, hole(~A, ss, m, last), 0n), Some{last}, hole_at0(~A, ss, m, last, hlen)) : {SL.mle(~A, ~cmp, Some{root}, _) == True{} : Bool}
      %hlast : {SL.mle(~A, ~cmp, Some{root}, _) == True{} : Bool}
      RT.root_le(~A, ~cmp, ~o, ss, 1n+m, m, root, m, N.lt_succ(m), N.le_refl(m), hho, hlay, h0)
    case 1n+ +p:
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, hole(~A, ss, m, last), 1n+p), SL.slot(~A, ss, 1n+p), hole_off(~A, ss, m, last, 1n+p, {==})) : {SL.mle(~A, ~cmp, Some{root}, _) == True{} : Bool}
      RT.root_le(~A, ~cmp, ~o, ss, 1n+m, 1n+p, root, 1n+p, N.lt_trans(1n+p, m, 1n+m, hjm, N.lt_succ(m)), N.le_refl(1n+p), hho, hlay, h0)

def pop_low(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ss: List<&2, Maybe<&2, A>>, +m: Nat, +root: A, +last: A, k: Nat, +hk: {Nat.is_le(k, m) == True{} : Bool}, +hho: {SL.ho_upto(~A, ~cmp, ss, 1n+m) == True{} : Bool}, +hlay: {SL.lay(~A, ss, 1n+m) == True{} : Bool}, +h0: {SL.slot(~A, ss, 0n) == Some{root} : Maybe<&2, A>}, +hlast: {SL.slot(~A, ss, m) == Some{last} : Maybe<&2, A>}, +hlen: {Nat.is_lt(0n, SC.length(Maybe<&2, A>, ss)) == True{} : Bool}) -> {RT.low_all(~A, ~cmp, hole(~A, ss, m, last), k, root) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      L.and_intro(SL.mle(~A, ~cmp, Some{root}, SL.slot(~A, hole(~A, ss, m, last), p)), RT.low_all(~A, ~cmp, hole(~A, ss, m, last), p, root),
        pop_low_at(~A, ~cmp, ~o, ss, m, root, last, p, N.succ_le_lt(p, m, hk), hho, hlay, h0, hlast, hlen),
        pop_low(~A, ~cmp, ~o, ss, m, root, last, p, N.le_trans(p, 1n+p, m, N.le_succ(p), hk), hho, hlay, h0, hlast, hlen))

# The observation of a pop: the multiset of the heap is the old root followed
# by the multiset the sift-down is given as its target.
def pop_split(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ss: List<&2, Maybe<&2, A>>, +m: Nat, +root: A, +last: A, +hm: {Nat.is_lt(0n, m) == True{} : Bool}, +hho: {SL.ho_upto(~A, ~cmp, ss, 1n+m) == True{} : Bool}, +hlay: {SL.lay(~A, ss, 1n+m) == True{} : Bool}, +h0: {SL.slot(~A, ss, 0n) == Some{root} : Maybe<&2, A>}, +hlast: {SL.slot(~A, ss, m) == Some{last} : Maybe<&2, A>}, +hlen: {Nat.is_lt(0n, SC.length(Maybe<&2, A>, ss)) == True{} : Bool}) -> {V.msort(~A, ~cmp, V.vals(~A, ss, 1n+m)) == Con{root, V.msort(~A, ~cmp, V.vals(~A, hole(~A, ss, m, last), m))} : List<&2, A>}:
  Equal.trans(List<&2, A>, V.msort(~A, ~cmp, V.vals(~A, ss, 1n+m)), S.ins(~A, ~cmp, root, V.msort(~A, ~cmp, V.vals(~A, hole(~A, ss, m, last), m))), Con{root, V.msort(~A, ~cmp, V.vals(~A, hole(~A, ss, m, last), m))},
    pop_ms(~A, ~cmp, ~o, ss, m, root, last, hm, h0, hlast),
    RT.front(~A, ~cmp, ~o, hole(~A, ss, m, last), m, root, pop_low(~A, ~cmp, ~o, ss, m, root, last, m, N.le_refl(m), hho, hlay, h0, hlast, hlen)))

# ---- what the implementation computes ----

def round_lt(+m: Nat, +d: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hm: {Nat.is_lt(m, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(U32.from_nat(m)), SC.pow2(d)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, m, U32.to_nat(U32.from_nat(m)), Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, UX.nat_round(m, d, N.lt_le(d, 32n, hd), hm)), hm)

def round_nth(~A: Data, +t: AR.Tree<Maybe<&2, A>>, +m: Nat, +d: Nat, +v: A, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hm: {Nat.is_lt(m, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), m) == Some{v} : Maybe<&2, A>}) -> {SC.nth(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), U32.to_nat(U32.from_nat(m))) == Some{Some{v}} : Maybe<&2, Maybe<&2, A>>}:
  L.subst(Nat, z => {SC.nth(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), z) == Some{Some{v}} : Maybe<&2, Maybe<&2, A>>}, m, U32.to_nat(U32.from_nat(m)), Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, UX.nat_round(m, d, N.lt_le(d, 32n, hd), hm)),
    V.nth_of_slot(~A, AR.slots(Maybe<&2, A>, t), m, v, hv))

# the last element is read, not cleared
def get_last(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +m: Nat, +last: A, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hm: {Nat.is_lt(m, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hlast: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), m) == Some{last} : Maybe<&2, A>}) -> {Array.get(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), U32.from_nat(m)) == (AR.thaw(Maybe<&2, A>, t), Some{last}) : Array<Maybe<&2, A>> & Maybe<&2, A>}:
  AR.get(Maybe<&2, A>, d, t, U32.from_nat(m), Some{last}, hd, round_lt(m, d, hd, hm), round_nth(~A, t, m, d, last, hd, hm, pf, hlast), pf)

def get_root(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +root: A, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +h0: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), 0n) == Some{root} : Maybe<&2, A>}) -> {Array.get(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), 0) == (AR.thaw(Maybe<&2, A>, t), Some{root}) : Array<Maybe<&2, A>> & Maybe<&2, A>}:
  AR.get(Maybe<&2, A>, d, t, 0, Some{root}, hd, N.succ_le_lt(0n, SC.pow2(d), N.pow2_pos(d)), V.nth_of_slot(~A, AR.slots(Maybe<&2, A>, t), 0n, root, h0), pf)

# The pop of a nonempty heap, reduced to the move that follows reading the
# last element. Each step is an explicit substitution rather than a rewrite
# annotation: the goal is normalised between steps, so naming the redex is
# the only robust way to transport it.
def pop_to_move(~A: Data, ~cmp: A -> A -> Cmp, +depth: Nat, +m: Nat, +t: AR.Tree<Maybe<&2, A>>, +root: A, +last: A, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, depth, t) == True{} : Bool}, +hs: {Nat.is_le(1n+m, SC.pow2(depth)) == True{} : Bool}, +h0: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), 0n) == Some{root} : Maybe<&2, A>}, +hlast: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), m) == Some{last} : Maybe<&2, A>}) -> {H.pop(~A, ~cmp, ST.real(~A, ST.Sh{1n+m, depth, t})) == H.pop_move(~A, ~cmp, m, U32.from_nat(m), depth, U.pow2u(depth), root, last, AR.thaw(Maybe<&2, A>, t), U32.is_eq(U32.from_nat(m), 0)) : H.Heap<A> & Result<&2, &2, E.Error, A>}:
  +hd32 = ST.depth_lt32(depth, hd)
  +hmp = N.succ_le_lt(m, SC.pow2(depth), hs)
  +hsp = N.le_lt_trans(1n+m, SC.pow2(depth), SC.pow2(1n+depth), hs, N.pow2_lt_succ(depth))
  L.subst(Array<Maybe<&2, A>> & Maybe<&2, A>, r => {H.pop(~A, ~cmp, ST.real(~A, ST.Sh{1n+m, depth, t})) == H.pop_last(~A, ~cmp, m, U32.from_nat(m), depth, U.pow2u(depth), root, r) : H.Heap<A> & Result<&2, &2, E.Error, A>},
    Array.get(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), U32.from_nat(m)), (AR.thaw(Maybe<&2, A>, t), Some{last}),
    get_last(~A, depth, t, m, last, hd32, hmp, pf, hlast),
    L.subst(Nat, k => {H.pop(~A, ~cmp, ST.real(~A, ST.Sh{1n+m, depth, t})) == H.pop_last(~A, ~cmp, k, U32.from_nat(m), depth, U.pow2u(depth), root, Array.get(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), U32.from_nat(m))) : H.Heap<A> & Result<&2, &2, E.Error, A>},
      Nat.sub(1n+m, 1n), m, N.sub_zero(m),
      L.subst(U32, i => {H.pop(~A, ~cmp, ST.real(~A, ST.Sh{1n+m, depth, t})) == H.pop_last(~A, ~cmp, Nat.sub(1n+m, 1n), i, depth, U.pow2u(depth), root, Array.get(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), i)) : H.Heap<A> & Result<&2, &2, E.Error, A>},
        U32.sub(U32.from_nat(1n+m), 1), U32.from_nat(m),
        Equal.trans(U32, U32.sub(U32.from_nat(1n+m), 1), U32.from_nat(Nat.sub(1n+m, 1n)), U32.from_nat(m), UX.sub_one(1n+m, 1n+depth, hd, hsp, N.zero_le(m)), Equal.cong(Nat, U32, z => U32.from_nat(z), Nat.sub(1n+m, 1n), m, N.sub_zero(m))),
        L.subst(Array<Maybe<&2, A>> & Maybe<&2, A>, r => {H.pop(~A, ~cmp, ST.real(~A, ST.Sh{1n+m, depth, t})) == H.pop_root(~A, ~cmp, 1n+m, U32.from_nat(1n+m), depth, U.pow2u(depth), r) : H.Heap<A> & Result<&2, &2, E.Error, A>},
          Array.get(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), 0), (AR.thaw(Maybe<&2, A>, t), Some{root}),
          get_root(~A, depth, t, root, hd32, pf, h0),
          L.subst(Bool, b => {H.pop(~A, ~cmp, ST.real(~A, ST.Sh{1n+m, depth, t})) == H.pop_go(~A, ~cmp, 1n+m, U32.from_nat(1n+m), depth, U.pow2u(depth), AR.thaw(Maybe<&2, A>, t), b) : H.Heap<A> & Result<&2, &2, E.Error, A>},
            U32.is_eq(U32.from_nat(1n+m), U32.from_nat(0n)), Nat.is_eq(1n+m, 0n),
            UX.eq_bridge(1n+m, 0n, 1n+depth, hd, hsp, N.lt_le_trans(0n, SC.pow2(depth), SC.pow2(1n+depth), N.succ_le_lt(0n, SC.pow2(depth), N.pow2_pos(depth)), N.lt_le(SC.pow2(depth), SC.pow2(1n+depth), N.pow2_lt_succ(depth)))),
            {==})))))

# ---- the sift-down that follows the swap ----

def pop_sift(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +depth: Nat, +m: Nat, +t: AR.Tree<Maybe<&2, A>>, +root: A, +last: A, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, depth, t) == True{} : Bool}, +hs: {Nat.is_le(1n+m, SC.pow2(depth)) == True{} : Bool}, +hho: {SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), 1n+m) == True{} : Bool}, +hlay: {SL.lay(~A, AR.slots(Maybe<&2, A>, t), 1n+m) == True{} : Bool}, +h0: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), 0n) == Some{root} : Maybe<&2, A>}, +hlast: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), m) == Some{last} : Maybe<&2, A>}, +hm: {Nat.is_lt(0n, m) == True{} : Bool}) -> DN.SiftDownOK(~A, ~cmp, depth, m, V.msort(~A, ~cmp, V.vals(~A, hole(~A, AR.slots(Maybe<&2, A>, t), m, last), m)), depth, t, 0n, last):
  +ss = AR.slots(Maybe<&2, A>, t)
  +hmp = N.succ_le_lt(m, SC.pow2(depth), hs)
  +hlen = N.lt_le_trans(0n, m, SC.length(Maybe<&2, A>, ss), hm, N.lt_le(m, SC.length(Maybe<&2, A>, ss), L.subst(Nat, z => {Nat.is_lt(m, z) == True{} : Bool}, SC.pow2(depth), SC.length(Maybe<&2, A>, ss), Equal.sym(Nat, SC.length(Maybe<&2, A>, ss), SC.pow2(depth), AR.slots_length(Maybe<&2, A>, depth, t, pf)), hmp)))
  DN.sift_down_ok(~A, ~cmp, ~o, depth, depth, m, V.msort(~A, ~cmp, V.vals(~A, hole(~A, ss, m, last), m)), t, 0n, last,
    ST.depth_lt32(depth, hd),
    N.succ_le_lt(0n, SC.pow2(depth), N.pow2_pos(depth)),
    hm,
    N.lt_le(m, SC.pow2(depth), hmp),
    L.subst(Nat, z => {Nat.is_le(m, z) == True{} : Bool}, SC.pow2(depth), IX.scale(depth, 1n), Equal.sym(Nat, IX.scale(depth, 1n), SC.pow2(depth), scale_one(depth)), N.lt_le(m, SC.pow2(depth), hmp)),
    pf,
    pop_exc(~A, ~cmp, ss, m, last, m, N.le_refl(m), hho),
    {==},
    pop_kids(~A, ~cmp, ~o, ss, m, root, hm, hho, hlay, h0),
    pop_lay(~A, ss, m, last, m, N.le_refl(m), hlay, hlen),
    {==})

# ---- pop, as a step on shadows ----

def PopRes(~A: Data, ~cmp: A -> A -> Cmp, sh: ST.Shadow<A>) -> Type:
  Sigma<&1, &1, ST.Shadow<A>, sh2 => Sigma<&1, &1, Result<&2, &2, E.Error, A>, r => {H.pop(~A, ~cmp, ST.real(~A, sh)) == (ST.real(~A, sh2), r) : H.Heap<A> & Result<&2, &2, E.Error, A>} & ({ST.good(~A, ~cmp, sh2) == True{} : Bool} & ({(ST.model(~A, ~cmp, sh2), E.OItem{r}) == S.pop(A, ST.model(~A, ~cmp, sh)) : List<&2, A> & E.Obs<A>} & {ST.sh_depth(~A, sh2) == ST.sh_depth(~A, sh) : Nat}))>>

def pop_from(~A: Data, ~cmp: A -> A -> Cmp, +depth: Nat, +m: Nat, +t: AR.Tree<Maybe<&2, A>>, +root: A, +last: A, +tgt: List<&2, A>, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hs: {Nat.is_le(1n+m, SC.pow2(depth)) == True{} : Bool}, +eq0: {H.pop(~A, ~cmp, ST.real(~A, ST.Sh{1n+m, depth, t})) == H.pop_move(~A, ~cmp, m, U32.from_nat(m), depth, U.pow2u(depth), root, last, AR.thaw(Maybe<&2, A>, t), False{}) : H.Heap<A> & Result<&2, &2, E.Error, A>}, +hsplit: {ST.model(~A, ~cmp, ST.Sh{1n+m, depth, t}) == Con{root, tgt} : List<&2, A>}, r: DN.SiftDownOK(~A, ~cmp, depth, m, tgt, depth, t, 0n, last)) -> PopRes(~A, ~cmp, ST.Sh{1n+m, depth, t}):
  match r:
    case Tuple{+t3, Tuple{esift, Tuple{pf3, Tuple{hho3, Tuple{hlay3, hms3}}}}}:
      (ST.Sh{m, depth, t3},
       (Done{root},
        (Equal.trans(H.Heap<A> & Result<&2, &2, E.Error, A>, H.pop(~A, ~cmp, ST.real(~A, ST.Sh{1n+m, depth, t})), H.pop_move(~A, ~cmp, m, U32.from_nat(m), depth, U.pow2u(depth), root, last, AR.thaw(Maybe<&2, A>, t), False{}), (ST.real(~A, ST.Sh{m, depth, t3}), Done{root}), eq0,
           Equal.cong(Array<Maybe<&2, A>>, H.Heap<A> & Result<&2, &2, E.Error, A>, a => (H.BH{m, U32.from_nat(m), depth, U.pow2u(depth), a}, Done{root}), H.sift_down(~A, ~cmp, depth, U32.from_nat(m), U32.from_nat(0n), last, AR.thaw(Maybe<&2, A>, t)), AR.thaw(Maybe<&2, A>, t3), esift)),
         (ST.good_intro(~A, ~cmp, m, depth, t3, hd, pf3, hlay3, hho3, N.le_trans(m, 1n+m, SC.pow2(depth), N.le_succ(m), hs)),
          (%Equal.sym(List<&2, A>, ST.model(~A, ~cmp, ST.Sh{1n+m, depth, t}), Con{root, tgt}, hsplit) : {(ST.model(~A, ~cmp, ST.Sh{m, depth, t3}), E.OItem{Done{root}}) == S.pop(A, _) : List<&2, A> & E.Obs<A>}
           Equal.cong(List<&2, A>, List<&2, A> & E.Obs<A>, zs => (zs, E.OItem{Done{root}}), ST.model(~A, ~cmp, ST.Sh{m, depth, t3}), tgt, hms3),
           {==})))))

def pop_nonempty(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +depth: Nat, m: Nat, +t: AR.Tree<Maybe<&2, A>>, +root: A, +last: A, +g: {ST.good(~A, ~cmp, ST.Sh{1n+m, depth, t}) == True{} : Bool}, +h0: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), 0n) == Some{root} : Maybe<&2, A>}, +hlast: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), m) == Some{last} : Maybe<&2, A>}) -> PopRes(~A, ~cmp, ST.Sh{1n+m, depth, t}):
  match m:
    case 0n:
      (ST.Sh{0n, depth, t},
       (Done{root},
        (pop_to_move(~A, ~cmp, depth, 0n, t, root, last, ST.g_depth(~A, ~cmp, 1n, depth, t, g), ST.g_perfect(~A, ~cmp, 1n, depth, t, g), ST.g_size(~A, ~cmp, 1n, depth, t, g), h0, hlast),
         (ST.good_intro(~A, ~cmp, 0n, depth, t, ST.g_depth(~A, ~cmp, 1n, depth, t, g), ST.g_perfect(~A, ~cmp, 1n, depth, t, g), {==}, {==}, N.zero_le(SC.pow2(depth))),
          (%Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), 0n), Some{root}, h0) : {(Nil{}, E.OItem{Done{root}}) == S.pop(A, V.msort(~A, ~cmp, V.cons_slot(~A, _, Nil{}))) : List<&2, A> & E.Obs<A>}
           {==},
           {==})))))
    case 1n+ +k:
      +hd = ST.g_depth(~A, ~cmp, 2n+k, depth, t, g)
      +pf = ST.g_perfect(~A, ~cmp, 2n+k, depth, t, g)
      +hs = ST.g_size(~A, ~cmp, 2n+k, depth, t, g)
      +hho = ST.g_ho(~A, ~cmp, 2n+k, depth, t, g)
      +hlay = ST.g_lay(~A, ~cmp, 2n+k, depth, t, g)
      +ss = AR.slots(Maybe<&2, A>, t)
      +hmp = N.succ_le_lt(1n+k, SC.pow2(depth), hs)
      +hlen = N.lt_le_trans(0n, 1n+k, SC.length(Maybe<&2, A>, ss), {==}, N.lt_le(1n+k, SC.length(Maybe<&2, A>, ss), L.subst(Nat, z => {Nat.is_lt(1n+k, z) == True{} : Bool}, SC.pow2(depth), SC.length(Maybe<&2, A>, ss), Equal.sym(Nat, SC.length(Maybe<&2, A>, ss), SC.pow2(depth), AR.slots_length(Maybe<&2, A>, depth, t, pf)), hmp)))
      +hsp = N.le_lt_trans(2n+k, SC.pow2(depth), SC.pow2(1n+depth), hs, N.pow2_lt_succ(depth))
      pop_from(~A, ~cmp, depth, 1n+k, t, root, last, V.msort(~A, ~cmp, V.vals(~A, hole(~A, ss, 1n+k, last), 1n+k)), hd, hs,
        L.subst(Bool, bb => {H.pop(~A, ~cmp, ST.real(~A, ST.Sh{2n+k, depth, t})) == H.pop_move(~A, ~cmp, 1n+k, U32.from_nat(1n+k), depth, U.pow2u(depth), root, last, AR.thaw(Maybe<&2, A>, t), bb) : H.Heap<A> & Result<&2, &2, E.Error, A>},
          U32.is_eq(U32.from_nat(1n+k), U32.from_nat(0n)), False{},
          UX.eq_bridge(1n+k, 0n, 1n+depth, hd, N.lt_trans(1n+k, 2n+k, SC.pow2(1n+depth), N.lt_succ(1n+k), hsp), N.lt_le_trans(0n, SC.pow2(depth), SC.pow2(1n+depth), N.succ_le_lt(0n, SC.pow2(depth), N.pow2_pos(depth)), N.lt_le(SC.pow2(depth), SC.pow2(1n+depth), N.pow2_lt_succ(depth)))),
          pop_to_move(~A, ~cmp, depth, 1n+k, t, root, last, hd, pf, hs, h0, hlast)),
        pop_split(~A, ~cmp, ~o, ss, 1n+k, root, last, {==}, hho, hlay, h0, hlast, hlen),
        pop_sift(~A, ~cmp, ~o, depth, 1n+k, t, root, last, hd, pf, hs, hho, hlay, h0, hlast, {==}))

def pop_with_last(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +depth: Nat, +m: Nat, +t: AR.Tree<Maybe<&2, A>>, +root: A, +g: {ST.good(~A, ~cmp, ST.Sh{1n+m, depth, t}) == True{} : Bool}, +h0: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), 0n) == Some{root} : Maybe<&2, A>}, sig: Sigma<&1, &1, A, v => {SL.slot(~A, AR.slots(Maybe<&2, A>, t), m) == Some{v} : Maybe<&2, A>}>) -> PopRes(~A, ~cmp, ST.Sh{1n+m, depth, t}):
  match sig:
    case Tuple{+last, +hlast}:
      pop_nonempty(~A, ~cmp, ~o, depth, m, t, root, last, g, h0, hlast)

def pop_with_root(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +depth: Nat, +m: Nat, +t: AR.Tree<Maybe<&2, A>>, +g: {ST.good(~A, ~cmp, ST.Sh{1n+m, depth, t}) == True{} : Bool}, sig: Sigma<&1, &1, A, v => {SL.slot(~A, AR.slots(Maybe<&2, A>, t), 0n) == Some{v} : Maybe<&2, A>}>) -> PopRes(~A, ~cmp, ST.Sh{1n+m, depth, t}):
  match sig:
    case Tuple{+root, +h0}:
      pop_with_last(~A, ~cmp, ~o, depth, m, t, root, g, h0,
        SL.slot_some(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), m), SL.lay_at(~A, AR.slots(Maybe<&2, A>, t), 1n+m, m, ST.g_lay(~A, ~cmp, 1n+m, depth, t, g), N.lt_succ(m))))

def pop_ok(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +g: {ST.good(~A, ~cmp, ST.Sh{size, depth, t}) == True{} : Bool}) -> PopRes(~A, ~cmp, ST.Sh{size, depth, t}):
  match size:
    case 0n:
      (ST.Sh{0n, depth, t}, (Fail{E.EmptyHeap{}}, ({==}, (g, ({==}, {==})))))
    case 1n+ +m:
      pop_with_root(~A, ~cmp, ~o, depth, m, t, g,
        SL.slot_some(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), 0n), SL.lay_at(~A, AR.slots(Maybe<&2, A>, t), 1n+m, 0n, ST.g_lay(~A, ~cmp, 1n+m, depth, t, g), N.succ_le_lt(0n, 1n+m, N.zero_le(m)))))
