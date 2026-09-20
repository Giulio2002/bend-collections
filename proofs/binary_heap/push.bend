import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../spec/binary_heap.bend as S
import ../../src/binary_heap.bend as H
import ../../types/binary_heap.bend as E
import ./idx.bend as IX
import ./u32idx.bend as UX
import ./slots.bend as SL
import ./vals.bend as V
import ./root.bend as RT
import ./up.bend as UPS
import ./grow.bend as GR
import ./state.bend as ST

# push: the element is written at slot `size` and sifted up. The four
# hypotheses of the sift-up law hold at a fresh leaf:
#   ho_exc   every pair except the one into the new slot holds already,
#   kids_le  the new slot has no children inside the heap,
#   lay      the slots below `size` are untouched and slot `size` is now full,
#   msort    the multiset gains exactly x.
# If the block is full it is doubled first (grow.bend: nothing but the
# capacity changes).

# ---- the pairs below the new leaf are untouched ----

def pair_off(~A: Data, ~cmp: A -> A -> Cmp, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, m: Nat, +hmi: {Nat.is_lt(m, i) == True{} : Bool}, +h: {SL.pair_ok(~A, ~cmp, AR.slots(Maybe<&2, A>, t), m) == True{} : Bool}) -> {SL.pair_ok(~A, ~cmp, UPS.ulog(~A, t, i, x), m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+ +p:
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, UPS.ulog(~A, t, i, x), 1n+p), SL.slot(~A, AR.slots(Maybe<&2, A>, t), 1n+p), UPS.ulog_off(~A, t, i, x, 1n+p, SL.ne_sym(i, 1n+p, N.is_eq_lt(1n+p, i, hmi)))) : {SL.mle(~A, ~cmp, SL.slot(~A, UPS.ulog(~A, t, i, x), IX.par(1n+p)), _) == True{} : Bool}
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, UPS.ulog(~A, t, i, x), IX.par(1n+p)), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(1n+p)), UPS.ulog_off(~A, t, i, x, IX.par(1n+p), SL.ne_sym(i, IX.par(1n+p), N.is_eq_lt(IX.par(1n+p), i, N.lt_trans(IX.par(1n+p), 1n+p, i, IX.par_lt(1n+p, {==}), hmi))))) : {SL.mle(~A, ~cmp, _, SL.slot(~A, AR.slots(Maybe<&2, A>, t), 1n+p)) == True{} : Bool}
      h

def exc_step(~A: Data, ~cmp: A -> A -> Cmp, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +m: Nat, +hm: {Nat.is_lt(m, 1n+i) == True{} : Bool}, +hho: {SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), i) == True{} : Bool}, b: Bool, +eb: {Nat.is_eq(m, i) == b : Bool}) -> {SL.pair_skip(~A, ~cmp, UPS.ulog(~A, t, i, x), m, i) == True{} : Bool}:
  match b:
    case True{}:
      SL.skip_eq(~A, ~cmp, UPS.ulog(~A, t, i, x), m, i, eb)
    case False{}:
      +hmi = N.lt_or_eq(m, i, N.lt_succ_le(m, i, hm), eb)
      SL.skip_ne(~A, ~cmp, UPS.ulog(~A, t, i, x), m, i, eb,
        pair_off(~A, ~cmp, t, i, x, m, hmi, SL.ho_at(~A, ~cmp, AR.slots(Maybe<&2, A>, t), i, m, hho, hmi)))

def exc_up(~A: Data, ~cmp: A -> A -> Cmp, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, k: Nat, +hk: {Nat.is_le(k, 1n+i) == True{} : Bool}, +hho: {SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), i) == True{} : Bool}) -> {SL.ho_exc(~A, ~cmp, UPS.ulog(~A, t, i, x), k, i) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +m:
      L.and_intro(SL.pair_skip(~A, ~cmp, UPS.ulog(~A, t, i, x), m, i), SL.ho_exc(~A, ~cmp, UPS.ulog(~A, t, i, x), m, i),
        exc_step(~A, ~cmp, t, i, x, m, N.succ_le_lt(m, 1n+i, hk), hho, Nat.is_eq(m, i), {==}),
        exc_up(~A, ~cmp, t, i, x, m, N.le_trans(m, 1n+m, 1n+i, N.le_succ(m), hk), hho))

# ---- the new leaf has no children inside the heap ----

def kids_leaf(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +u: Nat, +i: Nat) -> {SL.kids_le(~A, ~cmp, ss, 1n+i, u, i) == True{} : Bool}:
  L.and_intro(SL.kid_le(~A, ~cmp, ss, 1n+i, u, IX.kidl(i)), SL.kid_le(~A, ~cmp, ss, 1n+i, u, IX.kidr(i)),
    SL.kid_le_out(~A, ~cmp, ss, 1n+i, u, IX.kidl(i), N.le_not_lt(IX.kidl(i), 1n+i, IX.double_le(i))),
    SL.kid_le_out(~A, ~cmp, ss, 1n+i, u, IX.kidr(i), N.le_not_lt(IX.kidr(i), 1n+i, N.le_trans(1n+i, IX.kidl(i), IX.kidr(i), IX.double_le(i), N.le_succ(IX.kidl(i))))))

# ---- the layout below the new leaf is untouched ----

def lay_off(~A: Data, +ss: List<&2, Maybe<&2, A>>, +i: Nat, +v: Maybe<&2, A>, k: Nat, +hk: {Nat.is_le(k, i) == True{} : Bool}, +h: {SL.lay(~A, ss, k) == True{} : Bool}) -> {SL.lay(~A, SC.update(Maybe<&2, A>, ss, i, v), k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +m:
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, SC.update(Maybe<&2, A>, ss, i, v), m), SL.slot(~A, ss, m), SL.slot_other(~A, ss, i, m, v, SL.ne_sym(i, m, N.is_eq_lt(m, i, N.succ_le_lt(m, i, hk))))) : {Bool.and(Maybe.is_some(&2, A, _), SL.lay(~A, SC.update(Maybe<&2, A>, ss, i, v), m)) == True{} : Bool}
      L.and_intro(Maybe.is_some(&2, A, SL.slot(~A, ss, m)), SL.lay(~A, SC.update(Maybe<&2, A>, ss, i, v), m),
        L.and_left(Maybe.is_some(&2, A, SL.slot(~A, ss, m)), SL.lay(~A, ss, m), h),
        lay_off(~A, ss, i, v, m, N.lt_le(m, i, N.succ_le_lt(m, i, hk)), L.and_right(Maybe.is_some(&2, A, SL.slot(~A, ss, m)), SL.lay(~A, ss, m), h)))

def lay_push(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +h: {SL.lay(~A, AR.slots(Maybe<&2, A>, t), i) == True{} : Bool}) -> {SL.lay(~A, UPS.ulog(~A, t, i, x), 1n+i) == True{} : Bool}:
  L.and_intro(Maybe.is_some(&2, A, SL.slot(~A, UPS.ulog(~A, t, i, x), i)), SL.lay(~A, UPS.ulog(~A, t, i, x), i),
    L.subst(Maybe<&2, A>, z => {Maybe.is_some(&2, A, z) == True{} : Bool}, Some{x}, SL.slot(~A, UPS.ulog(~A, t, i, x), i), Equal.sym(Maybe<&2, A>, SL.slot(~A, UPS.ulog(~A, t, i, x), i), Some{x}, UPS.ulog_at(~A, d, t, i, x, hi, pf)), {==}),
    lay_off(~A, AR.slots(Maybe<&2, A>, t), i, Some{x}, i, N.le_refl(i), h))

# ---- the multiset gains exactly x ----

def ms_push(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {V.msort(~A, ~cmp, V.vals(~A, UPS.ulog(~A, t, i, x), 1n+i)) == S.ins(~A, ~cmp, x, V.msort(~A, ~cmp, V.vals(~A, AR.slots(Maybe<&2, A>, t), i))) : List<&2, A>}:
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, UPS.ulog(~A, t, i, x), i), Some{x}, UPS.ulog_at(~A, d, t, i, x, hi, pf)) : {V.msort(~A, ~cmp, V.cons_slot(~A, _, V.vals(~A, UPS.ulog(~A, t, i, x), i))) == S.ins(~A, ~cmp, x, V.msort(~A, ~cmp, V.vals(~A, AR.slots(Maybe<&2, A>, t), i))) : List<&2, A>}
  Equal.cong(List<&2, A>, List<&2, A>, zs => S.ins(~A, ~cmp, x, V.msort(~A, ~cmp, zs)), V.vals(~A, UPS.ulog(~A, t, i, x), i), V.vals(~A, AR.slots(Maybe<&2, A>, t), i), V.vals_above(~A, AR.slots(Maybe<&2, A>, t), i, Some{x}, i, N.le_refl(i)))

# ---- one sift-up at the fresh leaf ----

def PushOK(~A: Data, ~cmp: A -> A -> Cmp, sh: ST.Shadow<A>, x: A) -> Type:
  Sigma<&1, &1, ST.Shadow<A>, sh2 => {H.push(~A, ~cmp, ST.real(~A, sh), x) == ST.real(~A, sh2) : H.Heap<A>} & ({ST.good(~A, ~cmp, sh2) == True{} : Bool} & {ST.model(~A, ~cmp, sh2) == S.ins(~A, ~cmp, x, ST.model(~A, ~cmp, sh)) : List<&2, A>})>

# The sift-up result, packaged as the new shadow. `d` is the depth of the
# block the element is written into (the grown depth if the block was full).
def push_from(~A: Data, ~cmp: A -> A -> Cmp, +size: Nat, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +x: A, +tgt: List<&2, A>, +hd: {Nat.is_le(d, 31n) == True{} : Bool}, +hs: {Nat.is_le(1n+size, SC.pow2(d)) == True{} : Bool}, +eq0: {H.push(~A, ~cmp, ST.real(~A, ST.Sh{size, d, t}), x) == H.BH{1n+size, U32.from_nat(1n+size), d, U.pow2u(d), H.sift_up(~A, ~cmp, d, U32.from_nat(size), x, AR.thaw(Maybe<&2, A>, t))} : H.Heap<A>}, r: UPS.SiftOK(~A, ~cmp, d, 1n+size, tgt, d, t, size, x)) -> Sigma<&1, &1, ST.Shadow<A>, sh2 => {H.push(~A, ~cmp, ST.real(~A, ST.Sh{size, d, t}), x) == ST.real(~A, sh2) : H.Heap<A>} & ({ST.good(~A, ~cmp, sh2) == True{} : Bool} & {ST.model(~A, ~cmp, sh2) == tgt : List<&2, A>})>:
  match r:
    case Tuple{+t2, Tuple{esift, Tuple{pf2, Tuple{hho2, Tuple{hlay2, hms2}}}}}:
      (ST.Sh{1n+size, d, t2},
       (Equal.trans(H.Heap<A>, H.push(~A, ~cmp, ST.real(~A, ST.Sh{size, d, t}), x), H.BH{1n+size, U32.from_nat(1n+size), d, U.pow2u(d), H.sift_up(~A, ~cmp, d, U32.from_nat(size), x, AR.thaw(Maybe<&2, A>, t))}, ST.real(~A, ST.Sh{1n+size, d, t2}), eq0,
          Equal.cong(Array<Maybe<&2, A>>, H.Heap<A>, a => H.BH{1n+size, U32.from_nat(1n+size), d, U.pow2u(d), a}, H.sift_up(~A, ~cmp, d, U32.from_nat(size), x, AR.thaw(Maybe<&2, A>, t)), AR.thaw(Maybe<&2, A>, t2), esift)),
        (ST.good_intro(~A, ~cmp, 1n+size, d, t2, hd, pf2, hlay2, hho2, hs),
         hms2)))

# ---- the capacity decision, in Nat ----

def room_bridge(+size: Nat, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hs: {Nat.is_le(size, SC.pow2(depth)) == True{} : Bool}) -> {U32.is_lt(U32.from_nat(size), U.pow2u(depth)) == Nat.is_lt(size, SC.pow2(depth)) : Bool}:
  +hk = N.le_lt_trans(size, SC.pow2(depth), SC.pow2(1n+depth), hs, N.pow2_lt_succ(depth))
  Equal.sym(Bool, Nat.is_lt(size, SC.pow2(depth)), U32.is_lt(U32.from_nat(size), U.pow2u(depth)),
    %UX.nat_round(size, 1n+depth, hd, hk) : {Nat.is_lt(_, SC.pow2(depth)) == U32.is_lt(U32.from_nat(size), U.pow2u(depth)) : Bool}
    AR.lt_bridge(U32.from_nat(size), depth, ST.depth_lt32(depth, hd), U32.is_lt(U32.from_nat(size), U.pow2u(depth)), {==}))

def succ_le_double(+p: Nat, +h: {Nat.is_le(1n, p) == True{} : Bool}) -> {Nat.is_le(1n+p, Nat.double(p)) == True{} : Bool}:
  match p:
    case 0n:
      Empty.absurd({Nat.is_le(1n, Nat.double(0n)) == True{} : Bool}, L.true_not_false(Nat.is_le(1n, 0n), h, {==}))
    case 1n+ +k:
      IX.double_le(k)

# ---- push into a block with room ----

def push_room_ok(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +x: A, +g: {ST.good(~A, ~cmp, ST.Sh{size, depth, t}) == True{} : Bool}, +hlt: {Nat.is_lt(size, SC.pow2(depth)) == True{} : Bool}) -> PushOK(~A, ~cmp, ST.Sh{size, depth, t}, x):
  +hd = ST.g_depth(~A, ~cmp, size, depth, t, g)
  +pf = ST.g_perfect(~A, ~cmp, size, depth, t, g)
  push_from(~A, ~cmp, size, depth, t, x, S.ins(~A, ~cmp, x, ST.model(~A, ~cmp, ST.Sh{size, depth, t})), hd,
    N.lt_succ_le_succ(size, SC.pow2(depth), hlt),
    %Equal.sym(Bool, U32.is_lt(U32.from_nat(size), U.pow2u(depth)), Nat.is_lt(size, SC.pow2(depth)), room_bridge(size, depth, hd, ST.g_size(~A, ~cmp, size, depth, t, g))) : {H.push_room(~A, ~cmp, size, U32.from_nat(size), depth, U.pow2u(depth), AR.thaw(Maybe<&2, A>, t), x, _) == H.BH{1n+size, U32.from_nat(1n+size), depth, U.pow2u(depth), H.sift_up(~A, ~cmp, depth, U32.from_nat(size), x, AR.thaw(Maybe<&2, A>, t))} : H.Heap<A>}
    %hlt : {H.push_room(~A, ~cmp, size, U32.from_nat(size), depth, U.pow2u(depth), AR.thaw(Maybe<&2, A>, t), x, _) == H.BH{1n+size, U32.from_nat(1n+size), depth, U.pow2u(depth), H.sift_up(~A, ~cmp, depth, U32.from_nat(size), x, AR.thaw(Maybe<&2, A>, t))} : H.Heap<A>}
    {==},
    UPS.sift_up_ok(~A, ~cmp, ~o, depth, depth, 1n+size, S.ins(~A, ~cmp, x, ST.model(~A, ~cmp, ST.Sh{size, depth, t})), t, size, x,
      ST.depth_lt32(depth, hd), hlt, N.lt_succ(size), hlt, pf,
      exc_up(~A, ~cmp, t, size, x, 1n+size, N.le_refl(1n+size), ST.g_ho(~A, ~cmp, size, depth, t, g)),
      kids_leaf(~A, ~cmp, UPS.ulog(~A, t, size, x), IX.par(size), size),
      lay_push(~A, depth, t, size, x, hlt, pf, ST.g_lay(~A, ~cmp, size, depth, t, g)),
      ms_push(~A, ~cmp, depth, t, size, x, hlt, pf)))

# ---- push into a full block: double it first ----

def push_grow_ok(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +x: A, +g: {ST.good(~A, ~cmp, ST.Sh{size, depth, t}) == True{} : Bool}, +hfull: {Nat.is_lt(size, SC.pow2(depth)) == False{} : Bool}, +hroom: {Nat.is_lt(depth, 31n) == True{} : Bool}) -> PushOK(~A, ~cmp, ST.Sh{size, depth, t}, x):
  +hd = ST.g_depth(~A, ~cmp, size, depth, t, g)
  +pf = ST.g_perfect(~A, ~cmp, size, depth, t, g)
  +hs = ST.g_size(~A, ~cmp, size, depth, t, g)
  +t2 = GR.gtree(~A, depth, t)
  +pf2 = GR.gtree_perfect(~A, depth, t, pf)
  +hi2 = N.le_lt_trans(size, SC.pow2(depth), SC.pow2(1n+depth), hs, N.pow2_lt_succ(depth))
  +hs2 = N.le_trans(1n+size, 1n+SC.pow2(depth), SC.pow2(1n+depth), hs, succ_le_double(SC.pow2(depth), N.pow2_pos(depth)))
  push_from(~A, ~cmp, size, 1n+depth, t2, x, S.ins(~A, ~cmp, x, ST.model(~A, ~cmp, ST.Sh{size, depth, t})), N.lt_succ_le_succ(depth, 31n, hroom), hs2,
    %Equal.sym(Array<Maybe<&2, A>>, H.grown(~A, depth, AR.thaw(Maybe<&2, A>, t)), AR.thaw(Maybe<&2, A>, t2), GR.gtree_real(~A, depth, t)) : {H.push_room(~A, ~cmp, size, U32.from_nat(size), depth, U.pow2u(depth), AR.thaw(Maybe<&2, A>, t), x, False{}) == H.BH{1n+size, U32.from_nat(1n+size), 1n+depth, U.pow2u(1n+depth), H.sift_up(~A, ~cmp, 1n+depth, U32.from_nat(size), x, _)} : H.Heap<A>}
    %Equal.sym(Bool, U32.is_lt(U32.from_nat(size), U.pow2u(depth)), Nat.is_lt(size, SC.pow2(depth)), room_bridge(size, depth, hd, hs)) : {H.push_room(~A, ~cmp, size, U32.from_nat(size), depth, U.pow2u(depth), AR.thaw(Maybe<&2, A>, t), x, _) == H.BH{1n+size, U32.from_nat(1n+size), 1n+depth, U.pow2u(1n+depth), H.sift_up(~A, ~cmp, 1n+depth, U32.from_nat(size), x, H.grown(~A, depth, AR.thaw(Maybe<&2, A>, t)))} : H.Heap<A>}
    %hfull : {H.push_room(~A, ~cmp, size, U32.from_nat(size), depth, U.pow2u(depth), AR.thaw(Maybe<&2, A>, t), x, _) == H.BH{1n+size, U32.from_nat(1n+size), 1n+depth, U.pow2u(1n+depth), H.sift_up(~A, ~cmp, 1n+depth, U32.from_nat(size), x, H.grown(~A, depth, AR.thaw(Maybe<&2, A>, t)))} : H.Heap<A>}
    {==},
    L.subst(List<&2, A>, zs => UPS.SiftOK(~A, ~cmp, 1n+depth, 1n+size, S.ins(~A, ~cmp, x, V.msort(~A, ~cmp, zs)), 1n+depth, t2, size, x), V.vals(~A, AR.slots(Maybe<&2, A>, t2), size), V.vals(~A, AR.slots(Maybe<&2, A>, t), size), GR.gtree_vals(~A, depth, t, size, pf, hs),
      UPS.sift_up_ok(~A, ~cmp, ~o, 1n+depth, 1n+depth, 1n+size, S.ins(~A, ~cmp, x, V.msort(~A, ~cmp, V.vals(~A, AR.slots(Maybe<&2, A>, t2), size))), t2, size, x,
        ST.depth_lt32(1n+depth, N.lt_succ_le_succ(depth, 31n, hroom)), hi2, N.lt_succ(size), hi2, pf2,
        exc_up(~A, ~cmp, t2, size, x, 1n+size, N.le_refl(1n+size), GR.gtree_ho(~A, ~cmp, depth, t, size, pf, hs, ST.g_ho(~A, ~cmp, size, depth, t, g))),
        kids_leaf(~A, ~cmp, UPS.ulog(~A, t2, size, x), IX.par(size), size),
        lay_push(~A, 1n+depth, t2, size, x, hi2, pf2, GR.gtree_lay(~A, depth, t, size, pf, hs, ST.g_lay(~A, ~cmp, size, depth, t, g))),
        ms_push(~A, ~cmp, 1n+depth, t2, size, x, hi2, pf2))))

def push_ok(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +x: A, +g: {ST.good(~A, ~cmp, ST.Sh{size, depth, t}) == True{} : Bool}, +hroom: {Bool.or(Nat.is_lt(size, SC.pow2(depth)), Nat.is_lt(depth, 31n)) == True{} : Bool}, b: Bool, +eb: {Nat.is_lt(size, SC.pow2(depth)) == b : Bool}) -> PushOK(~A, ~cmp, ST.Sh{size, depth, t}, x):
  match b:
    case True{}:
      push_room_ok(~A, ~cmp, ~o, size, depth, t, x, g, eb)
    case False{}:
      push_grow_ok(~A, ~cmp, ~o, size, depth, t, x, g, eb,
        L.subst(Bool, c => {Bool.or(c, Nat.is_lt(depth, 31n)) == True{} : Bool}, Nat.is_lt(size, SC.pow2(depth)), False{}, eb, hroom))
