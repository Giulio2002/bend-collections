import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../lib/order.bend as O
import ../../lib/u32.bend as U
import ../../lib/array.bend as AR
import ../../lib/spec_common.bend as SC
import ./spec.bend as S
import ../../../src/containers/binary_heap.bend as H
import ../../../src/containers/types/binary_heap.bend as E
import ./idx.bend as IX
import ./u32idx.bend as UX
import ./slots.bend as SL
import ./vals.bend as V
import ./root.bend as RT
import ./down.bend as DN
import ./state.bend as ST
import ./pop.bend as PO

# to_sorted_list drains a COPY of the block: every iteration is exactly the
# pop of the copy, so the lemmas of pop.bend carry the whole induction. The
# heap itself is returned unchanged (the copy is what is drained).

# One drain iteration: the root comes out and the last element is sifted down
# over the copy -- the same reduction pop performs, on the copy.
def drain_unfold(~A: Data, ~cmp: A -> A -> Cmp, +depth: Nat, +m: Nat, +f: Nat, +t: AR.Tree<Maybe<&2, A>>, +root: A, +last: A, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, depth, t) == True{} : Bool}, +hs: {Nat.is_le(1n+m, SC.pow2(depth)) == True{} : Bool}, +h0: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), 0n) == Some{root} : Maybe<&2, A>}, +hlast: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), m) == Some{last} : Maybe<&2, A>}, +hm: {Nat.is_lt(0n, m) == True{} : Bool}) -> {H.drain_go(~A, ~cmp, 1n+f, depth, H.drain_probe(~A, U32.from_nat(1n+m), AR.thaw(Maybe<&2, A>, t))) == Con{root, H.drain_go(~A, ~cmp, f, depth, H.drain_probe(~A, U32.from_nat(m), H.sift_down(~A, ~cmp, depth, U32.from_nat(m), U32.from_nat(0n), last, AR.thaw(Maybe<&2, A>, t))))} : List<&2, A>}:
  +hd32 = ST.depth_lt32(depth, hd)
  +hmp = N.succ_le_lt(m, SC.pow2(depth), hs)
  +hsp = N.le_lt_trans(1n+m, SC.pow2(depth), SC.pow2(1n+depth), hs, N.pow2_lt_succ(depth))
  +hzp = N.lt_le_trans(0n, SC.pow2(depth), SC.pow2(1n+depth), N.succ_le_lt(0n, SC.pow2(depth), N.pow2_pos(depth)), N.lt_le(SC.pow2(depth), SC.pow2(1n+depth), N.pow2_lt_succ(depth)))
  %Equal.sym(Bool, U32.is_eq(U32.from_nat(1n+m), U32.from_nat(0n)), Nat.is_eq(1n+m, 0n), UX.eq_bridge(1n+m, 0n, 1n+depth, hd, hsp, hzp)) : {H.drain_go(~A, ~cmp, 1n+f, depth, H.drain_take_go(~A, U32.from_nat(1n+m), AR.thaw(Maybe<&2, A>, t), _)) == Con{root, H.drain_go(~A, ~cmp, f, depth, H.drain_probe(~A, U32.from_nat(m), H.sift_down(~A, ~cmp, depth, U32.from_nat(m), U32.from_nat(0n), last, AR.thaw(Maybe<&2, A>, t))))} : List<&2, A>}
  %Equal.sym(U32, U32.sub(U32.from_nat(1n+m), 1), U32.from_nat(m), Equal.trans(U32, U32.sub(U32.from_nat(1n+m), 1), U32.from_nat(Nat.sub(1n+m, 1n)), U32.from_nat(m), UX.sub_one(1n+m, 1n+depth, hd, hsp, N.zero_le(m)), Equal.cong(Nat, U32, z => U32.from_nat(z), Nat.sub(1n+m, 1n), m, N.sub_zero(m)))) : {H.drain_go(~A, ~cmp, 1n+f, depth, H.drain_take(~A, _, Array.get(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), 0))) == Con{root, H.drain_go(~A, ~cmp, f, depth, H.drain_probe(~A, U32.from_nat(m), H.sift_down(~A, ~cmp, depth, U32.from_nat(m), U32.from_nat(0n), last, AR.thaw(Maybe<&2, A>, t))))} : List<&2, A>}
  %Equal.sym(Array<Maybe<&2, A>> & Maybe<&2, A>, Array.get(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), 0), (AR.thaw(Maybe<&2, A>, t), Some{root}), PO.get_root(~A, depth, t, root, hd32, pf, h0)) : {H.drain_go(~A, ~cmp, 1n+f, depth, H.drain_take(~A, U32.from_nat(m), _)) == Con{root, H.drain_go(~A, ~cmp, f, depth, H.drain_probe(~A, U32.from_nat(m), H.sift_down(~A, ~cmp, depth, U32.from_nat(m), U32.from_nat(0n), last, AR.thaw(Maybe<&2, A>, t))))} : List<&2, A>}
  %Equal.sym(Array<Maybe<&2, A>> & Maybe<&2, A>, Array.get(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), U32.from_nat(m)), (AR.thaw(Maybe<&2, A>, t), Some{last}), PO.get_last(~A, depth, t, m, last, hd32, hmp, pf, hlast)) : {H.drain_go(~A, ~cmp, 1n+f, depth, H.drain_last(~A, root, U32.from_nat(m), U32.is_eq(U32.from_nat(m), 0), _)) == Con{root, H.drain_go(~A, ~cmp, f, depth, H.drain_probe(~A, U32.from_nat(m), H.sift_down(~A, ~cmp, depth, U32.from_nat(m), U32.from_nat(0n), last, AR.thaw(Maybe<&2, A>, t))))} : List<&2, A>}
  %Equal.sym(Bool, U32.is_eq(U32.from_nat(m), U32.from_nat(0n)), Nat.is_eq(m, 0n), UX.eq_bridge(m, 0n, 1n+depth, hd, N.lt_trans(m, 1n+m, SC.pow2(1n+depth), N.lt_succ(m), hsp), hzp)) : {H.drain_go(~A, ~cmp, 1n+f, depth, H.drain_mb(~A, AR.thaw(Maybe<&2, A>, t), root, U32.from_nat(m), Some{last}, _)) == Con{root, H.drain_go(~A, ~cmp, f, depth, H.drain_probe(~A, U32.from_nat(m), H.sift_down(~A, ~cmp, depth, U32.from_nat(m), U32.from_nat(0n), last, AR.thaw(Maybe<&2, A>, t))))} : List<&2, A>}
  %Equal.sym(Bool, Nat.is_eq(m, 0n), False{}, SL.ne_sym(m, 0n, N.is_eq_lt(0n, m, hm))) : {H.drain_go(~A, ~cmp, 1n+f, depth, H.drain_mb(~A, AR.thaw(Maybe<&2, A>, t), root, U32.from_nat(m), Some{last}, _)) == Con{root, H.drain_go(~A, ~cmp, f, depth, H.drain_probe(~A, U32.from_nat(m), H.sift_down(~A, ~cmp, depth, U32.from_nat(m), U32.from_nat(0n), last, AR.thaw(Maybe<&2, A>, t))))} : List<&2, A>}
  {==}

# The last element of the copy: the drain stops with it.
def drain_one(~A: Data, ~cmp: A -> A -> Cmp, +depth: Nat, +f: Nat, +t: AR.Tree<Maybe<&2, A>>, +root: A, +last: A, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, depth, t) == True{} : Bool}, +hs: {Nat.is_le(1n, SC.pow2(depth)) == True{} : Bool}, +h0: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), 0n) == Some{root} : Maybe<&2, A>}, +hlast: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), 0n) == Some{last} : Maybe<&2, A>}) -> {H.drain_go(~A, ~cmp, 1n+f, depth, H.drain_probe(~A, U32.from_nat(1n), AR.thaw(Maybe<&2, A>, t))) == Con{root, Nil{}} : List<&2, A>}:
  +hd32 = ST.depth_lt32(depth, hd)
  +hmp = N.succ_le_lt(0n, SC.pow2(depth), hs)
  +hsp = N.le_lt_trans(1n, SC.pow2(depth), SC.pow2(1n+depth), hs, N.pow2_lt_succ(depth))
  +hzp = N.lt_le_trans(0n, SC.pow2(depth), SC.pow2(1n+depth), N.succ_le_lt(0n, SC.pow2(depth), N.pow2_pos(depth)), N.lt_le(SC.pow2(depth), SC.pow2(1n+depth), N.pow2_lt_succ(depth)))
  %Equal.sym(Bool, U32.is_eq(U32.from_nat(1n), U32.from_nat(0n)), Nat.is_eq(1n, 0n), UX.eq_bridge(1n, 0n, 1n+depth, hd, hsp, hzp)) : {H.drain_go(~A, ~cmp, 1n+f, depth, H.drain_take_go(~A, U32.from_nat(1n), AR.thaw(Maybe<&2, A>, t), _)) == Con{root, Nil{}} : List<&2, A>}
  %Equal.sym(U32, U32.sub(U32.from_nat(1n), 1), U32.from_nat(0n), Equal.trans(U32, U32.sub(U32.from_nat(1n), 1), U32.from_nat(Nat.sub(1n, 1n)), U32.from_nat(0n), UX.sub_one(1n, 1n+depth, hd, hsp, N.zero_le(0n)), Equal.cong(Nat, U32, z => U32.from_nat(z), Nat.sub(1n, 1n), 0n, N.sub_zero(0n)))) : {H.drain_go(~A, ~cmp, 1n+f, depth, H.drain_take(~A, _, Array.get(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), 0))) == Con{root, Nil{}} : List<&2, A>}
  %Equal.sym(Array<Maybe<&2, A>> & Maybe<&2, A>, Array.get(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), 0), (AR.thaw(Maybe<&2, A>, t), Some{root}), PO.get_root(~A, depth, t, root, hd32, pf, h0)) : {H.drain_go(~A, ~cmp, 1n+f, depth, H.drain_take(~A, U32.from_nat(0n), _)) == Con{root, Nil{}} : List<&2, A>}
  %Equal.sym(Array<Maybe<&2, A>> & Maybe<&2, A>, Array.get(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), U32.from_nat(0n)), (AR.thaw(Maybe<&2, A>, t), Some{last}), PO.get_last(~A, depth, t, 0n, last, hd32, hmp, pf, hlast)) : {H.drain_go(~A, ~cmp, 1n+f, depth, H.drain_last(~A, root, U32.from_nat(0n), U32.is_eq(U32.from_nat(0n), 0), _)) == Con{root, Nil{}} : List<&2, A>}
  %Equal.sym(Bool, U32.is_eq(U32.from_nat(0n), U32.from_nat(0n)), Nat.is_eq(0n, 0n), UX.eq_bridge(0n, 0n, 1n+depth, hd, hzp, hzp)) : {H.drain_go(~A, ~cmp, 1n+f, depth, H.drain_mb(~A, AR.thaw(Maybe<&2, A>, t), root, U32.from_nat(0n), Some{last}, _)) == Con{root, Nil{}} : List<&2, A>}
  {==}

# The recursive call the drain makes, as a (linear) function argument: Bend
# has no mutual recursion, so the induction hands its own instance down.
def DrainRec(~A: Data, ~cmp: A -> A -> Cmp, f: Nat, depth: Nat, m: Nat) -> Type:
  @+t3: AR.Tree<Maybe<&2, A>> -> @+g3: {ST.good(~A, ~cmp, ST.Sh{m, depth, t3}) == True{} : Bool} -> {H.drain_go(~A, ~cmp, f, depth, H.drain_probe(~A, U32.from_nat(m), AR.thaw(Maybe<&2, A>, t3))) == ST.model(~A, ~cmp, ST.Sh{m, depth, t3}) : List<&2, A>}

def drain_move(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +depth: Nat, +f: Nat, +k: Nat, +t: AR.Tree<Maybe<&2, A>>, +root: A, +last: A, +g: {ST.good(~A, ~cmp, ST.Sh{2n+k, depth, t}) == True{} : Bool}, +h0: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), 0n) == Some{root} : Maybe<&2, A>}, +hlast: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), 1n+k) == Some{last} : Maybe<&2, A>}, rec: DrainRec(~A, ~cmp, f, depth, 1n+k), r: DN.SiftDownOK(~A, ~cmp, depth, 1n+k, V.msort(~A, ~cmp, V.vals(~A, PO.hole(~A, AR.slots(Maybe<&2, A>, t), 1n+k, last), 1n+k)), depth, t, 0n, last)) -> {H.drain_go(~A, ~cmp, 1n+f, depth, H.drain_probe(~A, U32.from_nat(2n+k), AR.thaw(Maybe<&2, A>, t))) == ST.model(~A, ~cmp, ST.Sh{2n+k, depth, t}) : List<&2, A>}:
  match r:
    case Tuple{+t3, Tuple{esift, Tuple{pf3, Tuple{hho3, Tuple{hlay3, hms3}}}}}:
      +hd = ST.g_depth(~A, ~cmp, 2n+k, depth, t, g)
      +hs = ST.g_size(~A, ~cmp, 2n+k, depth, t, g)
      +hlen = N.lt_le_trans(0n, 1n+k, SC.length(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t)), N.succ_le_lt(0n, 1n+k, N.zero_le(k)), N.lt_le(1n+k, SC.length(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t)), L.subst(Nat, z => {Nat.is_lt(1n+k, z) == True{} : Bool}, SC.pow2(depth), SC.length(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t)), Equal.sym(Nat, SC.length(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t)), SC.pow2(depth), AR.slots_length(Maybe<&2, A>, depth, t, ST.g_perfect(~A, ~cmp, 2n+k, depth, t, g))), N.succ_le_lt(1n+k, SC.pow2(depth), hs))))
      Equal.trans(List<&2, A>, H.drain_go(~A, ~cmp, 1n+f, depth, H.drain_probe(~A, U32.from_nat(2n+k), AR.thaw(Maybe<&2, A>, t))), Con{root, H.drain_go(~A, ~cmp, f, depth, H.drain_probe(~A, U32.from_nat(1n+k), AR.thaw(Maybe<&2, A>, t3)))}, ST.model(~A, ~cmp, ST.Sh{2n+k, depth, t}),
        Equal.trans(List<&2, A>, H.drain_go(~A, ~cmp, 1n+f, depth, H.drain_probe(~A, U32.from_nat(2n+k), AR.thaw(Maybe<&2, A>, t))), Con{root, H.drain_go(~A, ~cmp, f, depth, H.drain_probe(~A, U32.from_nat(1n+k), H.sift_down(~A, ~cmp, depth, U32.from_nat(1n+k), U32.from_nat(0n), last, AR.thaw(Maybe<&2, A>, t))))}, Con{root, H.drain_go(~A, ~cmp, f, depth, H.drain_probe(~A, U32.from_nat(1n+k), AR.thaw(Maybe<&2, A>, t3)))},
          drain_unfold(~A, ~cmp, depth, 1n+k, f, t, root, last, hd, ST.g_perfect(~A, ~cmp, 2n+k, depth, t, g), hs, h0, hlast, N.succ_le_lt(0n, 1n+k, N.zero_le(k))),
          Equal.cong(Array<Maybe<&2, A>>, List<&2, A>, a => Con{root, H.drain_go(~A, ~cmp, f, depth, H.drain_probe(~A, U32.from_nat(1n+k), a))}, H.sift_down(~A, ~cmp, depth, U32.from_nat(1n+k), U32.from_nat(0n), last, AR.thaw(Maybe<&2, A>, t)), AR.thaw(Maybe<&2, A>, t3), esift)),
        Equal.trans(List<&2, A>, Con{root, H.drain_go(~A, ~cmp, f, depth, H.drain_probe(~A, U32.from_nat(1n+k), AR.thaw(Maybe<&2, A>, t3)))}, Con{root, ST.model(~A, ~cmp, ST.Sh{1n+k, depth, t3})}, ST.model(~A, ~cmp, ST.Sh{2n+k, depth, t}),
          LL.cons_cong(A, root, H.drain_go(~A, ~cmp, f, depth, H.drain_probe(~A, U32.from_nat(1n+k), AR.thaw(Maybe<&2, A>, t3))), ST.model(~A, ~cmp, ST.Sh{1n+k, depth, t3}),
            rec(t3, ST.good_intro(~A, ~cmp, 1n+k, depth, t3, hd, pf3, hlay3, hho3, N.le_trans(1n+k, 2n+k, SC.pow2(depth), N.le_succ(1n+k), hs)))),
          Equal.trans(List<&2, A>, Con{root, ST.model(~A, ~cmp, ST.Sh{1n+k, depth, t3})}, Con{root, V.msort(~A, ~cmp, V.vals(~A, PO.hole(~A, AR.slots(Maybe<&2, A>, t), 1n+k, last), 1n+k))}, ST.model(~A, ~cmp, ST.Sh{2n+k, depth, t}),
            LL.cons_cong(A, root, ST.model(~A, ~cmp, ST.Sh{1n+k, depth, t3}), V.msort(~A, ~cmp, V.vals(~A, PO.hole(~A, AR.slots(Maybe<&2, A>, t), 1n+k, last), 1n+k)), hms3),
            Equal.sym(List<&2, A>, ST.model(~A, ~cmp, ST.Sh{2n+k, depth, t}), Con{root, V.msort(~A, ~cmp, V.vals(~A, PO.hole(~A, AR.slots(Maybe<&2, A>, t), 1n+k, last), 1n+k))},
              PO.pop_split(~A, ~cmp, ~o, AR.slots(Maybe<&2, A>, t), 1n+k, root, last, N.succ_le_lt(0n, 1n+k, N.zero_le(k)), ST.g_ho(~A, ~cmp, 2n+k, depth, t, g), ST.g_lay(~A, ~cmp, 2n+k, depth, t, g), h0, hlast, hlen)))))

# the one-element copy
def drain_single(~A: Data, ~cmp: A -> A -> Cmp, +depth: Nat, +f: Nat, +t: AR.Tree<Maybe<&2, A>>, +g: {ST.good(~A, ~cmp, ST.Sh{1n, depth, t}) == True{} : Bool}, sig: Sigma<&1, &1, A, v => {SL.slot(~A, AR.slots(Maybe<&2, A>, t), 0n) == Some{v} : Maybe<&2, A>}>) -> {H.drain_go(~A, ~cmp, 1n+f, depth, H.drain_probe(~A, U32.from_nat(1n), AR.thaw(Maybe<&2, A>, t))) == ST.model(~A, ~cmp, ST.Sh{1n, depth, t}) : List<&2, A>}:
  match sig:
    case Tuple{+root, +h0}:
      Equal.trans(List<&2, A>, H.drain_go(~A, ~cmp, 1n+f, depth, H.drain_probe(~A, U32.from_nat(1n), AR.thaw(Maybe<&2, A>, t))), Con{root, Nil{}}, ST.model(~A, ~cmp, ST.Sh{1n, depth, t}),
        drain_one(~A, ~cmp, depth, f, t, root, root, ST.g_depth(~A, ~cmp, 1n, depth, t, g), ST.g_perfect(~A, ~cmp, 1n, depth, t, g), N.pow2_pos(depth), h0, h0),
        Equal.sym(List<&2, A>, ST.model(~A, ~cmp, ST.Sh{1n, depth, t}), Con{root, Nil{}},
          Equal.cong(Maybe<&2, A>, List<&2, A>, ms => V.msort(~A, ~cmp, V.cons_slot(~A, ms, Nil{})), SL.slot(~A, AR.slots(Maybe<&2, A>, t), 0n), Some{root}, h0)))

def drain_two(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +depth: Nat, +f: Nat, +k: Nat, +t: AR.Tree<Maybe<&2, A>>, +root: A, +g: {ST.good(~A, ~cmp, ST.Sh{2n+k, depth, t}) == True{} : Bool}, +h0: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), 0n) == Some{root} : Maybe<&2, A>}, rec: DrainRec(~A, ~cmp, f, depth, 1n+k), sig: Sigma<&1, &1, A, v => {SL.slot(~A, AR.slots(Maybe<&2, A>, t), 1n+k) == Some{v} : Maybe<&2, A>}>) -> {H.drain_go(~A, ~cmp, 1n+f, depth, H.drain_probe(~A, U32.from_nat(2n+k), AR.thaw(Maybe<&2, A>, t))) == ST.model(~A, ~cmp, ST.Sh{2n+k, depth, t}) : List<&2, A>}:
  match sig:
    case Tuple{+last, +hlast}:
      drain_move(~A, ~cmp, ~o, depth, f, k, t, root, last, g, h0, hlast, rec,
        PO.pop_sift(~A, ~cmp, ~o, depth, 1n+k, t, root, last, ST.g_depth(~A, ~cmp, 2n+k, depth, t, g), ST.g_perfect(~A, ~cmp, 2n+k, depth, t, g), ST.g_size(~A, ~cmp, 2n+k, depth, t, g), ST.g_ho(~A, ~cmp, 2n+k, depth, t, g), ST.g_lay(~A, ~cmp, 2n+k, depth, t, g), h0, hlast, N.succ_le_lt(0n, 1n+k, N.zero_le(k))))

def drain_pair(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +depth: Nat, +f: Nat, +k: Nat, +t: AR.Tree<Maybe<&2, A>>, +g: {ST.good(~A, ~cmp, ST.Sh{2n+k, depth, t}) == True{} : Bool}, rec: DrainRec(~A, ~cmp, f, depth, 1n+k), sig: Sigma<&1, &1, A, v => {SL.slot(~A, AR.slots(Maybe<&2, A>, t), 0n) == Some{v} : Maybe<&2, A>}>) -> {H.drain_go(~A, ~cmp, 1n+f, depth, H.drain_probe(~A, U32.from_nat(2n+k), AR.thaw(Maybe<&2, A>, t))) == ST.model(~A, ~cmp, ST.Sh{2n+k, depth, t}) : List<&2, A>}:
  match sig:
    case Tuple{+root, +h0}:
      drain_two(~A, ~cmp, ~o, depth, f, k, t, root, g, h0, rec,
        SL.slot_some(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), 1n+k), SL.lay_at(~A, AR.slots(Maybe<&2, A>, t), 2n+k, 1n+k, ST.g_lay(~A, ~cmp, 2n+k, depth, t, g), N.lt_succ(1n+k))))

# The whole drain: as many iterations as the copy has elements.
def drain_ok(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), fuel: Nat, +depth: Nat, size: Nat, +t: AR.Tree<Maybe<&2, A>>, +g: {ST.good(~A, ~cmp, ST.Sh{size, depth, t}) == True{} : Bool}, +hf: {Nat.is_le(size, fuel) == True{} : Bool}) -> {H.drain_go(~A, ~cmp, fuel, depth, H.drain_probe(~A, U32.from_nat(size), AR.thaw(Maybe<&2, A>, t))) == ST.model(~A, ~cmp, ST.Sh{size, depth, t}) : List<&2, A>}:
  match fuel size:
    case 0n 0n:
      {==}
    case 1n+f 0n:
      {==}
    case 0n 1n+m:
      Empty.absurd({H.drain_go(~A, ~cmp, 0n, depth, H.drain_probe(~A, U32.from_nat(1n+m), AR.thaw(Maybe<&2, A>, t))) == ST.model(~A, ~cmp, ST.Sh{1n+m, depth, t}) : List<&2, A>}, L.true_not_false(Nat.is_le(1n+m, 0n), hf, {==}))
    case 1n+f 1n+0n:
      drain_single(~A, ~cmp, depth, f, t, g,
        SL.slot_some(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), 0n), SL.lay_at(~A, AR.slots(Maybe<&2, A>, t), 1n, 0n, ST.g_lay(~A, ~cmp, 1n, depth, t, g), {==})))
    case 1n+ +f 1n+1n+ +k:
      drain_pair(~A, ~cmp, ~o, depth, f, k, t, g,
        t3 => g3 => drain_ok(~A, ~cmp, ~o, f, depth, 1n+k, t3, g3, N.lt_succ_le(1n+k, f, N.succ_le_lt(1n+k, 1n+f, hf))),
        SL.slot_some(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), 0n), SL.lay_at(~A, AR.slots(Maybe<&2, A>, t), 2n+k, 0n, ST.g_lay(~A, ~cmp, 2n+k, depth, t, g), N.succ_le_lt(0n, 2n+k, N.zero_le(1n+k)))))

# ---- to_sorted_list ----
#
# The heap is returned unchanged and the observation is its sorted multiset:
# the drain runs on the clone.
def to_sorted_ok(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +g: {ST.good(~A, ~cmp, ST.Sh{size, depth, t}) == True{} : Bool}) -> {H.to_sorted_list(~A, ~cmp, ST.real(~A, ST.Sh{size, depth, t})) == (ST.real(~A, ST.Sh{size, depth, t}), ST.model(~A, ~cmp, ST.Sh{size, depth, t})) : H.Heap<A> & List<&2, A>}:
  %Equal.sym(Array<Maybe<&2, A>> & Array<Maybe<&2, A>>, Array.clone(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t)), (AR.thaw(Maybe<&2, A>, t), AR.thaw(Maybe<&2, A>, t)), AR.clone(Maybe<&2, A>, t)) : {H.sorted_of(~A, ~cmp, size, U32.from_nat(size), depth, U.pow2u(depth), _) == (ST.real(~A, ST.Sh{size, depth, t}), ST.model(~A, ~cmp, ST.Sh{size, depth, t})) : H.Heap<A> & List<&2, A>}
  Equal.cong(List<&2, A>, H.Heap<A> & List<&2, A>, zs => (ST.real(~A, ST.Sh{size, depth, t}), zs), H.drain_go(~A, ~cmp, size, depth, H.drain_probe(~A, U32.from_nat(size), AR.thaw(Maybe<&2, A>, t))), ST.model(~A, ~cmp, ST.Sh{size, depth, t}),
    drain_ok(~A, ~cmp, ~o, size, depth, size, t, g, N.le_refl(size)))
