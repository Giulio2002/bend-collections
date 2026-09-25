import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../lib/order.bend as O
import ../../lib/array.bend as AR
import ../../lib/u32.bend as U
import ../../../spec/lib/common.bend as SC
import ../../../spec/containers/binary_heap.bend as S
import ../../../src/containers/binary_heap.bend as H
import ./idx.bend as IX
import ./u32idx.bend as UX
import ./slots.bend as SL
import ./vals.bend as V
import ./bag.bend as BG
import ./multiset.bend as M

# The sift-up loop, mirrored on the shadow tree, and the bridge that says the
# executable loop state is the mirror of the shadow one.

type UpS<-A: Data> is Data:
  Stp{t: AR.Tree<Maybe<&2, A>>, i: Nat}
  Mv{t: AR.Tree<Maybe<&2, A>>, i: Nat, pv: A, p: Nat}

def ureal(~A: Data, s: UpS<A>) -> H.Up<A>:
  match s:
    case Stp{t, i}:
      H.UStop{AR.thaw(Maybe<&2, A>, t), U32.from_nat(i)}
    case Mv{t, i, pv, p}:
      H.UMove{AR.thaw(Maybe<&2, A>, t), U32.from_nat(i), pv, U32.from_nat(p)}

# ---- the mirror of `H.up_probe` ----

def udec(~A: Data, ~cmp: A -> A -> Cmp, t: AR.Tree<Maybe<&2, A>>, +i: Nat, pv: A, p: Nat, ok: Bool) -> UpS<A>:
  match ok:
    case True{}:
      Stp{t, i}
    case False{}:
      Mv{t, i, pv, p}

def umb(~A: Data, ~cmp: A -> A -> Cmp, t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, p: Nat, m: Maybe<&2, A>) -> UpS<A>:
  match m:
    case None{}:
      Stp{t, i}
    case Some{+pv}:
      udec(~A, ~cmp, t, i, pv, p, S.le(~A, ~cmp, pv, x))

def uroot(~A: Data, ~cmp: A -> A -> Cmp, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, root: Bool) -> UpS<A>:
  match root:
    case True{}:
      Stp{t, i}
    case False{}:
      umb(~A, ~cmp, t, i, x, IX.par(i), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)))

def uprobe(~A: Data, ~cmp: A -> A -> Cmp, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A) -> UpS<A>:
  uroot(~A, ~cmp, t, i, x, Nat.is_eq(i, 0n))

# ---- the bridge ----

# the slot the implementation reads, as an `Array.get` result
def get_slot(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +j: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {Array.get(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), U32.from_nat(j)) == (AR.thaw(Maybe<&2, A>, t), SL.slot(~A, AR.slots(Maybe<&2, A>, t), j)) : Array<Maybe<&2, A>> & Maybe<&2, A>}:
  +ss = AR.slots(Maybe<&2, A>, t)
  +ej = UX.nat_round(j, d, N.lt_le(d, 32n, hd), hj)
  AR.get(Maybe<&2, A>, d, t, U32.from_nat(j), SL.slot(~A, ss, j), hd,
    L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, j, U32.to_nat(U32.from_nat(j)), Equal.sym(Nat, U32.to_nat(U32.from_nat(j)), j, ej), hj),
    L.subst(Nat, z => {SC.nth(Maybe<&2, A>, ss, z) == Some{SL.slot(~A, ss, j)} : Maybe<&2, Maybe<&2, A>>}, j, U32.to_nat(U32.from_nat(j)), Equal.sym(Nat, U32.to_nat(U32.from_nat(j)), j, ej),
      SL.nth_slot(~A, ss, j, L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, SC.pow2(d), SC.length(Maybe<&2, A>, ss), Equal.sym(Nat, SC.length(Maybe<&2, A>, ss), SC.pow2(d), AR.slots_length(Maybe<&2, A>, d, t, pf)), hj))),
    pf)

def double_pos(+v: Nat, +h: {Nat.is_lt(0n, v) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.double(v)) == True{} : Bool}:
  match v:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, L.true_not_false(Nat.is_lt(0n, 0n), h, N.lt_irrefl(0n)))
    case 1n+k:
      {==}

def pow2_pos(+d: Nat) -> {Nat.is_lt(0n, SC.pow2(d)) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      double_pos(SC.pow2(p), pow2_pos(p))

def pos_of(+i: Nat, +eb: {Nat.is_eq(i, 0n) == False{} : Bool}) -> {Nat.is_le(i, 0n) == False{} : Bool}:
  match i:
    case 0n:
      Empty.absurd({Nat.is_le(0n, 0n) == False{} : Bool}, L.true_not_false(Nat.is_eq(0n, 0n), {==}, eb))
    case 1n+k:
      {==}

def udec_ok(~A: Data, ~cmp: A -> A -> Cmp, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +pv: A, +p: Nat, b: Bool) -> {H.up_dec(~A, AR.thaw(Maybe<&2, A>, t), U32.from_nat(i), pv, U32.from_nat(p), b) == ureal(~A, udec(~A, ~cmp, t, i, pv, p, b)) : H.Up<A>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def umb_ok(~A: Data, ~cmp: A -> A -> Cmp, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +p: Nat, m: Maybe<&2, A>) -> {H.up_mb(~A, ~cmp, AR.thaw(Maybe<&2, A>, t), U32.from_nat(i), x, U32.from_nat(p), m) == ureal(~A, umb(~A, ~cmp, t, i, x, p, m)) : H.Up<A>}:
  match m:
    case None{}:
      {==}
    case Some{+pv}:
      udec_ok(~A, ~cmp, t, i, pv, p, S.le(~A, ~cmp, pv, x))

# i > 0: the implementation reads the parent slot and the mirror reads the
# same slot of the shadow's slot list.
def uroot_false(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {H.up_root(~A, ~cmp, U32.from_nat(i), x, AR.thaw(Maybe<&2, A>, t), False{}) == ureal(~A, uroot(~A, ~cmp, t, i, x, False{})) : H.Up<A>}:
  +hp = N.lt_trans(IX.par(i), i, SC.pow2(d), IX.par_lt(i, N.succ_le_lt(0n, i, hpos)), hi)
  %Equal.sym(U32, U32.shr(U32.sub(U32.from_nat(i), 1)), U32.from_nat(IX.par(i)), UX.par_bridge(i, d, N.lt_le(d, 32n, hd), hi, hpos)) : {H.up_slot(~A, ~cmp, U32.from_nat(i), x, _, Array.get(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), _)) == ureal(~A, uroot(~A, ~cmp, t, i, x, False{})) : H.Up<A>}
  %Equal.sym(Array<Maybe<&2, A>> & Maybe<&2, A>, Array.get(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), U32.from_nat(IX.par(i))), (AR.thaw(Maybe<&2, A>, t), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i))), get_slot(~A, d, t, IX.par(i), hd, hp, pf)) : {H.up_slot(~A, ~cmp, U32.from_nat(i), x, U32.from_nat(IX.par(i)), _) == ureal(~A, uroot(~A, ~cmp, t, i, x, False{})) : H.Up<A>}
  umb_ok(~A, ~cmp, t, i, x, IX.par(i), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)))

def uroot_ok(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, b: Bool, +eb: {Nat.is_eq(i, 0n) == b : Bool}) -> {H.up_root(~A, ~cmp, U32.from_nat(i), x, AR.thaw(Maybe<&2, A>, t), b) == ureal(~A, uroot(~A, ~cmp, t, i, x, b)) : H.Up<A>}:
  match b:
    case True{}:
      {==}
    case False{}:
      uroot_false(~A, ~cmp, d, t, i, x, hd, hi, N.lt_succ_le_succ(0n, i, N.not_le_lt(i, 0n, pos_of(i, eb))), pf)

# is_eq(i, 0) = False gives 1 <= i
def uprobe_ok(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {H.up_probe(~A, ~cmp, U32.from_nat(i), x, AR.thaw(Maybe<&2, A>, t)) == ureal(~A, uprobe(~A, ~cmp, t, i, x)) : H.Up<A>}:
  %Equal.sym(Bool, U32.is_eq(U32.from_nat(i), U32.from_nat(0n)), Nat.is_eq(i, 0n), UX.eq_bridge(i, 0n, d, N.lt_le(d, 32n, hd), hi, pow2_pos(d))) : {H.up_root(~A, ~cmp, U32.from_nat(i), x, AR.thaw(Maybe<&2, A>, t), _) == ureal(~A, uprobe(~A, ~cmp, t, i, x)) : H.Up<A>}
  uroot_ok(~A, ~cmp, d, t, i, x, hd, hi, pf, Nat.is_eq(i, 0n), {==})

# ---- the logical slot list of a loop state ----
#
# While the loop runs, slot i of the block holds a value that is about to be
# overwritten; the array the invariant talks about is the block with the
# sifted value x at slot i.

def ulog(~A: Data, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A) -> List<&2, Maybe<&2, A>>:
  SC.update(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), i, Some{x})

def mval(~A: Data, m: Maybe<&2, A>, d: A) -> A:
  match m:
    case None{}:
      d
    case Some{v}:
      v

# slot bookkeeping for a tree whose slot list has 2^d entries
def in_range(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +j: Nat, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {Nat.is_lt(j, SC.length(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t))) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, SC.pow2(d), SC.length(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t)), Equal.sym(Nat, SC.length(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t)), SC.pow2(d), AR.slots_length(Maybe<&2, A>, d, t, pf)), hj)

def ulog_at(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {SL.slot(~A, ulog(~A, t, i, x), i) == Some{x} : Maybe<&2, A>}:
  SL.slot_same(~A, AR.slots(Maybe<&2, A>, t), i, Some{x}, in_range(~A, d, t, i, hi, pf))

def ulog_off(~A: Data, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +j: Nat, +ne: {Nat.is_eq(i, j) == False{} : Bool}) -> {SL.slot(~A, ulog(~A, t, i, x), j) == SL.slot(~A, AR.slots(Maybe<&2, A>, t), j) : Maybe<&2, A>}:
  SL.slot_other(~A, AR.slots(Maybe<&2, A>, t), i, j, Some{x}, ne)

# ---- what the loop delivers ----

def UpOK(~A: Data, ~cmp: A -> A -> Cmp, d: Nat, n: Nat, tgt: List<&2, A>, fuel: Nat, x: A, s: UpS<A>) -> Type:
  Sigma<&1, &1, AR.Tree<Maybe<&2, A>>, t2 => {H.up_go(~A, ~cmp, fuel, x, ureal(~A, s)) == AR.thaw(Maybe<&2, A>, t2) : Array<Maybe<&2, A>>} & ({AR.perfect(Maybe<&2, A>, d, t2) == True{} : Bool} & ({SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t2), n) == True{} : Bool} & ({SL.lay(~A, AR.slots(Maybe<&2, A>, t2), n) == True{} : Bool} & {V.msort(~A, ~cmp, V.vals(~A, AR.slots(Maybe<&2, A>, t2), n)) == tgt : List<&2, A>})))>

# the block after the last write, and the fact that its slot list is the
# logical array the invariant is about
def set_tree(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A) -> AR.Tree<Maybe<&2, A>>:
  AR.upd(Maybe<&2, A>, d, t, i, Some{x})

def set_slots(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {AR.slots(Maybe<&2, A>, set_tree(~A, d, t, i, x)) == ulog(~A, t, i, x) : List<&2, Maybe<&2, A>>}:
  AR.upd_slots(Maybe<&2, A>, d, t, i, Some{x}, hi, pf)

def set_eq(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {Array.set(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), U32.from_nat(i), Some{x}) == AR.thaw(Maybe<&2, A>, set_tree(~A, d, t, i, x)) : Array<Maybe<&2, A>>}:
  +ss = AR.slots(Maybe<&2, A>, t)
  +ei = UX.nat_round(i, d, N.lt_le(d, 32n, hd), hi)
  %ei : {Array.set(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), U32.from_nat(i), Some{x}) == AR.thaw(Maybe<&2, A>, AR.upd(Maybe<&2, A>, d, t, _, Some{x})) : Array<Maybe<&2, A>>}
  AR.set(Maybe<&2, A>, d, t, U32.from_nat(i), Some{x}, SL.slot(~A, ss, i), hd,
    L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, ei), hi),
    L.subst(Nat, z => {SC.nth(Maybe<&2, A>, ss, z) == Some{SL.slot(~A, ss, i)} : Maybe<&2, Maybe<&2, A>>}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, ei), SL.nth_slot(~A, ss, i, in_range(~A, d, t, i, hi, pf))),
    pf)

# ---- the loop stops: the sifted value is written where the hole is ----

def up_stop_mk(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +tgt: List<&2, A>, +fuel: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +eq: {H.up_go(~A, ~cmp, fuel, x, ureal(~A, Stp{t, i})) == AR.thaw(Maybe<&2, A>, set_tree(~A, d, t, i, x)) : Array<Maybe<&2, A>>}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hpair: {SL.pair_ok(~A, ~cmp, ulog(~A, t, i, x), i) == True{} : Bool}, +hexc: {SL.ho_exc(~A, ~cmp, ulog(~A, t, i, x), n, i) == True{} : Bool}, +hlay: {SL.lay(~A, ulog(~A, t, i, x), n) == True{} : Bool}, +hms: {V.msort(~A, ~cmp, V.vals(~A, ulog(~A, t, i, x), n)) == tgt : List<&2, A>}) -> UpOK(~A, ~cmp, d, n, tgt, fuel, x, Stp{t, i}):
  +es = set_slots(~A, d, t, i, x, hi, pf)
  (set_tree(~A, d, t, i, x),
   (eq,
    (AR.upd_perfect(Maybe<&2, A>, d, t, i, Some{x}, pf),
     (L.subst(List<&2, Maybe<&2, A>>, ss => {SL.ho_upto(~A, ~cmp, ss, n) == True{} : Bool}, ulog(~A, t, i, x), AR.slots(Maybe<&2, A>, set_tree(~A, d, t, i, x)), Equal.sym(List<&2, Maybe<&2, A>>, AR.slots(Maybe<&2, A>, set_tree(~A, d, t, i, x)), ulog(~A, t, i, x), es),
        SL.ho_of_exc(~A, ~cmp, ulog(~A, t, i, x), n, i, hexc, hpair)),
      (L.subst(List<&2, Maybe<&2, A>>, ss => {SL.lay(~A, ss, n) == True{} : Bool}, ulog(~A, t, i, x), AR.slots(Maybe<&2, A>, set_tree(~A, d, t, i, x)), Equal.sym(List<&2, Maybe<&2, A>>, AR.slots(Maybe<&2, A>, set_tree(~A, d, t, i, x)), ulog(~A, t, i, x), es), hlay),
       L.subst(List<&2, Maybe<&2, A>>, ss => {V.msort(~A, ~cmp, V.vals(~A, ss, n)) == tgt : List<&2, A>}, ulog(~A, t, i, x), AR.slots(Maybe<&2, A>, set_tree(~A, d, t, i, x)), Equal.sym(List<&2, Maybe<&2, A>>, AR.slots(Maybe<&2, A>, set_tree(~A, d, t, i, x)), ulog(~A, t, i, x), es), hms))))))

def up_stop_ok(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +tgt: List<&2, A>, fuel: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hpair: {SL.pair_ok(~A, ~cmp, ulog(~A, t, i, x), i) == True{} : Bool}, +hexc: {SL.ho_exc(~A, ~cmp, ulog(~A, t, i, x), n, i) == True{} : Bool}, +hlay: {SL.lay(~A, ulog(~A, t, i, x), n) == True{} : Bool}, +hms: {V.msort(~A, ~cmp, V.vals(~A, ulog(~A, t, i, x), n)) == tgt : List<&2, A>}) -> UpOK(~A, ~cmp, d, n, tgt, fuel, x, Stp{t, i}):
  match fuel:
    case 0n:
      up_stop_mk(~A, ~cmp, d, n, tgt, 0n, t, i, x, set_eq(~A, d, t, i, x, hd, hi, pf), hi, pf, hpair, hexc, hlay, hms)
    case 1n+f:
      up_stop_mk(~A, ~cmp, d, n, tgt, 1n+f, t, i, x, set_eq(~A, d, t, i, x, hd, hi, pf), hi, pf, hpair, hexc, hlay, hms)

# ---- one step of the loop: the parent value moves down into the hole ----
#
# `t2` is the block after that write and the hole is now at par(i); `u2` is
# the logical array of the new state. The three lemmas below say what each of
# its slots holds.

def t2_of(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +pv: A) -> AR.Tree<Maybe<&2, A>>:
  set_tree(~A, d, t, i, pv)

def u2_of(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A) -> List<&2, Maybe<&2, A>>:
  ulog(~A, t2_of(~A, d, t, i, pv), IX.par(i), x)

def par_ne(+i: Nat, +hpos: {Nat.is_le(1n, i) == True{} : Bool}) -> {Nat.is_eq(IX.par(i), i) == False{} : Bool}:
  N.is_eq_lt(IX.par(i), i, IX.par_lt(i, N.succ_le_lt(0n, i, hpos)))

def par_lt_d(+d: Nat, +i: Nat, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}) -> {Nat.is_lt(IX.par(i), SC.pow2(d)) == True{} : Bool}:
  N.lt_trans(IX.par(i), i, SC.pow2(d), IX.par_lt(i, N.succ_le_lt(0n, i, hpos)), hi)

def t2_perfect(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +pv: A, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {AR.perfect(Maybe<&2, A>, d, t2_of(~A, d, t, i, pv)) == True{} : Bool}:
  AR.upd_perfect(Maybe<&2, A>, d, t, i, Some{pv}, pf)

def u2_at_p(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(i)) == Some{x} : Maybe<&2, A>}:
  ulog_at(~A, d, t2_of(~A, d, t, i, pv), IX.par(i), x, par_lt_d(d, i, hi, hpos), t2_perfect(~A, d, t, i, pv, pf))

def u2_at_i(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {SL.slot(~A, u2_of(~A, d, t, i, x, pv), i) == Some{pv} : Maybe<&2, A>}:
  Equal.trans(Maybe<&2, A>, SL.slot(~A, u2_of(~A, d, t, i, x, pv), i), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, pv)), i), Some{pv},
    ulog_off(~A, t2_of(~A, d, t, i, pv), IX.par(i), x, i, par_ne(i, hpos)),
    Equal.trans(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, pv)), i), SL.slot(~A, ulog(~A, t, i, pv), i), Some{pv},
      Equal.cong(List<&2, Maybe<&2, A>>, Maybe<&2, A>, ss => SL.slot(~A, ss, i), AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, pv)), ulog(~A, t, i, pv), set_slots(~A, d, t, i, pv, hi, pf)),
      ulog_at(~A, d, t, i, pv, hi, pf)))

def u2_off(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +j: Nat, +hji: {Nat.is_eq(i, j) == False{} : Bool}, +hjp: {Nat.is_eq(IX.par(i), j) == False{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {SL.slot(~A, u2_of(~A, d, t, i, x, pv), j) == SL.slot(~A, AR.slots(Maybe<&2, A>, t), j) : Maybe<&2, A>}:
  Equal.trans(Maybe<&2, A>, SL.slot(~A, u2_of(~A, d, t, i, x, pv), j), SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, pv)), j), SL.slot(~A, AR.slots(Maybe<&2, A>, t), j),
    ulog_off(~A, t2_of(~A, d, t, i, pv), IX.par(i), x, j, hjp),
    Equal.trans(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, pv)), j), SL.slot(~A, ulog(~A, t, i, pv), j), SL.slot(~A, AR.slots(Maybe<&2, A>, t), j),
      Equal.cong(List<&2, Maybe<&2, A>>, Maybe<&2, A>, ss => SL.slot(~A, ss, j), AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, pv)), ulog(~A, t, i, pv), set_slots(~A, d, t, i, pv, hi, pf)),
      ulog_off(~A, t, i, pv, j, hji)))

# the same three for the CURRENT logical array
def u1_at_p(~A: Data, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}) -> {SL.slot(~A, ulog(~A, t, i, x), IX.par(i)) == Some{pv} : Maybe<&2, A>}:
  Equal.trans(Maybe<&2, A>, SL.slot(~A, ulog(~A, t, i, x), IX.par(i)), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)), Some{pv},
    ulog_off(~A, t, i, x, IX.par(i), SL.ne_sym(i, IX.par(i), par_ne(i, hpos))),
    hpv)

# ---- the pair condition at an index that has a parent ----

def pair_ok_pos(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, i: Nat, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +h: {SL.mle(~A, ~cmp, SL.slot(~A, ss, IX.par(i)), SL.slot(~A, ss, i)) == True{} : Bool}) -> {SL.pair_ok(~A, ~cmp, ss, i) == True{} : Bool}:
  match i:
    case 0n:
      Empty.absurd({SL.pair_ok(~A, ~cmp, ss, 0n) == True{} : Bool}, L.true_not_false(Nat.is_le(1n, 0n), hpos, {==}))
    case 1n+k:
      h

def pair_ok_val(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, i: Nat, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +h: {SL.pair_ok(~A, ~cmp, ss, i) == True{} : Bool}) -> {SL.mle(~A, ~cmp, SL.slot(~A, ss, IX.par(i)), SL.slot(~A, ss, i)) == True{} : Bool}:
  match i:
    case 0n:
      Empty.absurd({SL.mle(~A, ~cmp, SL.slot(~A, ss, IX.par(0n)), SL.slot(~A, ss, 0n)) == True{} : Bool}, L.true_not_false(Nat.is_le(1n, 0n), hpos, {==}))
    case 1n+k:
      h

# j >= 1 whenever j is not 0
def pos_of_ne(+j: Nat, +h: {Nat.is_eq(j, 0n) == False{} : Bool}) -> {Nat.is_le(1n, j) == True{} : Bool}:
  match j:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, L.true_not_false(Nat.is_eq(0n, 0n), {==}, h))
    case 1n+k:
      N.zero_le(k)

# ---- the heap order of the next state, one index at a time ----
#
#   case i     the hole's old index now holds the parent value pv, and the
#              new hole above it holds x, with x <= pv because the sift moved
#   case kid   a child of the old hole: pv is not larger than it, which is
#              exactly the invariant H2 the state carries
#   case sib   a child of the new hole other than the old one: x <= pv and pv
#              was not larger than it
#   case far   an index none of whose two slots changed

def h1n_i_mle(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hnle: {S.le(~A, ~cmp, pv, x) == False{} : Bool}) -> {SL.mle(~A, ~cmp, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(i)), SL.slot(~A, u2_of(~A, d, t, i, x, pv), i)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(i)), Some{x}, u2_at_p(~A, d, t, i, x, pv, hi, hpos, pf)) : {SL.mle(~A, ~cmp, _, SL.slot(~A, u2_of(~A, d, t, i, x, pv), i)) == True{} : Bool}
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, u2_of(~A, d, t, i, x, pv), i), Some{pv}, u2_at_i(~A, d, t, i, x, pv, hi, hpos, pf)) : {SL.mle(~A, ~cmp, Some{x}, _) == True{} : Bool}
  O.total(~A, ~cmp, ~o, pv, x, hnle)

def h1n_i(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +j: Nat, +ej: {Nat.is_eq(j, i) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hnle: {S.le(~A, ~cmp, pv, x) == False{} : Bool}) -> {SL.pair_ok(~A, ~cmp, u2_of(~A, d, t, i, x, pv), j) == True{} : Bool}:
  L.subst(Nat, z => {SL.pair_ok(~A, ~cmp, u2_of(~A, d, t, i, x, pv), z) == True{} : Bool}, i, j, Equal.sym(Nat, j, i, N.eq_from_is_eq(j, i, ej)),
    pair_ok_pos(~A, ~cmp, u2_of(~A, d, t, i, x, pv), i, hpos, h1n_i_mle(~A, ~cmp, ~o, d, t, i, x, pv, hi, hpos, pf, hnle)))

def kid_at(+i: Nat, +j: Nat, +epj: {IX.par(j) == i : Nat}, e: {j == IX.kidl(IX.par(j)) : Nat} | {j == IX.kidr(IX.par(j)) : Nat}) -> {j == IX.kidl(i) : Nat} | {j == IX.kidr(i) : Nat}:
  match e:
    case Inl{ej}:
      Inl{L.subst(Nat, z => {j == IX.kidl(z) : Nat}, IX.par(j), i, epj, ej)}
    case Inr{ej}:
      Inr{L.subst(Nat, z => {j == IX.kidr(z) : Nat}, IX.par(j), i, epj, ej)}

# rewrite H2 from the logical array to the block
def h1n_kid_fix(~A: Data, ~cmp: A -> A -> Cmp, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +j: Nat, +hjne: {Nat.is_eq(i, j) == False{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}, +h: {SL.mle(~A, ~cmp, SL.slot(~A, ulog(~A, t, i, x), IX.par(i)), SL.slot(~A, ulog(~A, t, i, x), j)) == True{} : Bool}) -> {SL.mle(~A, ~cmp, Some{pv}, SL.slot(~A, AR.slots(Maybe<&2, A>, t), j)) == True{} : Bool}:
  %u1_at_p(~A, t, i, x, pv, hpos, hpv) : {SL.mle(~A, ~cmp, _, SL.slot(~A, AR.slots(Maybe<&2, A>, t), j)) == True{} : Bool}
  %ulog_off(~A, t, i, x, j, hjne) : {SL.mle(~A, ~cmp, SL.slot(~A, ulog(~A, t, i, x), IX.par(i)), _) == True{} : Bool}
  h

# pv is not larger than a child of the old hole (this is H2)
def h1n_kid_mle(~A: Data, ~cmp: A -> A -> Cmp, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +n: Nat, +j: Nat, +hjne: {Nat.is_eq(i, j) == False{} : Bool}, +hjn: {Nat.is_lt(j, n) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}, +hkids: {SL.kids_le(~A, ~cmp, ulog(~A, t, i, x), n, IX.par(i), i) == True{} : Bool}, e: {j == IX.kidl(i) : Nat} | {j == IX.kidr(i) : Nat}) -> {SL.mle(~A, ~cmp, Some{pv}, SL.slot(~A, AR.slots(Maybe<&2, A>, t), j)) == True{} : Bool}:
  match e:
    case Inl{+ej}:
      h1n_kid_fix(~A, ~cmp, t, i, x, pv, j, hjne, hpos, hpv,
        L.subst(Nat, z => {SL.mle(~A, ~cmp, SL.slot(~A, ulog(~A, t, i, x), IX.par(i)), SL.slot(~A, ulog(~A, t, i, x), z)) == True{} : Bool}, IX.kidl(i), j, Equal.sym(Nat, j, IX.kidl(i), ej),
          SL.kid_le_at(~A, ~cmp, ulog(~A, t, i, x), n, IX.par(i), IX.kidl(i), L.subst(Nat, z => {Nat.is_lt(z, n) == True{} : Bool}, j, IX.kidl(i), ej, hjn),
            L.and_left(SL.kid_le(~A, ~cmp, ulog(~A, t, i, x), n, IX.par(i), IX.kidl(i)), SL.kid_le(~A, ~cmp, ulog(~A, t, i, x), n, IX.par(i), IX.kidr(i)), hkids))))
    case Inr{+ej}:
      h1n_kid_fix(~A, ~cmp, t, i, x, pv, j, hjne, hpos, hpv,
        L.subst(Nat, z => {SL.mle(~A, ~cmp, SL.slot(~A, ulog(~A, t, i, x), IX.par(i)), SL.slot(~A, ulog(~A, t, i, x), z)) == True{} : Bool}, IX.kidr(i), j, Equal.sym(Nat, j, IX.kidr(i), ej),
          SL.kid_le_at(~A, ~cmp, ulog(~A, t, i, x), n, IX.par(i), IX.kidr(i), L.subst(Nat, z => {Nat.is_lt(z, n) == True{} : Bool}, j, IX.kidr(i), ej, hjn),
            L.and_right(SL.kid_le(~A, ~cmp, ulog(~A, t, i, x), n, IX.par(i), IX.kidl(i)), SL.kid_le(~A, ~cmp, ulog(~A, t, i, x), n, IX.par(i), IX.kidr(i)), hkids))))

def par_lt_kid(+i: Nat, +j: Nat, +epj: {IX.par(j) == i : Nat}, +hjpos: {Nat.is_le(1n, j) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}) -> {Nat.is_lt(IX.par(i), j) == True{} : Bool}:
  N.lt_trans(IX.par(i), i, j, IX.par_lt(i, N.succ_le_lt(0n, i, hpos)),
    L.subst(Nat, z => {Nat.is_lt(z, j) == True{} : Bool}, IX.par(j), i, epj, IX.par_lt(j, N.succ_le_lt(0n, j, hjpos))))
def h1n_kid_goal(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +n: Nat, +j: Nat, +epj: {IX.par(j) == i : Nat}, +hij: {Nat.is_eq(i, j) == False{} : Bool}, +hpij: {Nat.is_eq(IX.par(i), j) == False{} : Bool}, +hjn: {Nat.is_lt(j, n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}, +h: {SL.mle(~A, ~cmp, Some{pv}, SL.slot(~A, AR.slots(Maybe<&2, A>, t), j)) == True{} : Bool}) -> {SL.mle(~A, ~cmp, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(j)), SL.slot(~A, u2_of(~A, d, t, i, x, pv), j)) == True{} : Bool}:
  %Equal.sym(Nat, IX.par(j), i, epj) : {SL.mle(~A, ~cmp, SL.slot(~A, u2_of(~A, d, t, i, x, pv), _), SL.slot(~A, u2_of(~A, d, t, i, x, pv), j)) == True{} : Bool}
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, u2_of(~A, d, t, i, x, pv), i), Some{pv}, u2_at_i(~A, d, t, i, x, pv, hi, hpos, pf)) : {SL.mle(~A, ~cmp, _, SL.slot(~A, u2_of(~A, d, t, i, x, pv), j)) == True{} : Bool}
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, u2_of(~A, d, t, i, x, pv), j), SL.slot(~A, AR.slots(Maybe<&2, A>, t), j), u2_off(~A, d, t, i, x, pv, j, hij, hpij, hi, pf)) : {SL.mle(~A, ~cmp, Some{pv}, _) == True{} : Bool}
  h
def h1n_kid(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +n: Nat, +j: Nat, +hjne: {Nat.is_eq(j, i) == False{} : Bool}, +epj: {IX.par(j) == i : Nat}, +hjpos: {Nat.is_le(1n, j) == True{} : Bool}, +hjn: {Nat.is_lt(j, n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}, +hkids: {SL.kids_le(~A, ~cmp, ulog(~A, t, i, x), n, IX.par(i), i) == True{} : Bool}) -> {SL.pair_ok(~A, ~cmp, u2_of(~A, d, t, i, x, pv), j) == True{} : Bool}:
  +hij = SL.ne_sym(i, j, hjne)
  +hpij = N.is_eq_lt(IX.par(i), j, par_lt_kid(i, j, epj, hjpos, hpos))
  pair_ok_pos(~A, ~cmp, u2_of(~A, d, t, i, x, pv), j, hjpos,
    h1n_kid_goal(~A, ~cmp, d, t, i, x, pv, n, j, epj, hij, hpij, hjn, hi, hpos, pf, hpv,
      h1n_kid_mle(~A, ~cmp, t, i, x, pv, n, j, hij, hjn, hpos, hpv, hkids, kid_at(i, j, epj, IX.kid_split(j, N.succ_le_lt(0n, j, hjpos))))))

def h1n_old(~A: Data, ~cmp: A -> A -> Cmp, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +j: Nat, +hij: {Nat.is_eq(i, j) == False{} : Bool}, +epj: {IX.par(j) == IX.par(i) : Nat}, +hjpos: {Nat.is_le(1n, j) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}, +h: {SL.pair_ok(~A, ~cmp, ulog(~A, t, i, x), j) == True{} : Bool}) -> {SL.mle(~A, ~cmp, Some{pv}, SL.slot(~A, AR.slots(Maybe<&2, A>, t), j)) == True{} : Bool}:
  +hm = pair_ok_val(~A, ~cmp, ulog(~A, t, i, x), j, hjpos, h)
  %ulog_off(~A, t, i, x, j, hij) : {SL.mle(~A, ~cmp, Some{pv}, _) == True{} : Bool}
  %u1_at_p(~A, t, i, x, pv, hpos, hpv) : {SL.mle(~A, ~cmp, _, SL.slot(~A, ulog(~A, t, i, x), j)) == True{} : Bool}
  %epj : {SL.mle(~A, ~cmp, SL.slot(~A, ulog(~A, t, i, x), _), SL.slot(~A, ulog(~A, t, i, x), j)) == True{} : Bool}
  hm
def h1n_sib_goal(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +j: Nat, +hij: {Nat.is_eq(i, j) == False{} : Bool}, +hpij: {Nat.is_eq(IX.par(i), j) == False{} : Bool}, +epj: {IX.par(j) == IX.par(i) : Nat}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hnle: {S.le(~A, ~cmp, pv, x) == False{} : Bool}, +h: {SL.mle(~A, ~cmp, Some{pv}, SL.slot(~A, AR.slots(Maybe<&2, A>, t), j)) == True{} : Bool}) -> {SL.mle(~A, ~cmp, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(j)), SL.slot(~A, u2_of(~A, d, t, i, x, pv), j)) == True{} : Bool}:
  %Equal.sym(Nat, IX.par(j), IX.par(i), epj) : {SL.mle(~A, ~cmp, SL.slot(~A, u2_of(~A, d, t, i, x, pv), _), SL.slot(~A, u2_of(~A, d, t, i, x, pv), j)) == True{} : Bool}
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(i)), Some{x}, u2_at_p(~A, d, t, i, x, pv, hi, hpos, pf)) : {SL.mle(~A, ~cmp, _, SL.slot(~A, u2_of(~A, d, t, i, x, pv), j)) == True{} : Bool}
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, u2_of(~A, d, t, i, x, pv), j), SL.slot(~A, AR.slots(Maybe<&2, A>, t), j), u2_off(~A, d, t, i, x, pv, j, hij, hpij, hi, pf)) : {SL.mle(~A, ~cmp, Some{x}, _) == True{} : Bool}
  SL.mle_trans(~A, ~cmp, ~o, Some{x}, pv, SL.slot(~A, AR.slots(Maybe<&2, A>, t), j), O.total(~A, ~cmp, ~o, pv, x, hnle), h)
def h1n_sib(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +n: Nat, +j: Nat, +hij: {Nat.is_eq(i, j) == False{} : Bool}, +hpij: {Nat.is_eq(IX.par(i), j) == False{} : Bool}, +epj: {IX.par(j) == IX.par(i) : Nat}, +hjpos: {Nat.is_le(1n, j) == True{} : Bool}, +hjn: {Nat.is_lt(j, n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}, +hnle: {S.le(~A, ~cmp, pv, x) == False{} : Bool}, +hexc: {SL.ho_exc(~A, ~cmp, ulog(~A, t, i, x), n, i) == True{} : Bool}) -> {SL.pair_ok(~A, ~cmp, u2_of(~A, d, t, i, x, pv), j) == True{} : Bool}:
  pair_ok_pos(~A, ~cmp, u2_of(~A, d, t, i, x, pv), j, hjpos,
    h1n_sib_goal(~A, ~cmp, ~o, d, t, i, x, pv, j, hij, hpij, epj, hi, hpos, pf, hnle,
      h1n_old(~A, ~cmp, t, i, x, pv, j, hij, epj, hjpos, hpos, hpv, SL.exc_at(~A, ~cmp, ulog(~A, t, i, x), n, i, j, hexc, hjn, SL.ne_sym(j, i, hij)))))
def h1n_far_goal(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +j: Nat, +hij: {Nat.is_eq(i, j) == False{} : Bool}, +hpij: {Nat.is_eq(IX.par(i), j) == False{} : Bool}, +hipj: {Nat.is_eq(i, IX.par(j)) == False{} : Bool}, +hppj: {Nat.is_eq(IX.par(i), IX.par(j)) == False{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +h: {SL.mle(~A, ~cmp, SL.slot(~A, ulog(~A, t, i, x), IX.par(j)), SL.slot(~A, ulog(~A, t, i, x), j)) == True{} : Bool}) -> {SL.mle(~A, ~cmp, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(j)), SL.slot(~A, u2_of(~A, d, t, i, x, pv), j)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(j)), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(j)), u2_off(~A, d, t, i, x, pv, IX.par(j), hipj, hppj, hi, pf)) : {SL.mle(~A, ~cmp, _, SL.slot(~A, u2_of(~A, d, t, i, x, pv), j)) == True{} : Bool}
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, u2_of(~A, d, t, i, x, pv), j), SL.slot(~A, AR.slots(Maybe<&2, A>, t), j), u2_off(~A, d, t, i, x, pv, j, hij, hpij, hi, pf)) : {SL.mle(~A, ~cmp, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(j)), _) == True{} : Bool}
  %ulog_off(~A, t, i, x, IX.par(j), hipj) : {SL.mle(~A, ~cmp, _, SL.slot(~A, AR.slots(Maybe<&2, A>, t), j)) == True{} : Bool}
  %ulog_off(~A, t, i, x, j, hij) : {SL.mle(~A, ~cmp, SL.slot(~A, ulog(~A, t, i, x), IX.par(j)), _) == True{} : Bool}
  h
def h1n_far(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +n: Nat, +j: Nat, +hij: {Nat.is_eq(i, j) == False{} : Bool}, +hpij: {Nat.is_eq(IX.par(i), j) == False{} : Bool}, +hipj: {Nat.is_eq(i, IX.par(j)) == False{} : Bool}, +hppj: {Nat.is_eq(IX.par(i), IX.par(j)) == False{} : Bool}, +hjpos: {Nat.is_le(1n, j) == True{} : Bool}, +hjn: {Nat.is_lt(j, n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hexc: {SL.ho_exc(~A, ~cmp, ulog(~A, t, i, x), n, i) == True{} : Bool}) -> {SL.pair_ok(~A, ~cmp, u2_of(~A, d, t, i, x, pv), j) == True{} : Bool}:
  +hm = pair_ok_val(~A, ~cmp, ulog(~A, t, i, x), j, hjpos, SL.exc_at(~A, ~cmp, ulog(~A, t, i, x), n, i, j, hexc, hjn, SL.ne_sym(j, i, hij)))
  pair_ok_pos(~A, ~cmp, u2_of(~A, d, t, i, x, pv), j, hjpos,
    h1n_far_goal(~A, ~cmp, d, t, i, x, pv, j, hij, hpij, hipj, hppj, hi, pf, hm))

# ---- the four cases, dispatched on the index ----

def h1_next_s(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +n: Nat, +j: Nat, +hij: {Nat.is_eq(i, j) == False{} : Bool}, +hpij: {Nat.is_eq(IX.par(i), j) == False{} : Bool}, +hipj: {Nat.is_eq(i, IX.par(j)) == False{} : Bool}, +hjpos: {Nat.is_le(1n, j) == True{} : Bool}, +hjn: {Nat.is_lt(j, n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}, +hnle: {S.le(~A, ~cmp, pv, x) == False{} : Bool}, +hexc: {SL.ho_exc(~A, ~cmp, ulog(~A, t, i, x), n, i) == True{} : Bool}, b3: Bool, +eb3: {Nat.is_eq(IX.par(i), IX.par(j)) == b3 : Bool}) -> {SL.pair_ok(~A, ~cmp, u2_of(~A, d, t, i, x, pv), j) == True{} : Bool}:
  match b3:
    case True{}:
      h1n_sib(~A, ~cmp, ~o, d, t, i, x, pv, n, j, hij, hpij, Equal.sym(Nat, IX.par(i), IX.par(j), N.eq_from_is_eq(IX.par(i), IX.par(j), eb3)), hjpos, hjn, hi, hpos, pf, hpv, hnle, hexc)
    case False{}:
      h1n_far(~A, ~cmp, d, t, i, x, pv, n, j, hij, hpij, hipj, eb3, hjpos, hjn, hi, pf, hexc)

def h1_next_p(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +n: Nat, +j: Nat, +hji: {Nat.is_eq(j, i) == False{} : Bool}, +hpij: {Nat.is_eq(IX.par(i), j) == False{} : Bool}, +hjpos: {Nat.is_le(1n, j) == True{} : Bool}, +hjn: {Nat.is_lt(j, n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}, +hnle: {S.le(~A, ~cmp, pv, x) == False{} : Bool}, +hexc: {SL.ho_exc(~A, ~cmp, ulog(~A, t, i, x), n, i) == True{} : Bool}, +hkids: {SL.kids_le(~A, ~cmp, ulog(~A, t, i, x), n, IX.par(i), i) == True{} : Bool}, b2: Bool, +eb2: {Nat.is_eq(IX.par(j), i) == b2 : Bool}) -> {SL.pair_ok(~A, ~cmp, u2_of(~A, d, t, i, x, pv), j) == True{} : Bool}:
  match b2:
    case True{}:
      h1n_kid(~A, ~cmp, d, t, i, x, pv, n, j, hji, N.eq_from_is_eq(IX.par(j), i, eb2), hjpos, hjn, hi, hpos, pf, hpv, hkids)
    case False{}:
      h1_next_s(~A, ~cmp, ~o, d, t, i, x, pv, n, j, SL.ne_sym(i, j, hji), hpij, SL.ne_sym(i, IX.par(j), eb2), hjpos, hjn, hi, hpos, pf, hpv, hnle, hexc, Nat.is_eq(IX.par(i), IX.par(j)), {==})

def h1_next_pos(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +n: Nat, +j: Nat, +hpij: {Nat.is_eq(IX.par(i), j) == False{} : Bool}, +hjpos: {Nat.is_le(1n, j) == True{} : Bool}, +hjn: {Nat.is_lt(j, n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}, +hnle: {S.le(~A, ~cmp, pv, x) == False{} : Bool}, +hexc: {SL.ho_exc(~A, ~cmp, ulog(~A, t, i, x), n, i) == True{} : Bool}, +hkids: {SL.kids_le(~A, ~cmp, ulog(~A, t, i, x), n, IX.par(i), i) == True{} : Bool}, b1: Bool, +eb1: {Nat.is_eq(j, i) == b1 : Bool}) -> {SL.pair_ok(~A, ~cmp, u2_of(~A, d, t, i, x, pv), j) == True{} : Bool}:
  match b1:
    case True{}:
      h1n_i(~A, ~cmp, ~o, d, t, i, x, pv, j, eb1, hi, hpos, pf, hnle)
    case False{}:
      h1_next_p(~A, ~cmp, ~o, d, t, i, x, pv, n, j, eb1, hpij, hjpos, hjn, hi, hpos, pf, hpv, hnle, hexc, hkids, Nat.is_eq(IX.par(j), i), {==})

def h1_next_at(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +n: Nat, j: Nat, +hjn: {Nat.is_lt(j, n) == True{} : Bool}, +hpij: {Nat.is_eq(IX.par(i), j) == False{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}, +hnle: {S.le(~A, ~cmp, pv, x) == False{} : Bool}, +hexc: {SL.ho_exc(~A, ~cmp, ulog(~A, t, i, x), n, i) == True{} : Bool}, +hkids: {SL.kids_le(~A, ~cmp, ulog(~A, t, i, x), n, IX.par(i), i) == True{} : Bool}) -> {SL.pair_ok(~A, ~cmp, u2_of(~A, d, t, i, x, pv), j) == True{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+ +m:
      h1_next_pos(~A, ~cmp, ~o, d, t, i, x, pv, n, 1n+m, hpij, N.zero_le(m), hjn, hi, hpos, pf, hpv, hnle, hexc, hkids, Nat.is_eq(1n+m, i), {==})

# ---- H2 for the next state: the new hole's parent is not larger than the
# new hole's children ----

def h2_key_root(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +e: {IX.par(i) == 0n : Nat}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hnle: {S.le(~A, ~cmp, pv, x) == False{} : Bool}) -> {SL.mle(~A, ~cmp, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(IX.par(i))), Some{pv}) == True{} : Bool}:
  +at0 = L.subst(Nat, z => {SL.slot(~A, u2_of(~A, d, t, i, x, pv), z) == Some{x} : Maybe<&2, A>}, IX.par(i), 0n, e, u2_at_p(~A, d, t, i, x, pv, hi, hpos, pf))
  %Equal.sym(Nat, IX.par(i), 0n, e) : {SL.mle(~A, ~cmp, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(_)), Some{pv}) == True{} : Bool}
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, u2_of(~A, d, t, i, x, pv), 0n), Some{x}, at0) : {SL.mle(~A, ~cmp, _, Some{pv}) == True{} : Bool}
  O.total(~A, ~cmp, ~o, pv, x, hnle)

def h2_key_deep(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +n: Nat, +e: {Nat.is_eq(IX.par(i), 0n) == False{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hin: {Nat.is_lt(i, n) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}, +hexc: {SL.ho_exc(~A, ~cmp, ulog(~A, t, i, x), n, i) == True{} : Bool}) -> {SL.mle(~A, ~cmp, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(IX.par(i))), Some{pv}) == True{} : Bool}:
  +ppos = pos_of_ne(IX.par(i), e)
  +hppi = N.lt_trans(IX.par(IX.par(i)), IX.par(i), i, IX.par_lt(IX.par(i), N.succ_le_lt(0n, IX.par(i), ppos)), IX.par_lt(i, N.succ_le_lt(0n, i, hpos)))
  +hm = pair_ok_val(~A, ~cmp, ulog(~A, t, i, x), IX.par(i), ppos, SL.exc_at(~A, ~cmp, ulog(~A, t, i, x), n, i, IX.par(i), hexc, N.lt_trans(IX.par(i), i, n, IX.par_lt(i, N.succ_le_lt(0n, i, hpos)), hin), par_ne(i, hpos)))
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(IX.par(i))), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(IX.par(i))), u2_off(~A, d, t, i, x, pv, IX.par(IX.par(i)), SL.ne_sym(i, IX.par(IX.par(i)), N.is_eq_lt(IX.par(IX.par(i)), i, hppi)), SL.ne_sym(IX.par(i), IX.par(IX.par(i)), N.is_eq_lt(IX.par(IX.par(i)), IX.par(i), IX.par_lt(IX.par(i), N.succ_le_lt(0n, IX.par(i), ppos)))), hi, pf)) : {SL.mle(~A, ~cmp, _, Some{pv}) == True{} : Bool}
  %ulog_off(~A, t, i, x, IX.par(IX.par(i)), SL.ne_sym(i, IX.par(IX.par(i)), N.is_eq_lt(IX.par(IX.par(i)), i, hppi))) : {SL.mle(~A, ~cmp, _, Some{pv}) == True{} : Bool}
  %u1_at_p(~A, t, i, x, pv, hpos, hpv) : {SL.mle(~A, ~cmp, SL.slot(~A, ulog(~A, t, i, x), IX.par(IX.par(i))), _) == True{} : Bool}
  hm


def h2_key(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +n: Nat, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hin: {Nat.is_lt(i, n) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}, +hnle: {S.le(~A, ~cmp, pv, x) == False{} : Bool}, +hexc: {SL.ho_exc(~A, ~cmp, ulog(~A, t, i, x), n, i) == True{} : Bool}, b: Bool, +eb: {Nat.is_eq(IX.par(i), 0n) == b : Bool}) -> {SL.mle(~A, ~cmp, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(IX.par(i))), Some{pv}) == True{} : Bool}:
  match b:
    case True{}:
      h2_key_root(~A, ~cmp, ~o, d, t, i, x, pv, N.eq_from_is_eq(IX.par(i), 0n, eb), hi, hpos, pf, hnle)
    case False{}:
      h2_key_deep(~A, ~cmp, d, t, i, x, pv, n, eb, hi, hin, hpos, pf, hpv, hexc)

def kid_mle_same(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +c: Nat, +eb: {Nat.is_eq(c, i) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +key: {SL.mle(~A, ~cmp, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(IX.par(i))), Some{pv}) == True{} : Bool}) -> {SL.mle(~A, ~cmp, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(IX.par(i))), SL.slot(~A, u2_of(~A, d, t, i, x, pv), c)) == True{} : Bool}:
  %Equal.sym(Nat, c, i, N.eq_from_is_eq(c, i, eb)) : {SL.mle(~A, ~cmp, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(IX.par(i))), SL.slot(~A, u2_of(~A, d, t, i, x, pv), _)) == True{} : Bool}
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, u2_of(~A, d, t, i, x, pv), i), Some{pv}, u2_at_i(~A, d, t, i, x, pv, hi, hpos, pf)) : {SL.mle(~A, ~cmp, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(IX.par(i))), _) == True{} : Bool}
  key
def kid_mle_other(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +n: Nat, +c: Nat, +epc: {IX.par(c) == IX.par(i) : Nat}, +hcpos: {Nat.is_le(1n, c) == True{} : Bool}, +hcn: {Nat.is_lt(c, n) == True{} : Bool}, +eb: {Nat.is_eq(c, i) == False{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}, +hexc: {SL.ho_exc(~A, ~cmp, ulog(~A, t, i, x), n, i) == True{} : Bool}, +key: {SL.mle(~A, ~cmp, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(IX.par(i))), Some{pv}) == True{} : Bool}) -> {SL.mle(~A, ~cmp, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(IX.par(i))), SL.slot(~A, u2_of(~A, d, t, i, x, pv), c)) == True{} : Bool}:
  +hpic = N.is_eq_lt(IX.par(i), c, L.subst(Nat, z => {Nat.is_lt(z, c) == True{} : Bool}, IX.par(c), IX.par(i), epc, IX.par_lt(c, N.succ_le_lt(0n, c, hcpos))))
  +hb = h1n_old(~A, ~cmp, t, i, x, pv, c, SL.ne_sym(i, c, eb), epc, hcpos, hpos, hpv, SL.exc_at(~A, ~cmp, ulog(~A, t, i, x), n, i, c, hexc, hcn, eb))
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, u2_of(~A, d, t, i, x, pv), c), SL.slot(~A, AR.slots(Maybe<&2, A>, t), c), u2_off(~A, d, t, i, x, pv, c, SL.ne_sym(i, c, eb), hpic, hi, pf)) : {SL.mle(~A, ~cmp, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(IX.par(i))), _) == True{} : Bool}
  SL.mle_trans(~A, ~cmp, ~o, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(IX.par(i))), pv, SL.slot(~A, AR.slots(Maybe<&2, A>, t), c), key, hb)
def kid_mle(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +n: Nat, +c: Nat, +epc: {IX.par(c) == IX.par(i) : Nat}, +hcpos: {Nat.is_le(1n, c) == True{} : Bool}, +hcn: {Nat.is_lt(c, n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hin: {Nat.is_lt(i, n) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}, +hnle: {S.le(~A, ~cmp, pv, x) == False{} : Bool}, +hexc: {SL.ho_exc(~A, ~cmp, ulog(~A, t, i, x), n, i) == True{} : Bool}, b: Bool, +eb: {Nat.is_eq(c, i) == b : Bool}) -> {SL.mle(~A, ~cmp, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(IX.par(i))), SL.slot(~A, u2_of(~A, d, t, i, x, pv), c)) == True{} : Bool}:
  match b:
    case True{}:
      kid_mle_same(~A, ~cmp, d, t, i, x, pv, c, eb, hi, hpos, pf, h2_key(~A, ~cmp, ~o, d, t, i, x, pv, n, hi, hin, hpos, pf, hpv, hnle, hexc, Nat.is_eq(IX.par(i), 0n), {==}))
    case False{}:
      kid_mle_other(~A, ~cmp, ~o, d, t, i, x, pv, n, c, epc, hcpos, hcn, eb, hi, hpos, pf, hpv, hexc, h2_key(~A, ~cmp, ~o, d, t, i, x, pv, n, hi, hin, hpos, pf, hpv, hnle, hexc, Nat.is_eq(IX.par(i), 0n), {==}))

# H2 for the next state: both children of the new hole
def kid_next(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +n: Nat, +c: Nat, +epc: {IX.par(c) == IX.par(i) : Nat}, +hcpos: {Nat.is_le(1n, c) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hin: {Nat.is_lt(i, n) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}, +hnle: {S.le(~A, ~cmp, pv, x) == False{} : Bool}, +hexc: {SL.ho_exc(~A, ~cmp, ulog(~A, t, i, x), n, i) == True{} : Bool}, b: Bool, +eb: {Nat.is_lt(c, n) == b : Bool}) -> {SL.kid_le(~A, ~cmp, u2_of(~A, d, t, i, x, pv), n, IX.par(IX.par(i)), c) == True{} : Bool}:
  match b:
    case False{}:
      SL.kid_le_out(~A, ~cmp, u2_of(~A, d, t, i, x, pv), n, IX.par(IX.par(i)), c, eb)
    case True{}:
      SL.kid_le_in(~A, ~cmp, u2_of(~A, d, t, i, x, pv), n, IX.par(IX.par(i)), c, eb,
        kid_mle(~A, ~cmp, ~o, d, t, i, x, pv, n, c, epc, hcpos, eb, hi, hin, hpos, pf, hpv, hnle, hexc, Nat.is_eq(c, i), {==}))

def kids_next(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +n: Nat, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hin: {Nat.is_lt(i, n) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}, +hnle: {S.le(~A, ~cmp, pv, x) == False{} : Bool}, +hexc: {SL.ho_exc(~A, ~cmp, ulog(~A, t, i, x), n, i) == True{} : Bool}) -> {SL.kids_le(~A, ~cmp, u2_of(~A, d, t, i, x, pv), n, IX.par(IX.par(i)), IX.par(i)) == True{} : Bool}:
  L.and_intro(SL.kid_le(~A, ~cmp, u2_of(~A, d, t, i, x, pv), n, IX.par(IX.par(i)), IX.kidl(IX.par(i))), SL.kid_le(~A, ~cmp, u2_of(~A, d, t, i, x, pv), n, IX.par(IX.par(i)), IX.kidr(IX.par(i))),
    kid_next(~A, ~cmp, ~o, d, t, i, x, pv, n, IX.kidl(IX.par(i)), IX.par_kidl(IX.par(i)), IX.kidl_pos1(IX.par(i)), hi, hin, hpos, pf, hpv, hnle, hexc, Nat.is_lt(IX.kidl(IX.par(i)), n), {==}),
    kid_next(~A, ~cmp, ~o, d, t, i, x, pv, n, IX.kidr(IX.par(i)), IX.par_kidr(IX.par(i)), IX.kidr_pos1(IX.par(i)), hi, hin, hpos, pf, hpv, hnle, hexc, Nat.is_lt(IX.kidr(IX.par(i)), n), {==}))

# ---- the three remaining invariants of the next state ----

def skip_next(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +n: Nat, +m: Nat, +hmn: {Nat.is_lt(m, n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}, +hnle: {S.le(~A, ~cmp, pv, x) == False{} : Bool}, +hexc: {SL.ho_exc(~A, ~cmp, ulog(~A, t, i, x), n, i) == True{} : Bool}, +hkids: {SL.kids_le(~A, ~cmp, ulog(~A, t, i, x), n, IX.par(i), i) == True{} : Bool}, b: Bool, +eb: {Nat.is_eq(m, IX.par(i)) == b : Bool}) -> {SL.pair_skip(~A, ~cmp, u2_of(~A, d, t, i, x, pv), m, IX.par(i)) == True{} : Bool}:
  match b:
    case True{}:
      SL.skip_eq(~A, ~cmp, u2_of(~A, d, t, i, x, pv), m, IX.par(i), eb)
    case False{}:
      SL.skip_ne(~A, ~cmp, u2_of(~A, d, t, i, x, pv), m, IX.par(i), eb,
        h1_next_at(~A, ~cmp, ~o, d, t, i, x, pv, n, m, hmn, SL.ne_sym(IX.par(i), m, eb), hi, hpos, pf, hpv, hnle, hexc, hkids))

def exc_next(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +n: Nat, k: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}, +hnle: {S.le(~A, ~cmp, pv, x) == False{} : Bool}, +hexc: {SL.ho_exc(~A, ~cmp, ulog(~A, t, i, x), n, i) == True{} : Bool}, +hkids: {SL.kids_le(~A, ~cmp, ulog(~A, t, i, x), n, IX.par(i), i) == True{} : Bool}) -> {SL.ho_exc(~A, ~cmp, u2_of(~A, d, t, i, x, pv), k, IX.par(i)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +m:
      L.and_intro(SL.pair_skip(~A, ~cmp, u2_of(~A, d, t, i, x, pv), m, IX.par(i)), SL.ho_exc(~A, ~cmp, u2_of(~A, d, t, i, x, pv), m, IX.par(i)),
        skip_next(~A, ~cmp, ~o, d, t, i, x, pv, n, m, N.lt_le_trans(m, 1n+m, n, N.lt_succ(m), hk), hi, hpos, pf, hpv, hnle, hexc, hkids, Nat.is_eq(m, IX.par(i)), {==}),
        exc_next(~A, ~cmp, ~o, d, t, i, x, pv, n, m, N.le_trans(m, 1n+m, n, N.le_succ(m), hk), hi, hpos, pf, hpv, hnle, hexc, hkids))

def some_of_eq(~A: Data, m: Maybe<&2, A>, +v: A, +e: {m == Some{v} : Maybe<&2, A>}) -> {Maybe.is_some(&2, A, m) == True{} : Bool}:
  L.subst(Maybe<&2, A>, w => {Maybe.is_some(&2, A, w) == True{} : Bool}, Some{v}, m, Equal.sym(Maybe<&2, A>, m, Some{v}, e), {==})

def some_next(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +n: Nat, +m: Nat, +hmn: {Nat.is_lt(m, n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hlay: {SL.lay(~A, ulog(~A, t, i, x), n) == True{} : Bool}, b: Bool, +eb: {Nat.is_eq(m, IX.par(i)) == b : Bool}, c: Bool, +ec: {Nat.is_eq(m, i) == c : Bool}) -> {Maybe.is_some(&2, A, SL.slot(~A, u2_of(~A, d, t, i, x, pv), m)) == True{} : Bool}:
  match b c:
    case True{} _:
      L.subst(Nat, z => {Maybe.is_some(&2, A, SL.slot(~A, u2_of(~A, d, t, i, x, pv), z)) == True{} : Bool}, IX.par(i), m, Equal.sym(Nat, m, IX.par(i), N.eq_from_is_eq(m, IX.par(i), eb)),
        some_of_eq(~A, SL.slot(~A, u2_of(~A, d, t, i, x, pv), IX.par(i)), x, u2_at_p(~A, d, t, i, x, pv, hi, hpos, pf)))
    case False{} True{}:
      L.subst(Nat, z => {Maybe.is_some(&2, A, SL.slot(~A, u2_of(~A, d, t, i, x, pv), z)) == True{} : Bool}, i, m, Equal.sym(Nat, m, i, N.eq_from_is_eq(m, i, ec)),
        some_of_eq(~A, SL.slot(~A, u2_of(~A, d, t, i, x, pv), i), pv, u2_at_i(~A, d, t, i, x, pv, hi, hpos, pf)))
    case False{} False{}:
      L.subst(Maybe<&2, A>, w => {Maybe.is_some(&2, A, w) == True{} : Bool}, SL.slot(~A, ulog(~A, t, i, x), m), SL.slot(~A, u2_of(~A, d, t, i, x, pv), m),
        Equal.trans(Maybe<&2, A>, SL.slot(~A, ulog(~A, t, i, x), m), SL.slot(~A, AR.slots(Maybe<&2, A>, t), m), SL.slot(~A, u2_of(~A, d, t, i, x, pv), m),
          ulog_off(~A, t, i, x, m, SL.ne_sym(i, m, ec)),
          Equal.sym(Maybe<&2, A>, SL.slot(~A, u2_of(~A, d, t, i, x, pv), m), SL.slot(~A, AR.slots(Maybe<&2, A>, t), m), u2_off(~A, d, t, i, x, pv, m, SL.ne_sym(i, m, ec), SL.ne_sym(IX.par(i), m, eb), hi, pf))),
        SL.lay_at(~A, ulog(~A, t, i, x), n, m, hlay, hmn))

def lay_next(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +n: Nat, k: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hlay: {SL.lay(~A, ulog(~A, t, i, x), n) == True{} : Bool}) -> {SL.lay(~A, u2_of(~A, d, t, i, x, pv), k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +m:
      L.and_intro(Maybe.is_some(&2, A, SL.slot(~A, u2_of(~A, d, t, i, x, pv), m)), SL.lay(~A, u2_of(~A, d, t, i, x, pv), m),
        some_next(~A, ~cmp, d, t, i, x, pv, n, m, N.lt_le_trans(m, 1n+m, n, N.lt_succ(m), hk), hi, hpos, pf, hlay, Nat.is_eq(m, IX.par(i)), {==}, Nat.is_eq(m, i), {==}),
        lay_next(~A, ~cmp, d, t, i, x, pv, n, m, N.le_trans(m, 1n+m, n, N.le_succ(m), hk), hi, hpos, pf, hlay))

# ---- the multiset of the next state ----

def u2_swap_form(~A: Data, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {u2_of(~A, d, t, i, x, pv) == SC.update(Maybe<&2, A>, SC.update(Maybe<&2, A>, ulog(~A, t, i, x), i, Some{pv}), IX.par(i), Some{x}) : List<&2, Maybe<&2, A>>}:
  Equal.cong(List<&2, Maybe<&2, A>>, List<&2, Maybe<&2, A>>, ss => SC.update(Maybe<&2, A>, ss, IX.par(i), Some{x}), AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, pv)), SC.update(Maybe<&2, A>, ulog(~A, t, i, x), i, Some{pv}),
    Equal.trans(List<&2, Maybe<&2, A>>, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, pv)), ulog(~A, t, i, pv), SC.update(Maybe<&2, A>, ulog(~A, t, i, x), i, Some{pv}),
      set_slots(~A, d, t, i, pv, hi, pf),
      Equal.sym(List<&2, Maybe<&2, A>>, SC.update(Maybe<&2, A>, ulog(~A, t, i, x), i, Some{pv}), ulog(~A, t, i, pv), BG.upd_upd_same(~A, AR.slots(Maybe<&2, A>, t), i, Some{x}, Some{pv}))))

def ms_next(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +n: Nat, +tgt: List<&2, A>, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hin: {Nat.is_lt(i, n) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}, +hms: {V.msort(~A, ~cmp, V.vals(~A, ulog(~A, t, i, x), n)) == tgt : List<&2, A>}) -> {V.msort(~A, ~cmp, V.vals(~A, u2_of(~A, d, t, i, x, pv), n)) == tgt : List<&2, A>}:
  %Equal.sym(List<&2, Maybe<&2, A>>, u2_of(~A, d, t, i, x, pv), SC.update(Maybe<&2, A>, SC.update(Maybe<&2, A>, ulog(~A, t, i, x), i, Some{pv}), IX.par(i), Some{x}), u2_swap_form(~A, d, t, i, x, pv, hi, pf)) : {V.msort(~A, ~cmp, V.vals(~A, _, n)) == tgt : List<&2, A>}
  Equal.trans(List<&2, A>, V.msort(~A, ~cmp, V.vals(~A, SC.update(Maybe<&2, A>, SC.update(Maybe<&2, A>, ulog(~A, t, i, x), i, Some{pv}), IX.par(i), Some{x}), n)), V.msort(~A, ~cmp, V.vals(~A, ulog(~A, t, i, x), n)), tgt,
    BG.vals_swap(~A, ~cmp, ~o, ulog(~A, t, i, x), n, i, IX.par(i), x, pv, hin,
      N.lt_trans(IX.par(i), i, n, IX.par_lt(i, N.succ_le_lt(0n, i, hpos)), hin),
      SL.ne_sym(i, IX.par(i), par_ne(i, hpos)),
      ulog_at(~A, d, t, i, x, hi, pf),
      u1_at_p(~A, t, i, x, pv, hpos, hpv)),
    hms)

# ---- the loop ----

def pair_ok_zero(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +i: Nat, +e: {Nat.is_eq(i, 0n) == True{} : Bool}) -> {SL.pair_ok(~A, ~cmp, ss, i) == True{} : Bool}:
  L.subst(Nat, z => {SL.pair_ok(~A, ~cmp, ss, z) == True{} : Bool}, 0n, i, Equal.sym(Nat, i, 0n, N.eq_from_is_eq(i, 0n, e)), {==})

def pair_none(~A: Data, ~cmp: A -> A -> Cmp, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +em: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == None{} : Maybe<&2, A>}) -> {SL.pair_ok(~A, ~cmp, ulog(~A, t, i, x), i) == True{} : Bool}:
  pair_ok_pos(~A, ~cmp, ulog(~A, t, i, x), i, hpos,
    L.subst(Maybe<&2, A>, w => {SL.mle(~A, ~cmp, w, SL.slot(~A, ulog(~A, t, i, x), i)) == True{} : Bool}, None{}, SL.slot(~A, ulog(~A, t, i, x), IX.par(i)),
      Equal.sym(Maybe<&2, A>, SL.slot(~A, ulog(~A, t, i, x), IX.par(i)), None{},
        Equal.trans(Maybe<&2, A>, SL.slot(~A, ulog(~A, t, i, x), IX.par(i)), SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)), None{}, ulog_off(~A, t, i, x, IX.par(i), SL.ne_sym(i, IX.par(i), par_ne(i, hpos))), em)),
      SL.mle_none_l(~A, ~cmp, SL.slot(~A, ulog(~A, t, i, x), i))))

def pair_stop_mle(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}, +hle: {S.le(~A, ~cmp, pv, x) == True{} : Bool}) -> {SL.mle(~A, ~cmp, SL.slot(~A, ulog(~A, t, i, x), IX.par(i)), SL.slot(~A, ulog(~A, t, i, x), i)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, ulog(~A, t, i, x), IX.par(i)), Some{pv}, u1_at_p(~A, t, i, x, pv, hpos, hpv)) : {SL.mle(~A, ~cmp, _, SL.slot(~A, ulog(~A, t, i, x), i)) == True{} : Bool}
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, ulog(~A, t, i, x), i), Some{x}, ulog_at(~A, d, t, i, x, hi, pf)) : {SL.mle(~A, ~cmp, Some{pv}, _) == True{} : Bool}
  hle

def pair_stop(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hpv: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == Some{pv} : Maybe<&2, A>}, +hle: {S.le(~A, ~cmp, pv, x) == True{} : Bool}) -> {SL.pair_ok(~A, ~cmp, ulog(~A, t, i, x), i) == True{} : Bool}:
  pair_ok_pos(~A, ~cmp, ulog(~A, t, i, x), i, hpos,
    pair_stop_mle(~A, ~cmp, d, t, i, x, pv, hi, hpos, pf, hpv, hle))

def up_carry_go(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +tgt: List<&2, A>, +f: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +t3: AR.Tree<Maybe<&2, A>>, +eq: {H.up_go(~A, ~cmp, 1n+f, x, ureal(~A, Mv{t, i, pv, IX.par(i)})) == H.up_go(~A, ~cmp, f, x, ureal(~A, uprobe(~A, ~cmp, t2_of(~A, d, t, i, pv), IX.par(i), x))) : Array<Maybe<&2, A>>}, rest: {H.up_go(~A, ~cmp, f, x, ureal(~A, uprobe(~A, ~cmp, t2_of(~A, d, t, i, pv), IX.par(i), x))) == AR.thaw(Maybe<&2, A>, t3) : Array<Maybe<&2, A>>} & ({AR.perfect(Maybe<&2, A>, d, t3) == True{} : Bool} & ({SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t3), n) == True{} : Bool} & ({SL.lay(~A, AR.slots(Maybe<&2, A>, t3), n) == True{} : Bool} & {V.msort(~A, ~cmp, V.vals(~A, AR.slots(Maybe<&2, A>, t3), n)) == tgt : List<&2, A>}))) ) -> UpOK(~A, ~cmp, d, n, tgt, 1n+f, x, Mv{t, i, pv, IX.par(i)}):
  (e1, more) = rest
  (t3, (Equal.trans(Array<Maybe<&2, A>>, H.up_go(~A, ~cmp, 1n+f, x, ureal(~A, Mv{t, i, pv, IX.par(i)})), H.up_go(~A, ~cmp, f, x, ureal(~A, uprobe(~A, ~cmp, t2_of(~A, d, t, i, pv), IX.par(i), x))), AR.thaw(Maybe<&2, A>, t3), eq, e1), more))

# The recursive result is about the next state; its first component has to be
# rewritten through the step the loop took.
def up_carry(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +tgt: List<&2, A>, +f: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +eq: {H.up_go(~A, ~cmp, 1n+f, x, ureal(~A, Mv{t, i, pv, IX.par(i)})) == H.up_go(~A, ~cmp, f, x, ureal(~A, uprobe(~A, ~cmp, t2_of(~A, d, t, i, pv), IX.par(i), x))) : Array<Maybe<&2, A>>}, rec: UpOK(~A, ~cmp, d, n, tgt, f, x, uprobe(~A, ~cmp, t2_of(~A, d, t, i, pv), IX.par(i), x))) -> UpOK(~A, ~cmp, d, n, tgt, 1n+f, x, Mv{t, i, pv, IX.par(i)}):
  (t3, rest) = rec
  up_carry_go(~A, ~cmp, d, n, tgt, f, t, i, x, pv, t3, eq, rest)

def up_step_eq(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +f: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +pv: A, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hpos: {Nat.is_le(1n, i) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {H.up_go(~A, ~cmp, 1n+f, x, ureal(~A, Mv{t, i, pv, IX.par(i)})) == H.up_go(~A, ~cmp, f, x, ureal(~A, uprobe(~A, ~cmp, t2_of(~A, d, t, i, pv), IX.par(i), x))) : Array<Maybe<&2, A>>}:
  %Equal.sym(Array<Maybe<&2, A>>, Array.set(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), U32.from_nat(i), Some{pv}), AR.thaw(Maybe<&2, A>, t2_of(~A, d, t, i, pv)), set_eq(~A, d, t, i, pv, hd, hi, pf)) : {H.up_go(~A, ~cmp, f, x, H.up_probe(~A, ~cmp, U32.from_nat(IX.par(i)), x, _)) == H.up_go(~A, ~cmp, f, x, ureal(~A, uprobe(~A, ~cmp, t2_of(~A, d, t, i, pv), IX.par(i), x))) : Array<Maybe<&2, A>>}
  Equal.cong(H.Up<A>, Array<Maybe<&2, A>>, s => H.up_go(~A, ~cmp, f, x, s), H.up_probe(~A, ~cmp, U32.from_nat(IX.par(i)), x, AR.thaw(Maybe<&2, A>, t2_of(~A, d, t, i, pv))), ureal(~A, uprobe(~A, ~cmp, t2_of(~A, d, t, i, pv), IX.par(i), x)),
    uprobe_ok(~A, ~cmp, d, t2_of(~A, d, t, i, pv), IX.par(i), x, hd, par_lt_d(d, i, hi, hpos), t2_perfect(~A, d, t, i, pv, pf)))

# The sift-up loop. `hfuel` is what says the loop has enough steps left: the
# hole index is below 2^fuel, which halves with the fuel, so the loop can only
# run out of fuel at the root -- where it stops anyway.
def up_loop(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), fuel: Nat, +d: Nat, +n: Nat, +tgt: List<&2, A>, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hin: {Nat.is_lt(i, n) == True{} : Bool}, +hfuel: {Nat.is_lt(i, SC.pow2(fuel)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hexc: {SL.ho_exc(~A, ~cmp, ulog(~A, t, i, x), n, i) == True{} : Bool}, +hkids: {SL.kids_le(~A, ~cmp, ulog(~A, t, i, x), n, IX.par(i), i) == True{} : Bool}, +hlay: {SL.lay(~A, ulog(~A, t, i, x), n) == True{} : Bool}, +hms: {V.msort(~A, ~cmp, V.vals(~A, ulog(~A, t, i, x), n)) == tgt : List<&2, A>}, bz: Bool, +ebz: {Nat.is_eq(i, 0n) == bz : Bool}, m: Maybe<&2, A>, +em: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)) == m : Maybe<&2, A>}, ble: Bool, +eble: {S.le(~A, ~cmp, mval(~A, m, x), x) == ble : Bool}) -> UpOK(~A, ~cmp, d, n, tgt, fuel, x, uprobe(~A, ~cmp, t, i, x)):
  match fuel bz m ble:
    case _ True{} _ _:
      %Equal.sym(Bool, Nat.is_eq(i, 0n), True{}, ebz) : UpOK(~A, ~cmp, d, n, tgt, fuel, x, uroot(~A, ~cmp, t, i, x, _))
      up_stop_ok(~A, ~cmp, d, n, tgt, fuel, t, i, x, hd, hi, pf, pair_ok_zero(~A, ~cmp, ulog(~A, t, i, x), i, ebz), hexc, hlay, hms)
    case _ False{} None{} _:
      %Equal.sym(Bool, Nat.is_eq(i, 0n), False{}, ebz) : UpOK(~A, ~cmp, d, n, tgt, fuel, x, uroot(~A, ~cmp, t, i, x, _))
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)), None{}, em) : UpOK(~A, ~cmp, d, n, tgt, fuel, x, umb(~A, ~cmp, t, i, x, IX.par(i), _))
      up_stop_ok(~A, ~cmp, d, n, tgt, fuel, t, i, x, hd, hi, pf, pair_none(~A, ~cmp, t, i, x, pos_of_ne(i, ebz), em), hexc, hlay, hms)
    case _ False{} Some{+pv} True{}:
      %Equal.sym(Bool, Nat.is_eq(i, 0n), False{}, ebz) : UpOK(~A, ~cmp, d, n, tgt, fuel, x, uroot(~A, ~cmp, t, i, x, _))
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)), Some{pv}, em) : UpOK(~A, ~cmp, d, n, tgt, fuel, x, umb(~A, ~cmp, t, i, x, IX.par(i), _))
      %Equal.sym(Bool, S.le(~A, ~cmp, pv, x), True{}, eble) : UpOK(~A, ~cmp, d, n, tgt, fuel, x, udec(~A, ~cmp, t, i, pv, IX.par(i), _))
      up_stop_ok(~A, ~cmp, d, n, tgt, fuel, t, i, x, hd, hi, pf, pair_stop(~A, ~cmp, d, t, i, x, pv, hi, pos_of_ne(i, ebz), pf, em, eble), hexc, hlay, hms)
    case 0n False{} Some{pv} False{}:
      Empty.absurd(UpOK(~A, ~cmp, d, n, tgt, 0n, x, uprobe(~A, ~cmp, t, i, x)),
        L.true_not_false(Nat.is_eq(i, 0n), L.subst(Nat, z => {Nat.is_eq(z, 0n) == True{} : Bool}, 0n, i, Equal.sym(Nat, i, 0n, U.lt_one_zero(i, hfuel)), {==}), ebz))
    case 1n+ +f False{} Some{+pv} False{}:
      %Equal.sym(Bool, Nat.is_eq(i, 0n), False{}, ebz) : UpOK(~A, ~cmp, d, n, tgt, 1n+f, x, uroot(~A, ~cmp, t, i, x, _))
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)), Some{pv}, em) : UpOK(~A, ~cmp, d, n, tgt, 1n+f, x, umb(~A, ~cmp, t, i, x, IX.par(i), _))
      %Equal.sym(Bool, S.le(~A, ~cmp, pv, x), False{}, eble) : UpOK(~A, ~cmp, d, n, tgt, 1n+f, x, udec(~A, ~cmp, t, i, pv, IX.par(i), _))
      up_carry(~A, ~cmp, d, n, tgt, f, t, i, x, pv, up_step_eq(~A, ~cmp, d, f, t, i, x, pv, hd, hi, pos_of_ne(i, ebz), pf),
        up_loop(~A, ~cmp, ~o, f, d, n, tgt, t2_of(~A, d, t, i, pv), IX.par(i), x, hd,
          par_lt_d(d, i, hi, pos_of_ne(i, ebz)),
          N.lt_trans(IX.par(i), i, n, IX.par_lt(i, N.succ_le_lt(0n, i, pos_of_ne(i, ebz))), hin),
          IX.par_bound(i, f, hfuel),
          t2_perfect(~A, d, t, i, pv, pf),
          exc_next(~A, ~cmp, ~o, d, t, i, x, pv, n, n, N.le_refl(n), hi, pos_of_ne(i, ebz), pf, em, eble, hexc, hkids),
          kids_next(~A, ~cmp, ~o, d, t, i, x, pv, n, hi, hin, pos_of_ne(i, ebz), pf, em, eble, hexc),
          lay_next(~A, ~cmp, d, t, i, x, pv, n, n, N.le_refl(n), hi, pos_of_ne(i, ebz), pf, hlay),
          ms_next(~A, ~cmp, ~o, d, t, i, x, pv, n, tgt, hi, hin, pos_of_ne(i, ebz), pf, em, hms),
          Nat.is_eq(IX.par(i), 0n), {==},
          SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, pv)), IX.par(IX.par(i))), {==},
          S.le(~A, ~cmp, mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t2_of(~A, d, t, i, pv)), IX.par(IX.par(i))), x), x), {==}))

# ---- the entry point ----

def SiftOK(~A: Data, ~cmp: A -> A -> Cmp, d: Nat, n: Nat, tgt: List<&2, A>, fuel: Nat, t: AR.Tree<Maybe<&2, A>>, i: Nat, x: A) -> Type:
  Sigma<&1, &1, AR.Tree<Maybe<&2, A>>, t2 => {H.sift_up(~A, ~cmp, fuel, U32.from_nat(i), x, AR.thaw(Maybe<&2, A>, t)) == AR.thaw(Maybe<&2, A>, t2) : Array<Maybe<&2, A>>} & ({AR.perfect(Maybe<&2, A>, d, t2) == True{} : Bool} & ({SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t2), n) == True{} : Bool} & ({SL.lay(~A, AR.slots(Maybe<&2, A>, t2), n) == True{} : Bool} & {V.msort(~A, ~cmp, V.vals(~A, AR.slots(Maybe<&2, A>, t2), n)) == tgt : List<&2, A>})))>

def sift_from_go(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +tgt: List<&2, A>, +fuel: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +t2: AR.Tree<Maybe<&2, A>>, +eq: {H.sift_up(~A, ~cmp, fuel, U32.from_nat(i), x, AR.thaw(Maybe<&2, A>, t)) == H.up_go(~A, ~cmp, fuel, x, ureal(~A, uprobe(~A, ~cmp, t, i, x))) : Array<Maybe<&2, A>>}, rest: {H.up_go(~A, ~cmp, fuel, x, ureal(~A, uprobe(~A, ~cmp, t, i, x))) == AR.thaw(Maybe<&2, A>, t2) : Array<Maybe<&2, A>>} & ({AR.perfect(Maybe<&2, A>, d, t2) == True{} : Bool} & ({SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t2), n) == True{} : Bool} & ({SL.lay(~A, AR.slots(Maybe<&2, A>, t2), n) == True{} : Bool} & {V.msort(~A, ~cmp, V.vals(~A, AR.slots(Maybe<&2, A>, t2), n)) == tgt : List<&2, A>}))) ) -> SiftOK(~A, ~cmp, d, n, tgt, fuel, t, i, x):
  (e1, more) = rest
  (t2, (Equal.trans(Array<Maybe<&2, A>>, H.sift_up(~A, ~cmp, fuel, U32.from_nat(i), x, AR.thaw(Maybe<&2, A>, t)), H.up_go(~A, ~cmp, fuel, x, ureal(~A, uprobe(~A, ~cmp, t, i, x))), AR.thaw(Maybe<&2, A>, t2), eq, e1), more))

def sift_from_loop(~A: Data, ~cmp: A -> A -> Cmp, +d: Nat, +n: Nat, +tgt: List<&2, A>, +fuel: Nat, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +eq: {H.sift_up(~A, ~cmp, fuel, U32.from_nat(i), x, AR.thaw(Maybe<&2, A>, t)) == H.up_go(~A, ~cmp, fuel, x, ureal(~A, uprobe(~A, ~cmp, t, i, x))) : Array<Maybe<&2, A>>}, r: UpOK(~A, ~cmp, d, n, tgt, fuel, x, uprobe(~A, ~cmp, t, i, x))) -> SiftOK(~A, ~cmp, d, n, tgt, fuel, t, i, x):
  (t2, rest) = r
  sift_from_go(~A, ~cmp, d, n, tgt, fuel, t, i, x, t2, eq, rest)

def sift_up_ok(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +fuel: Nat, +d: Nat, +n: Nat, +tgt: List<&2, A>, +t: AR.Tree<Maybe<&2, A>>, +i: Nat, +x: A, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hin: {Nat.is_lt(i, n) == True{} : Bool}, +hfuel: {Nat.is_lt(i, SC.pow2(fuel)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}, +hexc: {SL.ho_exc(~A, ~cmp, ulog(~A, t, i, x), n, i) == True{} : Bool}, +hkids: {SL.kids_le(~A, ~cmp, ulog(~A, t, i, x), n, IX.par(i), i) == True{} : Bool}, +hlay: {SL.lay(~A, ulog(~A, t, i, x), n) == True{} : Bool}, +hms: {V.msort(~A, ~cmp, V.vals(~A, ulog(~A, t, i, x), n)) == tgt : List<&2, A>}) -> SiftOK(~A, ~cmp, d, n, tgt, fuel, t, i, x):
  sift_from_loop(~A, ~cmp, d, n, tgt, fuel, t, i, x,
    Equal.cong(H.Up<A>, Array<Maybe<&2, A>>, s => H.up_go(~A, ~cmp, fuel, x, s), H.up_probe(~A, ~cmp, U32.from_nat(i), x, AR.thaw(Maybe<&2, A>, t)), ureal(~A, uprobe(~A, ~cmp, t, i, x)), uprobe_ok(~A, ~cmp, d, t, i, x, hd, hi, pf)),
    up_loop(~A, ~cmp, ~o, fuel, d, n, tgt, t, i, x, hd, hi, hin, hfuel, pf, hexc, hkids, hlay, hms, Nat.is_eq(i, 0n), {==}, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)), {==}, S.le(~A, ~cmp, mval(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), IX.par(i)), x), x), {==}))
