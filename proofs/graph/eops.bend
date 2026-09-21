import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/u32alg.bend as UA
import ../lib/order.bend as O
import ../lib/array.bend as AR
import ../lib/array2.bend as A2
import ../balanced_search_tree/sorted.bend as SO
import ../../spec/common.bend as SC
import ../../spec/balanced_search_tree.bend as S
import ../../spec/graph.bend as GS
import ../../src/graph.bend as G
import ../../types/balanced_search_tree.bend as BE
import ../../types/graph.bend as E
import ./state.bend as ST
import ./shift.bend as SH
import ./search.bend as SE
import ./window.bend as W
import ./lb.bend as LB
import ./blk.bend as BK
import ./edge.bend as ED
import ./ops.bend as OP
import ./lists.bend as LS
import ./blkops.bend as BO
import ./nbrops.bend as NO

# The model after replacing the neighbour block of one present vertex, and
# the edge operations built from it.

# ---- windows and the abstraction under an update ----

def drop_update(-A: Data, +xs: List<&2, A>, +lo: Nat, +l: Nat, +b: A) -> {SC.drop(A, SC.update(A, xs, Nat.add(lo, l), b), lo) == SC.update(A, SC.drop(A, xs, lo), l, b) : List<&2, A>}:
  match xs lo:
    case Nil{} lo0:
      Equal.trans(List<&2, A>, SC.drop(A, SC.update(A, Nil{}, Nat.add(lo0, l), b), lo0), Nil{}, SC.update(A, SC.drop(A, Nil{}, lo0), l, b),
        W.nil_drop(A, lo0),
        L.subst(List<&2, A>, z => {Nil{} == SC.update(A, z, l, b) : List<&2, A>}, Nil{}, SC.drop(A, Nil{}, lo0), Equal.sym(List<&2, A>, SC.drop(A, Nil{}, lo0), Nil{}, W.nil_drop(A, lo0)), {==}))
    case Con{+h, +t} 0n:
      Equal.trans(List<&2, A>, SC.drop(A, SC.update(A, Con{h, t}, l, b), 0n), SC.update(A, Con{h, t}, l, b), SC.update(A, SC.drop(A, Con{h, t}, 0n), l, b),
        W.drop_zero(A, SC.update(A, Con{h, t}, l, b)),
        {==})
    case Con{+h, +t} 1n+p:
      drop_update(A, t, p, l, b)

def win_update(-A: Data, +xs: List<&2, A>, +lo: Nat, +k: Nat, +l: Nat, +b: A) -> {ST.win(A, SC.update(A, xs, Nat.add(lo, l), b), lo, k) == SC.update(A, ST.win(A, xs, lo, k), l, b) : List<&2, A>}:
  Equal.trans(List<&2, A>, SC.take(A, SC.drop(A, SC.update(A, xs, Nat.add(lo, l), b), lo), k), SC.take(A, SC.update(A, SC.drop(A, xs, lo), l, b), k), SC.update(A, ST.win(A, xs, lo, k), l, b),
    Equal.cong(List<&2, A>, List<&2, A>, z => SC.take(A, z, k), SC.drop(A, SC.update(A, xs, Nat.add(lo, l), b), lo), SC.update(A, SC.drop(A, xs, lo), l, b), drop_update(A, xs, lo, l, b)),
    LL.sc_take_update(A, SC.drop(A, xs, lo), l, b, k))

# The window of the adjacency array after storing b at slot lo + l.
def win_upd_tree(+d: Nat, +at: AR.Tree<AR.Tree<U32>>, +lo: Nat, +k: Nat, +l: Nat, +b: AR.Tree<U32>, +hj: {Nat.is_lt(Nat.add(lo, l), SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(AR.Tree<U32>, d, at) == True{} : Bool}) -> {ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, AR.upd(AR.Tree<U32>, d, at, Nat.add(lo, l), b)), lo, k) == SC.update(AR.Tree<U32>, ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, k), l, b) : List<&2, AR.Tree<U32>>}:
  Equal.trans(List<&2, AR.Tree<U32>>, ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, AR.upd(AR.Tree<U32>, d, at, Nat.add(lo, l), b)), lo, k), ST.win(AR.Tree<U32>, SC.update(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), Nat.add(lo, l), b), lo, k), SC.update(AR.Tree<U32>, ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, k), l, b),
    Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => ST.win(AR.Tree<U32>, z, lo, k), AR.slots(AR.Tree<U32>, AR.upd(AR.Tree<U32>, d, at, Nat.add(lo, l), b)), SC.update(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), Nat.add(lo, l), b), AR.upd_slots(AR.Tree<U32>, d, at, Nat.add(lo, l), b, hj, pf)),
    win_update(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, k, l, b))

def amodel_upd(+ks: List<&2, U32>, +bs: List<&2, AR.Tree<U32>>, +l: Nat, +b: AR.Tree<U32>, +hlen: {SC.length(U32, ks) == SC.length(AR.Tree<U32>, bs) : Nat}) -> {ST.amodel(ks, SC.update(AR.Tree<U32>, bs, l, b)) == LB.upd_at(List<&2, BE.Entry<U32, Unit>>, ST.amodel(ks, bs), l, BE.Entry{W.val_i(ks, l), ST.uset(ST.bents(b))}) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}:
  match ks bs l:
    case Nil{} Nil{} 0n:
      {==}
    case Nil{} Nil{} 1n+p:
      {==}
    case Nil{} Con{b0, bt} l0:
      Empty.absurd({ST.amodel(Nil{}, SC.update(AR.Tree<U32>, Con{b0, bt}, l0, b)) == LB.upd_at(List<&2, BE.Entry<U32, Unit>>, ST.amodel(Nil{}, Con{b0, bt}), l0, BE.Entry{W.val_i(Nil{}, l0), ST.uset(ST.bents(b))}) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}, N.zero_succ(SC.length(AR.Tree<U32>, bt), hlen))
    case Con{k0, kt} Nil{} l0:
      Empty.absurd({ST.amodel(Con{k0, kt}, SC.update(AR.Tree<U32>, Nil{}, l0, b)) == LB.upd_at(List<&2, BE.Entry<U32, Unit>>, ST.amodel(Con{k0, kt}, Nil{}), l0, BE.Entry{W.val_i(Con{k0, kt}, l0), ST.uset(ST.bents(b))}) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}, N.succ_zero(SC.length(U32, kt), hlen))
    case Con{+k0, +kt} Con{+b0, +bt} 0n:
      {==}
    case Con{+k0, +kt} Con{+b0, +bt} 1n+p:
      Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => Con{BE.Entry{k0, ST.uset(ST.bents(b0))}, z},
        ST.amodel(kt, SC.update(AR.Tree<U32>, bt, p, b)), LB.upd_at(List<&2, BE.Entry<U32, Unit>>, ST.amodel(kt, bt), p, BE.Entry{W.val_i(kt, p), ST.uset(ST.bents(b))}),
        amodel_upd(kt, bt, p, b, N.succ_inj(SC.length(U32, kt), SC.length(AR.Tree<U32>, bt), hlen)))

def val_of_eq(+ks: List<&2, U32>, +l: Nat, +x: U32, +h: {LB.eq_at(ks, l, x) == True{} : Bool}) -> {W.val_i(ks, l) == x : U32}:
  match ks l:
    case Nil{} l0:
      Empty.absurd({W.val_i(Nil{}, l0) == x : U32}, L.false_true(h))
    case Con{+y, +t} 0n:
      NO.is_eq_eq(y, x, h)
    case Con{+y, +t} 1n+p:
      val_of_eq(t, p, x, h)

# Replacing the block of a present vertex x is the specification's `put`.
def put_model(+ks: List<&2, U32>, +bs: List<&2, AR.Tree<U32>>, +x: U32, +b: AR.Tree<U32>, +hlen: {SC.length(U32, ks) == SC.length(AR.Tree<U32>, bs) : Nat}, +hf: {LB.eq_at(ks, W.lbu(x, ks), x) == True{} : Bool}) -> {ST.amodel(ks, SC.update(AR.Tree<U32>, bs, W.lbu(x, ks), b)) == GS.put(x, ST.uset(ST.bents(b)), ST.amodel(ks, bs)) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}:
  +am = ST.amodel(ks, bs)
  +l = W.lbu(x, ks)
  +s = ST.uset(ST.bents(b))
  +ekeys = W.amodel_keys(ks, bs, hlen)
  +elbx = Equal.trans(Nat, LB.lbx(List<&2, BE.Entry<U32, Unit>>, x, am), W.lbu(x, LB.keys_of(List<&2, BE.Entry<U32, Unit>>, am)), l,
    W.lbx_lbu(List<&2, BE.Entry<U32, Unit>>, x, am),
    Equal.cong(List<&2, U32>, Nat, ys => W.lbu(x, ys), LB.keys_of(List<&2, BE.Entry<U32, Unit>>, am), ks, ekeys))
  +hf2 = L.subst(Nat, z => {LB.eq_at(LB.keys_of(List<&2, BE.Entry<U32, Unit>>, am), z, x) == True{} : Bool}, l, LB.lbx(List<&2, BE.Entry<U32, Unit>>, x, am), Equal.sym(Nat, LB.lbx(List<&2, BE.Entry<U32, Unit>>, x, am), l, elbx),
    L.subst(List<&2, U32>, ys => {LB.eq_at(ys, l, x) == True{} : Bool}, ks, LB.keys_of(List<&2, BE.Entry<U32, Unit>>, am), Equal.sym(List<&2, U32>, LB.keys_of(List<&2, BE.Entry<U32, Unit>>, am), ks, ekeys), hf))
  Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, ST.amodel(ks, SC.update(AR.Tree<U32>, bs, l, b)), LB.upd_at(List<&2, BE.Entry<U32, Unit>>, am, l, BE.Entry{x, s}), GS.put(x, s, am),
    Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, ST.amodel(ks, SC.update(AR.Tree<U32>, bs, l, b)), LB.upd_at(List<&2, BE.Entry<U32, Unit>>, am, l, BE.Entry{W.val_i(ks, l), s}), LB.upd_at(List<&2, BE.Entry<U32, Unit>>, am, l, BE.Entry{x, s}),
      amodel_upd(ks, bs, l, b, hlen),
      Equal.cong(U32, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => LB.upd_at(List<&2, BE.Entry<U32, Unit>>, am, l, BE.Entry{z, s}), W.val_i(ks, l), x, val_of_eq(ks, l, x, hf))),
    L.subst(Nat, z => {LB.upd_at(List<&2, BE.Entry<U32, Unit>>, am, z, BE.Entry{x, s}) == GS.put(x, s, am) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}, LB.lbx(List<&2, BE.Entry<U32, Unit>>, x, am), l, elbx,
      LS.ins_old(List<&2, BE.Entry<U32, Unit>>, am, x, s, hf2)))

def blocks_update(+bs: List<&2, AR.Tree<U32>>, +l: Nat, +b: AR.Tree<U32>, +h: {ST.blocks_ok(bs) == True{} : Bool}, +hb: {ST.blk_ok(b) == True{} : Bool}) -> {ST.blocks_ok(SC.update(AR.Tree<U32>, bs, l, b)) == True{} : Bool}:
  match bs l:
    case Nil{} l0:
      {==}
    case Con{+b0, +t} 0n:
      L.and_intro(ST.blk_ok(b), ST.blocks_ok(t), hb, L.and_right(ST.blk_ok(b0), ST.blocks_ok(t), h))
    case Con{+b0, +t} 1n+p:
      L.and_intro(ST.blk_ok(b0), ST.blocks_ok(SC.update(AR.Tree<U32>, t, p, b)), L.and_left(ST.blk_ok(b0), ST.blocks_ok(t), h), blocks_update(t, p, b, L.and_right(ST.blk_ok(b0), ST.blocks_ok(t), h), hb))

# Another slot of an updated adjacency array still holds its old block.
def tree_other(+d: Nat, +at: AR.Tree<AR.Tree<U32>>, +j: Nat, +b: AR.Tree<U32>, +i: Nat, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(AR.Tree<U32>, d, at) == True{} : Bool}, +hne: {Nat.is_eq(i, j) == False{} : Bool}) -> {SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, AR.upd(AR.Tree<U32>, d, at, j, b)), i) == SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), i) : Maybe<&2, AR.Tree<U32>>}:
  L.subst(List<&2, AR.Tree<U32>>, ys => {SC.nth(AR.Tree<U32>, ys, i) == SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), i) : Maybe<&2, AR.Tree<U32>>}, SC.update(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), j, b), AR.slots(AR.Tree<U32>, AR.upd(AR.Tree<U32>, d, at, j, b)),
    Equal.sym(List<&2, AR.Tree<U32>>, AR.slots(AR.Tree<U32>, AR.upd(AR.Tree<U32>, d, at, j, b)), SC.update(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), j, b), AR.upd_slots(AR.Tree<U32>, d, at, j, b, hj, pf)),
    LL.nth_update_other(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), j, i, b, SH.ne_flip(i, j, hne)))

# Two different present vertices own different slots.
def slots_differ(+ks: List<&2, U32>, +lu: Nat, +lv: Nat, +u: U32, +v: U32, +hu: {LB.eq_at(ks, lu, u) == True{} : Bool}, +hv: {LB.eq_at(ks, lv, v) == True{} : Bool}, +huv: {U32.is_eq(u, v) == False{} : Bool}, e: Bool, +ee: {Nat.is_eq(lu, lv) == e : Bool}) -> {Nat.is_eq(lu, lv) == False{} : Bool}:
  match e:
    case False{}:
      ee
    case True{}:
      +el = N.eq_from_is_eq(lu, lv, ee)
      +eu = Equal.trans(U32, u, W.val_i(ks, lu), v, Equal.sym(U32, W.val_i(ks, lu), u, val_of_eq(ks, lu, u, hu)),
        L.subst(Nat, z => {W.val_i(ks, z) == v : U32}, lv, lu, Equal.sym(Nat, lu, lv, el), val_of_eq(ks, lv, v, hv)))
      Empty.absurd({Nat.is_eq(lu, lv) == False{} : Bool}, L.false_true(Equal.trans(Bool, False{}, U32.is_eq(u, v), True{}, Equal.sym(Bool, U32.is_eq(u, v), False{}, huv),
        L.subst(U32, z => {U32.is_eq(u, z) == True{} : Bool}, u, v, eu, UA.eq_refl(u)))))

# ---- loop-freedom: a vertex is not its own neighbour ----

def not_true(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, L.false_true(h))
    case False{}:
      {==}

def LfIH(+t: List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, +u: U32) -> Type:
  @+su2: List<&2, BE.Entry<U32, Unit>> -> @+hf2: {GS.find(u, t) == Some{su2} : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>} -> {GS.smem(u, su2) == False{} : Bool}

def lf_c(+k: U32, +s: List<&2, BE.Entry<U32, Unit>>, +t: List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, +u: U32, +su: List<&2, BE.Entry<U32, Unit>>, +hl: {GS.loopfree(Con{BE.Entry{k, s}, t}) == True{} : Bool}, +hf: {GS.find(u, Con{BE.Entry{k, s}, t}) == Some{su} : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>}, c: Cmp, +ec: {U32.cmp(u, k) == c : Cmp}, ih: LfIH(t, u)) -> {GS.smem(u, su) == False{} : Bool}:
  match c:
    case EQ{}:
      +hf1 = L.subst(Cmp, z => {S.find_at(U32, List<&2, BE.Entry<U32, Unit>>, z, BE.Entry{k, s}, GS.find(u, t)) == Some{su} : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>}, U32.cmp(u, k), EQ{}, ec, hf)
      +es = Equal.cong(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, List<&2, BE.Entry<U32, Unit>>, m => L.some_value(List<&2, BE.Entry<U32, Unit>>, m, s), Some{s}, Some{su}, hf1)
      +eu = O.u32_antisym(u, k, ec)
      L.subst(U32, z => {GS.smem(z, su) == False{} : Bool}, k, u, Equal.sym(U32, u, k, eu),
        L.subst(List<&2, BE.Entry<U32, Unit>>, z => {GS.smem(k, z) == False{} : Bool}, s, su, es,
          not_true(GS.smem(k, s), L.and_left(Bool.not(GS.smem(k, s)), GS.loopfree(t), hl))))
    case LT{}:
      ih(su, L.subst(Cmp, z => {S.find_at(U32, List<&2, BE.Entry<U32, Unit>>, z, BE.Entry{k, s}, GS.find(u, t)) == Some{su} : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>}, U32.cmp(u, k), LT{}, ec, hf))
    case GT{}:
      ih(su, L.subst(Cmp, z => {S.find_at(U32, List<&2, BE.Entry<U32, Unit>>, z, BE.Entry{k, s}, GS.find(u, t)) == Some{su} : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>}, U32.cmp(u, k), GT{}, ec, hf))

def loopfree_find(+am: List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, +u: U32, +su: List<&2, BE.Entry<U32, Unit>>, +hl: {GS.loopfree(am) == True{} : Bool}, +hf: {GS.find(u, am) == Some{su} : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>}) -> {GS.smem(u, su) == False{} : Bool}:
  match am:
    case Nil{}:
      Empty.absurd({GS.smem(u, su) == False{} : Bool}, L.false_true(Equal.cong(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, Bool, m => Maybe.is_some(&2, List<&2, BE.Entry<U32, Unit>>, m), None{}, Some{su}, hf)))
    case Con{BE.Entry{+k, +s}, +t}:
      lf_c(k, s, t, u, su, hl, hf, U32.cmp(u, k), {==}, su2 => hf2 => loopfree_find(t, u, su2, L.and_right(Bool.not(GS.smem(k, s)), GS.loopfree(t), hl), hf2))

def wf_loopfree(+d: Bool, +am: List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, +h: {GS.wf(GS.GM{d, am}) == True{} : Bool}) -> {GS.loopfree(am) == True{} : Bool}:
  L.and_right(GS.closed(am, am), GS.loopfree(am), L.and_left(Bool.and(GS.closed(am, am), GS.loopfree(am)), Bool.or(d, GS.symmetric(am, am)), h))
