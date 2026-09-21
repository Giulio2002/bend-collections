import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
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
import ./search.bend as SE
import ./window.bend as W
import ./lb.bend as LB
import ./blk.bend as BK
import ./ops.bend as OP

# Neighbour sets: an adjacency block's entries against the specification's
# Unit-valued ordered map `uset(bents(b))`.

def uset_keys(+ws: List<&2, U32>) -> {LB.keys_of(Unit, ST.uset(ws)) == ws : List<&2, U32>}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => Con{w, ys}, LB.keys_of(Unit, ST.uset(t)), t, uset_keys(t))

def above_uset(+k: U32, +ws: List<&2, U32>, +h: {ST.above(k, ws) == True{} : Bool}) -> {SO.above(~U32, ~U32.cmp, Unit, ST.uset(ws), k) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      L.and_intro(Cmp.is_lt(U32.cmp(k, w)), SO.above(~U32, ~U32.cmp, Unit, ST.uset(t), k),
        L.and_left(Cmp.is_lt(U32.cmp(k, w)), ST.above(k, t), h),
        above_uset(k, t, L.and_right(Cmp.is_lt(U32.cmp(k, w)), ST.above(k, t), h)))

def sorted_uset(+ws: List<&2, U32>, +h: {ST.asc(ws) == True{} : Bool}) -> {SO.sorted(~U32, ~U32.cmp, Unit, ST.uset(ws)) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      L.and_intro(SO.above(~U32, ~U32.cmp, Unit, ST.uset(t), w), SO.sorted(~U32, ~U32.cmp, Unit, ST.uset(t)),
        above_uset(w, t, L.and_left(ST.above(w, t), ST.asc(t), h)),
        sorted_uset(t, L.and_right(ST.above(w, t), ST.asc(t), h)))

# The lower bound in a neighbour set is the lower bound over its entries.
def uset_lbx(+v: U32, +ws: List<&2, U32>) -> {LB.lbx(Unit, v, ST.uset(ws)) == W.lbu(v, ws) : Nat}:
  Equal.trans(Nat, LB.lbx(Unit, v, ST.uset(ws)), W.lbu(v, LB.keys_of(Unit, ST.uset(ws))), W.lbu(v, ws),
    W.lbx_lbu(Unit, v, ST.uset(ws)),
    Equal.cong(List<&2, U32>, Nat, ys => W.lbu(v, ys), LB.keys_of(Unit, ST.uset(ws)), ws, uset_keys(ws)))

# Membership in a well-formed block, as the specification sees it, is the
# runtime's `found` flag at the block's lower bound.
def blk_found(+bt: AR.Tree<U32>, +v: U32, +bp: {AR.perfect(U32, ST.blcap(bt), bt) == True{} : Bool}, +bcap: {Nat.is_le(Nat.add(3n, ST.bdeg(bt)), SC.pow2(ST.blcap(bt))) == True{} : Bool}, +bs: {SE.asc_at(ST.bdeg(bt), AR.slots(U32, bt), 3n) == True{} : Bool}) -> {S.is_some(Unit, S.find(~U32, ~U32.cmp, Unit, v, ST.uset(ST.bents(bt)))) == SE.found_of(bt, BK.lbb(bt, v), Nat.add(3n, ST.bdeg(bt)), v) : Bool}:
  +dg = ST.bdeg(bt)
  +xs = AR.slots(U32, bt)
  +ws = ST.bents(bt)
  +l = W.lbs(v, xs, dg, 3n)
  Equal.trans(Bool, S.is_some(Unit, S.find(~U32, ~U32.cmp, Unit, v, ST.uset(ws))), LB.eq_at(ws, l, v), SE.found_of(bt, Nat.add(3n, l), Nat.add(3n, dg), v),
    Equal.trans(Bool, S.is_some(Unit, S.find(~U32, ~U32.cmp, Unit, v, ST.uset(ws))), LB.eq_at(LB.keys_of(Unit, ST.uset(ws)), LB.lbx(Unit, v, ST.uset(ws)), v), LB.eq_at(ws, l, v),
      LB.find_some(Unit, ST.uset(ws), v, sorted_uset(ws, W.asc_win(dg, xs, 3n, bs))),
      Equal.trans(Bool, LB.eq_at(LB.keys_of(Unit, ST.uset(ws)), LB.lbx(Unit, v, ST.uset(ws)), v), LB.eq_at(ws, LB.lbx(Unit, v, ST.uset(ws)), v), LB.eq_at(ws, l, v),
        Equal.cong(List<&2, U32>, Bool, ys => LB.eq_at(ys, LB.lbx(Unit, v, ST.uset(ws)), v), LB.keys_of(Unit, ST.uset(ws)), ws, uset_keys(ws)),
        Equal.cong(Nat, Bool, z => LB.eq_at(ws, z, v), LB.lbx(Unit, v, ST.uset(ws)), l,
          Equal.trans(Nat, LB.lbx(Unit, v, ST.uset(ws)), W.lbu(v, ws), l, uset_lbx(v, ws), Equal.sym(Nat, l, W.lbu(v, ws), W.lbs_lbu(v, xs, dg, 3n)))))),
    Equal.trans(Bool, LB.eq_at(ws, l, v), W.eq_at(ws, l, v), SE.found_of(bt, Nat.add(3n, l), Nat.add(3n, dg), v),
      W.eqm_same(SC.nth(U32, ws, l), v),
      Equal.sym(Bool, SE.found_of(bt, Nat.add(3n, l), Nat.add(3n, dg), v), W.eq_at(ws, l, v),
        W.found_bridge(bt, 3n, Nat.add(3n, dg), dg, l, v, Equal.sym(Nat, Nat.sub(dg, 0n), dg, LL.sub_zero_eq(dg)), N.le_add_right(3n, dg), W.lbs_le(v, xs, dg, 3n),
          L.subst(Nat, z => {Nat.is_le(Nat.add(3n, dg), z) == True{} : Bool}, SC.pow2(ST.blcap(bt)), SC.length(U32, xs), Equal.sym(Nat, SC.length(U32, xs), SC.pow2(ST.blcap(bt)), AR.slots_length(U32, ST.blcap(bt), bt, bp)), bcap)))))

# ---- the abstraction at one index ----

def bnth(+bs: List<&2, AR.Tree<U32>>, +l: Nat) -> AR.Tree<U32>:
  L.some_value(AR.Tree<U32>, SC.nth(AR.Tree<U32>, bs, l), BK.leaf0())

def amodel_at(+ks: List<&2, U32>, +bs: List<&2, AR.Tree<U32>>, +l: Nat, +u: U32, +hlen: {SC.length(U32, ks) == SC.length(AR.Tree<U32>, bs) : Nat}) -> {LB.ent_val(List<&2, BE.Entry<U32, Unit>>, SC.nth(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(ks, bs), l), u) == LB.pickv(List<&2, BE.Entry<U32, Unit>>, SE.eqm(SC.nth(U32, ks, l), u), ST.uset(ST.bents(bnth(bs, l)))) : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>}:
  match ks bs l:
    case Nil{} Nil{} l0:
      {==}
    case Nil{} Con{b, bt} l0:
      Empty.absurd({LB.ent_val(List<&2, BE.Entry<U32, Unit>>, SC.nth(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(Nil{}, Con{b, bt}), l0), u) == LB.pickv(List<&2, BE.Entry<U32, Unit>>, SE.eqm(SC.nth(U32, Nil{}, l0), u), ST.uset(ST.bents(bnth(Con{b, bt}, l0)))) : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>}, N.zero_succ(SC.length(AR.Tree<U32>, bt), hlen))
    case Con{k, kt} Nil{} l0:
      Empty.absurd({LB.ent_val(List<&2, BE.Entry<U32, Unit>>, SC.nth(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(Con{k, kt}, Nil{}), l0), u) == LB.pickv(List<&2, BE.Entry<U32, Unit>>, SE.eqm(SC.nth(U32, Con{k, kt}, l0), u), ST.uset(ST.bents(bnth(Nil{}, l0)))) : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>}, N.succ_zero(SC.length(U32, kt), hlen))
    case Con{+k, +kt} Con{+b, +bt} 0n:
      {==}
    case Con{+k, +kt} Con{+b, +bt} 1n+p:
      amodel_at(kt, bt, p, u, N.succ_inj(SC.length(U32, kt), SC.length(AR.Tree<U32>, bt), hlen))

# The specification's `find` on the abstraction: Some of the neighbour set
# of the block at the lower bound exactly when that slot holds u.
def am_find(+ks: List<&2, U32>, +bs: List<&2, AR.Tree<U32>>, +u: U32, +xs: List<&2, U32>, +lo: Nat, +k: Nat, +hks: {ks == ST.win(U32, xs, lo, k) : List<&2, U32>}, +hlen: {SC.length(U32, ks) == SC.length(AR.Tree<U32>, bs) : Nat}, +hs: {ST.asc(ks) == True{} : Bool}) -> {GS.find(u, ST.amodel(ks, bs)) == LB.pickv(List<&2, BE.Entry<U32, Unit>>, SE.eqm(SC.nth(U32, ks, W.lbs(u, xs, k, lo)), u), ST.uset(ST.bents(bnth(bs, W.lbs(u, xs, k, lo))))) : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>}:
  +es = ST.amodel(ks, bs)
  +l = W.lbs(u, xs, k, lo)
  +el = Equal.trans(Nat, LB.lbx(List<&2, BE.Entry<U32, Unit>>, u, es), W.lbu(u, LB.keys_of(List<&2, BE.Entry<U32, Unit>>, es)), l,
    W.lbx_lbu(List<&2, BE.Entry<U32, Unit>>, u, es),
    Equal.trans(Nat, W.lbu(u, LB.keys_of(List<&2, BE.Entry<U32, Unit>>, es)), W.lbu(u, ks), l,
      Equal.cong(List<&2, U32>, Nat, ys => W.lbu(u, ys), LB.keys_of(List<&2, BE.Entry<U32, Unit>>, es), ks, W.amodel_keys(ks, bs, hlen)),
      Equal.trans(Nat, W.lbu(u, ks), W.lbu(u, ST.win(U32, xs, lo, k)), l,
        Equal.cong(List<&2, U32>, Nat, ys => W.lbu(u, ys), ks, ST.win(U32, xs, lo, k), hks),
        Equal.sym(Nat, l, W.lbu(u, ST.win(U32, xs, lo, k)), W.lbs_lbu(u, xs, k, lo)))))
  Equal.trans(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(u, es), LB.at_val(List<&2, BE.Entry<U32, Unit>>, es, LB.lbx(List<&2, BE.Entry<U32, Unit>>, u, es), u), LB.pickv(List<&2, BE.Entry<U32, Unit>>, SE.eqm(SC.nth(U32, ks, l), u), ST.uset(ST.bents(bnth(bs, l)))),
    LB.find_val(List<&2, BE.Entry<U32, Unit>>, es, u, W.sorted_amodel(ks, bs, hs)),
    Equal.trans(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, LB.at_val(List<&2, BE.Entry<U32, Unit>>, es, LB.lbx(List<&2, BE.Entry<U32, Unit>>, u, es), u), LB.at_val(List<&2, BE.Entry<U32, Unit>>, es, l, u), LB.pickv(List<&2, BE.Entry<U32, Unit>>, SE.eqm(SC.nth(U32, ks, l), u), ST.uset(ST.bents(bnth(bs, l)))),
      Equal.cong(Nat, Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, z => LB.at_val(List<&2, BE.Entry<U32, Unit>>, es, z, u), LB.lbx(List<&2, BE.Entry<U32, Unit>>, u, es), l, el),
      amodel_at(ks, bs, l, u, hlen)))

# `found` implies the lower bound is inside the window.
def found_lt(+t: AR.Tree<U32>, +lb: Nat, +hi: Nat, +v: U32, inside: Bool, +ein: {Nat.is_lt(lb, hi) == inside : Bool}, +h: {SE.found_of(t, lb, hi, v) == True{} : Bool}) -> {Nat.is_lt(lb, hi) == True{} : Bool}:
  match inside:
    case True{}:
      ein
    case False{}:
      Empty.absurd({Nat.is_lt(lb, hi) == True{} : Bool},
        L.false_true(L.subst(Bool, b => {SE.pick(b, SE.eqat(AR.slots(U32, t), lb, v)) == True{} : Bool}, Nat.is_lt(lb, hi), False{}, ein, h)))

# ---- lengths of the two windows ----

def win_len(-A: Data, +xs: List<&2, A>, +lo: Nat, +k: Nat, +h: {Nat.is_le(Nat.add(lo, k), SC.length(A, xs)) == True{} : Bool}) -> {SC.length(A, ST.win(A, xs, lo, k)) == k : Nat}:
  LL.sc_length_take(A, SC.drop(A, xs, lo), k,
    L.subst(Nat, z => {Nat.is_le(k, z) == True{} : Bool}, Nat.sub(SC.length(A, xs), lo), SC.length(A, SC.drop(A, xs, lo)),
      Equal.sym(Nat, SC.length(A, SC.drop(A, xs, lo)), Nat.sub(SC.length(A, xs), lo), W.drop_length(A, xs, lo)),
      W.le_sub_of_add(k, lo, SC.length(A, xs), h)))

def win_fits(-A: Data, +d: Nat, +t: AR.Tree<A>, +lo: Nat, +hi: Nat, +pf: {AR.perfect(A, d, t) == True{} : Bool}, +hlo: {Nat.is_le(lo, hi) == True{} : Bool}, +hcap: {Nat.is_le(hi, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_le(Nat.add(lo, Nat.sub(hi, lo)), SC.length(A, AR.slots(A, t))) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(z, SC.length(A, AR.slots(A, t))) == True{} : Bool}, hi, Nat.add(lo, Nat.sub(hi, lo)), Equal.sym(Nat, Nat.add(lo, Nat.sub(hi, lo)), hi, W.window_end(lo, hi, Nat.sub(hi, lo), {==}, hlo)),
    L.subst(Nat, z => {Nat.is_le(hi, z) == True{} : Bool}, SC.pow2(d), SC.length(A, AR.slots(A, t)), Equal.sym(Nat, SC.length(A, AR.slots(A, t)), SC.pow2(d), AR.slots_length(A, d, t, pf)), hcap))

# ---- well-formed blocks ----

def blocks_nth(+bs: List<&2, AR.Tree<U32>>, +l: Nat, +h: {ST.blocks_ok(bs) == True{} : Bool}, +hl: {Nat.is_lt(l, SC.length(AR.Tree<U32>, bs)) == True{} : Bool}) -> {ST.blk_ok(bnth(bs, l)) == True{} : Bool}:
  match bs l:
    case Nil{} l0:
      Empty.absurd({ST.blk_ok(bnth(Nil{}, l0)) == True{} : Bool}, L.false_true(L.subst(Bool, b => {b == True{} : Bool}, Nat.is_lt(l0, 0n), False{}, N.not_lt_zero(l0), hl)))
    case Con{+b, +bt} 0n:
      L.and_left(ST.blk_ok(b), ST.blocks_ok(bt), h)
    case Con{+b, +bt} 1n+p:
      blocks_nth(bt, p, L.and_right(ST.blk_ok(b), ST.blocks_ok(bt), h), hl)

def b1(+b: AR.Tree<U32>) -> Bool:
  Bool.and(Nat.is_le(2n, ST.blcap(b)), Bool.and(Nat.is_le(ST.blcap(b), 31n), Bool.and(Nat.is_eq(ST.bsize(b), SC.pow2(ST.blcap(b))), Bool.and(Nat.is_le(Nat.add(3n, ST.bdeg(b)), ST.bsize(b)), SE.asc_at(ST.bdeg(b), AR.slots(U32, b), 3n)))))

def b2(+b: AR.Tree<U32>) -> Bool:
  Bool.and(Nat.is_le(ST.blcap(b), 31n), Bool.and(Nat.is_eq(ST.bsize(b), SC.pow2(ST.blcap(b))), Bool.and(Nat.is_le(Nat.add(3n, ST.bdeg(b)), ST.bsize(b)), SE.asc_at(ST.bdeg(b), AR.slots(U32, b), 3n))))

def b3(+b: AR.Tree<U32>) -> Bool:
  Bool.and(Nat.is_eq(ST.bsize(b), SC.pow2(ST.blcap(b))), Bool.and(Nat.is_le(Nat.add(3n, ST.bdeg(b)), ST.bsize(b)), SE.asc_at(ST.bdeg(b), AR.slots(U32, b), 3n)))

def b4(+b: AR.Tree<U32>) -> Bool:
  Bool.and(Nat.is_le(Nat.add(3n, ST.bdeg(b)), ST.bsize(b)), SE.asc_at(ST.bdeg(b), AR.slots(U32, b), 3n))

def bk_perfect(+b: AR.Tree<U32>, +h: {ST.blk_ok(b) == True{} : Bool}) -> {AR.perfect(U32, ST.blcap(b), b) == True{} : Bool}:
  L.and_left(AR.perfect(U32, ST.blcap(b), b), b1(b), h)

def bk_r1(+b: AR.Tree<U32>, +h: {ST.blk_ok(b) == True{} : Bool}) -> {b1(b) == True{} : Bool}:
  L.and_right(AR.perfect(U32, ST.blcap(b), b), b1(b), h)

def bk_two(+b: AR.Tree<U32>, +h: {ST.blk_ok(b) == True{} : Bool}) -> {Nat.is_le(2n, ST.blcap(b)) == True{} : Bool}:
  L.and_left(Nat.is_le(2n, ST.blcap(b)), b2(b), bk_r1(b, h))

def bk_r2(+b: AR.Tree<U32>, +h: {ST.blk_ok(b) == True{} : Bool}) -> {b2(b) == True{} : Bool}:
  L.and_right(Nat.is_le(2n, ST.blcap(b)), b2(b), bk_r1(b, h))

def bk_le31(+b: AR.Tree<U32>, +h: {ST.blk_ok(b) == True{} : Bool}) -> {Nat.is_le(ST.blcap(b), 31n) == True{} : Bool}:
  L.and_left(Nat.is_le(ST.blcap(b), 31n), b3(b), bk_r2(b, h))

def bk_lt32(+b: AR.Tree<U32>, +h: {ST.blk_ok(b) == True{} : Bool}) -> {Nat.is_lt(ST.blcap(b), 32n) == True{} : Bool}:
  N.le_lt_succ(ST.blcap(b), 31n, bk_le31(b, h))

def bk_r3(+b: AR.Tree<U32>, +h: {ST.blk_ok(b) == True{} : Bool}) -> {b3(b) == True{} : Bool}:
  L.and_right(Nat.is_le(ST.blcap(b), 31n), b3(b), bk_r2(b, h))

def bk_size(+b: AR.Tree<U32>, +h: {ST.blk_ok(b) == True{} : Bool}) -> {Nat.is_eq(ST.bsize(b), SC.pow2(ST.blcap(b))) == True{} : Bool}:
  L.and_left(Nat.is_eq(ST.bsize(b), SC.pow2(ST.blcap(b))), b4(b), bk_r3(b, h))

def bk_r4(+b: AR.Tree<U32>, +h: {ST.blk_ok(b) == True{} : Bool}) -> {b4(b) == True{} : Bool}:
  L.and_right(Nat.is_eq(ST.bsize(b), SC.pow2(ST.blcap(b))), b4(b), bk_r3(b, h))

def bk_fit(+b: AR.Tree<U32>, +h: {ST.blk_ok(b) == True{} : Bool}) -> {Nat.is_le(Nat.add(3n, ST.bdeg(b)), ST.bsize(b)) == True{} : Bool}:
  L.and_left(Nat.is_le(Nat.add(3n, ST.bdeg(b)), ST.bsize(b)), SE.asc_at(ST.bdeg(b), AR.slots(U32, b), 3n), bk_r4(b, h))

def bk_asc(+b: AR.Tree<U32>, +h: {ST.blk_ok(b) == True{} : Bool}) -> {SE.asc_at(ST.bdeg(b), AR.slots(U32, b), 3n) == True{} : Bool}:
  L.and_right(Nat.is_le(Nat.add(3n, ST.bdeg(b)), ST.bsize(b)), SE.asc_at(ST.bdeg(b), AR.slots(U32, b), 3n), bk_r4(b, h))

def bk_cap(+b: AR.Tree<U32>, +h: {ST.blk_ok(b) == True{} : Bool}) -> {Nat.is_le(Nat.add(3n, ST.bdeg(b)), SC.pow2(ST.blcap(b))) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(Nat.add(3n, ST.bdeg(b)), z) == True{} : Bool}, ST.bsize(b), SC.pow2(ST.blcap(b)), N.eq_from_is_eq(ST.bsize(b), SC.pow2(ST.blcap(b)), bk_size(b, h)), bk_fit(b, h))

# ---- has_edge ----

def nth_some(-A: Data, +xs: List<&2, A>, +i: Nat, +d: A, +hl: {Nat.is_lt(i, SC.length(A, xs)) == True{} : Bool}, m: Maybe<&2, A>, +em: {SC.nth(A, xs, i) == m : Maybe<&2, A>}) -> {SC.nth(A, xs, i) == Some{L.some_value(A, SC.nth(A, xs, i), d)} : Maybe<&2, A>}:
  match m:
    case None{}:
      Empty.absurd({SC.nth(A, xs, i) == Some{L.some_value(A, SC.nth(A, xs, i), d)} : Maybe<&2, A>}, LL.sc_nth_some(A, xs, i, hl, em))
    case Some{+x}:
      L.subst(A, z => {SC.nth(A, xs, i) == Some{z} : Maybe<&2, A>}, x, L.some_value(A, SC.nth(A, xs, i), d),
        Equal.sym(A, L.some_value(A, SC.nth(A, xs, i), d), x, Equal.cong(Maybe<&2, A>, A, mm => L.some_value(A, mm, d), SC.nth(A, xs, i), Some{x}, em)),
        em)

# lo + l < hi  gives  l < hi - lo.
def off_lt(+lo: Nat, +hi: Nat, +l: Nat, +h: {Nat.is_lt(Nat.add(lo, l), hi) == True{} : Bool}, +hlo: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Nat.is_lt(l, Nat.sub(hi, lo)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(z, Nat.sub(hi, lo)) == True{} : Bool}, Nat.sub(Nat.add(lo, l), lo), l, N.add_sub_cancel(lo, l),
    N.sub_lt(Nat.add(lo, l), lo, Nat.sub(hi, lo), N.le_add_right(lo, l),
      L.subst(Nat, z => {Nat.is_lt(Nat.add(lo, l), z) == True{} : Bool}, hi, Nat.add(lo, Nat.sub(hi, lo)), Equal.sym(Nat, Nat.add(lo, Nat.sub(hi, lo)), hi, W.window_end(lo, hi, Nat.sub(hi, lo), {==}, hlo)), h)))

def PK(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>) -> Type:
  {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}

# The specification's find on the model, in terms of the runtime's flag.
def gfind(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +x: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {GS.find(x, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))) == LB.pickv(List<&2, BE.Entry<U32, Unit>>, SE.found_of(it, OP.lbv(lo, hi, it, x), hi, x), ST.uset(ST.bents(bnth(ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)), W.lbs(x, AR.slots(U32, it), Nat.sub(hi, lo), lo))))) : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>}:
  +k = Nat.sub(hi, lo)
  +xs = AR.slots(U32, it)
  +ks = ST.win(U32, xs, lo, k)
  +bw = ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, k)
  +l = W.lbs(x, xs, k, lo)
  +hlo = OP.g_lohi(dir, lo, hi, depth, it, at, h)
  +hcap = OP.g_cap(dir, lo, hi, depth, it, at, h)
  +hlen = Equal.trans(Nat, SC.length(U32, ks), k, SC.length(AR.Tree<U32>, bw),
    win_len(U32, xs, lo, k, win_fits(U32, depth, it, lo, hi, OP.g_ids(dir, lo, hi, depth, it, at, h), hlo, hcap)),
    Equal.sym(Nat, SC.length(AR.Tree<U32>, bw), k, win_len(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, k, win_fits(AR.Tree<U32>, depth, at, lo, hi, OP.g_adj(dir, lo, hi, depth, it, at, h), hlo, hcap))))
  L.subst(Bool, b => {GS.find(x, ST.amodel(ks, bw)) == LB.pickv(List<&2, BE.Entry<U32, Unit>>, b, ST.uset(ST.bents(bnth(bw, l)))) : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>}, W.eq_at(ks, l, x), SE.found_of(it, Nat.add(lo, l), hi, x),
    Equal.sym(Bool, SE.found_of(it, Nat.add(lo, l), hi, x), W.eq_at(ks, l, x),
      W.found_bridge(it, lo, hi, k, l, x, {==}, hlo, W.lbs_le(x, xs, k, lo),
        L.subst(Nat, z => {Nat.is_le(hi, z) == True{} : Bool}, SC.pow2(depth), SC.length(U32, xs), Equal.sym(Nat, SC.length(U32, xs), SC.pow2(depth), AR.slots_length(U32, depth, it, OP.g_ids(dir, lo, hi, depth, it, at, h))), hcap))),
    am_find(ks, bw, x, xs, lo, k, {==}, hlen, W.asc_win(k, xs, lo, OP.g_asc(dir, lo, hi, depth, it, at, h))))

def lbv_lt_cap(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +x: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hin: {Nat.is_lt(OP.lbv(lo, hi, it, x), hi) == True{} : Bool}) -> {Nat.is_lt(OP.lbv(lo, hi, it, x), SC.pow2(depth)) == True{} : Bool}:
  N.lt_le_trans(OP.lbv(lo, hi, it, x), hi, SC.pow2(depth), hin, OP.g_cap(dir, lo, hi, depth, it, at, h))

def dep32(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {Nat.is_lt(depth, 32n) == True{} : Bool}:
  N.le_lt_succ(depth, 31n, OP.g_depth(dir, lo, hi, depth, it, at, h))

# the slot index the runtime computes, as a Nat
def slot_nat(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +x: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hin: {Nat.is_lt(OP.lbv(lo, hi, it, x), hi) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(OP.lbv(lo, hi, it, x))) == OP.lbv(lo, hi, it, x) : Nat}:
  U.to_nat_from_nat(OP.lbv(lo, hi, it, x), depth, N.lt_le(depth, 32n, dep32(dir, lo, hi, depth, it, at, h)), lbv_lt_cap(dir, lo, hi, depth, it, at, x, h, hin))

# The block the found vertex owns, and the facts mem_nbr_ok needs about it.
def blk_of(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +x: U32) -> AR.Tree<U32>:
  bnth(ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)), W.lbs(x, AR.slots(U32, it), Nat.sub(hi, lo), lo))

def blk_in(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +x: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hin: {Nat.is_lt(OP.lbv(lo, hi, it, x), hi) == True{} : Bool}) -> {Nat.is_lt(W.lbs(x, AR.slots(U32, it), Nat.sub(hi, lo), lo), SC.length(AR.Tree<U32>, ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))) == True{} : Bool}:
  +k = Nat.sub(hi, lo)
  +hlo = OP.g_lohi(dir, lo, hi, depth, it, at, h)
  L.subst(Nat, z => {Nat.is_lt(W.lbs(x, AR.slots(U32, it), k, lo), z) == True{} : Bool}, k, SC.length(AR.Tree<U32>, ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, k)),
    Equal.sym(Nat, SC.length(AR.Tree<U32>, ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, k)), k, win_len(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, k, win_fits(AR.Tree<U32>, depth, at, lo, hi, OP.g_adj(dir, lo, hi, depth, it, at, h), hlo, OP.g_cap(dir, lo, hi, depth, it, at, h)))),
    off_lt(lo, hi, W.lbs(x, AR.slots(U32, it), k, lo), hin, hlo))

def blk_ok_of(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +x: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hin: {Nat.is_lt(OP.lbv(lo, hi, it, x), hi) == True{} : Bool}) -> {ST.blk_ok(blk_of(dir, lo, hi, depth, it, at, x)) == True{} : Bool}:
  blocks_nth(ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)), W.lbs(x, AR.slots(U32, it), Nat.sub(hi, lo), lo), OP.g_blocks(dir, lo, hi, depth, it, at, h), blk_in(dir, lo, hi, depth, it, at, x, h, hin))

def blk_at(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +x: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hin: {Nat.is_lt(OP.lbv(lo, hi, it, x), hi) == True{} : Bool}) -> {SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), U32.to_nat(U32.from_nat(OP.lbv(lo, hi, it, x)))) == Some{blk_of(dir, lo, hi, depth, it, at, x)} : Maybe<&2, AR.Tree<U32>>}:
  +k = Nat.sub(hi, lo)
  +l = W.lbs(x, AR.slots(U32, it), k, lo)
  +bw = ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, k)
  +hl = blk_in(dir, lo, hi, depth, it, at, x, h, hin)
  L.subst(Nat, z => {SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), z) == Some{bnth(bw, l)} : Maybe<&2, AR.Tree<U32>>}, Nat.add(lo, l), U32.to_nat(U32.from_nat(Nat.add(lo, l))),
    Equal.sym(Nat, U32.to_nat(U32.from_nat(Nat.add(lo, l))), Nat.add(lo, l), slot_nat(dir, lo, hi, depth, it, at, x, h, hin)),
    Equal.trans(Maybe<&2, AR.Tree<U32>>, SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), Nat.add(lo, l)), SC.nth(AR.Tree<U32>, bw, l), Some{bnth(bw, l)},
      Equal.sym(Maybe<&2, AR.Tree<U32>>, SC.nth(AR.Tree<U32>, bw, l), SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), Nat.add(lo, l)),
        W.nth_win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, k, l, off_lt(lo, hi, l, hin, OP.g_lohi(dir, lo, hi, depth, it, at, h)))),
      nth_some(AR.Tree<U32>, bw, l, BK.leaf0(), hl, SC.nth(AR.Tree<U32>, bw, l), {==})))

def he_v_case(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hu: {SE.found_of(it, OP.lbv(lo, hi, it, u), hi, u) == True{} : Bool}, fv: Bool) -> {G.he_vf(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), U32.from_nat(OP.lbv(lo, hi, it, u)), v, fv) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.has_edge_at(Some{ST.uset(ST.bents(blk_of(dir, lo, hi, depth, it, at, u)))}, LB.pickv(List<&2, BE.Entry<U32, Unit>>, fv, ST.uset(ST.bents(blk_of(dir, lo, hi, depth, it, at, v)))), v)) : G.Graph & Result<&2, &2, E.Error, Bool>}:
  match fv:
    case False{}:
      {==}
    case True{}:
      +bt = blk_of(dir, lo, hi, depth, it, at, u)
      +hin = found_lt(it, OP.lbv(lo, hi, it, u), hi, u, Nat.is_lt(OP.lbv(lo, hi, it, u), hi), {==}, hu)
      +bk = blk_ok_of(dir, lo, hi, depth, it, at, u, h, hin)
      +iu = U32.from_nat(OP.lbv(lo, hi, it, u))
      +fb = SE.found_of(bt, BK.lbb(bt, v), Nat.add(3n, ST.bdeg(bt)), v)
      %Equal.sym(G.Upd, G.mem_nbr(A2.thaw2(at), iu, v), G.UP{A2.thaw2(at), fb},
        BK.mem_nbr_ok(depth, at, iu, bt, v, dep32(dir, lo, hi, depth, it, at, h),
          L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(depth)) == True{} : Bool}, OP.lbv(lo, hi, it, u), U32.to_nat(iu), Equal.sym(Nat, U32.to_nat(iu), OP.lbv(lo, hi, it, u), slot_nat(dir, lo, hi, depth, it, at, u, h, hin)), lbv_lt_cap(dir, lo, hi, depth, it, at, u, h, hin)),
          blk_at(dir, lo, hi, depth, it, at, u, h, hin),
          OP.g_adj(dir, lo, hi, depth, it, at, h),
          bk_lt32(bt, bk), bk_two(bt, bk), bk_perfect(bt, bk), bk_cap(bt, bk), bk_asc(bt, bk))) : {G.he_test(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), _) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.has_edge_at(Some{ST.uset(ST.bents(bt))}, Some{ST.uset(ST.bents(blk_of(dir, lo, hi, depth, it, at, v)))}, v)) : G.Graph & Result<&2, &2, E.Error, Bool>}
      Equal.cong(Bool, G.Graph & Result<&2, &2, E.Error, Bool>, b => (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), Done{b}), fb, GS.smem(v, ST.uset(ST.bents(bt))),
        Equal.sym(Bool, GS.smem(v, ST.uset(ST.bents(bt))), fb, blk_found(bt, v, bk_perfect(bt, bk), bk_cap(bt, bk), bk_asc(bt, bk))))

def he_u_case(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, fu: Bool, +efu: {SE.found_of(it, OP.lbv(lo, hi, it, u), hi, u) == fu : Bool}) -> {G.he_uf(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), U32.from_nat(OP.lbv(lo, hi, it, u)), v, fu) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.has_edge_at(LB.pickv(List<&2, BE.Entry<U32, Unit>>, fu, ST.uset(ST.bents(blk_of(dir, lo, hi, depth, it, at, u)))), GS.find(v, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))), v)) : G.Graph & Result<&2, &2, E.Error, Bool>}:
  match fu:
    case False{}:
      {==}
    case True{}:
      +fv = SE.found_of(it, OP.lbv(lo, hi, it, v), hi, v)
      %Equal.sym(G.Loc, G.locate(depth, v, U32.from_nat(lo), U32.from_nat(hi), AR.thaw(U32, it)), G.LC{AR.thaw(U32, it), U32.from_nat(OP.lbv(lo, hi, it, v)), fv}, OP.hv_locate(dir, lo, hi, depth, it, at, v, h)) : {G.he_v(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, A2.thaw2(at), U32.from_nat(OP.lbv(lo, hi, it, u)), v, _) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.has_edge_at(Some{ST.uset(ST.bents(blk_of(dir, lo, hi, depth, it, at, u)))}, GS.find(v, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))), v)) : G.Graph & Result<&2, &2, E.Error, Bool>}
      %Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(v, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))), LB.pickv(List<&2, BE.Entry<U32, Unit>>, fv, ST.uset(ST.bents(blk_of(dir, lo, hi, depth, it, at, v)))), gfind(dir, lo, hi, depth, it, at, v, h)) : {G.he_vf(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), U32.from_nat(OP.lbv(lo, hi, it, u)), v, fv) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.has_edge_at(Some{ST.uset(ST.bents(blk_of(dir, lo, hi, depth, it, at, u)))}, _, v)) : G.Graph & Result<&2, &2, E.Error, Bool>}
      he_v_case(dir, lo, hi, depth, it, at, u, v, h, efu, fv)

# has_edge refines the specification and returns the state unchanged.
def has_edge_ok(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {G.has_edge(ST.real(ST.Sh{dir, lo, hi, depth, it, at}), u, v) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.has_edge_at(GS.find(u, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))), GS.find(v, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))), v)) : G.Graph & Result<&2, &2, E.Error, Bool>}:
  +am = ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))
  +fu = SE.found_of(it, OP.lbv(lo, hi, it, u), hi, u)
  %Equal.sym(G.Loc, G.locate(depth, u, U32.from_nat(lo), U32.from_nat(hi), AR.thaw(U32, it)), G.LC{AR.thaw(U32, it), U32.from_nat(OP.lbv(lo, hi, it, u)), fu}, OP.hv_locate(dir, lo, hi, depth, it, at, u, h)) : {G.he_u(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, A2.thaw2(at), v, _) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.has_edge_at(GS.find(u, am), GS.find(v, am), v)) : G.Graph & Result<&2, &2, E.Error, Bool>}
  %Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(u, am), LB.pickv(List<&2, BE.Entry<U32, Unit>>, fu, ST.uset(ST.bents(blk_of(dir, lo, hi, depth, it, at, u)))), gfind(dir, lo, hi, depth, it, at, u, h)) : {G.he_uf(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), U32.from_nat(OP.lbv(lo, hi, it, u)), v, fu) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.has_edge_at(_, GS.find(v, am), v)) : G.Graph & Result<&2, &2, E.Error, Bool>}
  he_u_case(dir, lo, hi, depth, it, at, u, v, h, fu, {==})
