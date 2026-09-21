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

# The public operations of src/graph.bend against spec/graph.bend, one by
# one. Each is stated about `ST.real(sh)` for a shadow that satisfies the
# representation invariant `ST.good`.

# ---- projections of the invariant ----

def t6(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>) -> Bool:
  Bool.and(ST.blocks_ok(ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo))), GS.wf(GS.GM{dir, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))}))

def t5(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>) -> Bool:
  Bool.and(SE.asc_at(Nat.sub(hi, lo), AR.slots(U32, it), lo), t6(dir, lo, hi, depth, it, at))

def t4(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>) -> Bool:
  Bool.and(Nat.is_le(hi, SC.pow2(depth)), t5(dir, lo, hi, depth, it, at))

def t3(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>) -> Bool:
  Bool.and(Nat.is_le(lo, hi), t4(dir, lo, hi, depth, it, at))

def t2(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>) -> Bool:
  Bool.and(AR.perfect(AR.Tree<U32>, depth, at), t3(dir, lo, hi, depth, it, at))

def t1(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>) -> Bool:
  Bool.and(AR.perfect(U32, depth, it), t2(dir, lo, hi, depth, it, at))

def r1(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {t1(dir, lo, hi, depth, it, at) == True{} : Bool}:
  L.and_right(Nat.is_le(depth, 31n), t1(dir, lo, hi, depth, it, at), h)

def r2(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {t2(dir, lo, hi, depth, it, at) == True{} : Bool}:
  L.and_right(AR.perfect(U32, depth, it), t2(dir, lo, hi, depth, it, at), r1(dir, lo, hi, depth, it, at, h))

def r3(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {t3(dir, lo, hi, depth, it, at) == True{} : Bool}:
  L.and_right(AR.perfect(AR.Tree<U32>, depth, at), t3(dir, lo, hi, depth, it, at), r2(dir, lo, hi, depth, it, at, h))

def r4(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {t4(dir, lo, hi, depth, it, at) == True{} : Bool}:
  L.and_right(Nat.is_le(lo, hi), t4(dir, lo, hi, depth, it, at), r3(dir, lo, hi, depth, it, at, h))

def r5(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {t5(dir, lo, hi, depth, it, at) == True{} : Bool}:
  L.and_right(Nat.is_le(hi, SC.pow2(depth)), t5(dir, lo, hi, depth, it, at), r4(dir, lo, hi, depth, it, at, h))

def r6(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {t6(dir, lo, hi, depth, it, at) == True{} : Bool}:
  L.and_right(SE.asc_at(Nat.sub(hi, lo), AR.slots(U32, it), lo), t6(dir, lo, hi, depth, it, at), r5(dir, lo, hi, depth, it, at, h))

def g_depth(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {Nat.is_le(depth, 31n) == True{} : Bool}:
  L.and_left(Nat.is_le(depth, 31n), t1(dir, lo, hi, depth, it, at), h)

def g_ids(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {AR.perfect(U32, depth, it) == True{} : Bool}:
  L.and_left(AR.perfect(U32, depth, it), t2(dir, lo, hi, depth, it, at), r1(dir, lo, hi, depth, it, at, h))

def g_adj(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {AR.perfect(AR.Tree<U32>, depth, at) == True{} : Bool}:
  L.and_left(AR.perfect(AR.Tree<U32>, depth, at), t3(dir, lo, hi, depth, it, at), r2(dir, lo, hi, depth, it, at, h))

def g_lohi(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {Nat.is_le(lo, hi) == True{} : Bool}:
  L.and_left(Nat.is_le(lo, hi), t4(dir, lo, hi, depth, it, at), r3(dir, lo, hi, depth, it, at, h))

def g_cap(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {Nat.is_le(hi, SC.pow2(depth)) == True{} : Bool}:
  L.and_left(Nat.is_le(hi, SC.pow2(depth)), t5(dir, lo, hi, depth, it, at), r4(dir, lo, hi, depth, it, at, h))

def g_asc(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {SE.asc_at(Nat.sub(hi, lo), AR.slots(U32, it), lo) == True{} : Bool}:
  L.and_left(SE.asc_at(Nat.sub(hi, lo), AR.slots(U32, it), lo), t6(dir, lo, hi, depth, it, at), r5(dir, lo, hi, depth, it, at, h))

def g_blocks(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {ST.blocks_ok(ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo))) == True{} : Bool}:
  L.and_left(ST.blocks_ok(ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo))), GS.wf(GS.GM{dir, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))}), r6(dir, lo, hi, depth, it, at, h))

def g_wf(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {GS.wf(GS.GM{dir, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))}) == True{} : Bool}:
  L.and_right(ST.blocks_ok(ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo))), GS.wf(GS.GM{dir, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))}), r6(dir, lo, hi, depth, it, at, h))

# ---- has_vertex ----
#
# The lower bound of v in the vertex window, as an absolute slot index.
def lbv(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +v: U32) -> Nat:
  Nat.add(lo, W.lbs(v, AR.slots(U32, it), Nat.sub(hi, lo), lo))

def hv_locate(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {G.locate(depth, v, U32.from_nat(lo), U32.from_nat(hi), AR.thaw(U32, it)) == G.LC{AR.thaw(U32, it), U32.from_nat(lbv(lo, hi, it, v)), SE.found_of(it, lbv(lo, hi, it, v), hi, v)} : G.Loc}:
  +k = Nat.sub(hi, lo)
  +l = W.lbs(v, AR.slots(U32, it), k, lo)
  SE.locate_ok(depth, it, v, lo, hi, Nat.add(lo, l),
    N.le_lt_trans(depth, 31n, 32n, g_depth(dir, lo, hi, depth, it, at, h), N.lt_succ(31n)),
    g_ids(dir, lo, hi, depth, it, at, h),
    N.le_add_right(lo, l),
    L.subst(Nat, z => {Nat.is_le(Nat.add(lo, l), z) == True{} : Bool}, Nat.add(lo, k), hi, W.window_end(lo, hi, k, {==}, g_lohi(dir, lo, hi, depth, it, at, h)),
      W.add_mono(lo, l, k, W.lbs_le(v, AR.slots(U32, it), k, lo))),
    g_cap(dir, lo, hi, depth, it, at, h),
    L.subst(Nat, z => {SE.alllt(z, AR.slots(U32, it), lo, v) == True{} : Bool}, l, Nat.sub(Nat.add(lo, l), lo),
      Equal.sym(Nat, Nat.sub(Nat.add(lo, l), lo), l, N.add_sub_cancel(lo, l)),
      W.lbs_alllt(v, AR.slots(U32, it), k, lo)),
    L.subst(Nat, z => {SE.allge(z, AR.slots(U32, it), Nat.add(lo, l), v) == True{} : Bool}, Nat.sub(k, l), Nat.sub(hi, Nat.add(lo, l)),
      SE.sub_add_eq(hi, lo, l),
      W.lbs_allge(v, AR.slots(U32, it), k, lo, g_asc(dir, lo, hi, depth, it, at, h))))

# The spec's `find` on the abstraction is the runtime's `found`.
def keys_and_index(+ks: List<&2, U32>, +bs: List<&2, AR.Tree<U32>>, +v: U32, +hlen: {SC.length(U32, ks) == SC.length(AR.Tree<U32>, bs) : Nat}, +xs: List<&2, U32>, +lo: Nat, +k: Nat, +hks: {ks == ST.win(U32, xs, lo, k) : List<&2, U32>}) -> {LB.eq_at(LB.keys_of(List<&2, BE.Entry<U32, Unit>>, ST.amodel(ks, bs)), LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, ST.amodel(ks, bs)), v) == LB.eq_at(ks, W.lbs(v, xs, k, lo), v) : Bool}:
  Equal.trans(Bool, LB.eq_at(LB.keys_of(List<&2, BE.Entry<U32, Unit>>, ST.amodel(ks, bs)), LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, ST.amodel(ks, bs)), v), LB.eq_at(ks, LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, ST.amodel(ks, bs)), v), LB.eq_at(ks, W.lbs(v, xs, k, lo), v),
    Equal.cong(List<&2, U32>, Bool, ys => LB.eq_at(ys, LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, ST.amodel(ks, bs)), v), LB.keys_of(List<&2, BE.Entry<U32, Unit>>, ST.amodel(ks, bs)), ks, W.amodel_keys(ks, bs, hlen)),
    Equal.cong(Nat, Bool, z => LB.eq_at(ks, z, v), LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, ST.amodel(ks, bs)), W.lbs(v, xs, k, lo),
      Equal.trans(Nat, LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, ST.amodel(ks, bs)), W.lbu(v, LB.keys_of(List<&2, BE.Entry<U32, Unit>>, ST.amodel(ks, bs))), W.lbs(v, xs, k, lo),
        W.lbx_lbu(List<&2, BE.Entry<U32, Unit>>, v, ST.amodel(ks, bs)),
        Equal.trans(Nat, W.lbu(v, LB.keys_of(List<&2, BE.Entry<U32, Unit>>, ST.amodel(ks, bs))), W.lbu(v, ks), W.lbs(v, xs, k, lo),
          Equal.cong(List<&2, U32>, Nat, ys => W.lbu(v, ys), LB.keys_of(List<&2, BE.Entry<U32, Unit>>, ST.amodel(ks, bs)), ks, W.amodel_keys(ks, bs, hlen)),
          Equal.trans(Nat, W.lbu(v, ks), W.lbu(v, ST.win(U32, xs, lo, k)), W.lbs(v, xs, k, lo),
            Equal.cong(List<&2, U32>, Nat, ys => W.lbu(v, ys), ks, ST.win(U32, xs, lo, k), hks),
            Equal.sym(Nat, W.lbs(v, xs, k, lo), W.lbu(v, ST.win(U32, xs, lo, k)), W.lbs_lbu(v, xs, k, lo)))))))

def hv_found(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hlen: {SC.length(U32, ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo))) == SC.length(AR.Tree<U32>, ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo))) : Nat}) -> {SE.found_of(it, lbv(lo, hi, it, v), hi, v) == S.is_some(List<&2, BE.Entry<U32, Unit>>, S.find(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo))))) : Bool}:
  +k = Nat.sub(hi, lo)
  +ks = ST.win(U32, AR.slots(U32, it), lo, k)
  +bs = ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, k)
  +es = ST.amodel(ks, bs)
  Equal.trans(Bool, SE.found_of(it, lbv(lo, hi, it, v), hi, v), W.eq_at(ks, W.lbs(v, AR.slots(U32, it), k, lo), v), S.is_some(List<&2, BE.Entry<U32, Unit>>, S.find(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, es)),
    W.found_bridge(it, lo, hi, k, W.lbs(v, AR.slots(U32, it), k, lo), v, {==}, g_lohi(dir, lo, hi, depth, it, at, h), W.lbs_le(v, AR.slots(U32, it), k, lo),
      L.subst(Nat, z => {Nat.is_le(hi, z) == True{} : Bool}, SC.pow2(depth), SC.length(U32, AR.slots(U32, it)),
        Equal.sym(Nat, SC.length(U32, AR.slots(U32, it)), SC.pow2(depth), AR.slots_length(U32, depth, it, g_ids(dir, lo, hi, depth, it, at, h))),
        g_cap(dir, lo, hi, depth, it, at, h))),
    Equal.sym(Bool, S.is_some(List<&2, BE.Entry<U32, Unit>>, S.find(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, es)), W.eq_at(ks, W.lbs(v, AR.slots(U32, it), k, lo), v),
      Equal.trans(Bool, S.is_some(List<&2, BE.Entry<U32, Unit>>, S.find(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, es)), LB.eq_at(LB.keys_of(List<&2, BE.Entry<U32, Unit>>, es), LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, es), v), W.eq_at(ks, W.lbs(v, AR.slots(U32, it), k, lo), v),
        LB.find_some(List<&2, BE.Entry<U32, Unit>>, es, v, W.sorted_amodel(ks, bs, W.asc_win(k, AR.slots(U32, it), lo, g_asc(dir, lo, hi, depth, it, at, h)))),
        Equal.trans(Bool, LB.eq_at(LB.keys_of(List<&2, BE.Entry<U32, Unit>>, es), LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, es), v), LB.eq_at(ks, W.lbs(v, AR.slots(U32, it), k, lo), v), W.eq_at(ks, W.lbs(v, AR.slots(U32, it), k, lo), v),
          keys_and_index(ks, bs, v, hlen, AR.slots(U32, it), lo, k, {==}),
          W.eqm_same(SC.nth(U32, ks, W.lbs(v, AR.slots(U32, it), k, lo)), v)))))

# `keys_of(amodel) = ks` and `lbx(amodel) = lbs`, so the index and the list
# the equality reads are the window's.
# has_vertex refines the specification and returns the state unchanged.
def has_vertex_ok(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hlen: {SC.length(U32, ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo))) == SC.length(AR.Tree<U32>, ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo))) : Nat}) -> {G.has_vertex(ST.real(ST.Sh{dir, lo, hi, depth, it, at}), v) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), S.is_some(List<&2, BE.Entry<U32, Unit>>, S.find(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))))) : G.Graph & Bool}:
  %Equal.sym(G.Loc, G.locate(depth, v, U32.from_nat(lo), U32.from_nat(hi), AR.thaw(U32, it)), G.LC{AR.thaw(U32, it), U32.from_nat(lbv(lo, hi, it, v)), SE.found_of(it, lbv(lo, hi, it, v), hi, v)},
    hv_locate(dir, lo, hi, depth, it, at, v, h)) : {G.hv_fin(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, A2.thaw2(at), _) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), S.is_some(List<&2, BE.Entry<U32, Unit>>, S.find(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))))) : G.Graph & Bool}
  L.subst(Bool, b => {(ST.real(ST.Sh{dir, lo, hi, depth, it, at}), b) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), S.is_some(List<&2, BE.Entry<U32, Unit>>, S.find(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))))) : G.Graph & Bool},
    S.is_some(List<&2, BE.Entry<U32, Unit>>, S.find(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo))))),
    SE.found_of(it, lbv(lo, hi, it, v), hi, v),
    Equal.sym(Bool, SE.found_of(it, lbv(lo, hi, it, v), hi, v), S.is_some(List<&2, BE.Entry<U32, Unit>>, S.find(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo))))), hv_found(dir, lo, hi, depth, it, at, v, h, hlen)),
    {==})
