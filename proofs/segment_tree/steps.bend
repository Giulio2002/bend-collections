import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as A
import ../lib/flat.bend as FL
import ../lib/u32alg.bend as UA
import ../lib/u32seq.bend as QS
import ../../spec/common.bend as SC
import ../../spec/u32seq.bend as Q
import ../../spec/segment_tree.bend as S
import ../../src/segment_tree.bend as F
import ../../src/internal/vec.bend as V
import ../../types/segment_tree.bend as E
import ./node.bend as TN
import ./model.bend as MD
import ./ops.bend as O
import ./arr.bend as AR
import ./walk.bend as W
import ./state.bend as ST

# Every public operation (errors included) refines the spec step and keeps
# the representation invariant.
#
# The two cell arrays are linear, so a step is stated as: the real operation
# on the arrays of a good shadow produces the arrays of another good shadow,
# whose model and observation are the spec step of the first shadow's model.

def StepOK(sh: ST.Sh, op: E.Op) -> Type:
  Sigma<&1, &1, ST.Sh, sh2 => Sigma<&1, &1, E.Obs, o => {F.step(ST.real(sh), op) == (ST.real(sh2), o) : F.SegTree & E.Obs} & ({ST.good(sh2) == True{} : Bool} & {(ST.model(sh2), o) == S.step(ST.model(sh), op) : List<&2, U32> & E.Obs})>>

def vals0(+t: TN.Node) -> {Q.add_each(MD.vals(t), 0) == MD.vals(t) : List<&2, U32>}:
  MD.each_zero(MD.vals(t))

# n <= 2^d in the vec.bend spelling the model lemmas use
def cap_v(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +g: {ST.repf(n, d, tc, tg) == True{} : Bool}) -> {Nat.is_le(n, V.pow2(d)) == True{} : Bool}:
  L.subst(Nat, q => {Nat.is_le(n, q) == True{} : Bool}, SC.pow2(d), V.pow2(d), Equal.sym(Nat, V.pow2(d), SC.pow2(d), W.vsc(d)), ST.g_cap(n, d, tc, tg, g))

# ---- length ----

def length_case(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +g: {ST.repf(n, d, tc, tg) == True{} : Bool}) -> StepOK(ST.Sh{n, d, tc, tg}, E.Length{}):
  (ST.Sh{n, d, tc, tg}, (E.ONat{n}, ({==},
    (g,
     %Equal.sym(Nat, SC.length(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n)), n, ST.len_model(n, d, tc, tg, g)) : {(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.ONat{n}) == (SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.ONat{_}) : List<&2, U32> & E.Obs}
     {==}))))

# ---- get ----

def get_case(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +i: Nat, b: Bool, +eb: {Nat.is_lt(i, n) == b : Bool}, +g: {ST.repf(n, d, tc, tg) == True{} : Bool}) -> StepOK(ST.Sh{n, d, tc, tg}, E.Get{i}):
  match b:
    case True{}:
      +hi = L.subst(Nat, q => {Nat.is_lt(i, q) == True{} : Bool}, SC.pow2(d), V.pow2(d), Equal.sym(Nat, V.pow2(d), SC.pow2(d), W.vsc(d)), N.lt_le_trans(i, n, SC.pow2(d), eb, ST.g_cap(n, d, tc, tg, g)))
      (ST.Sh{n, d, tc, tg}, (E.OItem{Done{TN.get_go(d, ST.mtree(d, tc, tg), i, 0, V.dec(d, i))}}, (
        %Equal.sym(Bool, Nat.is_lt(i, n), True{}, eb) : {F.obs_item(F.get_if(_, n, d, SC.pow2(d), A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), i)) == (ST.real(ST.Sh{n, d, tc, tg}), E.OItem{Done{TN.get_go(d, ST.mtree(d, tc, tg), i, 0, V.dec(d, i))}}) : F.SegTree & E.Obs}
        %Equal.sym(Bool, Nat.is_lt(i, FL.hof(d)), V.dec(d, i), W.vdec(d, i, FL.hof(d), {==})) : {F.obs_item(F.get_done(F.get_go(d, F.pre_t(d, A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), SC.pow2(d), FL.hof(d), 0n), SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0, 0n, i, _), n, d, SC.pow2(d))) == (ST.real(ST.Sh{n, d, tc, tg}), E.OItem{Done{TN.get_go(d, ST.mtree(d, tc, tg), i, 0, V.dec(d, i))}}) : F.SegTree & E.Obs}
        %Equal.sym(Array<F.Cel> & Array<F.Cel> & U32, F.get_go(d, F.pre_t(d, A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), SC.pow2(d), FL.hof(d), 0n), SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0, 0n, i, V.dec(d, i)), (A.thaw(F.Cel, tc), (A.thaw(F.Cel, tg), TN.get_go(d, ST.mtree(d, tc, tg), i, 0, V.dec(d, i)))), W.get_ok(d, tc, tg, d, SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0, 0n, i, V.dec(d, i), ST.g_lt(n, d, tc, tg, g), ST.g_ltg(n, d, tc, tg, g), ST.whole(d), ST.g_pf(n, d, tc, tg, g), ST.g_pg(n, d, tc, tg, g), {==}, {==}, {==})) : {F.obs_item(F.get_done(_, n, d, SC.pow2(d))) == (ST.real(ST.Sh{n, d, tc, tg}), E.OItem{Done{TN.get_go(d, ST.mtree(d, tc, tg), i, 0, V.dec(d, i))}}) : F.SegTree & E.Obs}
        {==},
        (g,
         %Equal.sym(Maybe<&2, U32>, SC.nth(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), i), SC.nth(U32, MD.vals(ST.mtree(d, tc, tg)), i), LL.sc_nth_take(U32, MD.vals(ST.mtree(d, tc, tg)), n, i, eb)) : {(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OItem{Done{TN.get_go(d, ST.mtree(d, tc, tg), i, 0, V.dec(d, i))}}) == (SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OItem{S.item(_)}) : List<&2, U32> & E.Obs}
         %Equal.cong(List<&2, U32>, Maybe<&2, U32>, xs => SC.nth(U32, xs, i), Q.add_each(MD.vals(ST.mtree(d, tc, tg)), 0), MD.vals(ST.mtree(d, tc, tg)), vals0(ST.mtree(d, tc, tg))) : {(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OItem{Done{TN.get_go(d, ST.mtree(d, tc, tg), i, 0, V.dec(d, i))}}) == (SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OItem{S.item(_)}) : List<&2, U32> & E.Obs}
         %O.get_ok(d, ST.mtree(d, tc, tg), i, 0, hi, V.dec(d, i), {==}, ST.mt_perfect(d, tc, tg)) : {(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OItem{Done{TN.get_go(d, ST.mtree(d, tc, tg), i, 0, V.dec(d, i))}}) == (SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OItem{S.item(_)}) : List<&2, U32> & E.Obs}
         {==}))))
    case False{}:
      +hn = L.subst(Nat, q => {Nat.is_le(q, i) == True{} : Bool}, n, SC.length(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n)), Equal.sym(Nat, SC.length(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n)), n, ST.len_model(n, d, tc, tg, g)), N.not_lt_le(i, n, eb))
      (ST.Sh{n, d, tc, tg}, (E.OItem{Fail{E.IndexOutOfRange{}}}, (
        %Equal.sym(Bool, Nat.is_lt(i, n), False{}, eb) : {F.obs_item(F.get_if(_, n, d, SC.pow2(d), A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), i)) == (ST.real(ST.Sh{n, d, tc, tg}), E.OItem{Fail{E.IndexOutOfRange{}}}) : F.SegTree & E.Obs}
        {==},
        (g,
         %Equal.sym(Maybe<&2, U32>, SC.nth(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), i), None{}, LL.nth_none(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), i, hn)) : {(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OItem{Fail{E.IndexOutOfRange{}}}) == (SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OItem{S.item(_)}) : List<&2, U32> & E.Obs}
         {==}))))

# ---- set ----

def setc(+d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +i: Nat, +v: U32) -> A.Tree<F.Cel>:
  W.stree(d, tc, tg, d, 0, 0n, i, v, V.dec(d, i))

def setc_mtree(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +i: Nat, +v: U32, +g: {ST.repf(n, d, tc, tg) == True{} : Bool}) -> {ST.mtree(d, setc(d, tc, tg, i, v), tg) == TN.set_go(d, ST.mtree(d, tc, tg), i, v, 0, V.dec(d, i)) : TN.Node}:
  Equal.trans(TN.Node,
    W.tree_of(AR.cl(setc(d, tc, tg, i, v)), AR.cl(tg), d, d, 0n),
    W.tree_of(W.scells(d, AR.cl(tc), AR.cl(tg), d, 0, 0n, i, v, V.dec(d, i)), AR.cl(tg), d, d, 0n),
    TN.set_go(d, ST.mtree(d, tc, tg), i, v, 0, V.dec(d, i)),
    Equal.cong(List<&2, U32>, TN.Node, z => W.tree_of(z, AR.cl(tg), d, d, 0n),
      AR.cl(setc(d, tc, tg, i, v)), W.scells(d, AR.cl(tc), AR.cl(tg), d, 0, 0n, i, v, V.dec(d, i)),
      W.stree_cl(d, tc, tg, d, 0, 0n, i, v, V.dec(d, i), ST.whole(d), ST.g_pf(n, d, tc, tg, g))),
    W.set_ok(d, AR.cl(tc), AR.cl(tg), d, 0, 0n, i, v, V.dec(d, i), ST.whole(d), ST.cells_len(n, d, tc, tg, g)))

def set_vals(+d: Nat, +t: TN.Node, +i: Nat, +v: U32, +hi: {Nat.is_lt(i, V.pow2(d)) == True{} : Bool}, +pf: {MD.perfect(d, t) == True{} : Bool}) -> {MD.vals(TN.set_go(d, t, i, v, 0, V.dec(d, i))) == SC.update(U32, MD.vals(t), i, v) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, MD.vals(TN.set_go(d, t, i, v, 0, V.dec(d, i))), Q.add_each(MD.vals(TN.set_go(d, t, i, v, 0, V.dec(d, i))), 0), SC.update(U32, MD.vals(t), i, v),
    Equal.sym(List<&2, U32>, Q.add_each(MD.vals(TN.set_go(d, t, i, v, 0, V.dec(d, i))), 0), MD.vals(TN.set_go(d, t, i, v, 0, V.dec(d, i))), vals0(TN.set_go(d, t, i, v, 0, V.dec(d, i)))),
    %Equal.sym(List<&2, U32>, Q.add_each(MD.vals(TN.set_go(d, t, i, v, 0, V.dec(d, i))), 0), SC.update(U32, Q.add_each(MD.vals(t), 0), i, v), O.set_ok(d, t, i, v, 0, hi, V.dec(d, i), {==}, pf)) : {_ == SC.update(U32, MD.vals(t), i, v) : List<&2, U32>}
    Equal.cong(List<&2, U32>, List<&2, U32>, xs => SC.update(U32, xs, i, v), Q.add_each(MD.vals(t), 0), MD.vals(t), vals0(t)))

def spec_set_m(+xs: List<&2, U32>, +i: Nat, +v: U32, +hi: {Nat.is_lt(i, SC.length(U32, xs)) == True{} : Bool}, m: Maybe<&2, U32>, +em: {SC.nth(U32, xs, i) == m : Maybe<&2, U32>}) -> {S.assign(m, xs, i, v) == (SC.update(U32, xs, i, v), E.OUnit{Done{Unit{}}}) : List<&2, U32> & E.Obs}:
  match m:
    case None{}:
      Empty.absurd({(xs, E.OUnit{Fail{E.IndexOutOfRange{}}}) == (SC.update(U32, xs, i, v), E.OUnit{Done{Unit{}}}) : List<&2, U32> & E.Obs}, LL.sc_nth_some(U32, xs, i, hi, em))
    case Some{y}:
      {==}

def set_case(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +i: Nat, +v: U32, b: Bool, +eb: {Nat.is_lt(i, n) == b : Bool}, +g: {ST.repf(n, d, tc, tg) == True{} : Bool}) -> StepOK(ST.Sh{n, d, tc, tg}, E.Set{i, v}):
  match b:
    case True{}:
      +hi = L.subst(Nat, q => {Nat.is_lt(i, q) == True{} : Bool}, SC.pow2(d), V.pow2(d), Equal.sym(Nat, V.pow2(d), SC.pow2(d), W.vsc(d)), N.lt_le_trans(i, n, SC.pow2(d), eb, ST.g_cap(n, d, tc, tg, g)))
      +hA = L.subst(Nat, q => {Nat.is_lt(i, q) == True{} : Bool}, n, SC.length(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n)), Equal.sym(Nat, SC.length(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n)), n, ST.len_model(n, d, tc, tg, g)), eb)
      (ST.Sh{n, d, setc(d, tc, tg, i, v), tg}, (E.OUnit{Done{Unit{}}}, (
        %Equal.sym(Bool, Nat.is_lt(i, n), True{}, eb) : {F.obs_unit(F.set_if(_, n, d, SC.pow2(d), A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), i, v)) == (ST.real(ST.Sh{n, d, setc(d, tc, tg, i, v), tg}), E.OUnit{Done{Unit{}}}) : F.SegTree & E.Obs}
        %Equal.sym(Bool, Nat.is_lt(i, FL.hof(d)), V.dec(d, i), W.vdec(d, i, FL.hof(d), {==})) : {F.obs_unit(F.set_done(F.set_go(d, F.pre_t(d, A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), SC.pow2(d), FL.hof(d), 0n), SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0, 0n, i, v, _), n, d, SC.pow2(d))) == (ST.real(ST.Sh{n, d, setc(d, tc, tg, i, v), tg}), E.OUnit{Done{Unit{}}}) : F.SegTree & E.Obs}
        %Equal.sym(Array<F.Cel> & Array<F.Cel>, F.set_go(d, F.pre_t(d, A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), SC.pow2(d), FL.hof(d), 0n), SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0, 0n, i, v, V.dec(d, i)), (A.thaw(F.Cel, setc(d, tc, tg, i, v)), A.thaw(F.Cel, tg)), W.set_thaw(d, tc, tg, d, SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0, 0n, i, v, V.dec(d, i), ST.g_lt(n, d, tc, tg, g), ST.g_ltg(n, d, tc, tg, g), ST.whole(d), ST.g_pf(n, d, tc, tg, g), ST.g_pg(n, d, tc, tg, g), {==}, {==}, {==})) : {F.obs_unit(F.set_done(_, n, d, SC.pow2(d))) == (ST.real(ST.Sh{n, d, setc(d, tc, tg, i, v), tg}), E.OUnit{Done{Unit{}}}) : F.SegTree & E.Obs}
        {==},
        (ST.g_mk(n, d, setc(d, tc, tg, i, v), tg,
           W.stree_perfect(d, tc, tg, d, 0, 0n, i, v, V.dec(d, i), ST.g_pf(n, d, tc, tg, g)),
           ST.g_pg(n, d, tc, tg, g), ST.g_lt(n, d, tc, tg, g), ST.g_cap(n, d, tc, tg, g),
           %Equal.sym(TN.Node, ST.mtree(d, setc(d, tc, tg, i, v), tg), TN.set_go(d, ST.mtree(d, tc, tg), i, v, 0, V.dec(d, i)), setc_mtree(n, d, tc, tg, i, v, g)) : {MD.goods(_) == True{} : Bool}
           O.set_good(d, ST.mtree(d, tc, tg), i, v, 0, V.dec(d, i), ST.mt_perfect(d, tc, tg), ST.g_good(n, d, tc, tg, g))),
         %Equal.sym(TN.Node, ST.mtree(d, setc(d, tc, tg, i, v), tg), TN.set_go(d, ST.mtree(d, tc, tg), i, v, 0, V.dec(d, i)), setc_mtree(n, d, tc, tg, i, v, g)) : {(SC.take(U32, MD.vals(_), n), E.OUnit{Done{Unit{}}}) == S.step(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.Set{i, v}) : List<&2, U32> & E.Obs}
         %Equal.sym(List<&2, U32>, MD.vals(TN.set_go(d, ST.mtree(d, tc, tg), i, v, 0, V.dec(d, i))), SC.update(U32, MD.vals(ST.mtree(d, tc, tg)), i, v), set_vals(d, ST.mtree(d, tc, tg), i, v, hi, ST.mt_perfect(d, tc, tg))) : {(SC.take(U32, _, n), E.OUnit{Done{Unit{}}}) == S.step(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.Set{i, v}) : List<&2, U32> & E.Obs}
         %Equal.sym(List<&2, U32>, SC.take(U32, SC.update(U32, MD.vals(ST.mtree(d, tc, tg)), i, v), n), SC.update(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), i, v), LL.sc_take_update(U32, MD.vals(ST.mtree(d, tc, tg)), i, v, n)) : {(_, E.OUnit{Done{Unit{}}}) == S.step(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.Set{i, v}) : List<&2, U32> & E.Obs}
         Equal.sym(List<&2, U32> & E.Obs, S.assign(SC.nth(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), i), SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), i, v), (SC.update(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), i, v), E.OUnit{Done{Unit{}}}),
           spec_set_m(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), i, v, hA, SC.nth(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), i), {==}))))))
    case False{}:
      +hn = L.subst(Nat, q => {Nat.is_le(q, i) == True{} : Bool}, n, SC.length(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n)), Equal.sym(Nat, SC.length(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n)), n, ST.len_model(n, d, tc, tg, g)), N.not_lt_le(i, n, eb))
      (ST.Sh{n, d, tc, tg}, (E.OUnit{Fail{E.IndexOutOfRange{}}}, (
        %Equal.sym(Bool, Nat.is_lt(i, n), False{}, eb) : {F.obs_unit(F.set_if(_, n, d, SC.pow2(d), A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), i, v)) == (ST.real(ST.Sh{n, d, tc, tg}), E.OUnit{Fail{E.IndexOutOfRange{}}}) : F.SegTree & E.Obs}
        {==},
        (g,
         %Equal.sym(Maybe<&2, U32>, SC.nth(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), i), None{}, LL.nth_none(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), i, hn)) : {(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OUnit{Fail{E.IndexOutOfRange{}}}) == S.assign(_, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), i, v) : List<&2, U32> & E.Obs}
         {==}))))

# ---- range queries ----

def prefix_run(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +e: Nat, +g: {ST.repf(n, d, tc, tg) == True{} : Bool}) -> {F.prefix(d, A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), SC.pow2(d), e) == (A.thaw(F.Cel, tc), (A.thaw(F.Cel, tg), TN.prefix(d, ST.mtree(d, tc, tg), e))) : Array<F.Cel> & Array<F.Cel> & U32}:
  %Equal.sym(Bool, Nat.is_lt(e, FL.hof(d)), V.dec(d, e), W.vdec(d, e, FL.hof(d), {==})) : {F.prefix_go(d, F.pre_p(d, A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), SC.pow2(d), FL.hof(d), 0n), SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0, 0, 0n, e, _) == (A.thaw(F.Cel, tc), (A.thaw(F.Cel, tg), TN.prefix(d, ST.mtree(d, tc, tg), e))) : Array<F.Cel> & Array<F.Cel> & U32}
  %UA.zero_add(TN.prefix_go(d, ST.mtree(d, tc, tg), e, 0, V.dec(d, e))) : {F.prefix_go(d, F.pre_p(d, A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), SC.pow2(d), FL.hof(d), 0n), SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0, 0, 0n, e, V.dec(d, e)) == (A.thaw(F.Cel, tc), (A.thaw(F.Cel, tg), _)) : Array<F.Cel> & Array<F.Cel> & U32}
  W.prefix_ok(d, tc, tg, d, SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0, 0, 0n, e, V.dec(d, e), ST.g_lt(n, d, tc, tg, g), ST.g_ltg(n, d, tc, tg, g), ST.whole(d), ST.g_pf(n, d, tc, tg, g), ST.g_pg(n, d, tc, tg, g), {==}, {==}, {==})

def prefix_spec(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +e: Nat, +he: {Nat.is_le(e, n) == True{} : Bool}, +g: {ST.repf(n, d, tc, tg) == True{} : Bool}) -> {TN.prefix(d, ST.mtree(d, tc, tg), e) == Q.sum(SC.take(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), e)) : U32}:
  %Equal.sym(List<&2, U32>, SC.take(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), e), SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), e), LL.sc_take_take(U32, MD.vals(ST.mtree(d, tc, tg)), n, e, he)) : {TN.prefix(d, ST.mtree(d, tc, tg), e) == Q.sum(_) : U32}
  Equal.trans(U32, TN.prefix(d, ST.mtree(d, tc, tg), e), Q.sum(SC.take(U32, Q.add_each(MD.vals(ST.mtree(d, tc, tg)), 0), e)), Q.sum(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), e)),
    O.prefix_ok(d, ST.mtree(d, tc, tg), e, 0, N.le_trans(e, V.pow2(d), V.pow2(d), N.le_trans(e, n, V.pow2(d), he, cap_v(n, d, tc, tg, g)), N.le_refl(V.pow2(d))), V.dec(d, e), {==}, ST.mt_perfect(d, tc, tg), ST.g_good(n, d, tc, tg, g)),
    Equal.cong(List<&2, U32>, U32, xs => Q.sum(SC.take(U32, xs, e)), Q.add_each(MD.vals(ST.mtree(d, tc, tg)), 0), MD.vals(ST.mtree(d, tc, tg)), vals0(ST.mtree(d, tc, tg))))

def query_case(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +l: Nat, +r: Nat, b: Bool, +eb: {Bool.and(Nat.is_le(l, r), Nat.is_le(r, n)) == b : Bool}, +g: {ST.repf(n, d, tc, tg) == True{} : Bool}) -> StepOK(ST.Sh{n, d, tc, tg}, E.RangeQuery{l, r}):
  match b:
    case True{}:
      +hlr = L.and_left(Nat.is_le(l, r), Nat.is_le(r, n), eb)
      +hrn = L.and_right(Nat.is_le(l, r), Nat.is_le(r, n), eb)
      (ST.Sh{n, d, tc, tg}, (E.OItem{Done{U32.sub(TN.prefix(d, ST.mtree(d, tc, tg), r), TN.prefix(d, ST.mtree(d, tc, tg), l))}}, (
        %Equal.sym(Bool, Bool.and(Nat.is_le(l, r), Nat.is_le(r, n)), True{}, eb) : {F.obs_item(F.query_if(_, n, d, SC.pow2(d), A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), l, r)) == (ST.real(ST.Sh{n, d, tc, tg}), E.OItem{Done{U32.sub(TN.prefix(d, ST.mtree(d, tc, tg), r), TN.prefix(d, ST.mtree(d, tc, tg), l))}}) : F.SegTree & E.Obs}
        %Equal.sym(Array<F.Cel> & Array<F.Cel> & U32, F.prefix(d, A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), SC.pow2(d), r), (A.thaw(F.Cel, tc), (A.thaw(F.Cel, tg), TN.prefix(d, ST.mtree(d, tc, tg), r))), prefix_run(n, d, tc, tg, r, g)) : {F.obs_item(F.query_lo(_, n, d, SC.pow2(d), l)) == (ST.real(ST.Sh{n, d, tc, tg}), E.OItem{Done{U32.sub(TN.prefix(d, ST.mtree(d, tc, tg), r), TN.prefix(d, ST.mtree(d, tc, tg), l))}}) : F.SegTree & E.Obs}
        %Equal.sym(Array<F.Cel> & Array<F.Cel> & U32, F.prefix(d, A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), SC.pow2(d), l), (A.thaw(F.Cel, tc), (A.thaw(F.Cel, tg), TN.prefix(d, ST.mtree(d, tc, tg), l))), prefix_run(n, d, tc, tg, l, g)) : {F.obs_item(F.query_sub(_, n, d, SC.pow2(d), TN.prefix(d, ST.mtree(d, tc, tg), r))) == (ST.real(ST.Sh{n, d, tc, tg}), E.OItem{Done{U32.sub(TN.prefix(d, ST.mtree(d, tc, tg), r), TN.prefix(d, ST.mtree(d, tc, tg), l))}}) : F.SegTree & E.Obs}
        {==},
        (g,
         %Equal.sym(Nat, SC.length(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n)), n, ST.len_model(n, d, tc, tg, g)) : {(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OItem{Done{U32.sub(TN.prefix(d, ST.mtree(d, tc, tg), r), TN.prefix(d, ST.mtree(d, tc, tg), l))}}) == (SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OItem{S.query_if(Bool.and(Nat.is_le(l, r), Nat.is_le(r, _)), SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), l, r)}) : List<&2, U32> & E.Obs}
         %Equal.sym(Bool, Bool.and(Nat.is_le(l, r), Nat.is_le(r, n)), True{}, eb) : {(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OItem{Done{U32.sub(TN.prefix(d, ST.mtree(d, tc, tg), r), TN.prefix(d, ST.mtree(d, tc, tg), l))}}) == (SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OItem{S.query_if(_, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), l, r)}) : List<&2, U32> & E.Obs}
         %Equal.sym(U32, TN.prefix(d, ST.mtree(d, tc, tg), r), Q.sum(SC.take(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), r)), prefix_spec(n, d, tc, tg, r, hrn, g)) : {(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OItem{Done{U32.sub(_, TN.prefix(d, ST.mtree(d, tc, tg), l))}}) == (SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OItem{Done{Q.sum(Q.slice(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), l, r))}}) : List<&2, U32> & E.Obs}
         %Equal.sym(U32, TN.prefix(d, ST.mtree(d, tc, tg), l), Q.sum(SC.take(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), l)), prefix_spec(n, d, tc, tg, l, N.le_trans(l, r, n, hlr, hrn), g)) : {(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OItem{Done{U32.sub(Q.sum(SC.take(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), r)), _)}}) == (SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OItem{Done{Q.sum(Q.slice(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), l, r))}}) : List<&2, U32> & E.Obs}
         Equal.cong(U32, List<&2, U32> & E.Obs, z => (SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OItem{Done{z}}),
           U32.sub(Q.sum(SC.take(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), r)), Q.sum(SC.take(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), l))),
           Q.sum(Q.slice(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), l, r)),
           QS.sum_slice(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), l, r, hlr))))))
    case False{}:
      (ST.Sh{n, d, tc, tg}, (E.OItem{Fail{E.InvalidRange{}}}, (
        %Equal.sym(Bool, Bool.and(Nat.is_le(l, r), Nat.is_le(r, n)), False{}, eb) : {F.obs_item(F.query_if(_, n, d, SC.pow2(d), A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), l, r)) == (ST.real(ST.Sh{n, d, tc, tg}), E.OItem{Fail{E.InvalidRange{}}}) : F.SegTree & E.Obs}
        {==},
        (g,
         %Equal.sym(Nat, SC.length(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n)), n, ST.len_model(n, d, tc, tg, g)) : {(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OItem{Fail{E.InvalidRange{}}}) == (SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OItem{S.query_if(Bool.and(Nat.is_le(l, r), Nat.is_le(r, _)), SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), l, r)}) : List<&2, U32> & E.Obs}
         %Equal.sym(Bool, Bool.and(Nat.is_le(l, r), Nat.is_le(r, n)), False{}, eb) : {(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OItem{Fail{E.InvalidRange{}}}) == (SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OItem{S.query_if(_, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), l, r)}) : List<&2, U32> & E.Obs}
         {==}))))

# ---- lazy range addition ----

def paddc(+d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +i: Nat, +v: U32) -> A.Tree<F.Cel>:
  W.ptc(d, tc, tg, d, 0n, i, v, V.dec(d, i))

def paddg(+d: Nat, +tg: A.Tree<F.Cel>, +i: Nat, +v: U32) -> A.Tree<F.Cel>:
  W.ptg(d, tg, d, 0n, i, v, V.dec(d, i))

def padd_mtree(+d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +i: Nat, +v: U32, +pfc: {A.perfect(F.Cel, 1n+d, tc) == True{} : Bool}, +pfg: {A.perfect(F.Cel, d, tg) == True{} : Bool}, +hlen: {SC.length(U32, AR.cl(tc)) == SC.pow2(1n+d) : Nat}, +hlg: {SC.length(U32, AR.cl(tg)) == SC.pow2(d) : Nat}) -> {ST.mtree(d, paddc(d, tc, tg, i, v), paddg(d, tg, i, v)) == TN.padd_go(d, ST.mtree(d, tc, tg), i, v, V.dec(d, i)) : TN.Node}:
  %Equal.sym(List<&2, U32>, AR.cl(W.ptc(d, tc, tg, d, 0n, i, v, V.dec(d, i))), W.pcells(d, AR.cl(tc), AR.cl(tg), d, 0n, i, v, V.dec(d, i)), W.ptc_cl(d, tc, tg, d, 0n, i, v, V.dec(d, i), ST.whole(d), pfc, pfg)) : {W.tree_of(_, AR.cl(paddg(d, tg, i, v)), d, d, 0n) == TN.padd_go(d, ST.mtree(d, tc, tg), i, v, V.dec(d, i)) : TN.Node}
  %Equal.sym(List<&2, U32>, AR.cl(W.ptg(d, tg, d, 0n, i, v, V.dec(d, i))), W.ptags(d, AR.cl(tg), d, 0n, i, v, V.dec(d, i)), W.ptg_cl(d, tg, d, 0n, i, v, V.dec(d, i), ST.whole(d), pfg)) : {W.tree_of(W.pcells(d, AR.cl(tc), AR.cl(tg), d, 0n, i, v, V.dec(d, i)), _, d, d, 0n) == TN.padd_go(d, ST.mtree(d, tc, tg), i, v, V.dec(d, i)) : TN.Node}
  W.padd_ok(d, AR.cl(tc), AR.cl(tg), d, 0n, i, v, V.dec(d, i), ST.whole(d), hlen, hlg)

def padd_run(+d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +i: Nat, +v: U32, +hd: {Nat.is_lt(1n+d, 32n) == True{} : Bool}, +hdg: {Nat.is_lt(d, 32n) == True{} : Bool}, +pfc: {A.perfect(F.Cel, 1n+d, tc) == True{} : Bool}, +pfg: {A.perfect(F.Cel, d, tg) == True{} : Bool}) -> {F.padd(d, A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), SC.pow2(d), i, v) == (A.thaw(F.Cel, paddc(d, tc, tg, i, v)), A.thaw(F.Cel, paddg(d, tg, i, v))) : Array<F.Cel> & Array<F.Cel>}:
  %Equal.sym(Bool, Nat.is_lt(i, FL.hof(d)), V.dec(d, i), W.vdec(d, i, FL.hof(d), {==})) : {F.padd_go(d, A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0n, i, v, _) == (A.thaw(F.Cel, paddc(d, tc, tg, i, v)), A.thaw(F.Cel, paddg(d, tg, i, v))) : Array<F.Cel> & Array<F.Cel>}
  W.padd_thaw(d, tc, tg, d, SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0n, i, v, V.dec(d, i), hd, hdg, ST.whole(d), pfc, pfg, {==}, {==}, {==})

def padd_good(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +i: Nat, +v: U32, +hi: {Nat.is_le(i, V.pow2(d)) == True{} : Bool}, +g: {ST.repf(n, d, tc, tg) == True{} : Bool}) -> {ST.repf(n, d, paddc(d, tc, tg, i, v), paddg(d, tg, i, v)) == True{} : Bool}:
  ST.g_mk(n, d, paddc(d, tc, tg, i, v), paddg(d, tg, i, v),
    W.ptc_perfect(d, tc, tg, d, 0n, i, v, V.dec(d, i), ST.g_pf(n, d, tc, tg, g)),
    W.ptg_perfect(d, tg, d, 0n, i, v, V.dec(d, i), ST.g_pg(n, d, tc, tg, g)),
    ST.g_lt(n, d, tc, tg, g), ST.g_cap(n, d, tc, tg, g),
    %Equal.sym(TN.Node, ST.mtree(d, paddc(d, tc, tg, i, v), paddg(d, tg, i, v)), TN.padd_go(d, ST.mtree(d, tc, tg), i, v, V.dec(d, i)), padd_mtree(d, tc, tg, i, v, ST.g_pf(n, d, tc, tg, g), ST.g_pg(n, d, tc, tg, g), ST.cells_len(n, d, tc, tg, g), ST.tags_len(n, d, tc, tg, g))) : {MD.goods(_) == True{} : Bool}
    O.padd_good(d, ST.mtree(d, tc, tg), i, v, V.dec(d, i), ST.mt_perfect(d, tc, tg), ST.g_good(n, d, tc, tg, g)))

def add_case(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +l: Nat, +r: Nat, +v: U32, b: Bool, +eb: {Bool.and(Nat.is_le(l, r), Nat.is_le(r, n)) == b : Bool}, +g: {ST.repf(n, d, tc, tg) == True{} : Bool}) -> StepOK(ST.Sh{n, d, tc, tg}, E.RangeAdd{l, r, v}):
  match b:
    case True{}:
      +hlr = L.and_left(Nat.is_le(l, r), Nat.is_le(r, n), eb)
      +hrn = L.and_right(Nat.is_le(l, r), Nat.is_le(r, n), eb)
      +hr = N.le_trans(r, n, V.pow2(d), hrn, cap_v(n, d, tc, tg, g))
      +hl = N.le_trans(l, r, V.pow2(d), hlr, hr)
      +g1 = padd_good(n, d, tc, tg, r, v, hr, g)
      +em1 = padd_mtree(d, tc, tg, r, v, ST.g_pf(n, d, tc, tg, g), ST.g_pg(n, d, tc, tg, g), ST.cells_len(n, d, tc, tg, g), ST.tags_len(n, d, tc, tg, g))
      +em2 = padd_mtree(d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), l, U32.sub(0, v), ST.g_pf(n, d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), g1), ST.g_pg(n, d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), g1), ST.cells_len(n, d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), g1), ST.tags_len(n, d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), g1))
      +ev = Equal.trans(List<&2, U32>,
        MD.vals(ST.mtree(d, paddc(d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), l, U32.sub(0, v)), paddg(d, paddg(d, tg, r, v), l, U32.sub(0, v)))),
        MD.addfirst(MD.vals(ST.mtree(d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v))), l, U32.sub(0, v)),
        MD.addfirst(MD.addfirst(MD.vals(ST.mtree(d, tc, tg)), r, v), l, U32.sub(0, v)),
        %Equal.sym(TN.Node, ST.mtree(d, paddc(d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), l, U32.sub(0, v)), paddg(d, paddg(d, tg, r, v), l, U32.sub(0, v))), TN.padd_go(d, ST.mtree(d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v)), l, U32.sub(0, v), V.dec(d, l)), em2) : {MD.vals(_) == MD.addfirst(MD.vals(ST.mtree(d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v))), l, U32.sub(0, v)) : List<&2, U32>}
        O.padd_vals(d, ST.mtree(d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v)), l, U32.sub(0, v), hl, V.dec(d, l), {==}, ST.mt_perfect(d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v))),
        Equal.cong(List<&2, U32>, List<&2, U32>, xs => MD.addfirst(xs, l, U32.sub(0, v)),
          MD.vals(ST.mtree(d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v))), MD.addfirst(MD.vals(ST.mtree(d, tc, tg)), r, v),
          %Equal.sym(TN.Node, ST.mtree(d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v)), TN.padd_go(d, ST.mtree(d, tc, tg), r, v, V.dec(d, r)), em1) : {MD.vals(_) == MD.addfirst(MD.vals(ST.mtree(d, tc, tg)), r, v) : List<&2, U32>}
          O.padd_vals(d, ST.mtree(d, tc, tg), r, v, hr, V.dec(d, r), {==}, ST.mt_perfect(d, tc, tg))))
      (ST.Sh{n, d, paddc(d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), l, U32.sub(0, v)), paddg(d, paddg(d, tg, r, v), l, U32.sub(0, v))}, (E.OUnit{Done{Unit{}}}, (
        %Equal.sym(Bool, Bool.and(Nat.is_le(l, r), Nat.is_le(r, n)), True{}, eb) : {F.obs_unit(F.add_if(_, n, d, SC.pow2(d), A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), l, r, v)) == (ST.real(ST.Sh{n, d, paddc(d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), l, U32.sub(0, v)), paddg(d, paddg(d, tg, r, v), l, U32.sub(0, v))}), E.OUnit{Done{Unit{}}}) : F.SegTree & E.Obs}
        %Equal.sym(Array<F.Cel> & Array<F.Cel>, F.padd(d, A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), SC.pow2(d), r, v), (A.thaw(F.Cel, paddc(d, tc, tg, r, v)), A.thaw(F.Cel, paddg(d, tg, r, v))), padd_run(d, tc, tg, r, v, ST.g_lt(n, d, tc, tg, g), ST.g_ltg(n, d, tc, tg, g), ST.g_pf(n, d, tc, tg, g), ST.g_pg(n, d, tc, tg, g))) : {F.obs_unit(F.add_lo(_, n, d, SC.pow2(d), l, v)) == (ST.real(ST.Sh{n, d, paddc(d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), l, U32.sub(0, v)), paddg(d, paddg(d, tg, r, v), l, U32.sub(0, v))}), E.OUnit{Done{Unit{}}}) : F.SegTree & E.Obs}
        %Equal.sym(Array<F.Cel> & Array<F.Cel>, F.padd(d, A.thaw(F.Cel, paddc(d, tc, tg, r, v)), A.thaw(F.Cel, paddg(d, tg, r, v)), SC.pow2(d), l, U32.sub(0, v)), (A.thaw(F.Cel, paddc(d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), l, U32.sub(0, v))), A.thaw(F.Cel, paddg(d, paddg(d, tg, r, v), l, U32.sub(0, v)))), padd_run(d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), l, U32.sub(0, v), ST.g_lt(n, d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), g1), ST.g_ltg(n, d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), g1), ST.g_pf(n, d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), g1), ST.g_pg(n, d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), g1))) : {F.obs_unit(F.set_done(_, n, d, SC.pow2(d))) == (ST.real(ST.Sh{n, d, paddc(d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), l, U32.sub(0, v)), paddg(d, paddg(d, tg, r, v), l, U32.sub(0, v))}), E.OUnit{Done{Unit{}}}) : F.SegTree & E.Obs}
        {==},
        (padd_good(n, d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), l, U32.sub(0, v), hl, g1),
         %Equal.sym(Nat, SC.length(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n)), n, ST.len_model(n, d, tc, tg, g)) : {(SC.take(U32, MD.vals(ST.mtree(d, paddc(d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), l, U32.sub(0, v)), paddg(d, paddg(d, tg, r, v), l, U32.sub(0, v)))), n), E.OUnit{Done{Unit{}}}) == S.add_if(Bool.and(Nat.is_le(l, r), Nat.is_le(r, _)), SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), l, r, v) : List<&2, U32> & E.Obs}
         %Equal.sym(Bool, Bool.and(Nat.is_le(l, r), Nat.is_le(r, n)), True{}, eb) : {(SC.take(U32, MD.vals(ST.mtree(d, paddc(d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), l, U32.sub(0, v)), paddg(d, paddg(d, tg, r, v), l, U32.sub(0, v)))), n), E.OUnit{Done{Unit{}}}) == S.add_if(_, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), l, r, v) : List<&2, U32> & E.Obs}
         Equal.cong(List<&2, U32>, List<&2, U32> & E.Obs, xs => (xs, E.OUnit{Done{Unit{}}}),
           SC.take(U32, MD.vals(ST.mtree(d, paddc(d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), l, U32.sub(0, v)), paddg(d, paddg(d, tg, r, v), l, U32.sub(0, v)))), n), S.added(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), l, r, v),
           %Equal.sym(List<&2, U32>, MD.vals(ST.mtree(d, paddc(d, paddc(d, tc, tg, r, v), paddg(d, tg, r, v), l, U32.sub(0, v)), paddg(d, paddg(d, tg, r, v), l, U32.sub(0, v)))), MD.addfirst(MD.addfirst(MD.vals(ST.mtree(d, tc, tg)), r, v), l, U32.sub(0, v)), ev) : {SC.take(U32, _, n) == S.added(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), l, r, v) : List<&2, U32>}
           %Equal.sym(List<&2, U32>, SC.take(U32, MD.addfirst(MD.addfirst(MD.vals(ST.mtree(d, tc, tg)), r, v), l, U32.sub(0, v)), n), MD.addfirst(SC.take(U32, MD.addfirst(MD.vals(ST.mtree(d, tc, tg)), r, v), n), l, U32.sub(0, v)), MD.take_addfirst(MD.addfirst(MD.vals(ST.mtree(d, tc, tg)), r, v), l, U32.sub(0, v), n)) : {_ == S.added(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), l, r, v) : List<&2, U32>}
           %Equal.sym(List<&2, U32>, SC.take(U32, MD.addfirst(MD.vals(ST.mtree(d, tc, tg)), r, v), n), MD.addfirst(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), r, v), MD.take_addfirst(MD.vals(ST.mtree(d, tc, tg)), r, v, n)) : {MD.addfirst(_, l, U32.sub(0, v)) == S.added(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), l, r, v) : List<&2, U32>}
           MD.range_add(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), l, r, v, hlr))))))
    case False{}:
      (ST.Sh{n, d, tc, tg}, (E.OUnit{Fail{E.InvalidRange{}}}, (
        %Equal.sym(Bool, Bool.and(Nat.is_le(l, r), Nat.is_le(r, n)), False{}, eb) : {F.obs_unit(F.add_if(_, n, d, SC.pow2(d), A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), l, r, v)) == (ST.real(ST.Sh{n, d, tc, tg}), E.OUnit{Fail{E.InvalidRange{}}}) : F.SegTree & E.Obs}
        {==},
        (g,
         %Equal.sym(Nat, SC.length(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n)), n, ST.len_model(n, d, tc, tg, g)) : {(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OUnit{Fail{E.InvalidRange{}}}) == S.add_if(Bool.and(Nat.is_le(l, r), Nat.is_le(r, _)), SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), l, r, v) : List<&2, U32> & E.Obs}
         %Equal.sym(Bool, Bool.and(Nat.is_le(l, r), Nat.is_le(r, n)), False{}, eb) : {(SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), E.OUnit{Fail{E.InvalidRange{}}}) == S.add_if(_, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), l, r, v) : List<&2, U32> & E.Obs}
         {==}))))

# ---- every operation ----

def step_ok(+sh: ST.Sh, op: E.Op, +g: {ST.good(sh) == True{} : Bool}) -> StepOK(sh, op):
  match sh op:
    case ST.Sh{+n, +d, +tc, +tg} E.Length{}:
      length_case(n, d, tc, tg, g)
    case ST.Sh{+n, +d, +tc, +tg} E.Get{+i}:
      get_case(n, d, tc, tg, i, Nat.is_lt(i, n), {==}, g)
    case ST.Sh{+n, +d, +tc, +tg} E.Set{+i, +v}:
      set_case(n, d, tc, tg, i, v, Nat.is_lt(i, n), {==}, g)
    case ST.Sh{+n, +d, +tc, +tg} E.RangeQuery{+l, +r}:
      query_case(n, d, tc, tg, l, r, Bool.and(Nat.is_le(l, r), Nat.is_le(r, n)), {==}, g)
    case ST.Sh{+n, +d, +tc, +tg} E.RangeAdd{+l, +r, +v}:
      add_case(n, d, tc, tg, l, r, v, Bool.and(Nat.is_le(l, r), Nat.is_le(r, n)), {==}, g)
