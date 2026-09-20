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
import ../../spec/fenwick_tree.bend as S
import ../../src/fenwick_tree.bend as F
import ../../types/fenwick_tree.bend as E
import ./model.bend as M
import ./tree.bend as T
import ./arr.bend as AR
import ./walk.bend as W
import ./state.bend as ST

# Every public operation (errors included) refines the spec step and keeps
# the representation invariant.
#
# The cell array is linear, so a step is stated as: the real operation on the
# array of a good shadow produces the array of another good shadow, whose
# model and observation are the spec step of the first shadow's model.

def StepOK(sh: ST.Sh, op: E.Op) -> Type:
  Sigma<&1, &1, ST.Sh, sh2 => Sigma<&1, &1, E.Obs, o => {F.step(ST.real(sh), op) == (ST.real(sh2), o) : F.Fenwick & E.Obs} & ({ST.good(sh2) == True{} : Bool} & {(ST.model(sh2), o) == S.step(ST.model(sh), op) : List<&2, U32> & E.Obs})>>

# ---- the spec's add on an in-range index ----

def spec_add_m(+xs: List<&2, U32>, +i: Nat, +v: U32, +hi: {Nat.is_lt(i, SC.length(U32, xs)) == True{} : Bool}, m: Maybe<&2, U32>, +em: {SC.nth(U32, xs, i) == m : Maybe<&2, U32>}) -> {S.add_at(m, xs, i, v) == (QS.addat(xs, i, v), E.OUnit{Done{Unit{}}}) : List<&2, U32> & E.Obs}:
  match m:
    case None{}:
      Empty.absurd({(xs, E.OUnit{Fail{E.IndexOutOfRange{}}}) == (QS.addat(xs, i, v), E.OUnit{Done{Unit{}}}) : List<&2, U32> & E.Obs}, LL.sc_nth_some(U32, xs, i, hi, em))
    case Some{y}:
      Equal.cong(List<&2, U32>, List<&2, U32> & E.Obs, zs => (zs, E.OUnit{Done{Unit{}}}), SC.update(U32, xs, i, U32.add(y, v)), QS.addat(xs, i, v), QS.update_addat(xs, i, y, v, em))

# ---- length ----

def length_case(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>, +g: {ST.repf(n, d, t) == True{} : Bool}) -> StepOK(ST.Sh{n, d, t}, E.Length{}):
  (ST.Sh{n, d, t}, (E.ONat{n}, ({==},
    (g,
     %Equal.sym(Nat, SC.length(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n)), n, ST.len_model(n, d, t, g)) : {(SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.ONat{n}) == (SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.ONat{_}) : List<&2, U32> & E.Obs}
     {==}))))

# ---- add ----

def added(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>, +i: Nat, +v: U32) -> A.Tree<F.Cel>:
  W.atree(d, t, d, 0n, i, v, M.dec(d, i))

def added_mtree(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>, +i: Nat, +v: U32, +g: {ST.repf(n, d, t) == True{} : Bool}) -> {ST.mtree(d, added(n, d, t, i, v)) == M.add_go(d, ST.mtree(d, t), i, v, M.dec(d, i)) : M.Node}:
  Equal.trans(M.Node,
    W.tree_of(AR.cl(W.atree(d, t, d, 0n, i, v, M.dec(d, i))), d, d, 0n),
    W.tree_of(W.acells(d, AR.cl(t), d, 0n, i, v, M.dec(d, i)), d, d, 0n),
    M.add_go(d, ST.mtree(d, t), i, v, M.dec(d, i)),
    Equal.cong(List<&2, U32>, M.Node, z => W.tree_of(z, d, d, 0n),
      AR.cl(W.atree(d, t, d, 0n, i, v, M.dec(d, i))), W.acells(d, AR.cl(t), d, 0n, i, v, M.dec(d, i)),
      W.atree_cl(d, t, d, 0n, i, v, M.dec(d, i), ST.whole(d), ST.g_pf(n, d, t, g))),
    W.add_ok(d, AR.cl(t), d, 0n, i, v, M.dec(d, i), ST.whole(d), ST.cells_len(n, d, t, g)))

def add_case(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>, +i: Nat, +v: U32, b: Bool, +eb: {Nat.is_lt(i, n) == b : Bool}, +g: {ST.repf(n, d, t) == True{} : Bool}) -> StepOK(ST.Sh{n, d, t}, E.Add{i, v}):
  match b:
    case True{}:
      +hi = N.lt_le_trans(i, n, SC.pow2(d), eb, ST.g_cap(n, d, t, g))
      +hA = L.subst(Nat, q => {Nat.is_lt(i, q) == True{} : Bool}, n, SC.length(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n)), Equal.sym(Nat, SC.length(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n)), n, ST.len_model(n, d, t, g)), eb)
      (ST.Sh{n, d, added(n, d, t, i, v)}, (E.OUnit{Done{Unit{}}}, (
        %Equal.sym(Bool, Nat.is_lt(i, n), True{}, eb) : {F.obs_unit(F.add_if(_, n, d, SC.pow2(d), A.thaw(F.Cel, t), i, v)) == (ST.real(ST.Sh{n, d, added(n, d, t, i, v)}), E.OUnit{Done{Unit{}}}) : F.Fenwick & E.Obs}
        %Equal.sym(Bool, Nat.is_lt(i, FL.hof(d)), M.dec(d, i), W.dec_h(d, i, FL.hof(d), {==})) : {F.obs_unit((F.FT{n, d, SC.pow2(d), F.add_go(d, A.thaw(F.Cel, t), SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0n, i, v, _)}, Done{Unit{}})) == (ST.real(ST.Sh{n, d, added(n, d, t, i, v)}), E.OUnit{Done{Unit{}}}) : F.Fenwick & E.Obs}
        %Equal.sym(Array<F.Cel>, F.add_go(d, A.thaw(F.Cel, t), SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0n, i, v, M.dec(d, i)), A.thaw(F.Cel, added(n, d, t, i, v)), W.add_thaw(d, t, d, SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0n, i, v, M.dec(d, i), ST.g_lt(n, d, t, g), ST.whole(d), ST.g_pf(n, d, t, g), {==}, {==}, {==})) : {F.obs_unit((F.FT{n, d, SC.pow2(d), _}, Done{Unit{}})) == (ST.real(ST.Sh{n, d, added(n, d, t, i, v)}), E.OUnit{Done{Unit{}}}) : F.Fenwick & E.Obs}
        {==},
        (ST.g_mk(n, d, added(n, d, t, i, v),
           W.atree_perfect(d, t, d, 0n, i, v, M.dec(d, i), ST.g_pf(n, d, t, g)),
           ST.g_lt(n, d, t, g), ST.g_cap(n, d, t, g),
           %Equal.sym(M.Node, ST.mtree(d, added(n, d, t, i, v)), M.add_go(d, ST.mtree(d, t), i, v, M.dec(d, i)), added_mtree(n, d, t, i, v, g)) : {T.goodf(_) == True{} : Bool}
           T.add_good(d, ST.mtree(d, t), i, v, hi, M.dec(d, i), {==}, ST.mt_perfect(d, t), ST.g_good(n, d, t, g))),
         %Equal.sym(M.Node, ST.mtree(d, added(n, d, t, i, v)), M.add_go(d, ST.mtree(d, t), i, v, M.dec(d, i)), added_mtree(n, d, t, i, v, g)) : {(SC.take(U32, T.leaves(_), n), E.OUnit{Done{Unit{}}}) == S.step(SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.Add{i, v}) : List<&2, U32> & E.Obs}
         %Equal.sym(List<&2, U32>, T.leaves(M.add_go(d, ST.mtree(d, t), i, v, M.dec(d, i))), QS.addat(T.leaves(ST.mtree(d, t)), i, v), T.add_leaves(d, ST.mtree(d, t), i, v, hi, M.dec(d, i), {==}, ST.mt_perfect(d, t))) : {(SC.take(U32, _, n), E.OUnit{Done{Unit{}}}) == S.step(SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.Add{i, v}) : List<&2, U32> & E.Obs}
         %Equal.sym(List<&2, U32>, SC.take(U32, QS.addat(T.leaves(ST.mtree(d, t)), i, v), n), QS.addat(SC.take(U32, T.leaves(ST.mtree(d, t)), n), i, v), QS.take_addat(T.leaves(ST.mtree(d, t)), i, v, n)) : {(_, E.OUnit{Done{Unit{}}}) == S.step(SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.Add{i, v}) : List<&2, U32> & E.Obs}
         Equal.sym(List<&2, U32> & E.Obs, S.add_at(SC.nth(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n), i), SC.take(U32, T.leaves(ST.mtree(d, t)), n), i, v), (QS.addat(SC.take(U32, T.leaves(ST.mtree(d, t)), n), i, v), E.OUnit{Done{Unit{}}}),
           spec_add_m(SC.take(U32, T.leaves(ST.mtree(d, t)), n), i, v, hA, SC.nth(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n), i), {==}))))))
    case False{}:
      +hn = L.subst(Nat, q => {Nat.is_le(q, i) == True{} : Bool}, n, SC.length(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n)), Equal.sym(Nat, SC.length(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n)), n, ST.len_model(n, d, t, g)), N.not_lt_le(i, n, eb))
      (ST.Sh{n, d, t}, (E.OUnit{Fail{E.IndexOutOfRange{}}}, (
        %Equal.sym(Bool, Nat.is_lt(i, n), False{}, eb) : {F.obs_unit(F.add_if(_, n, d, SC.pow2(d), A.thaw(F.Cel, t), i, v)) == (ST.real(ST.Sh{n, d, t}), E.OUnit{Fail{E.IndexOutOfRange{}}}) : F.Fenwick & E.Obs}
        {==},
        (g,
         %Equal.sym(Maybe<&2, U32>, SC.nth(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n), i), None{}, LL.nth_none(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n), i, hn)) : {(SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OUnit{Fail{E.IndexOutOfRange{}}}) == S.add_at(_, SC.take(U32, T.leaves(ST.mtree(d, t)), n), i, v) : List<&2, U32> & E.Obs}
         {==}))))

# ---- prefix sums ----

# The runtime walk from the root computes the model's prefix sum.
def prefix_run(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>, +e: Nat, +g: {ST.repf(n, d, t) == True{} : Bool}) -> {F.prefix(d, A.thaw(F.Cel, t), SC.pow2(d), e) == (A.thaw(F.Cel, t), M.prefix(d, ST.mtree(d, t), e)) : Array<F.Cel> & U32}:
  %Equal.sym(Bool, Nat.is_lt(e, FL.hof(d)), M.dec(d, e), W.dec_h(d, e, FL.hof(d), {==})) : {F.prefix_go(d, F.pre(d, A.thaw(F.Cel, t), SC.pow2(d), FL.hof(d), 0n), SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0, 0n, e, _) == (A.thaw(F.Cel, t), M.prefix(d, ST.mtree(d, t), e)) : Array<F.Cel> & U32}
  %UA.zero_add(M.prefix_go(d, ST.mtree(d, t), e, M.dec(d, e))) : {F.prefix_go(d, F.pre(d, A.thaw(F.Cel, t), SC.pow2(d), FL.hof(d), 0n), SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0, 0n, e, M.dec(d, e)) == (A.thaw(F.Cel, t), _) : Array<F.Cel> & U32}
  W.prefix_ok(d, t, d, SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0, 0n, e, M.dec(d, e), ST.g_lt(n, d, t, g), ST.whole(d), ST.g_pf(n, d, t, g), {==}, {==}, {==})

def prefix_spec(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>, +e: Nat, +he: {Nat.is_le(e, n) == True{} : Bool}, +g: {ST.repf(n, d, t) == True{} : Bool}) -> {M.prefix(d, ST.mtree(d, t), e) == Q.sum(SC.take(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n), e)) : U32}:
  %Equal.sym(List<&2, U32>, SC.take(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n), e), SC.take(U32, T.leaves(ST.mtree(d, t)), e), LL.sc_take_take(U32, T.leaves(ST.mtree(d, t)), n, e, he)) : {M.prefix(d, ST.mtree(d, t), e) == Q.sum(_) : U32}
  T.prefix_ok(d, ST.mtree(d, t), e, N.le_trans(e, n, SC.pow2(d), he, ST.g_cap(n, d, t, g)), M.dec(d, e), {==}, ST.mt_perfect(d, t), ST.g_good(n, d, t, g))

def prefix_case(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>, +e: Nat, b: Bool, +eb: {Nat.is_le(e, n) == b : Bool}, +g: {ST.repf(n, d, t) == True{} : Bool}) -> StepOK(ST.Sh{n, d, t}, E.PrefixSum{e}):
  match b:
    case True{}:
      (ST.Sh{n, d, t}, (E.OSum{Done{M.prefix(d, ST.mtree(d, t), e)}}, (
        %Equal.sym(Bool, Nat.is_le(e, n), True{}, eb) : {F.obs_sum(F.prefix_if(_, n, d, SC.pow2(d), A.thaw(F.Cel, t), e)) == (ST.real(ST.Sh{n, d, t}), E.OSum{Done{M.prefix(d, ST.mtree(d, t), e)}}) : F.Fenwick & E.Obs}
        %Equal.sym(Array<F.Cel> & U32, F.prefix(d, A.thaw(F.Cel, t), SC.pow2(d), e), (A.thaw(F.Cel, t), M.prefix(d, ST.mtree(d, t), e)), prefix_run(n, d, t, e, g)) : {F.obs_sum(F.prefix_done(_, n, d, SC.pow2(d))) == (ST.real(ST.Sh{n, d, t}), E.OSum{Done{M.prefix(d, ST.mtree(d, t), e)}}) : F.Fenwick & E.Obs}
        {==},
        (g,
         %Equal.sym(Nat, SC.length(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n)), n, ST.len_model(n, d, t, g)) : {(SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{Done{M.prefix(d, ST.mtree(d, t), e)}}) == (SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{S.prefix_if(Nat.is_le(e, _), SC.take(U32, T.leaves(ST.mtree(d, t)), n), e)}) : List<&2, U32> & E.Obs}
         %Equal.sym(Bool, Nat.is_le(e, n), True{}, eb) : {(SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{Done{M.prefix(d, ST.mtree(d, t), e)}}) == (SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{S.prefix_if(_, SC.take(U32, T.leaves(ST.mtree(d, t)), n), e)}) : List<&2, U32> & E.Obs}
         %Equal.sym(U32, M.prefix(d, ST.mtree(d, t), e), Q.sum(SC.take(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n), e)), prefix_spec(n, d, t, e, eb, g)) : {(SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{Done{_}}) == (SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{Done{Q.sum(SC.take(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n), e))}}) : List<&2, U32> & E.Obs}
         {==}))))
    case False{}:
      (ST.Sh{n, d, t}, (E.OSum{Fail{E.InvalidRange{}}}, (
        %Equal.sym(Bool, Nat.is_le(e, n), False{}, eb) : {F.obs_sum(F.prefix_if(_, n, d, SC.pow2(d), A.thaw(F.Cel, t), e)) == (ST.real(ST.Sh{n, d, t}), E.OSum{Fail{E.InvalidRange{}}}) : F.Fenwick & E.Obs}
        {==},
        (g,
         %Equal.sym(Nat, SC.length(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n)), n, ST.len_model(n, d, t, g)) : {(SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{Fail{E.InvalidRange{}}}) == (SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{S.prefix_if(Nat.is_le(e, _), SC.take(U32, T.leaves(ST.mtree(d, t)), n), e)}) : List<&2, U32> & E.Obs}
         %Equal.sym(Bool, Nat.is_le(e, n), False{}, eb) : {(SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{Fail{E.InvalidRange{}}}) == (SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{S.prefix_if(_, SC.take(U32, T.leaves(ST.mtree(d, t)), n), e)}) : List<&2, U32> & E.Obs}
         {==}))))

# ---- range sums ----

def range_case(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>, +l: Nat, +r: Nat, b: Bool, +eb: {Bool.and(Nat.is_le(l, r), Nat.is_le(r, n)) == b : Bool}, +g: {ST.repf(n, d, t) == True{} : Bool}) -> StepOK(ST.Sh{n, d, t}, E.RangeSum{l, r}):
  match b:
    case True{}:
      +hlr = L.and_left(Nat.is_le(l, r), Nat.is_le(r, n), eb)
      +hrn = L.and_right(Nat.is_le(l, r), Nat.is_le(r, n), eb)
      (ST.Sh{n, d, t}, (E.OSum{Done{U32.sub(M.prefix(d, ST.mtree(d, t), r), M.prefix(d, ST.mtree(d, t), l))}}, (
        %Equal.sym(Bool, Bool.and(Nat.is_le(l, r), Nat.is_le(r, n)), True{}, eb) : {F.obs_sum(F.range_if(_, n, d, SC.pow2(d), A.thaw(F.Cel, t), l, r)) == (ST.real(ST.Sh{n, d, t}), E.OSum{Done{U32.sub(M.prefix(d, ST.mtree(d, t), r), M.prefix(d, ST.mtree(d, t), l))}}) : F.Fenwick & E.Obs}
        %Equal.sym(Array<F.Cel> & U32, F.prefix(d, A.thaw(F.Cel, t), SC.pow2(d), r), (A.thaw(F.Cel, t), M.prefix(d, ST.mtree(d, t), r)), prefix_run(n, d, t, r, g)) : {F.obs_sum(F.range_lo(_, n, d, SC.pow2(d), l)) == (ST.real(ST.Sh{n, d, t}), E.OSum{Done{U32.sub(M.prefix(d, ST.mtree(d, t), r), M.prefix(d, ST.mtree(d, t), l))}}) : F.Fenwick & E.Obs}
        %Equal.sym(Array<F.Cel> & U32, F.prefix(d, A.thaw(F.Cel, t), SC.pow2(d), l), (A.thaw(F.Cel, t), M.prefix(d, ST.mtree(d, t), l)), prefix_run(n, d, t, l, g)) : {F.obs_sum(F.range_fin(_, n, d, SC.pow2(d), M.prefix(d, ST.mtree(d, t), r))) == (ST.real(ST.Sh{n, d, t}), E.OSum{Done{U32.sub(M.prefix(d, ST.mtree(d, t), r), M.prefix(d, ST.mtree(d, t), l))}}) : F.Fenwick & E.Obs}
        {==},
        (g,
         %Equal.sym(Nat, SC.length(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n)), n, ST.len_model(n, d, t, g)) : {(SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{Done{U32.sub(M.prefix(d, ST.mtree(d, t), r), M.prefix(d, ST.mtree(d, t), l))}}) == (SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{S.range_if(Bool.and(Nat.is_le(l, r), Nat.is_le(r, _)), SC.take(U32, T.leaves(ST.mtree(d, t)), n), l, r)}) : List<&2, U32> & E.Obs}
         %Equal.sym(Bool, Bool.and(Nat.is_le(l, r), Nat.is_le(r, n)), True{}, eb) : {(SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{Done{U32.sub(M.prefix(d, ST.mtree(d, t), r), M.prefix(d, ST.mtree(d, t), l))}}) == (SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{S.range_if(_, SC.take(U32, T.leaves(ST.mtree(d, t)), n), l, r)}) : List<&2, U32> & E.Obs}
         %Equal.sym(U32, M.prefix(d, ST.mtree(d, t), r), Q.sum(SC.take(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n), r)), prefix_spec(n, d, t, r, hrn, g)) : {(SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{Done{U32.sub(_, M.prefix(d, ST.mtree(d, t), l))}}) == (SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{Done{Q.sum(Q.slice(SC.take(U32, T.leaves(ST.mtree(d, t)), n), l, r))}}) : List<&2, U32> & E.Obs}
         %Equal.sym(U32, M.prefix(d, ST.mtree(d, t), l), Q.sum(SC.take(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n), l)), prefix_spec(n, d, t, l, N.le_trans(l, r, n, hlr, hrn), g)) : {(SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{Done{U32.sub(Q.sum(SC.take(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n), r)), _)}}) == (SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{Done{Q.sum(Q.slice(SC.take(U32, T.leaves(ST.mtree(d, t)), n), l, r))}}) : List<&2, U32> & E.Obs}
         Equal.cong(U32, List<&2, U32> & E.Obs, z => (SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{Done{z}}),
           U32.sub(Q.sum(SC.take(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n), r)), Q.sum(SC.take(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n), l))),
           Q.sum(Q.slice(SC.take(U32, T.leaves(ST.mtree(d, t)), n), l, r)),
           QS.sum_slice(SC.take(U32, T.leaves(ST.mtree(d, t)), n), l, r, hlr))))))
    case False{}:
      (ST.Sh{n, d, t}, (E.OSum{Fail{E.InvalidRange{}}}, (
        %Equal.sym(Bool, Bool.and(Nat.is_le(l, r), Nat.is_le(r, n)), False{}, eb) : {F.obs_sum(F.range_if(_, n, d, SC.pow2(d), A.thaw(F.Cel, t), l, r)) == (ST.real(ST.Sh{n, d, t}), E.OSum{Fail{E.InvalidRange{}}}) : F.Fenwick & E.Obs}
        {==},
        (g,
         %Equal.sym(Nat, SC.length(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n)), n, ST.len_model(n, d, t, g)) : {(SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{Fail{E.InvalidRange{}}}) == (SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{S.range_if(Bool.and(Nat.is_le(l, r), Nat.is_le(r, _)), SC.take(U32, T.leaves(ST.mtree(d, t)), n), l, r)}) : List<&2, U32> & E.Obs}
         %Equal.sym(Bool, Bool.and(Nat.is_le(l, r), Nat.is_le(r, n)), False{}, eb) : {(SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{Fail{E.InvalidRange{}}}) == (SC.take(U32, T.leaves(ST.mtree(d, t)), n), E.OSum{S.range_if(_, SC.take(U32, T.leaves(ST.mtree(d, t)), n), l, r)}) : List<&2, U32> & E.Obs}
         {==}))))

# ---- every operation ----

def step_ok(+sh: ST.Sh, op: E.Op, +g: {ST.good(sh) == True{} : Bool}) -> StepOK(sh, op):
  match sh op:
    case ST.Sh{+n, +d, +t} E.Length{}:
      length_case(n, d, t, g)
    case ST.Sh{+n, +d, +t} E.Add{+i, +v}:
      add_case(n, d, t, i, v, Nat.is_lt(i, n), {==}, g)
    case ST.Sh{+n, +d, +t} E.PrefixSum{+e}:
      prefix_case(n, d, t, e, Nat.is_le(e, n), {==}, g)
    case ST.Sh{+n, +d, +t} E.RangeSum{+l, +r}:
      range_case(n, d, t, l, r, Bool.and(Nat.is_le(l, r), Nat.is_le(r, n)), {==}, g)
