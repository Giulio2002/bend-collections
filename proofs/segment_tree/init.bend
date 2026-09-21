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
import ./depth.bend as DP
import ./state.bend as ST
import ./steps.bend as PS

# The constructors: `new(n)` is two all-zero cell arrays, and `from_list(xs)`
# fills position after position with a real `set`.

def initial(+n: Nat) -> ST.Sh:
  {ST.Sh{n, F.depth_for(n), A.trep(F.Cel, 1n+F.depth_for(n), F.CV{0}), A.trep(F.Cel, F.depth_for(n), F.CV{0})} : ST.Sh}

def cmap_rep(m: Nat) -> {AR.cmap(SC.replicate(F.Cel, m, F.CV{0})) == SC.replicate(U32, m, 0) : List<&2, U32>}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{0, z}, AR.cmap(SC.replicate(F.Cel, p, F.CV{0})), SC.replicate(U32, p, 0), cmap_rep(p))

def zero_cl(+dd: Nat) -> {AR.cl(A.trep(F.Cel, dd, F.CV{0})) == SC.replicate(U32, SC.pow2(dd), 0) : List<&2, U32>}:
  Equal.trans(List<&2, U32>,
    AR.cmap(A.slots(F.Cel, A.trep(F.Cel, dd, F.CV{0}))),
    AR.cmap(SC.replicate(F.Cel, SC.pow2(dd), F.CV{0})),
    SC.replicate(U32, SC.pow2(dd), 0),
    Equal.cong(List<&2, F.Cel>, List<&2, U32>, z => AR.cmap(z), A.slots(F.Cel, A.trep(F.Cel, dd, F.CV{0})), SC.replicate(F.Cel, SC.pow2(dd), F.CV{0}), A.trep_slots(F.Cel, dd, F.CV{0})),
    cmap_rep(SC.pow2(dd)))

def zero_mtree(+d: Nat) -> {ST.mtree(d, A.trep(F.Cel, 1n+d, F.CV{0}), A.trep(F.Cel, d, F.CV{0})) == TN.zeros(d) : TN.Node}:
  %Equal.sym(List<&2, U32>, AR.cl(A.trep(F.Cel, 1n+d, F.CV{0})), SC.replicate(U32, SC.pow2(1n+d), 0), zero_cl(1n+d)) : {W.tree_of(_, AR.cl(A.trep(F.Cel, d, F.CV{0})), d, d, 0n) == TN.zeros(d) : TN.Node}
  %Equal.sym(List<&2, U32>, AR.cl(A.trep(F.Cel, d, F.CV{0})), SC.replicate(U32, SC.pow2(d), 0), zero_cl(d)) : {W.tree_of(SC.replicate(U32, SC.pow2(1n+d), 0), _, d, d, 0n) == TN.zeros(d) : TN.Node}
  W.tree_of_rep(SC.pow2(1n+d), SC.pow2(d), d, d, 0n)

def new_real(+n: Nat) -> {F.new(n) == ST.real(initial(n)) : F.SegTree}:
  %Equal.sym(Nat, F.pow2(F.depth_for(n)), SC.pow2(F.depth_for(n)), W.fpow2(F.depth_for(n))) : {F.ST{n, F.depth_for(n), _, Array.new(F.Cel, 1n+F.depth_for(n), F.CV{0}), Array.new(F.Cel, F.depth_for(n), F.CV{0})} == ST.real(initial(n)) : F.SegTree}
  Equal.trans(F.SegTree,
    F.ST{n, F.depth_for(n), SC.pow2(F.depth_for(n)), Array.new(F.Cel, 1n+F.depth_for(n), F.CV{0}), Array.new(F.Cel, F.depth_for(n), F.CV{0})},
    F.ST{n, F.depth_for(n), SC.pow2(F.depth_for(n)), A.thaw(F.Cel, A.trep(F.Cel, 1n+F.depth_for(n), F.CV{0})), Array.new(F.Cel, F.depth_for(n), F.CV{0})},
    ST.real(initial(n)),
    Equal.cong(Array<F.Cel>, F.SegTree, z => F.ST{n, F.depth_for(n), SC.pow2(F.depth_for(n)), z, Array.new(F.Cel, F.depth_for(n), F.CV{0})},
      Array.new(F.Cel, 1n+F.depth_for(n), F.CV{0}), A.thaw(F.Cel, A.trep(F.Cel, 1n+F.depth_for(n), F.CV{0})),
      A.new(F.Cel, 1n+F.depth_for(n), F.CV{0})),
    Equal.cong(Array<F.Cel>, F.SegTree, z => F.ST{n, F.depth_for(n), SC.pow2(F.depth_for(n)), A.thaw(F.Cel, A.trep(F.Cel, 1n+F.depth_for(n), F.CV{0})), z},
      Array.new(F.Cel, F.depth_for(n), F.CV{0}), A.thaw(F.Cel, A.trep(F.Cel, F.depth_for(n), F.CV{0})),
      A.new(F.Cel, F.depth_for(n), F.CV{0})))

def new_good(+n: Nat, +h: {Nat.is_le(n, SC.pow2(F.depth_for(n))) == True{} : Bool}) -> {ST.good(initial(n)) == True{} : Bool}:
  ST.g_mk(n, F.depth_for(n), A.trep(F.Cel, 1n+F.depth_for(n), F.CV{0}), A.trep(F.Cel, F.depth_for(n), F.CV{0}),
    A.trep_perfect(F.Cel, 1n+F.depth_for(n), F.CV{0}),
    A.trep_perfect(F.Cel, F.depth_for(n), F.CV{0}),
    DP.depth_lt(n), h,
    %Equal.sym(TN.Node, ST.mtree(F.depth_for(n), A.trep(F.Cel, 1n+F.depth_for(n), F.CV{0}), A.trep(F.Cel, F.depth_for(n), F.CV{0})), TN.zeros(F.depth_for(n)), zero_mtree(F.depth_for(n))) : {MD.goods(_) == True{} : Bool}
    MD.zeros_good(F.depth_for(n)))

def new_model(+n: Nat, +h: {Nat.is_le(n, SC.pow2(F.depth_for(n))) == True{} : Bool}) -> {ST.model(initial(n)) == S.new(n) : List<&2, U32>}:
  %Equal.sym(TN.Node, ST.mtree(F.depth_for(n), A.trep(F.Cel, 1n+F.depth_for(n), F.CV{0}), A.trep(F.Cel, F.depth_for(n), F.CV{0})), TN.zeros(F.depth_for(n)), zero_mtree(F.depth_for(n))) : {SC.take(U32, MD.vals(_), n) == Q.zeros(n) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, MD.vals(TN.zeros(F.depth_for(n))), Q.zeros(V.pow2(F.depth_for(n))), MD.zeros_vals(F.depth_for(n))) : {SC.take(U32, _, n) == Q.zeros(n) : List<&2, U32>}
  %Equal.sym(Nat, V.pow2(F.depth_for(n)), SC.pow2(F.depth_for(n)), W.vsc(F.depth_for(n))) : {SC.take(U32, Q.zeros(_), n) == Q.zeros(n) : List<&2, U32>}
  LL.sc_take_rep(U32, SC.pow2(F.depth_for(n)), 0, n, h)

# ---- from_list ----

def count_len(+xs: List<&2, U32>) -> {F.count(xs) == SC.length(U32, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      N.succ_cong(F.count(t), SC.length(U32, t), count_len(t))

def lt_add_succ(+a: Nat, +x: Nat) -> {Nat.is_lt(a, Nat.add(a, 1n+x)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(a, 1n+x), 1n+Nat.add(a, x), N.add_succ(a, x)) : {Nat.is_lt(a, _) == True{} : Bool}
  N.le_lt_succ(a, Nat.add(a, x), N.le_add_right(a, x))

# Filling position |p| of p ++ 0 ++ zeros with x.
def PutOK(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +p: List<&2, U32>, +x: U32, +r: List<&2, U32>) -> Type:
  {ST.model(ST.Sh{n, d, PS.setc(d, tc, tg, SC.length(U32, p), x), tg}) == SC.append(U32, SC.snoc(U32, p, x), Q.zeros(SC.length(U32, r))) : List<&2, U32>} & {ST.good(ST.Sh{n, d, PS.setc(d, tc, tg, SC.length(U32, p), x), tg}) == True{} : Bool}

def put_ok(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +g: {ST.repf(n, d, tc, tg) == True{} : Bool}, +p: List<&2, U32>, +x: U32, +r: List<&2, U32>, +ea: {SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n) == SC.append(U32, p, Con{0, Q.zeros(SC.length(U32, r))}) : List<&2, U32>}, +hlt: {Nat.is_lt(SC.length(U32, p), n) == True{} : Bool}) -> PutOK(n, d, tc, tg, p, x, r):
  +i = SC.length(U32, p)
  +hi = L.subst(Nat, q => {Nat.is_lt(i, q) == True{} : Bool}, SC.pow2(d), V.pow2(d), Equal.sym(Nat, V.pow2(d), SC.pow2(d), W.vsc(d)), N.lt_le_trans(i, n, SC.pow2(d), hlt, ST.g_cap(n, d, tc, tg, g)))
  (%Equal.sym(TN.Node, ST.mtree(d, PS.setc(d, tc, tg, i, x), tg), TN.set_go(d, ST.mtree(d, tc, tg), i, x, 0, V.dec(d, i)), PS.setc_mtree(n, d, tc, tg, i, x, g)) : {SC.take(U32, MD.vals(_), n) == SC.append(U32, SC.snoc(U32, p, x), Q.zeros(SC.length(U32, r))) : List<&2, U32>}
   %Equal.sym(List<&2, U32>, MD.vals(TN.set_go(d, ST.mtree(d, tc, tg), i, x, 0, V.dec(d, i))), SC.update(U32, MD.vals(ST.mtree(d, tc, tg)), i, x), PS.set_vals(d, ST.mtree(d, tc, tg), i, x, hi, ST.mt_perfect(d, tc, tg))) : {SC.take(U32, _, n) == SC.append(U32, SC.snoc(U32, p, x), Q.zeros(SC.length(U32, r))) : List<&2, U32>}
   %Equal.sym(List<&2, U32>, SC.take(U32, SC.update(U32, MD.vals(ST.mtree(d, tc, tg)), i, x), n), SC.update(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), i, x), LL.sc_take_update(U32, MD.vals(ST.mtree(d, tc, tg)), i, x, n)) : {_ == SC.append(U32, SC.snoc(U32, p, x), Q.zeros(SC.length(U32, r))) : List<&2, U32>}
   %Equal.sym(List<&2, U32>, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), SC.append(U32, p, Con{0, Q.zeros(SC.length(U32, r))}), ea) : {SC.update(U32, _, i, x) == SC.append(U32, SC.snoc(U32, p, x), Q.zeros(SC.length(U32, r))) : List<&2, U32>}
   %Equal.sym(List<&2, U32>, SC.update(U32, SC.append(U32, p, Con{0, Q.zeros(SC.length(U32, r))}), i, x), SC.append(U32, p, SC.update(U32, Con{0, Q.zeros(SC.length(U32, r))}, Nat.sub(i, SC.length(U32, p)), x)), LL.update_append_right(U32, p, Con{0, Q.zeros(SC.length(U32, r))}, i, x, N.le_refl(i))) : {_ == SC.append(U32, SC.snoc(U32, p, x), Q.zeros(SC.length(U32, r))) : List<&2, U32>}
   %Equal.sym(Nat, Nat.sub(i, i), 0n, N.sub_self(i)) : {SC.append(U32, p, SC.update(U32, Con{0, Q.zeros(SC.length(U32, r))}, _, x)) == SC.append(U32, SC.snoc(U32, p, x), Q.zeros(SC.length(U32, r))) : List<&2, U32>}
   Equal.sym(List<&2, U32>, SC.append(U32, SC.snoc(U32, p, x), Q.zeros(SC.length(U32, r))), SC.append(U32, p, Con{x, Q.zeros(SC.length(U32, r))}), LL.snoc_append_cons(U32, p, x, Q.zeros(SC.length(U32, r)))),
   ST.g_mk(n, d, PS.setc(d, tc, tg, i, x), tg,
     W.stree_perfect(d, tc, tg, d, 0, 0n, i, x, V.dec(d, i), ST.g_pf(n, d, tc, tg, g)),
     ST.g_pg(n, d, tc, tg, g), ST.g_lt(n, d, tc, tg, g), ST.g_cap(n, d, tc, tg, g),
     %Equal.sym(TN.Node, ST.mtree(d, PS.setc(d, tc, tg, i, x), tg), TN.set_go(d, ST.mtree(d, tc, tg), i, x, 0, V.dec(d, i)), PS.setc_mtree(n, d, tc, tg, i, x, g)) : {MD.goods(_) == True{} : Bool}
     O.set_good(d, ST.mtree(d, tc, tg), i, x, 0, V.dec(d, i), ST.mt_perfect(d, tc, tg), ST.g_good(n, d, tc, tg, g))))

def FillOK(xs: List<&2, U32>, +p: List<&2, U32>, sh: ST.Sh) -> Type:
  Sigma<&1, &1, ST.Sh, sh2 => {F.fill(xs, SC.length(U32, p), ST.real(sh)) == ST.real(sh2) : F.SegTree} & ({ST.good(sh2) == True{} : Bool} & {ST.model(sh2) == SC.append(U32, p, xs) : List<&2, U32>})>

def fo_sh(-xs: List<&2, U32>, -p: List<&2, U32>, -sh: ST.Sh, fo: FillOK(xs, p, sh)) -> ST.Sh:
  match fo:
    case Tuple{sh2, r}:
      sh2

def fo_run(-xs: List<&2, U32>, -p: List<&2, U32>, -sh: ST.Sh, fo: FillOK(xs, p, sh)) -> {F.fill(xs, SC.length(U32, p), ST.real(sh)) == ST.real(fo_sh(xs, p, sh, fo)) : F.SegTree}:
  match fo:
    case Tuple{sh2, Tuple{e, r}}:
      e

def fo_good(-xs: List<&2, U32>, -p: List<&2, U32>, -sh: ST.Sh, fo: FillOK(xs, p, sh)) -> {ST.good(fo_sh(xs, p, sh, fo)) == True{} : Bool}:
  match fo:
    case Tuple{sh2, Tuple{e, Tuple{g, m}}}:
      g

def fo_model(-xs: List<&2, U32>, -p: List<&2, U32>, -sh: ST.Sh, fo: FillOK(xs, p, sh)) -> {ST.model(fo_sh(xs, p, sh, fo)) == SC.append(U32, p, xs) : List<&2, U32>}:
  match fo:
    case Tuple{sh2, Tuple{e, Tuple{g, m}}}:
      m

def fill_ok(xs: List<&2, U32>, +p: List<&2, U32>, sh: ST.Sh, +gs: {ST.good(sh) == True{} : Bool}, +ea: {ST.model(sh) == SC.append(U32, p, Q.zeros(SC.length(U32, xs))) : List<&2, U32>}) -> FillOK(xs, p, sh):
  match xs sh:
    case Nil{} _:
      (sh, ({==}, (gs, ea)))
    case Con{+x, +r} ST.Sh{+n, +d, +tc, +tg}:
      +i = SC.length(U32, p)
      +el = Equal.trans(Nat, n, SC.length(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n)), Nat.add(i, 1n+SC.length(U32, Q.zeros(SC.length(U32, r)))),
        Equal.sym(Nat, SC.length(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n)), n, ST.len_model(n, d, tc, tg, gs)),
        Equal.trans(Nat, SC.length(U32, SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n)), SC.length(U32, SC.append(U32, p, Con{0, Q.zeros(SC.length(U32, r))})), Nat.add(i, 1n+SC.length(U32, Q.zeros(SC.length(U32, r)))),
          Equal.cong(List<&2, U32>, Nat, z => SC.length(U32, z), SC.take(U32, MD.vals(ST.mtree(d, tc, tg)), n), SC.append(U32, p, Con{0, Q.zeros(SC.length(U32, r))}), ea),
          LL.length_append(U32, p, Con{0, Q.zeros(SC.length(U32, r))})))
      +hlt = L.subst(Nat, q => {Nat.is_lt(i, q) == True{} : Bool}, Nat.add(i, 1n+SC.length(U32, Q.zeros(SC.length(U32, r)))), n, Equal.sym(Nat, n, Nat.add(i, 1n+SC.length(U32, Q.zeros(SC.length(U32, r)))), el), lt_add_succ(i, SC.length(U32, Q.zeros(SC.length(U32, r)))))
      -A1 = {ST.model(ST.Sh{n, d, PS.setc(d, tc, tg, SC.length(U32, p), x), tg}) == SC.append(U32, SC.snoc(U32, p, x), Q.zeros(SC.length(U32, r))) : List<&2, U32>}
      -I1 = {ST.good(ST.Sh{n, d, PS.setc(d, tc, tg, SC.length(U32, p), x), tg}) == True{} : Bool}
      (fo_sh(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.setc(d, tc, tg, i, x), tg}, fill_ok(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.setc(d, tc, tg, i, x), tg}, Pair.snd(A1, I1, put_ok(n, d, tc, tg, gs, p, x, r, ea, hlt)), Pair.fst(A1, I1, put_ok(n, d, tc, tg, gs, p, x, r, ea, hlt)))),
       (%Equal.sym(Bool, Nat.is_lt(i, n), True{}, hlt) : {F.fill(r, 1n+i, Pair.fst(F.SegTree, Result<&2, &2, E.Error, Unit>, F.set_if(_, n, d, SC.pow2(d), A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), i, x))) == ST.real(fo_sh(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.setc(d, tc, tg, i, x), tg}, fill_ok(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.setc(d, tc, tg, i, x), tg}, Pair.snd(A1, I1, put_ok(n, d, tc, tg, gs, p, x, r, ea, hlt)), Pair.fst(A1, I1, put_ok(n, d, tc, tg, gs, p, x, r, ea, hlt))))) : F.SegTree}
        %Equal.sym(Bool, Nat.is_lt(i, FL.hof(d)), V.dec(d, i), W.vdec(d, i, FL.hof(d), {==})) : {F.fill(r, 1n+i, Pair.fst(F.SegTree, Result<&2, &2, E.Error, Unit>, F.set_done(F.set_go(d, F.pre_t(d, A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), SC.pow2(d), FL.hof(d), 0n), SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0, 0n, i, x), n, d, SC.pow2(d)))) == ST.real(fo_sh(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.setc(d, tc, tg, i, x), tg}, fill_ok(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.setc(d, tc, tg, i, x), tg}, Pair.snd(A1, I1, put_ok(n, d, tc, tg, gs, p, x, r, ea, hlt)), Pair.fst(A1, I1, put_ok(n, d, tc, tg, gs, p, x, r, ea, hlt))))) : F.SegTree}
        %Equal.sym(Array<F.Cel> & Array<F.Cel>, F.set_go(d, F.pre_t(d, A.thaw(F.Cel, tc), A.thaw(F.Cel, tg), SC.pow2(d), FL.hof(d), 0n), SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0, 0n, i, x), (A.thaw(F.Cel, PS.setc(d, tc, tg, i, x)), A.thaw(F.Cel, tg)), W.set_thaw(d, tc, tg, d, SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0, 0n, i, x, V.dec(d, i), W.vdec(d, i, FL.hof(d), {==}), ST.g_lt(n, d, tc, tg, gs), ST.g_ltg(n, d, tc, tg, gs), ST.whole(d), ST.g_pf(n, d, tc, tg, gs), ST.g_pg(n, d, tc, tg, gs), {==}, {==}, {==})) : {F.fill(r, 1n+i, Pair.fst(F.SegTree, Result<&2, &2, E.Error, Unit>, F.set_done(_, n, d, SC.pow2(d)))) == ST.real(fo_sh(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.setc(d, tc, tg, i, x), tg}, fill_ok(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.setc(d, tc, tg, i, x), tg}, Pair.snd(A1, I1, put_ok(n, d, tc, tg, gs, p, x, r, ea, hlt)), Pair.fst(A1, I1, put_ok(n, d, tc, tg, gs, p, x, r, ea, hlt))))) : F.SegTree}
        %LL.length_snoc(U32, p, x) : {F.fill(r, _, ST.real(ST.Sh{n, d, PS.setc(d, tc, tg, i, x), tg})) == ST.real(fo_sh(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.setc(d, tc, tg, i, x), tg}, fill_ok(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.setc(d, tc, tg, i, x), tg}, Pair.snd(A1, I1, put_ok(n, d, tc, tg, gs, p, x, r, ea, hlt)), Pair.fst(A1, I1, put_ok(n, d, tc, tg, gs, p, x, r, ea, hlt))))) : F.SegTree}
        fo_run(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.setc(d, tc, tg, i, x), tg}, fill_ok(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.setc(d, tc, tg, i, x), tg}, Pair.snd(A1, I1, put_ok(n, d, tc, tg, gs, p, x, r, ea, hlt)), Pair.fst(A1, I1, put_ok(n, d, tc, tg, gs, p, x, r, ea, hlt)))),
        (fo_good(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.setc(d, tc, tg, i, x), tg}, fill_ok(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.setc(d, tc, tg, i, x), tg}, Pair.snd(A1, I1, put_ok(n, d, tc, tg, gs, p, x, r, ea, hlt)), Pair.fst(A1, I1, put_ok(n, d, tc, tg, gs, p, x, r, ea, hlt)))),
         %LL.snoc_append_cons(U32, p, x, r) : {ST.model(fo_sh(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.setc(d, tc, tg, i, x), tg}, fill_ok(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.setc(d, tc, tg, i, x), tg}, Pair.snd(A1, I1, put_ok(n, d, tc, tg, gs, p, x, r, ea, hlt)), Pair.fst(A1, I1, put_ok(n, d, tc, tg, gs, p, x, r, ea, hlt))))) == _ : List<&2, U32>}
         fo_model(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.setc(d, tc, tg, i, x), tg}, fill_ok(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.setc(d, tc, tg, i, x), tg}, Pair.snd(A1, I1, put_ok(n, d, tc, tg, gs, p, x, r, ea, hlt)), Pair.fst(A1, I1, put_ok(n, d, tc, tg, gs, p, x, r, ea, hlt)))))))

# from_list(xs) = fill(xs, 0, new(|xs|))
def from_ok(+xs: List<&2, U32>, +h: {Nat.is_le(F.count(xs), SC.pow2(F.depth_for(F.count(xs)))) == True{} : Bool}) -> FillOK(xs, Nil{}, initial(F.count(xs))):
  fill_ok(xs, Nil{}, initial(F.count(xs)), new_good(F.count(xs), h),
    %count_len(xs) : {ST.model(initial(F.count(xs))) == Q.zeros(_) : List<&2, U32>}
    new_model(F.count(xs), h))
