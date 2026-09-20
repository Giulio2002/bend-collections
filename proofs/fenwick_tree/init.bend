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
import ./depth.bend as DP
import ./state.bend as ST
import ./steps.bend as PS

# The constructors: `new(n)` is an all-zero cell array, and `from_list(xs)`
# fills position after position with a real `add`.

def initial(+n: Nat) -> ST.Sh:
  {ST.Sh{n, F.depth_for(n), A.trep(F.Cel, 1n+F.depth_for(n), F.CV{0})} : ST.Sh}

def cmap_rep(m: Nat) -> {AR.cmap(SC.replicate(F.Cel, m, F.CV{0})) == SC.replicate(U32, m, 0) : List<&2, U32>}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{0, z}, AR.cmap(SC.replicate(F.Cel, p, F.CV{0})), SC.replicate(U32, p, 0), cmap_rep(p))

def zero_cl(+d: Nat) -> {AR.cl(A.trep(F.Cel, 1n+d, F.CV{0})) == SC.replicate(U32, SC.pow2(1n+d), 0) : List<&2, U32>}:
  Equal.trans(List<&2, U32>,
    AR.cmap(A.slots(F.Cel, A.trep(F.Cel, 1n+d, F.CV{0}))),
    AR.cmap(SC.replicate(F.Cel, SC.pow2(1n+d), F.CV{0})),
    SC.replicate(U32, SC.pow2(1n+d), 0),
    Equal.cong(List<&2, F.Cel>, List<&2, U32>, z => AR.cmap(z), A.slots(F.Cel, A.trep(F.Cel, 1n+d, F.CV{0})), SC.replicate(F.Cel, SC.pow2(1n+d), F.CV{0}), A.trep_slots(F.Cel, 1n+d, F.CV{0})),
    cmap_rep(SC.pow2(1n+d)))

def zero_mtree(+d: Nat) -> {ST.mtree(d, A.trep(F.Cel, 1n+d, F.CV{0})) == M.zeros(d) : M.Node}:
  %Equal.sym(List<&2, U32>, AR.cl(A.trep(F.Cel, 1n+d, F.CV{0})), SC.replicate(U32, SC.pow2(1n+d), 0), zero_cl(d)) : {W.tree_of(_, d, d, 0n) == M.zeros(d) : M.Node}
  W.tree_of_rep(SC.pow2(1n+d), d, d, 0n)

def new_real(+n: Nat) -> {F.new(n) == ST.real(initial(n)) : F.Fenwick}:
  %Equal.sym(Nat, F.pow2(F.depth_for(n)), SC.pow2(F.depth_for(n)), W.fpow2(F.depth_for(n))) : {F.FT{n, F.depth_for(n), _, Array.new(F.Cel, 1n+F.depth_for(n), F.CV{0})} == ST.real(initial(n)) : F.Fenwick}
  Equal.cong(Array<F.Cel>, F.Fenwick, z => F.FT{n, F.depth_for(n), SC.pow2(F.depth_for(n)), z},
    Array.new(F.Cel, 1n+F.depth_for(n), F.CV{0}), A.thaw(F.Cel, A.trep(F.Cel, 1n+F.depth_for(n), F.CV{0})),
    A.new(F.Cel, 1n+F.depth_for(n), F.CV{0}))

def new_good(+n: Nat, +h: {Nat.is_le(n, SC.pow2(F.depth_for(n))) == True{} : Bool}) -> {ST.good(initial(n)) == True{} : Bool}:
  ST.g_mk(n, F.depth_for(n), A.trep(F.Cel, 1n+F.depth_for(n), F.CV{0}),
    A.trep_perfect(F.Cel, 1n+F.depth_for(n), F.CV{0}),
    DP.depth_lt(n), h,
    %Equal.sym(M.Node, ST.mtree(F.depth_for(n), A.trep(F.Cel, 1n+F.depth_for(n), F.CV{0})), M.zeros(F.depth_for(n)), zero_mtree(F.depth_for(n))) : {T.goodf(_) == True{} : Bool}
    T.zeros_good(F.depth_for(n)))

def new_model(+n: Nat, +h: {Nat.is_le(n, SC.pow2(F.depth_for(n))) == True{} : Bool}) -> {ST.model(initial(n)) == S.new(n) : List<&2, U32>}:
  %Equal.sym(M.Node, ST.mtree(F.depth_for(n), A.trep(F.Cel, 1n+F.depth_for(n), F.CV{0})), M.zeros(F.depth_for(n)), zero_mtree(F.depth_for(n))) : {SC.take(U32, T.leaves(_), n) == Q.zeros(n) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, T.leaves(M.zeros(F.depth_for(n))), Q.zeros(SC.pow2(F.depth_for(n))), T.zeros_leaves(F.depth_for(n))) : {SC.take(U32, _, n) == Q.zeros(n) : List<&2, U32>}
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
def PutOK(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>, +p: List<&2, U32>, +x: U32, +r: List<&2, U32>) -> Type:
  {ST.model(ST.Sh{n, d, PS.added(n, d, t, SC.length(U32, p), x)}) == SC.append(U32, SC.snoc(U32, p, x), Q.zeros(SC.length(U32, r))) : List<&2, U32>} & {ST.good(ST.Sh{n, d, PS.added(n, d, t, SC.length(U32, p), x)}) == True{} : Bool}

def put_ok(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>, +g: {ST.repf(n, d, t) == True{} : Bool}, +p: List<&2, U32>, +x: U32, +r: List<&2, U32>, +ea: {SC.take(U32, T.leaves(ST.mtree(d, t)), n) == SC.append(U32, p, Con{0, Q.zeros(SC.length(U32, r))}) : List<&2, U32>}, +hlt: {Nat.is_lt(SC.length(U32, p), n) == True{} : Bool}) -> PutOK(n, d, t, p, x, r):
  +i = SC.length(U32, p)
  +hi = N.lt_le_trans(i, n, SC.pow2(d), hlt, ST.g_cap(n, d, t, g))
  (%Equal.sym(M.Node, ST.mtree(d, PS.added(n, d, t, i, x)), M.add_go(d, ST.mtree(d, t), i, x, M.dec(d, i)), PS.added_mtree(n, d, t, i, x, g)) : {SC.take(U32, T.leaves(_), n) == SC.append(U32, SC.snoc(U32, p, x), Q.zeros(SC.length(U32, r))) : List<&2, U32>}
   %Equal.sym(List<&2, U32>, T.leaves(M.add_go(d, ST.mtree(d, t), i, x, M.dec(d, i))), QS.addat(T.leaves(ST.mtree(d, t)), i, x), T.add_leaves(d, ST.mtree(d, t), i, x, hi, M.dec(d, i), {==}, ST.mt_perfect(d, t))) : {SC.take(U32, _, n) == SC.append(U32, SC.snoc(U32, p, x), Q.zeros(SC.length(U32, r))) : List<&2, U32>}
   %Equal.sym(List<&2, U32>, SC.take(U32, QS.addat(T.leaves(ST.mtree(d, t)), i, x), n), QS.addat(SC.take(U32, T.leaves(ST.mtree(d, t)), n), i, x), QS.take_addat(T.leaves(ST.mtree(d, t)), i, x, n)) : {_ == SC.append(U32, SC.snoc(U32, p, x), Q.zeros(SC.length(U32, r))) : List<&2, U32>}
   %Equal.sym(List<&2, U32>, SC.take(U32, T.leaves(ST.mtree(d, t)), n), SC.append(U32, p, Con{0, Q.zeros(SC.length(U32, r))}), ea) : {QS.addat(_, i, x) == SC.append(U32, SC.snoc(U32, p, x), Q.zeros(SC.length(U32, r))) : List<&2, U32>}
   %Equal.sym(List<&2, U32>, QS.addat(SC.append(U32, p, Con{0, Q.zeros(SC.length(U32, r))}), i, x), SC.append(U32, p, QS.addat(Con{0, Q.zeros(SC.length(U32, r))}, Nat.sub(i, SC.length(U32, p)), x)), QS.addat_right(p, Con{0, Q.zeros(SC.length(U32, r))}, i, x, N.le_refl(i))) : {_ == SC.append(U32, SC.snoc(U32, p, x), Q.zeros(SC.length(U32, r))) : List<&2, U32>}
   %Equal.sym(Nat, Nat.sub(i, i), 0n, N.sub_self(i)) : {SC.append(U32, p, QS.addat(Con{0, Q.zeros(SC.length(U32, r))}, _, x)) == SC.append(U32, SC.snoc(U32, p, x), Q.zeros(SC.length(U32, r))) : List<&2, U32>}
   %Equal.sym(U32, U32.add(0, x), x, UA.zero_add(x)) : {SC.append(U32, p, Con{_, Q.zeros(SC.length(U32, r))}) == SC.append(U32, SC.snoc(U32, p, x), Q.zeros(SC.length(U32, r))) : List<&2, U32>}
   Equal.sym(List<&2, U32>, SC.append(U32, SC.snoc(U32, p, x), Q.zeros(SC.length(U32, r))), SC.append(U32, p, Con{x, Q.zeros(SC.length(U32, r))}), LL.snoc_append_cons(U32, p, x, Q.zeros(SC.length(U32, r)))),
   ST.g_mk(n, d, PS.added(n, d, t, i, x),
     W.atree_perfect(d, t, d, 0n, i, x, M.dec(d, i), ST.g_pf(n, d, t, g)),
     ST.g_lt(n, d, t, g), ST.g_cap(n, d, t, g),
     %Equal.sym(M.Node, ST.mtree(d, PS.added(n, d, t, i, x)), M.add_go(d, ST.mtree(d, t), i, x, M.dec(d, i)), PS.added_mtree(n, d, t, i, x, g)) : {T.goodf(_) == True{} : Bool}
     T.add_good(d, ST.mtree(d, t), i, x, hi, M.dec(d, i), {==}, ST.mt_perfect(d, t), ST.g_good(n, d, t, g))))

def FillOK(xs: List<&2, U32>, +p: List<&2, U32>, sh: ST.Sh) -> Type:
  Sigma<&1, &1, ST.Sh, sh2 => {F.fill(xs, SC.length(U32, p), ST.real(sh)) == ST.real(sh2) : F.Fenwick} & ({ST.good(sh2) == True{} : Bool} & {ST.model(sh2) == SC.append(U32, p, xs) : List<&2, U32>})>

def fo_sh(-xs: List<&2, U32>, -p: List<&2, U32>, -sh: ST.Sh, fo: FillOK(xs, p, sh)) -> ST.Sh:
  match fo:
    case Tuple{sh2, r}:
      sh2

def fo_run(-xs: List<&2, U32>, -p: List<&2, U32>, -sh: ST.Sh, fo: FillOK(xs, p, sh)) -> {F.fill(xs, SC.length(U32, p), ST.real(sh)) == ST.real(fo_sh(xs, p, sh, fo)) : F.Fenwick}:
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
    case Con{+x, +r} ST.Sh{+n, +d, +t}:
      +i = SC.length(U32, p)
      +el = Equal.trans(Nat, n, SC.length(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n)), Nat.add(i, 1n+SC.length(U32, Q.zeros(SC.length(U32, r)))),
        Equal.sym(Nat, SC.length(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n)), n, ST.len_model(n, d, t, gs)),
        Equal.trans(Nat, SC.length(U32, SC.take(U32, T.leaves(ST.mtree(d, t)), n)), SC.length(U32, SC.append(U32, p, Con{0, Q.zeros(SC.length(U32, r))})), Nat.add(i, 1n+SC.length(U32, Q.zeros(SC.length(U32, r)))),
          Equal.cong(List<&2, U32>, Nat, z => SC.length(U32, z), SC.take(U32, T.leaves(ST.mtree(d, t)), n), SC.append(U32, p, Con{0, Q.zeros(SC.length(U32, r))}), ea),
          LL.length_append(U32, p, Con{0, Q.zeros(SC.length(U32, r))})))
      +hlt = L.subst(Nat, q => {Nat.is_lt(i, q) == True{} : Bool}, Nat.add(i, 1n+SC.length(U32, Q.zeros(SC.length(U32, r)))), n, Equal.sym(Nat, n, Nat.add(i, 1n+SC.length(U32, Q.zeros(SC.length(U32, r)))), el), lt_add_succ(i, SC.length(U32, Q.zeros(SC.length(U32, r)))))
      -A1 = {ST.model(ST.Sh{n, d, PS.added(n, d, t, SC.length(U32, p), x)}) == SC.append(U32, SC.snoc(U32, p, x), Q.zeros(SC.length(U32, r))) : List<&2, U32>}
      -I1 = {ST.good(ST.Sh{n, d, PS.added(n, d, t, SC.length(U32, p), x)}) == True{} : Bool}
      (fo_sh(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.added(n, d, t, i, x)}, fill_ok(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.added(n, d, t, i, x)}, Pair.snd(A1, I1, put_ok(n, d, t, gs, p, x, r, ea, hlt)), Pair.fst(A1, I1, put_ok(n, d, t, gs, p, x, r, ea, hlt)))),
       (%Equal.sym(Bool, Nat.is_lt(i, n), True{}, hlt) : {F.fill(r, 1n+i, Pair.fst(F.Fenwick, Result<&2, &2, E.Error, Unit>, F.add_if(_, n, d, SC.pow2(d), A.thaw(F.Cel, t), i, x))) == ST.real(fo_sh(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.added(n, d, t, i, x)}, fill_ok(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.added(n, d, t, i, x)}, Pair.snd(A1, I1, put_ok(n, d, t, gs, p, x, r, ea, hlt)), Pair.fst(A1, I1, put_ok(n, d, t, gs, p, x, r, ea, hlt))))) : F.Fenwick}
        %Equal.sym(Bool, Nat.is_lt(i, FL.hof(d)), M.dec(d, i), W.dec_h(d, i, FL.hof(d), {==})) : {F.fill(r, 1n+i, F.FT{n, d, SC.pow2(d), F.add_go(d, A.thaw(F.Cel, t), SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0n, i, x, _)}) == ST.real(fo_sh(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.added(n, d, t, i, x)}, fill_ok(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.added(n, d, t, i, x)}, Pair.snd(A1, I1, put_ok(n, d, t, gs, p, x, r, ea, hlt)), Pair.fst(A1, I1, put_ok(n, d, t, gs, p, x, r, ea, hlt))))) : F.Fenwick}
        %Equal.sym(Array<F.Cel>, F.add_go(d, A.thaw(F.Cel, t), SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0n, i, x, M.dec(d, i)), A.thaw(F.Cel, PS.added(n, d, t, i, x)), W.add_thaw(d, t, d, SC.pow2(d), FL.hof(d), Nat.div(FL.hof(d), 2n), 0n, i, x, M.dec(d, i), ST.g_lt(n, d, t, gs), ST.whole(d), ST.g_pf(n, d, t, gs), {==}, {==}, {==})) : {F.fill(r, 1n+i, F.FT{n, d, SC.pow2(d), _}) == ST.real(fo_sh(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.added(n, d, t, i, x)}, fill_ok(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.added(n, d, t, i, x)}, Pair.snd(A1, I1, put_ok(n, d, t, gs, p, x, r, ea, hlt)), Pair.fst(A1, I1, put_ok(n, d, t, gs, p, x, r, ea, hlt))))) : F.Fenwick}
        %LL.length_snoc(U32, p, x) : {F.fill(r, _, ST.real(ST.Sh{n, d, PS.added(n, d, t, i, x)})) == ST.real(fo_sh(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.added(n, d, t, i, x)}, fill_ok(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.added(n, d, t, i, x)}, Pair.snd(A1, I1, put_ok(n, d, t, gs, p, x, r, ea, hlt)), Pair.fst(A1, I1, put_ok(n, d, t, gs, p, x, r, ea, hlt))))) : F.Fenwick}
        fo_run(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.added(n, d, t, i, x)}, fill_ok(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.added(n, d, t, i, x)}, Pair.snd(A1, I1, put_ok(n, d, t, gs, p, x, r, ea, hlt)), Pair.fst(A1, I1, put_ok(n, d, t, gs, p, x, r, ea, hlt)))),
        (fo_good(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.added(n, d, t, i, x)}, fill_ok(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.added(n, d, t, i, x)}, Pair.snd(A1, I1, put_ok(n, d, t, gs, p, x, r, ea, hlt)), Pair.fst(A1, I1, put_ok(n, d, t, gs, p, x, r, ea, hlt)))),
         %LL.snoc_append_cons(U32, p, x, r) : {ST.model(fo_sh(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.added(n, d, t, i, x)}, fill_ok(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.added(n, d, t, i, x)}, Pair.snd(A1, I1, put_ok(n, d, t, gs, p, x, r, ea, hlt)), Pair.fst(A1, I1, put_ok(n, d, t, gs, p, x, r, ea, hlt))))) == _ : List<&2, U32>}
         fo_model(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.added(n, d, t, i, x)}, fill_ok(r, SC.snoc(U32, p, x), ST.Sh{n, d, PS.added(n, d, t, i, x)}, Pair.snd(A1, I1, put_ok(n, d, t, gs, p, x, r, ea, hlt)), Pair.fst(A1, I1, put_ok(n, d, t, gs, p, x, r, ea, hlt)))))))

# from_list(xs) = fill(xs, 0, new(|xs|))
def from_ok(+xs: List<&2, U32>, +h: {Nat.is_le(F.count(xs), SC.pow2(F.depth_for(F.count(xs)))) == True{} : Bool}) -> FillOK(xs, Nil{}, initial(F.count(xs))):
  fill_ok(xs, Nil{}, initial(F.count(xs)), new_good(F.count(xs), h),
    %count_len(xs) : {ST.model(initial(F.count(xs))) == Q.zeros(_) : List<&2, U32>}
    new_model(F.count(xs), h))
