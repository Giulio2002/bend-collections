import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as A
import ../../spec/common.bend as SC
import ../../spec/union_find.bend as S
import ../../src/union_find.bend as U
import ../../types/union_find.bend as E
import ./cells.bend as CL
import ./model.bend as M
import ./union.bend as UN
import ./arr.bend as AR
import ./bridge.bend as BR
import ./depth.bend as DP
import ./state.bend as ST

# Every public operation (errors included) refines the spec step and keeps
# the representation invariant.
#
# The three arenas are linear, so a step is stated as: the real operation on
# the arenas of a good shadow produces the arenas of another good shadow,
# whose model and observation are the spec step of the first shadow's model.

def StepOK(sh: ST.Sh, op: E.Op) -> Type:
  Sigma<&1, &1, ST.Sh, sh2 => Sigma<&1, &1, E.Obs, o => {U.step(ST.real(sh), op) == (ST.real(sh2), o) : U.UnionFind & E.Obs} & ({ST.good(sh2) == True{} : Bool} & {(ST.model(sh2), o) == S.step(ST.model(sh), op) : List<&2, Nat> & E.Obs})>>

# ---- shared ----

def labs_in(+n: Nat, +cl: List<&2, CL.Cell>, +x: Nat, +h: {Nat.is_lt(x, n) == True{} : Bool}) -> {Some{M.rt(cl, x)} == SC.nth(Nat, M.labs(cl, n), x) : Maybe<&2, Nat>}:
  Equal.sym(Maybe<&2, Nat>, SC.nth(Nat, M.labs(cl, n), x), Some{M.rt(cl, x)}, M.nth_labs(cl, n, x, h))

def labs_out(+n: Nat, +cl: List<&2, CL.Cell>, +x: Nat, +h: {Nat.is_lt(x, n) == False{} : Bool}) -> {None{} == SC.nth(Nat, M.labs(cl, n), x) : Maybe<&2, Nat>}:
  Equal.sym(Maybe<&2, Nat>, SC.nth(Nat, M.labs(cl, n), x), None{}, M.nth_labs_out(cl, n, x, h))

def root_read(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +x: Nat, +g: {ST.repf(n, d, tr, tz, tm, c) == True{} : Bool}, +hx: {Nat.is_lt(x, n) == True{} : Bool}) -> {U.read_nat(A.thaw(U.Nt, tr), d, x) == (A.thaw(U.Nt, tr), M.rt(ST.clist(d, tr, tz, tm), x)) : Array<U.Nt> & Nat}:
  %Equal.sym(Nat, M.rt(ST.clist(d, tr, tz, tm), x), AR.nthn(AR.rsl(tr), x), ST.rt_at(d, tr, tz, tm, x, ST.g_pr(n, d, tr, tz, tm, c, g), ST.g_pz(n, d, tr, tz, tm, c, g), ST.g_pm(n, d, tr, tz, tm, c, g), ST.in_cap(n, d, x, hx, ST.g_cap(n, d, tr, tz, tm, c, g)))) : {U.read_nat(A.thaw(U.Nt, tr), d, x) == (A.thaw(U.Nt, tr), _) : Array<U.Nt> & Nat}
  AR.read_nat_ok(d, tr, x, ST.g_lt32(n, d, tr, tz, tm, c, g), ST.in_cap(n, d, x, hx, ST.g_cap(n, d, tr, tz, tm, c, g)), ST.g_pr(n, d, tr, tz, tm, c, g))

# ---- find ----

def find_case(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +x: Nat, b: Bool, +eb: {Nat.is_lt(x, n) == b : Bool}, +g: {ST.repf(n, d, tr, tz, tm, c) == True{} : Bool}) -> StepOK(ST.Sh{n, d, tr, tz, tm, c}, E.Find{x}):
  match b:
    case True{}:
      (ST.Sh{n, d, tr, tz, tm, c}, (E.OItem{Done{M.rt(ST.clist(d, tr, tz, tm), x)}}, (
        %Equal.sym(Bool, Nat.is_lt(x, n), True{}, eb) : {U.obs_item(U.find_if(_, n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, x)) == (ST.real(ST.Sh{n, d, tr, tz, tm, c}), E.OItem{Done{M.rt(ST.clist(d, tr, tz, tm), x)}}) : U.UnionFind & E.Obs}
        %Equal.sym(Array<U.Nt> & Nat, U.read_nat(A.thaw(U.Nt, tr), d, x), (A.thaw(U.Nt, tr), M.rt(ST.clist(d, tr, tz, tm), x)), root_read(n, d, tr, tz, tm, c, x, g, eb)) : {U.obs_item(U.find_read(_, n, d, A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c)) == (ST.real(ST.Sh{n, d, tr, tz, tm, c}), E.OItem{Done{M.rt(ST.clist(d, tr, tz, tm), x)}}) : U.UnionFind & E.Obs}
        {==},
        (g,
         %labs_in(n, ST.clist(d, tr, tz, tm), x, eb) : {(M.labs(ST.clist(d, tr, tz, tm), n), E.OItem{Done{M.rt(ST.clist(d, tr, tz, tm), x)}}) == (M.labs(ST.clist(d, tr, tz, tm), n), E.OItem{S.label(_)}) : List<&2, Nat> & E.Obs}
         {==}))))
    case False{}:
      (ST.Sh{n, d, tr, tz, tm, c}, (E.OItem{Fail{E.OutOfRange{}}}, (
        %Equal.sym(Bool, Nat.is_lt(x, n), False{}, eb) : {U.obs_item(U.find_if(_, n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, x)) == (ST.real(ST.Sh{n, d, tr, tz, tm, c}), E.OItem{Fail{E.OutOfRange{}}}) : U.UnionFind & E.Obs}
        {==},
        (g,
         %labs_out(n, ST.clist(d, tr, tz, tm), x, eb) : {(M.labs(ST.clist(d, tr, tz, tm), n), E.OItem{Fail{E.OutOfRange{}}}) == (M.labs(ST.clist(d, tr, tz, tm), n), E.OItem{S.label(_)}) : List<&2, Nat> & E.Obs}
         {==}))))

# ---- connected ----

def conn_case(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +a: Nat, +b: Nat, ba: Bool, +eba: {Nat.is_lt(a, n) == ba : Bool}, bb: Bool, +ebb: {Nat.is_lt(b, n) == bb : Bool}, +g: {ST.repf(n, d, tr, tz, tm, c) == True{} : Bool}) -> StepOK(ST.Sh{n, d, tr, tz, tm, c}, E.Connected{a, b}):
  match ba bb:
    case True{} True{}:
      (ST.Sh{n, d, tr, tz, tm, c}, (E.OBool{Done{Nat.is_eq(M.rt(ST.clist(d, tr, tz, tm), a), M.rt(ST.clist(d, tr, tz, tm), b))}}, (
        %Equal.sym(Bool, Nat.is_lt(a, n), True{}, eba) : {U.obs_bool(U.connected_if(Bool.and(_, Nat.is_lt(b, n)), n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, a, b)) == (ST.real(ST.Sh{n, d, tr, tz, tm, c}), E.OBool{Done{Nat.is_eq(M.rt(ST.clist(d, tr, tz, tm), a), M.rt(ST.clist(d, tr, tz, tm), b))}}) : U.UnionFind & E.Obs}
        %Equal.sym(Bool, Nat.is_lt(b, n), True{}, ebb) : {U.obs_bool(U.connected_if(Bool.and(True{}, _), n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, a, b)) == (ST.real(ST.Sh{n, d, tr, tz, tm, c}), E.OBool{Done{Nat.is_eq(M.rt(ST.clist(d, tr, tz, tm), a), M.rt(ST.clist(d, tr, tz, tm), b))}}) : U.UnionFind & E.Obs}
        %Equal.sym(Array<U.Nt> & Nat, U.read_nat(A.thaw(U.Nt, tr), d, a), (A.thaw(U.Nt, tr), M.rt(ST.clist(d, tr, tz, tm), a)), root_read(n, d, tr, tz, tm, c, a, g, eba)) : {U.obs_bool(U.conn_a(_, n, d, A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, b)) == (ST.real(ST.Sh{n, d, tr, tz, tm, c}), E.OBool{Done{Nat.is_eq(M.rt(ST.clist(d, tr, tz, tm), a), M.rt(ST.clist(d, tr, tz, tm), b))}}) : U.UnionFind & E.Obs}
        %Equal.sym(Array<U.Nt> & Nat, U.read_nat(A.thaw(U.Nt, tr), d, b), (A.thaw(U.Nt, tr), M.rt(ST.clist(d, tr, tz, tm), b)), root_read(n, d, tr, tz, tm, c, b, g, ebb)) : {U.obs_bool(U.conn_b(_, n, d, A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, M.rt(ST.clist(d, tr, tz, tm), a))) == (ST.real(ST.Sh{n, d, tr, tz, tm, c}), E.OBool{Done{Nat.is_eq(M.rt(ST.clist(d, tr, tz, tm), a), M.rt(ST.clist(d, tr, tz, tm), b))}}) : U.UnionFind & E.Obs}
        {==},
        (g,
         %labs_in(n, ST.clist(d, tr, tz, tm), a, eba) : {(M.labs(ST.clist(d, tr, tz, tm), n), E.OBool{Done{Nat.is_eq(M.rt(ST.clist(d, tr, tz, tm), a), M.rt(ST.clist(d, tr, tz, tm), b))}}) == (M.labs(ST.clist(d, tr, tz, tm), n), E.OBool{S.same_class(_, SC.nth(Nat, M.labs(ST.clist(d, tr, tz, tm), n), b))}) : List<&2, Nat> & E.Obs}
         %labs_in(n, ST.clist(d, tr, tz, tm), b, ebb) : {(M.labs(ST.clist(d, tr, tz, tm), n), E.OBool{Done{Nat.is_eq(M.rt(ST.clist(d, tr, tz, tm), a), M.rt(ST.clist(d, tr, tz, tm), b))}}) == (M.labs(ST.clist(d, tr, tz, tm), n), E.OBool{S.same_class(Some{M.rt(ST.clist(d, tr, tz, tm), a)}, _)}) : List<&2, Nat> & E.Obs}
         {==}))))
    case True{} False{}:
      (ST.Sh{n, d, tr, tz, tm, c}, (E.OBool{Fail{E.OutOfRange{}}}, (
        %Equal.sym(Bool, Nat.is_lt(a, n), True{}, eba) : {U.obs_bool(U.connected_if(Bool.and(_, Nat.is_lt(b, n)), n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, a, b)) == (ST.real(ST.Sh{n, d, tr, tz, tm, c}), E.OBool{Fail{E.OutOfRange{}}}) : U.UnionFind & E.Obs}
        %Equal.sym(Bool, Nat.is_lt(b, n), False{}, ebb) : {U.obs_bool(U.connected_if(Bool.and(True{}, _), n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, a, b)) == (ST.real(ST.Sh{n, d, tr, tz, tm, c}), E.OBool{Fail{E.OutOfRange{}}}) : U.UnionFind & E.Obs}
        {==},
        (g,
         %labs_in(n, ST.clist(d, tr, tz, tm), a, eba) : {(M.labs(ST.clist(d, tr, tz, tm), n), E.OBool{Fail{E.OutOfRange{}}}) == (M.labs(ST.clist(d, tr, tz, tm), n), E.OBool{S.same_class(_, SC.nth(Nat, M.labs(ST.clist(d, tr, tz, tm), n), b))}) : List<&2, Nat> & E.Obs}
         %labs_out(n, ST.clist(d, tr, tz, tm), b, ebb) : {(M.labs(ST.clist(d, tr, tz, tm), n), E.OBool{Fail{E.OutOfRange{}}}) == (M.labs(ST.clist(d, tr, tz, tm), n), E.OBool{S.same_class(Some{M.rt(ST.clist(d, tr, tz, tm), a)}, _)}) : List<&2, Nat> & E.Obs}
         {==}))))
    case False{} _:
      (ST.Sh{n, d, tr, tz, tm, c}, (E.OBool{Fail{E.OutOfRange{}}}, (
        %Equal.sym(Bool, Nat.is_lt(a, n), False{}, eba) : {U.obs_bool(U.connected_if(Bool.and(_, Nat.is_lt(b, n)), n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, a, b)) == (ST.real(ST.Sh{n, d, tr, tz, tm, c}), E.OBool{Fail{E.OutOfRange{}}}) : U.UnionFind & E.Obs}
        {==},
        (g,
         %labs_out(n, ST.clist(d, tr, tz, tm), a, eba) : {(M.labs(ST.clist(d, tr, tz, tm), n), E.OBool{Fail{E.OutOfRange{}}}) == (M.labs(ST.clist(d, tr, tz, tm), n), E.OBool{S.same_class(_, SC.nth(Nat, M.labs(ST.clist(d, tr, tz, tm), n), b))}) : List<&2, Nat> & E.Obs}
         {==}))))

# ---- component_size ----

def size_case(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +x: Nat, b: Bool, +eb: {Nat.is_lt(x, n) == b : Bool}, +g: {ST.repf(n, d, tr, tz, tm, c) == True{} : Bool}) -> StepOK(ST.Sh{n, d, tr, tz, tm, c}, E.ComponentSize{x}):
  match b:
    case True{}:
      +cl = ST.clist(d, tr, tz, tm)
      +gx = M.good_elim(cl, n, n, x, ST.g_good(n, d, tr, tz, tm, c, g), eb)
      +hr = M.at_lt(cl, n, x, gx)
      +gr = M.good_elim(cl, n, n, M.rt(cl, x), ST.g_good(n, d, tr, tz, tm, c, g), hr)
      +isr = M.eq_true(M.rt(cl, M.rt(cl, x)), M.rt(cl, x), M.at_idem(cl, n, x, gx))
      (ST.Sh{n, d, tr, tz, tm, c}, (E.OItem{Done{M.sz(cl, M.rt(cl, x))}}, (
        %Equal.sym(Bool, Nat.is_lt(x, n), True{}, eb) : {U.obs_item(U.size_if(_, n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, x)) == (ST.real(ST.Sh{n, d, tr, tz, tm, c}), E.OItem{Done{M.sz(cl, M.rt(cl, x))}}) : U.UnionFind & E.Obs}
        %Equal.sym(Array<U.Nt> & Nat, U.read_nat(A.thaw(U.Nt, tr), d, x), (A.thaw(U.Nt, tr), M.rt(cl, x)), root_read(n, d, tr, tz, tm, c, x, g, eb)) : {U.obs_item(U.size_at(_, n, d, A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c)) == (ST.real(ST.Sh{n, d, tr, tz, tm, c}), E.OItem{Done{M.sz(cl, M.rt(cl, x))}}) : U.UnionFind & E.Obs}
        %Equal.sym(Nat, M.sz(cl, M.rt(cl, x)), AR.nthn(AR.rsl(tz), M.rt(cl, x)), ST.sz_at(d, tr, tz, tm, M.rt(cl, x), ST.g_pr(n, d, tr, tz, tm, c, g), ST.g_pz(n, d, tr, tz, tm, c, g), ST.g_pm(n, d, tr, tz, tm, c, g), ST.in_cap(n, d, M.rt(cl, x), hr, ST.g_cap(n, d, tr, tz, tm, c, g)))) : {U.obs_item(U.size_root(U.read_nat(A.thaw(U.Nt, tz), d, M.rt(cl, x)), n, d, A.thaw(U.Nt, tr), A.thaw(U.Ms, tm), c)) == (ST.real(ST.Sh{n, d, tr, tz, tm, c}), E.OItem{Done{_}}) : U.UnionFind & E.Obs}
        %Equal.sym(Array<U.Nt> & Nat, U.read_nat(A.thaw(U.Nt, tz), d, M.rt(cl, x)), (A.thaw(U.Nt, tz), AR.nthn(AR.rsl(tz), M.rt(cl, x))), AR.read_nat_ok(d, tz, M.rt(cl, x), ST.g_lt32(n, d, tr, tz, tm, c, g), ST.in_cap(n, d, M.rt(cl, x), hr, ST.g_cap(n, d, tr, tz, tm, c, g)), ST.g_pz(n, d, tr, tz, tm, c, g))) : {U.obs_item(U.size_root(_, n, d, A.thaw(U.Nt, tr), A.thaw(U.Ms, tm), c)) == (ST.real(ST.Sh{n, d, tr, tz, tm, c}), E.OItem{Done{AR.nthn(AR.rsl(tz), M.rt(cl, x))}}) : U.UnionFind & E.Obs}
        {==},
        (g,
         %labs_in(n, cl, x, eb) : {(M.labs(cl, n), E.OItem{Done{M.sz(cl, M.rt(cl, x))}}) == (M.labs(cl, n), E.OItem{S.class_size(_, M.labs(cl, n))}) : List<&2, Nat> & E.Obs}
         %Equal.sym(Nat, S.count_eq(M.labs(cl, n), M.rt(cl, x)), M.cnt_r(cl, M.rt(cl, x), n), M.count_labs(cl, M.rt(cl, x), n)) : {(M.labs(cl, n), E.OItem{Done{M.sz(cl, M.rt(cl, x))}}) == (M.labs(cl, n), E.OItem{Done{_}}) : List<&2, Nat> & E.Obs}
         %Equal.sym(Nat, M.sz(cl, M.rt(cl, x)), M.cnt_r(cl, M.rt(cl, x), n), M.root_size(cl, n, M.rt(cl, x), M.at_root(cl, n, M.rt(cl, x), gr, isr))) : {(M.labs(cl, n), E.OItem{Done{_}}) == (M.labs(cl, n), E.OItem{Done{M.cnt_r(cl, M.rt(cl, x), n)}}) : List<&2, Nat> & E.Obs}
         {==}))))
    case False{}:
      (ST.Sh{n, d, tr, tz, tm, c}, (E.OItem{Fail{E.OutOfRange{}}}, (
        %Equal.sym(Bool, Nat.is_lt(x, n), False{}, eb) : {U.obs_item(U.size_if(_, n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, x)) == (ST.real(ST.Sh{n, d, tr, tz, tm, c}), E.OItem{Fail{E.OutOfRange{}}}) : U.UnionFind & E.Obs}
        {==},
        (g,
         %labs_out(n, ST.clist(d, tr, tz, tm), x, eb) : {(M.labs(ST.clist(d, tr, tz, tm), n), E.OItem{Fail{E.OutOfRange{}}}) == (M.labs(ST.clist(d, tr, tz, tm), n), E.OItem{S.class_size(_, M.labs(ST.clist(d, tr, tz, tm), n))}) : List<&2, Nat> & E.Obs}
         {==}))))

# ---- component_count ----

def count_ok(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +g: {ST.repf(n, d, tr, tz, tm, c) == True{} : Bool}) -> StepOK(ST.Sh{n, d, tr, tz, tm, c}, E.ComponentCount{}):
  (ST.Sh{n, d, tr, tz, tm, c}, (E.ONat{c}, ({==},
    (g,
     %Equal.sym(Nat, S.fixed(M.labs(ST.clist(d, tr, tz, tm), n), 0n), M.cnt_fix(ST.clist(d, tr, tz, tm), n), M.fixed_labs(ST.clist(d, tr, tz, tm), n)) : {(M.labs(ST.clist(d, tr, tz, tm), n), E.ONat{c}) == (M.labs(ST.clist(d, tr, tz, tm), n), E.ONat{_}) : List<&2, Nat> & E.Obs}
     %Equal.sym(Nat, c, M.cnt_fix(ST.clist(d, tr, tz, tm), n), N.eq_from_is_eq(c, M.cnt_fix(ST.clist(d, tr, tz, tm), n), ST.g_cnt(n, d, tr, tz, tm, c, g))) : {(M.labs(ST.clist(d, tr, tz, tm), n), E.ONat{_}) == (M.labs(ST.clist(d, tr, tz, tm), n), E.ONat{M.cnt_fix(ST.clist(d, tr, tz, tm), n)}) : List<&2, Nat> & E.Obs}
     {==}))))

# ---- union: merging two distinct classes ----

def below_mono(+m: List<&2, Nat>, +n: Nat, +k: Nat, +h: {M.below(m, n) == True{} : Bool}, +le: {Nat.is_le(n, k) == True{} : Bool}) -> {M.below(m, k) == True{} : Bool}:
  match m:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.and_intro(Nat.is_lt(x, k), M.below(t, k), N.lt_le_trans(x, n, k, L.and_left(Nat.is_lt(x, n), M.below(t, n), h), le), below_mono(t, n, k, L.and_right(Nat.is_lt(x, n), M.below(t, n), h), le))

def bel(+n: Nat, +d: Nat, +cl: List<&2, CL.Cell>, +big: Nat, +small: Nat, +h: {UN.H(cl, n, big, small) == True{} : Bool}, +hc: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}) -> {M.below(M.ms(cl, small), SC.pow2(d)) == True{} : Bool}:
  below_mono(M.ms(cl, small), n, SC.pow2(d), M.root_below(cl, n, small, UN.root_of_small(cl, n, big, small, h)), hc)

def tot_of(+cl: List<&2, CL.Cell>, +big: Nat, +small: Nat) -> Nat:
  Nat.add(M.sz(cl, big), M.sz(cl, small))

def nms_of(+cl: List<&2, CL.Cell>, +big: Nat, +small: Nat) -> List<&2, Nat>:
  SC.append(Nat, M.ms(cl, small), M.ms(cl, big))

def msh(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +big: Nat, +small: Nat) -> ST.Sh:
  {ST.Sh{n, d,
    AR.rtree(M.ms(ST.clist(d, tr, tz, tm), small), d, tr, big),
    A.upd(U.Nt, d, tz, big, U.N{tot_of(ST.clist(d, tr, tz, tm), big, small)}),
    A.upd(U.Ms, d, tm, big, U.M{nms_of(ST.clist(d, tr, tz, tm), big, small)}),
    Nat.sub(c, 1n)} : ST.Sh}

def root_is_big(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +big: Nat, +small: Nat, +g: {ST.repf(n, d, tr, tz, tm, c) == True{} : Bool}, +h: {UN.H(ST.clist(d, tr, tz, tm), n, big, small) == True{} : Bool}) -> {SC.nth(Nat, AR.rsl(tr), big) == Some{big} : Maybe<&2, Nat>}:
  +cl = ST.clist(d, tr, tz, tm)
  +hb = ST.in_cap(n, d, big, UN.h_big(cl, n, big, small, h), ST.g_cap(n, d, tr, tz, tm, c, g))
  %N.eq_from_is_eq(M.rt(cl, big), big, UN.h_rb(cl, n, big, small, h)) : {SC.nth(Nat, AR.rsl(tr), big) == Some{_} : Maybe<&2, Nat>}
  %Equal.sym(Nat, M.rt(cl, big), AR.nthn(AR.rsl(tr), big), ST.rt_at(d, tr, tz, tm, big, ST.g_pr(n, d, tr, tz, tm, c, g), ST.g_pz(n, d, tr, tz, tm, c, g), ST.g_pm(n, d, tr, tz, tm, c, g), hb)) : {SC.nth(Nat, AR.rsl(tr), big) == Some{_} : Maybe<&2, Nat>}
  AR.nthn_nth(AR.rsl(tr), big, L.subst(Nat, k => {Nat.is_lt(big, k) == True{} : Bool}, SC.pow2(d), SC.length(Nat, AR.rsl(tr)), Equal.sym(Nat, SC.length(Nat, AR.rsl(tr)), SC.pow2(d), AR.rsl_length(d, tr, ST.g_pr(n, d, tr, tz, tm, c, g))), hb))

def msh_clist(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +big: Nat, +small: Nat, +g: {ST.repf(n, d, tr, tz, tm, c) == True{} : Bool}, +h: {UN.H(ST.clist(d, tr, tz, tm), n, big, small) == True{} : Bool}) -> {ST.cl(msh(n, d, tr, tz, tm, c, big, small)) == UN.cl2(ST.clist(d, tr, tz, tm), big, small) : List<&2, CL.Cell>}:
  +cl = ST.clist(d, tr, tz, tm)
  +pr = ST.g_pr(n, d, tr, tz, tm, c, g)
  +pz = ST.g_pz(n, d, tr, tz, tm, c, g)
  +pm = ST.g_pm(n, d, tr, tz, tm, c, g)
  +hc = ST.g_cap(n, d, tr, tz, tm, c, g)
  +hb = ST.in_cap(n, d, big, UN.h_big(cl, n, big, small, h), hc)
  +hbel = bel(n, d, cl, big, small, h, hc)
  %Equal.sym(List<&2, Nat>, AR.rsl(AR.rtree(M.ms(cl, small), d, tr, big)), CL.rlr(M.ms(cl, small), AR.rsl(tr), big), AR.rsl_rtree(M.ms(cl, small), d, tr, big, pr, hbel)) : {CL.cells(_, AR.rsl(A.upd(U.Nt, d, tz, big, U.N{tot_of(cl, big, small)})), AR.msl(A.upd(U.Ms, d, tm, big, U.M{nms_of(cl, big, small)}))) == UN.cl2(cl, big, small) : List<&2, CL.Cell>}
  %Equal.sym(List<&2, Nat>, AR.rsl(A.upd(U.Nt, d, tz, big, U.N{tot_of(cl, big, small)})), SC.update(Nat, AR.rsl(tz), big, tot_of(cl, big, small)), AR.rsl_upd(d, tz, big, tot_of(cl, big, small), hb, pz)) : {CL.cells(CL.rlr(M.ms(cl, small), AR.rsl(tr), big), _, AR.msl(A.upd(U.Ms, d, tm, big, U.M{nms_of(cl, big, small)}))) == UN.cl2(cl, big, small) : List<&2, CL.Cell>}
  %Equal.sym(List<&2, List<&2, Nat>>, AR.msl(A.upd(U.Ms, d, tm, big, U.M{nms_of(cl, big, small)})), SC.update(List<&2, Nat>, AR.msl(tm), big, nms_of(cl, big, small)), AR.msl_upd(d, tm, big, nms_of(cl, big, small), hb, pm)) : {CL.cells(CL.rlr(M.ms(cl, small), AR.rsl(tr), big), SC.update(Nat, AR.rsl(tz), big, tot_of(cl, big, small)), _) == UN.cl2(cl, big, small) : List<&2, CL.Cell>}
  Equal.trans(List<&2, CL.Cell>,
    CL.cells(CL.rlr(M.ms(cl, small), AR.rsl(tr), big), SC.update(Nat, AR.rsl(tz), big, tot_of(cl, big, small)), SC.update(List<&2, Nat>, AR.msl(tm), big, nms_of(cl, big, small))),
    SC.update(CL.Cell, CL.cells(CL.rlr(M.ms(cl, small), AR.rsl(tr), big), AR.rsl(tz), AR.msl(tm)), big, CL.Cell{big, tot_of(cl, big, small), nms_of(cl, big, small)}),
    UN.cl2(cl, big, small),
    CL.cells_set_sm(CL.rlr(M.ms(cl, small), AR.rsl(tr), big), AR.rsl(tz), AR.msl(tm), big, big, tot_of(cl, big, small), nms_of(cl, big, small),
      CL.rlr_fix(M.ms(cl, small), AR.rsl(tr), big, big, root_is_big(n, d, tr, tz, tm, c, big, small, g, h))),
    Equal.cong(List<&2, CL.Cell>, List<&2, CL.Cell>, w => SC.update(CL.Cell, w, big, CL.Cell{big, tot_of(cl, big, small), nms_of(cl, big, small)}),
      CL.cells(CL.rlr(M.ms(cl, small), AR.rsl(tr), big), AR.rsl(tz), AR.msl(tm)), UN.rl(M.ms(cl, small), cl, big),
      BR.cells_rl(M.ms(cl, small), AR.rsl(tr), AR.rsl(tz), AR.msl(tm), big)))

def msh_good(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +big: Nat, +small: Nat, +g: {ST.repf(n, d, tr, tz, tm, c) == True{} : Bool}, +h: {UN.H(ST.clist(d, tr, tz, tm), n, big, small) == True{} : Bool}) -> {ST.good(msh(n, d, tr, tz, tm, c, big, small)) == True{} : Bool}:
  +cl = ST.clist(d, tr, tz, tm)
  +pr = ST.g_pr(n, d, tr, tz, tm, c, g)
  +pz = ST.g_pz(n, d, tr, tz, tm, c, g)
  +pm = ST.g_pm(n, d, tr, tz, tm, c, g)
  +es = Equal.sym(List<&2, CL.Cell>, ST.cl(msh(n, d, tr, tz, tm, c, big, small)), UN.cl2(ST.clist(d, tr, tz, tm), big, small), msh_clist(n, d, tr, tz, tm, c, big, small, g, h))
  +ec = Equal.trans(Nat, Nat.sub(c, 1n), Nat.sub(1n+M.cnt_fix(UN.cl2(cl, big, small), n), 1n), M.cnt_fix(UN.cl2(cl, big, small), n),
    Equal.cong(Nat, Nat, q => Nat.sub(q, 1n), c, 1n+M.cnt_fix(UN.cl2(cl, big, small), n), Equal.trans(Nat, c, M.cnt_fix(cl, n), 1n+M.cnt_fix(UN.cl2(cl, big, small), n), N.eq_from_is_eq(c, M.cnt_fix(cl, n), ST.g_cnt(n, d, tr, tz, tm, c, g)), UN.fix_count(cl, n, big, small, h))),
    N.sub_zero(M.cnt_fix(UN.cl2(cl, big, small), n)))
  ST.g_mk(n, d, AR.rtree(M.ms(cl, small), d, tr, big), A.upd(U.Nt, d, tz, big, U.N{tot_of(cl, big, small)}), A.upd(U.Ms, d, tm, big, U.M{nms_of(cl, big, small)}), Nat.sub(c, 1n),
    ST.g_depth(n, d, tr, tz, tm, c, g),
    AR.rtree_perfect(M.ms(cl, small), d, tr, big, pr),
    A.upd_perfect(U.Nt, d, tz, big, U.N{tot_of(cl, big, small)}, pz),
    A.upd_perfect(U.Ms, d, tm, big, U.M{nms_of(cl, big, small)}, pm),
    ST.g_cap(n, d, tr, tz, tm, c, g),
    %es : {M.good(_, n, n) == True{} : Bool}
    UN.good2(cl, n, big, small, h, n, N.le_refl(n)),
    %es : {Nat.is_eq(Nat.sub(c, 1n), M.cnt_fix(_, n)) == True{} : Bool}
    M.eq_true(Nat.sub(c, 1n), M.cnt_fix(UN.cl2(cl, big, small), n), ec))

def msh_model(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +big: Nat, +small: Nat, +g: {ST.repf(n, d, tr, tz, tm, c) == True{} : Bool}, +h: {UN.H(ST.clist(d, tr, tz, tm), n, big, small) == True{} : Bool}) -> {ST.model(msh(n, d, tr, tz, tm, c, big, small)) == S.relabel(M.labs(ST.clist(d, tr, tz, tm), n), small, big) : List<&2, Nat>}:
  %Equal.sym(List<&2, CL.Cell>, ST.cl(msh(n, d, tr, tz, tm, c, big, small)), UN.cl2(ST.clist(d, tr, tz, tm), big, small), msh_clist(n, d, tr, tz, tm, c, big, small, g, h)) : {M.labs(_, n) == S.relabel(M.labs(ST.clist(d, tr, tz, tm), n), small, big) : List<&2, Nat>}
  UN.labs_relabel(ST.clist(d, tr, tz, tm), n, big, small, h, n, N.le_refl(n))

def msh_run(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +big: Nat, +small: Nat, +g: {ST.repf(n, d, tr, tz, tm, c) == True{} : Bool}, +h: {UN.H(ST.clist(d, tr, tz, tm), n, big, small) == True{} : Bool}) -> {U.union_write(n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, big, tot_of(ST.clist(d, tr, tz, tm), big, small), M.ms(ST.clist(d, tr, tz, tm), big), M.ms(ST.clist(d, tr, tz, tm), small)) == (ST.real(msh(n, d, tr, tz, tm, c, big, small)), Done{True{}}) : U.UnionFind & Result<&2, &2, E.Error, Bool>}:
  +cl = ST.clist(d, tr, tz, tm)
  +pr = ST.g_pr(n, d, tr, tz, tm, c, g)
  +pz = ST.g_pz(n, d, tr, tz, tm, c, g)
  +pm = ST.g_pm(n, d, tr, tz, tm, c, g)
  +hd = ST.g_lt32(n, d, tr, tz, tm, c, g)
  +hc = ST.g_cap(n, d, tr, tz, tm, c, g)
  +hb = ST.in_cap(n, d, big, UN.h_big(cl, n, big, small, h), hc)
  +hbel = bel(n, d, cl, big, small, h, hc)
  %Equal.sym(List<&2, Nat>, List.reverse.go(&2, Nat, List.reverse.go(&2, Nat, M.ms(cl, small), Nil{}), M.ms(cl, big)), SC.append(Nat, M.ms(cl, small), M.ms(cl, big)), LL.rev_go_twice(Nat, M.ms(cl, small), Nil{}, M.ms(cl, big))) : {(U.UF{n, d, U.relink(M.ms(cl, small), A.thaw(U.Nt, tr), d, big), U.write_nat(A.thaw(U.Nt, tz), d, big, tot_of(cl, big, small)), U.write_ms(A.thaw(U.Ms, tm), d, big, _), Nat.sub(c, 1n)}, Done{True{}}) == (ST.real(msh(n, d, tr, tz, tm, c, big, small)), Done{True{}}) : U.UnionFind & Result<&2, &2, E.Error, Bool>}
  %Equal.sym(Array<U.Nt>, U.relink(M.ms(cl, small), A.thaw(U.Nt, tr), d, big), A.thaw(U.Nt, AR.rtree(M.ms(cl, small), d, tr, big)), AR.relink_ok(M.ms(cl, small), d, tr, big, hd, pr, hbel)) : {(U.UF{n, d, _, U.write_nat(A.thaw(U.Nt, tz), d, big, tot_of(cl, big, small)), U.write_ms(A.thaw(U.Ms, tm), d, big, nms_of(cl, big, small)), Nat.sub(c, 1n)}, Done{True{}}) == (ST.real(msh(n, d, tr, tz, tm, c, big, small)), Done{True{}}) : U.UnionFind & Result<&2, &2, E.Error, Bool>}
  %Equal.sym(Array<U.Nt>, U.write_nat(A.thaw(U.Nt, tz), d, big, tot_of(cl, big, small)), A.thaw(U.Nt, A.upd(U.Nt, d, tz, big, U.N{tot_of(cl, big, small)})), AR.write_nat_ok(d, tz, big, tot_of(cl, big, small), hd, hb, pz)) : {(U.UF{n, d, A.thaw(U.Nt, AR.rtree(M.ms(cl, small), d, tr, big)), _, U.write_ms(A.thaw(U.Ms, tm), d, big, nms_of(cl, big, small)), Nat.sub(c, 1n)}, Done{True{}}) == (ST.real(msh(n, d, tr, tz, tm, c, big, small)), Done{True{}}) : U.UnionFind & Result<&2, &2, E.Error, Bool>}
  %Equal.sym(Array<U.Ms>, U.write_ms(A.thaw(U.Ms, tm), d, big, nms_of(cl, big, small)), A.thaw(U.Ms, A.upd(U.Ms, d, tm, big, U.M{nms_of(cl, big, small)})), AR.write_ms_ok(d, tm, big, nms_of(cl, big, small), hd, hb, pm)) : {(U.UF{n, d, A.thaw(U.Nt, AR.rtree(M.ms(cl, small), d, tr, big)), A.thaw(U.Nt, A.upd(U.Nt, d, tz, big, U.N{tot_of(cl, big, small)})), _, Nat.sub(c, 1n)}, Done{True{}}) == (ST.real(msh(n, d, tr, tz, tm, c, big, small)), Done{True{}}) : U.UnionFind & Result<&2, &2, E.Error, Bool>}
  {==}

def ms_read(+d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +x: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pr: {A.perfect(U.Nt, d, tr) == True{} : Bool}, +pz: {A.perfect(U.Nt, d, tz) == True{} : Bool}, +pm: {A.perfect(U.Ms, d, tm) == True{} : Bool}, +hx: {Nat.is_lt(x, SC.pow2(d)) == True{} : Bool}) -> {U.read_ms(A.thaw(U.Ms, tm), d, x) == (A.thaw(U.Ms, tm), M.ms(ST.clist(d, tr, tz, tm), x)) : Array<U.Ms> & List<&2, Nat>}:
  %Equal.sym(List<&2, Nat>, M.ms(ST.clist(d, tr, tz, tm), x), AR.nthm(AR.msl(tm), x), ST.ms_at(d, tr, tz, tm, x, pr, pz, pm, hx)) : {U.read_ms(A.thaw(U.Ms, tm), d, x) == (A.thaw(U.Ms, tm), _) : Array<U.Ms> & List<&2, Nat>}
  AR.read_ms_ok(d, tm, x, hd, hx, pm)

# A union step that really merges: the shadow after the merge is good and its
# model is the spec relabelling.
def JoinOK(r: U.UnionFind & Result<&2, &2, E.Error, Bool>, sp: List<&2, Nat> & E.Obs) -> Type:
  Sigma<&1, &1, ST.Sh, sh2 => Sigma<&1, &1, E.Obs, o => {U.obs_bool(r) == (ST.real(sh2), o) : U.UnionFind & E.Obs} & ({ST.good(sh2) == True{} : Bool} & {(ST.model(sh2), o) == sp : List<&2, Nat> & E.Obs})>>

def merged(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +big: Nat, +small: Nat, +g: {ST.repf(n, d, tr, tz, tm, c) == True{} : Bool}, +h: {UN.H(ST.clist(d, tr, tz, tm), n, big, small) == True{} : Bool}) -> JoinOK(U.union_write(n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, big, tot_of(ST.clist(d, tr, tz, tm), big, small), M.ms(ST.clist(d, tr, tz, tm), big), M.ms(ST.clist(d, tr, tz, tm), small)), (S.relabel(M.labs(ST.clist(d, tr, tz, tm), n), small, big), E.OBool{Done{True{}}})):
  (msh(n, d, tr, tz, tm, c, big, small), (E.OBool{Done{True{}}}, (
    Equal.cong(U.UnionFind & Result<&2, &2, E.Error, Bool>, U.UnionFind & E.Obs, q => U.obs_bool(q),
      U.union_write(n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, big, tot_of(ST.clist(d, tr, tz, tm), big, small), M.ms(ST.clist(d, tr, tz, tm), big), M.ms(ST.clist(d, tr, tz, tm), small)),
      (ST.real(msh(n, d, tr, tz, tm, c, big, small)), Done{True{}}),
      msh_run(n, d, tr, tz, tm, c, big, small, g, h)),
    (msh_good(n, d, tr, tz, tm, c, big, small, g, h),
     Equal.cong(List<&2, Nat>, List<&2, Nat> & E.Obs, xs => (xs, E.OBool{Done{True{}}}),
       ST.model(msh(n, d, tr, tz, tm, c, big, small)), S.relabel(M.labs(ST.clist(d, tr, tz, tm), n), small, big),
       msh_model(n, d, tr, tz, tm, c, big, small, g, h))))))

def keep_ok(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +ra: Nat, +rb: Nat, +g: {ST.repf(n, d, tr, tz, tm, c) == True{} : Bool}, +hab: {UN.H(ST.clist(d, tr, tz, tm), n, ra, rb) == True{} : Bool}, +hba: {UN.H(ST.clist(d, tr, tz, tm), n, rb, ra) == True{} : Bool}, keep: Bool, +tot: Nat, +et: {Nat.add(M.sz(ST.clist(d, tr, tz, tm), ra), M.sz(ST.clist(d, tr, tz, tm), rb)) == tot : Nat}) -> JoinOK(U.union_pick(keep, n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, ra, rb, tot), (S.join_keep(keep, M.labs(ST.clist(d, tr, tz, tm), n), ra, rb), E.OBool{Done{True{}}})):
  match keep:
    case True{}:
    +cl = ST.clist(d, tr, tz, tm)
    +hd = ST.g_lt32(n, d, tr, tz, tm, c, g)
    +pr = ST.g_pr(n, d, tr, tz, tm, c, g)
    +pz = ST.g_pz(n, d, tr, tz, tm, c, g)
    +pm = ST.g_pm(n, d, tr, tz, tm, c, g)
    +hc = ST.g_cap(n, d, tr, tz, tm, c, g)
    +hra = ST.in_cap(n, d, ra, UN.h_big(cl, n, ra, rb, hab), hc)
    +hrb = ST.in_cap(n, d, rb, UN.h_small(cl, n, ra, rb, hab), hc)
      %Equal.sym(Array<U.Ms> & List<&2, Nat>, U.read_ms(A.thaw(U.Ms, tm), d, rb), (A.thaw(U.Ms, tm), M.ms(cl, rb)), ms_read(d, tr, tz, tm, rb, hd, pr, pz, pm, hrb)) : JoinOK(U.union_mss(_, n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), c, ra, rb, tot), (S.join_keep(True{}, M.labs(cl, n), ra, rb), E.OBool{Done{True{}}}))
      %Equal.sym(Array<U.Ms> & List<&2, Nat>, U.read_ms(A.thaw(U.Ms, tm), d, ra), (A.thaw(U.Ms, tm), M.ms(cl, ra)), ms_read(d, tr, tz, tm, ra, hd, pr, pz, pm, hra)) : JoinOK(U.union_msb(_, n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), c, ra, tot, M.ms(cl, rb)), (S.join_keep(True{}, M.labs(cl, n), ra, rb), E.OBool{Done{True{}}}))
      %et : JoinOK(U.union_write(n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, ra, _, M.ms(cl, ra), M.ms(cl, rb)), (S.join_keep(True{}, M.labs(cl, n), ra, rb), E.OBool{Done{True{}}}))
      merged(n, d, tr, tz, tm, c, ra, rb, g, hab)
    case False{}:
    +cl = ST.clist(d, tr, tz, tm)
    +hd = ST.g_lt32(n, d, tr, tz, tm, c, g)
    +pr = ST.g_pr(n, d, tr, tz, tm, c, g)
    +pz = ST.g_pz(n, d, tr, tz, tm, c, g)
    +pm = ST.g_pm(n, d, tr, tz, tm, c, g)
    +hc = ST.g_cap(n, d, tr, tz, tm, c, g)
    +hra = ST.in_cap(n, d, ra, UN.h_big(cl, n, ra, rb, hab), hc)
    +hrb = ST.in_cap(n, d, rb, UN.h_small(cl, n, ra, rb, hab), hc)
      %Equal.sym(Array<U.Ms> & List<&2, Nat>, U.read_ms(A.thaw(U.Ms, tm), d, ra), (A.thaw(U.Ms, tm), M.ms(cl, ra)), ms_read(d, tr, tz, tm, ra, hd, pr, pz, pm, hra)) : JoinOK(U.union_mss(_, n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), c, rb, ra, tot), (S.join_keep(False{}, M.labs(cl, n), ra, rb), E.OBool{Done{True{}}}))
      %Equal.sym(Array<U.Ms> & List<&2, Nat>, U.read_ms(A.thaw(U.Ms, tm), d, rb), (A.thaw(U.Ms, tm), M.ms(cl, rb)), ms_read(d, tr, tz, tm, rb, hd, pr, pz, pm, hrb)) : JoinOK(U.union_msb(_, n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), c, rb, tot, M.ms(cl, ra)), (S.join_keep(False{}, M.labs(cl, n), ra, rb), E.OBool{Done{True{}}}))
      %Equal.trans(Nat, Nat.add(M.sz(cl, rb), M.sz(cl, ra)), Nat.add(M.sz(cl, ra), M.sz(cl, rb)), tot, N.add_comm(M.sz(cl, rb), M.sz(cl, ra)), et) : JoinOK(U.union_write(n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, rb, _, M.ms(cl, rb), M.ms(cl, ra)), (S.join_keep(False{}, M.labs(cl, n), ra, rb), E.OBool{Done{True{}}}))
      merged(n, d, tr, tz, tm, c, rb, ra, g, hba)

def sz_read(+d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +x: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pr: {A.perfect(U.Nt, d, tr) == True{} : Bool}, +pz: {A.perfect(U.Nt, d, tz) == True{} : Bool}, +pm: {A.perfect(U.Ms, d, tm) == True{} : Bool}, +hx: {Nat.is_lt(x, SC.pow2(d)) == True{} : Bool}) -> {U.read_nat(A.thaw(U.Nt, tz), d, x) == (A.thaw(U.Nt, tz), M.sz(ST.clist(d, tr, tz, tm), x)) : Array<U.Nt> & Nat}:
  %Equal.sym(Nat, M.sz(ST.clist(d, tr, tz, tm), x), AR.nthn(AR.rsl(tz), x), ST.sz_at(d, tr, tz, tm, x, pr, pz, pm, hx)) : {U.read_nat(A.thaw(U.Nt, tz), d, x) == (A.thaw(U.Nt, tz), _) : Array<U.Nt> & Nat}
  AR.read_nat_ok(d, tz, x, hd, hx, pz)

# The class size stored at a root is the spec's count of that label.
def sz_count(+n: Nat, +cl: List<&2, CL.Cell>, +x: Nat, +hr: {M.root_ok(True{}, cl, n, x) == True{} : Bool}) -> {S.count_eq(M.labs(cl, n), x) == M.sz(cl, x) : Nat}:
  Equal.trans(Nat, S.count_eq(M.labs(cl, n), x), M.cnt_r(cl, x, n), M.sz(cl, x),
    M.count_labs(cl, x, n),
    Equal.sym(Nat, M.sz(cl, x), M.cnt_r(cl, x, n), M.root_size(cl, n, x, hr)))

def roots_ok(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +g: {ST.repf(n, d, tr, tz, tm, c) == True{} : Bool}, +ra: Nat, +rb: Nat, +hra: {Nat.is_lt(ra, n) == True{} : Bool}, +hrb: {Nat.is_lt(rb, n) == True{} : Bool}, +rra: {Nat.is_eq(M.rt(ST.clist(d, tr, tz, tm), ra), ra) == True{} : Bool}, +rrb: {Nat.is_eq(M.rt(ST.clist(d, tr, tz, tm), rb), rb) == True{} : Bool}, same: Bool, +es: {Nat.is_eq(ra, rb) == same : Bool}) -> JoinOK(U.union_roots(same, n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, ra, rb), S.join_labels(same, M.labs(ST.clist(d, tr, tz, tm), n), ra, rb)):
  match same:
    case True{}:
      (ST.Sh{n, d, tr, tz, tm, c}, (E.OBool{Done{False{}}}, ({==}, (g, {==}))))
    case False{}:
      +cl = ST.clist(d, tr, tz, tm)
      +hd = ST.g_lt32(n, d, tr, tz, tm, c, g)
      +pr = ST.g_pr(n, d, tr, tz, tm, c, g)
      +pz = ST.g_pz(n, d, tr, tz, tm, c, g)
      +pm = ST.g_pm(n, d, tr, tz, tm, c, g)
      +hc = ST.g_cap(n, d, tr, tz, tm, c, g)
      +ca = ST.in_cap(n, d, ra, hra, hc)
      +cb = ST.in_cap(n, d, rb, hrb, hc)
      +hab = UN.h_mk(cl, n, ra, rb, ST.g_good(n, d, tr, tz, tm, c, g), ST.g_len(n, d, tr, tz, tm, c, g), hra, hrb, rra, rrb, es)
      +hba = UN.h_mk(cl, n, rb, ra, ST.g_good(n, d, tr, tz, tm, c, g), ST.g_len(n, d, tr, tz, tm, c, g), hrb, hra, rrb, rra, Equal.trans(Bool, Nat.is_eq(rb, ra), Nat.is_eq(ra, rb), False{}, M.is_eq_sym(rb, ra), es))
      %Equal.sym(Array<U.Nt> & Nat, U.read_nat(A.thaw(U.Nt, tz), d, ra), (A.thaw(U.Nt, tz), M.sz(cl, ra)), sz_read(d, tr, tz, tm, ra, hd, pr, pz, pm, ca)) : JoinOK(U.union_za(_, n, d, A.thaw(U.Nt, tr), A.thaw(U.Ms, tm), c, ra, rb), S.join_labels(False{}, M.labs(cl, n), ra, rb))
      %Equal.sym(Array<U.Nt> & Nat, U.read_nat(A.thaw(U.Nt, tz), d, rb), (A.thaw(U.Nt, tz), M.sz(cl, rb)), sz_read(d, tr, tz, tm, rb, hd, pr, pz, pm, cb)) : JoinOK(U.union_zb(_, n, d, A.thaw(U.Nt, tr), A.thaw(U.Ms, tm), c, ra, rb, M.sz(cl, ra)), S.join_labels(False{}, M.labs(cl, n), ra, rb))
      %Equal.sym(Nat, S.count_eq(M.labs(cl, n), rb), M.sz(cl, rb), sz_count(n, cl, rb, UN.root_of_small(cl, n, ra, rb, hab))) : JoinOK(U.union_pick(Nat.is_le(M.sz(cl, rb), M.sz(cl, ra)), n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, ra, rb, Nat.add(M.sz(cl, ra), M.sz(cl, rb))), (S.join_keep(Nat.is_le(_, S.count_eq(M.labs(cl, n), ra)), M.labs(cl, n), ra, rb), E.OBool{Done{True{}}}))
      %Equal.sym(Nat, S.count_eq(M.labs(cl, n), ra), M.sz(cl, ra), sz_count(n, cl, ra, UN.root_of_big(cl, n, ra, rb, hab))) : JoinOK(U.union_pick(Nat.is_le(M.sz(cl, rb), M.sz(cl, ra)), n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, ra, rb, Nat.add(M.sz(cl, ra), M.sz(cl, rb))), (S.join_keep(Nat.is_le(M.sz(cl, rb), _), M.labs(cl, n), ra, rb), E.OBool{Done{True{}}}))
      keep_ok(n, d, tr, tz, tm, c, ra, rb, g, hab, hba, Nat.is_le(M.sz(cl, rb), M.sz(cl, ra)), Nat.add(M.sz(cl, ra), M.sz(cl, rb)), {==})

def union_case(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +a: Nat, +b: Nat, ba: Bool, +eba: {Nat.is_lt(a, n) == ba : Bool}, bb: Bool, +ebb: {Nat.is_lt(b, n) == bb : Bool}, +g: {ST.repf(n, d, tr, tz, tm, c) == True{} : Bool}) -> StepOK(ST.Sh{n, d, tr, tz, tm, c}, E.Union{a, b}):
  match ba bb:
    case True{} True{}:
      +cl = ST.clist(d, tr, tz, tm)
      +gg = ST.g_good(n, d, tr, tz, tm, c, g)
      +ga = M.good_elim(cl, n, n, a, gg, eba)
      +gb = M.good_elim(cl, n, n, b, gg, ebb)
      %Equal.sym(Bool, Nat.is_lt(a, n), True{}, eba) : JoinOK(U.union_if(Bool.and(_, Nat.is_lt(b, n)), n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, a, b), S.join(SC.nth(Nat, M.labs(cl, n), a), SC.nth(Nat, M.labs(cl, n), b), M.labs(cl, n)))
      %Equal.sym(Bool, Nat.is_lt(b, n), True{}, ebb) : JoinOK(U.union_if(Bool.and(True{}, _), n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, a, b), S.join(SC.nth(Nat, M.labs(cl, n), a), SC.nth(Nat, M.labs(cl, n), b), M.labs(cl, n)))
      %labs_in(n, cl, a, eba) : JoinOK(U.union_if(True{}, n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, a, b), S.join(_, SC.nth(Nat, M.labs(cl, n), b), M.labs(cl, n)))
      %labs_in(n, cl, b, ebb) : JoinOK(U.union_if(True{}, n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, a, b), S.join(Some{M.rt(cl, a)}, _, M.labs(cl, n)))
      %Equal.sym(Array<U.Nt> & Nat, U.read_nat(A.thaw(U.Nt, tr), d, a), (A.thaw(U.Nt, tr), M.rt(cl, a)), root_read(n, d, tr, tz, tm, c, a, g, eba)) : JoinOK(U.union_a(_, n, d, A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, b), S.join_labels(Nat.is_eq(M.rt(cl, a), M.rt(cl, b)), M.labs(cl, n), M.rt(cl, a), M.rt(cl, b)))
      %Equal.sym(Array<U.Nt> & Nat, U.read_nat(A.thaw(U.Nt, tr), d, b), (A.thaw(U.Nt, tr), M.rt(cl, b)), root_read(n, d, tr, tz, tm, c, b, g, ebb)) : JoinOK(U.union_b(_, n, d, A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, M.rt(cl, a)), S.join_labels(Nat.is_eq(M.rt(cl, a), M.rt(cl, b)), M.labs(cl, n), M.rt(cl, a), M.rt(cl, b)))
      roots_ok(n, d, tr, tz, tm, c, g, M.rt(cl, a), M.rt(cl, b), M.at_lt(cl, n, a, ga), M.at_lt(cl, n, b, gb), M.eq_true(M.rt(cl, M.rt(cl, a)), M.rt(cl, a), M.at_idem(cl, n, a, ga)), M.eq_true(M.rt(cl, M.rt(cl, b)), M.rt(cl, b), M.at_idem(cl, n, b, gb)), Nat.is_eq(M.rt(cl, a), M.rt(cl, b)), {==})
    case True{} False{}:
      %Equal.sym(Bool, Nat.is_lt(a, n), True{}, eba) : JoinOK(U.union_if(Bool.and(_, Nat.is_lt(b, n)), n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, a, b), S.join(SC.nth(Nat, M.labs(ST.clist(d, tr, tz, tm), n), a), SC.nth(Nat, M.labs(ST.clist(d, tr, tz, tm), n), b), M.labs(ST.clist(d, tr, tz, tm), n)))
      %Equal.sym(Bool, Nat.is_lt(b, n), False{}, ebb) : JoinOK(U.union_if(Bool.and(True{}, _), n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, a, b), S.join(SC.nth(Nat, M.labs(ST.clist(d, tr, tz, tm), n), a), SC.nth(Nat, M.labs(ST.clist(d, tr, tz, tm), n), b), M.labs(ST.clist(d, tr, tz, tm), n)))
      %labs_in(n, ST.clist(d, tr, tz, tm), a, eba) : JoinOK(U.union_if(False{}, n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, a, b), S.join(_, SC.nth(Nat, M.labs(ST.clist(d, tr, tz, tm), n), b), M.labs(ST.clist(d, tr, tz, tm), n)))
      %labs_out(n, ST.clist(d, tr, tz, tm), b, ebb) : JoinOK(U.union_if(False{}, n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, a, b), S.join(Some{M.rt(ST.clist(d, tr, tz, tm), a)}, _, M.labs(ST.clist(d, tr, tz, tm), n)))
      (ST.Sh{n, d, tr, tz, tm, c}, (E.OBool{Fail{E.OutOfRange{}}}, ({==}, (g, {==}))))
    case False{} _:
      %Equal.sym(Bool, Nat.is_lt(a, n), False{}, eba) : JoinOK(U.union_if(Bool.and(_, Nat.is_lt(b, n)), n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, a, b), S.join(SC.nth(Nat, M.labs(ST.clist(d, tr, tz, tm), n), a), SC.nth(Nat, M.labs(ST.clist(d, tr, tz, tm), n), b), M.labs(ST.clist(d, tr, tz, tm), n)))
      %labs_out(n, ST.clist(d, tr, tz, tm), a, eba) : JoinOK(U.union_if(False{}, n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c, a, b), S.join(_, SC.nth(Nat, M.labs(ST.clist(d, tr, tz, tm), n), b), M.labs(ST.clist(d, tr, tz, tm), n)))
      (ST.Sh{n, d, tr, tz, tm, c}, (E.OBool{Fail{E.OutOfRange{}}}, ({==}, (g, {==}))))

# ---- every operation ----

# A materialised shadow.
def step_sh(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, op: E.Op, +g: {ST.repf(n, d, tr, tz, tm, c) == True{} : Bool}) -> StepOK(ST.Sh{n, d, tr, tz, tm, c}, op):
  match op:
    case E.Find{+x}:
      find_case(n, d, tr, tz, tm, c, x, Nat.is_lt(x, n), {==}, g)
    case E.Union{+a, +b}:
      union_case(n, d, tr, tz, tm, c, a, b, Nat.is_lt(a, n), {==}, Nat.is_lt(b, n), {==}, g)
    case E.Connected{+a, +b}:
      conn_case(n, d, tr, tz, tm, c, a, b, Nat.is_lt(a, n), {==}, Nat.is_lt(b, n), {==}, g)
    case E.ComponentSize{+x}:
      size_case(n, d, tr, tz, tm, c, x, Nat.is_lt(x, n), {==}, g)
    case E.ComponentCount{}:
      count_ok(n, d, tr, tz, tm, c, g)

# ---- every operation ----

def step_ok(+sh: ST.Sh, op: E.Op, +g: {ST.good(sh) == True{} : Bool}) -> StepOK(sh, op):
  match sh:
    case ST.Sh{+n, +d, +tr, +tz, +tm, +c}:
      step_sh(n, d, tr, tz, tm, c, op, g)
