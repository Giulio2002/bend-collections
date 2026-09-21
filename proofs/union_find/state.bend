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
import ./arr.bend as AR
import ./depth.bend as DP

# Abstraction, invariant and shadow of src/union_find.bend.
#
# The three arenas are linear Base.Arrays, so every statement is about
# `real(sh)`, the structure built from three Data mirror trees, exactly as in
# proofs/dynamic_array and proofs/bitset. `cl(sh)` is the record list the
# mathematics of proofs/union_find/model.bend and union.bend works over.

type Sh is Data:
  Sh{len: Nat, depth: Nat, tr: A.Tree<U.Nt>, tz: A.Tree<U.Nt>, tm: A.Tree<U.Ms>, count: Nat}

def real(sh: Sh) -> U.UnionFind:
  match sh:
    case Sh{n, d, tr, tz, tm, c}:
      U.UF{n, d, A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm), c}

def clist(+d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>) -> List<&2, CL.Cell>:
  CL.cells(AR.rsl(tr), AR.rsl(tz), AR.msl(tm))

def cl(sh: Sh) -> List<&2, CL.Cell>:
  match sh:
    case Sh{n, d, tr, tz, tm, c}:
      clist(d, tr, tz, tm)

def model(sh: Sh) -> List<&2, Nat>:
  match sh:
    case Sh{+n, d, tr, tz, tm, c}:
      M.labs(clist(d, tr, tz, tm), n)

def repf(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat) -> Bool:
  Bool.and(Nat.is_eq(d, U.depth_for(n)),
    Bool.and(A.perfect(U.Nt, d, tr),
      Bool.and(A.perfect(U.Nt, d, tz),
        Bool.and(A.perfect(U.Ms, d, tm),
          Bool.and(Nat.is_le(n, SC.pow2(d)),
            Bool.and(M.good(clist(d, tr, tz, tm), n, n),
                     Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n))))))))

def good(sh: Sh) -> Bool:
  match sh:
    case Sh{+n, +d, +tr, +tz, +tm, +c}:
      repf(n, d, tr, tz, tm, c)

# ---- the parts of the invariant ----

def g_depth(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +g: {repf(n, d, tr, tz, tm, c) == True{} : Bool}) -> {Nat.is_eq(d, U.depth_for(n)) == True{} : Bool}:
  L.and_left(Nat.is_eq(d, U.depth_for(n)), Bool.and(A.perfect(U.Nt, d, tr), Bool.and(A.perfect(U.Nt, d, tz), Bool.and(A.perfect(U.Ms, d, tm), Bool.and(Nat.is_le(n, SC.pow2(d)), Bool.and(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n))))))), g)

def g_rest(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +g: {repf(n, d, tr, tz, tm, c) == True{} : Bool}) -> {Bool.and(A.perfect(U.Nt, d, tr), Bool.and(A.perfect(U.Nt, d, tz), Bool.and(A.perfect(U.Ms, d, tm), Bool.and(Nat.is_le(n, SC.pow2(d)), Bool.and(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n))))))) == True{} : Bool}:
  L.and_right(Nat.is_eq(d, U.depth_for(n)), Bool.and(A.perfect(U.Nt, d, tr), Bool.and(A.perfect(U.Nt, d, tz), Bool.and(A.perfect(U.Ms, d, tm), Bool.and(Nat.is_le(n, SC.pow2(d)), Bool.and(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n))))))), g)

def g_pr(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +g: {repf(n, d, tr, tz, tm, c) == True{} : Bool}) -> {A.perfect(U.Nt, d, tr) == True{} : Bool}:
  L.and_left(A.perfect(U.Nt, d, tr), Bool.and(A.perfect(U.Nt, d, tz), Bool.and(A.perfect(U.Ms, d, tm), Bool.and(Nat.is_le(n, SC.pow2(d)), Bool.and(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n)))))), g_rest(n, d, tr, tz, tm, c, g))

def g_rest2(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +g: {repf(n, d, tr, tz, tm, c) == True{} : Bool}) -> {Bool.and(A.perfect(U.Nt, d, tz), Bool.and(A.perfect(U.Ms, d, tm), Bool.and(Nat.is_le(n, SC.pow2(d)), Bool.and(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n)))))) == True{} : Bool}:
  L.and_right(A.perfect(U.Nt, d, tr), Bool.and(A.perfect(U.Nt, d, tz), Bool.and(A.perfect(U.Ms, d, tm), Bool.and(Nat.is_le(n, SC.pow2(d)), Bool.and(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n)))))), g_rest(n, d, tr, tz, tm, c, g))

def g_pz(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +g: {repf(n, d, tr, tz, tm, c) == True{} : Bool}) -> {A.perfect(U.Nt, d, tz) == True{} : Bool}:
  L.and_left(A.perfect(U.Nt, d, tz), Bool.and(A.perfect(U.Ms, d, tm), Bool.and(Nat.is_le(n, SC.pow2(d)), Bool.and(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n))))), g_rest2(n, d, tr, tz, tm, c, g))

def g_rest3(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +g: {repf(n, d, tr, tz, tm, c) == True{} : Bool}) -> {Bool.and(A.perfect(U.Ms, d, tm), Bool.and(Nat.is_le(n, SC.pow2(d)), Bool.and(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n))))) == True{} : Bool}:
  L.and_right(A.perfect(U.Nt, d, tz), Bool.and(A.perfect(U.Ms, d, tm), Bool.and(Nat.is_le(n, SC.pow2(d)), Bool.and(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n))))), g_rest2(n, d, tr, tz, tm, c, g))

def g_pm(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +g: {repf(n, d, tr, tz, tm, c) == True{} : Bool}) -> {A.perfect(U.Ms, d, tm) == True{} : Bool}:
  L.and_left(A.perfect(U.Ms, d, tm), Bool.and(Nat.is_le(n, SC.pow2(d)), Bool.and(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n)))), g_rest3(n, d, tr, tz, tm, c, g))

def g_rest4(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +g: {repf(n, d, tr, tz, tm, c) == True{} : Bool}) -> {Bool.and(Nat.is_le(n, SC.pow2(d)), Bool.and(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n)))) == True{} : Bool}:
  L.and_right(A.perfect(U.Ms, d, tm), Bool.and(Nat.is_le(n, SC.pow2(d)), Bool.and(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n)))), g_rest3(n, d, tr, tz, tm, c, g))

def g_cap(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +g: {repf(n, d, tr, tz, tm, c) == True{} : Bool}) -> {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}:
  L.and_left(Nat.is_le(n, SC.pow2(d)), Bool.and(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n))), g_rest4(n, d, tr, tz, tm, c, g))

def g_rest5(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +g: {repf(n, d, tr, tz, tm, c) == True{} : Bool}) -> {Bool.and(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n))) == True{} : Bool}:
  L.and_right(Nat.is_le(n, SC.pow2(d)), Bool.and(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n))), g_rest4(n, d, tr, tz, tm, c, g))

def g_good(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +g: {repf(n, d, tr, tz, tm, c) == True{} : Bool}) -> {M.good(clist(d, tr, tz, tm), n, n) == True{} : Bool}:
  L.and_left(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n)), g_rest5(n, d, tr, tz, tm, c, g))

def g_cnt(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +g: {repf(n, d, tr, tz, tm, c) == True{} : Bool}) -> {Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n)) == True{} : Bool}:
  L.and_right(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n)), g_rest5(n, d, tr, tz, tm, c, g))

def g_mk(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +a: {Nat.is_eq(d, U.depth_for(n)) == True{} : Bool}, +b: {A.perfect(U.Nt, d, tr) == True{} : Bool}, +e: {A.perfect(U.Nt, d, tz) == True{} : Bool}, +f: {A.perfect(U.Ms, d, tm) == True{} : Bool}, +i: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}, +j: {M.good(clist(d, tr, tz, tm), n, n) == True{} : Bool}, +k: {Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n)) == True{} : Bool}) -> {repf(n, d, tr, tz, tm, c) == True{} : Bool}:
  L.and_intro(Nat.is_eq(d, U.depth_for(n)), Bool.and(A.perfect(U.Nt, d, tr), Bool.and(A.perfect(U.Nt, d, tz), Bool.and(A.perfect(U.Ms, d, tm), Bool.and(Nat.is_le(n, SC.pow2(d)), Bool.and(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n))))))), a,
    L.and_intro(A.perfect(U.Nt, d, tr), Bool.and(A.perfect(U.Nt, d, tz), Bool.and(A.perfect(U.Ms, d, tm), Bool.and(Nat.is_le(n, SC.pow2(d)), Bool.and(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n)))))), b,
      L.and_intro(A.perfect(U.Nt, d, tz), Bool.and(A.perfect(U.Ms, d, tm), Bool.and(Nat.is_le(n, SC.pow2(d)), Bool.and(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n))))), e,
        L.and_intro(A.perfect(U.Ms, d, tm), Bool.and(Nat.is_le(n, SC.pow2(d)), Bool.and(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n)))), f,
          L.and_intro(Nat.is_le(n, SC.pow2(d)), Bool.and(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n))), i,
            L.and_intro(M.good(clist(d, tr, tz, tm), n, n), Nat.is_eq(c, M.cnt_fix(clist(d, tr, tz, tm), n)), j, k))))))

# ---- derived facts ----

def g_lt32(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +g: {repf(n, d, tr, tz, tm, c) == True{} : Bool}) -> {Nat.is_lt(d, 32n) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(z, 32n) == True{} : Bool}, U.depth_for(n), d,
    Equal.sym(Nat, d, U.depth_for(n), N.eq_from_is_eq(d, U.depth_for(n), g_depth(n, d, tr, tz, tm, c, g))),
    DP.depth_lt(n))

def in_cap(+n: Nat, +d: Nat, +x: Nat, +hx: {Nat.is_lt(x, n) == True{} : Bool}, +hc: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(x, SC.pow2(d)) == True{} : Bool}:
  N.lt_le_trans(x, n, SC.pow2(d), hx, hc)

# Reading a slot of the zipped record list.
def cl_nth(+d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +x: Nat, +pr: {A.perfect(U.Nt, d, tr) == True{} : Bool}, +pz: {A.perfect(U.Nt, d, tz) == True{} : Bool}, +pm: {A.perfect(U.Ms, d, tm) == True{} : Bool}, +hx: {Nat.is_lt(x, SC.pow2(d)) == True{} : Bool}) -> {SC.nth(CL.Cell, clist(d, tr, tz, tm), x) == Some{CL.Cell{AR.nthn(AR.rsl(tr), x), AR.nthn(AR.rsl(tz), x), AR.nthm(AR.msl(tm), x)}} : Maybe<&2, CL.Cell>}:
  CL.cells_nth(AR.rsl(tr), AR.rsl(tz), AR.msl(tm), x, AR.nthn(AR.rsl(tr), x), AR.nthn(AR.rsl(tz), x), AR.nthm(AR.msl(tm), x),
    AR.nthn_nth(AR.rsl(tr), x, L.subst(Nat, k => {Nat.is_lt(x, k) == True{} : Bool}, SC.pow2(d), SC.length(Nat, AR.rsl(tr)), Equal.sym(Nat, SC.length(Nat, AR.rsl(tr)), SC.pow2(d), AR.rsl_length(d, tr, pr)), hx)),
    AR.nthn_nth(AR.rsl(tz), x, L.subst(Nat, k => {Nat.is_lt(x, k) == True{} : Bool}, SC.pow2(d), SC.length(Nat, AR.rsl(tz)), Equal.sym(Nat, SC.length(Nat, AR.rsl(tz)), SC.pow2(d), AR.rsl_length(d, tz, pz)), hx)),
    AR.nthm_nth(AR.msl(tm), x, L.subst(Nat, k => {Nat.is_lt(x, k) == True{} : Bool}, SC.pow2(d), SC.length(List<&2, Nat>, AR.msl(tm)), Equal.sym(Nat, SC.length(List<&2, Nat>, AR.msl(tm)), SC.pow2(d), AR.msl_length(d, tm, pm)), hx)),)

def lc_at(+d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +x: Nat, +pr: {A.perfect(U.Nt, d, tr) == True{} : Bool}, +pz: {A.perfect(U.Nt, d, tz) == True{} : Bool}, +pm: {A.perfect(U.Ms, d, tm) == True{} : Bool}, +hx: {Nat.is_lt(x, SC.pow2(d)) == True{} : Bool}) -> {M.lc(clist(d, tr, tz, tm), x) == CL.Cell{AR.nthn(AR.rsl(tr), x), AR.nthn(AR.rsl(tz), x), AR.nthm(AR.msl(tm), x)} : CL.Cell}:
  Equal.cong(Maybe<&2, CL.Cell>, CL.Cell, m => CL.cell_of(m, x), SC.nth(CL.Cell, clist(d, tr, tz, tm), x), Some{CL.Cell{AR.nthn(AR.rsl(tr), x), AR.nthn(AR.rsl(tz), x), AR.nthm(AR.msl(tm), x)}}, cl_nth(d, tr, tz, tm, x, pr, pz, pm, hx))

def rt_at(+d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +x: Nat, +pr: {A.perfect(U.Nt, d, tr) == True{} : Bool}, +pz: {A.perfect(U.Nt, d, tz) == True{} : Bool}, +pm: {A.perfect(U.Ms, d, tm) == True{} : Bool}, +hx: {Nat.is_lt(x, SC.pow2(d)) == True{} : Bool}) -> {M.rt(clist(d, tr, tz, tm), x) == AR.nthn(AR.rsl(tr), x) : Nat}:
  Equal.cong(CL.Cell, Nat, CL.croot, M.lc(clist(d, tr, tz, tm), x), CL.Cell{AR.nthn(AR.rsl(tr), x), AR.nthn(AR.rsl(tz), x), AR.nthm(AR.msl(tm), x)}, lc_at(d, tr, tz, tm, x, pr, pz, pm, hx))

def sz_at(+d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +x: Nat, +pr: {A.perfect(U.Nt, d, tr) == True{} : Bool}, +pz: {A.perfect(U.Nt, d, tz) == True{} : Bool}, +pm: {A.perfect(U.Ms, d, tm) == True{} : Bool}, +hx: {Nat.is_lt(x, SC.pow2(d)) == True{} : Bool}) -> {M.sz(clist(d, tr, tz, tm), x) == AR.nthn(AR.rsl(tz), x) : Nat}:
  Equal.cong(CL.Cell, Nat, CL.csize, M.lc(clist(d, tr, tz, tm), x), CL.Cell{AR.nthn(AR.rsl(tr), x), AR.nthn(AR.rsl(tz), x), AR.nthm(AR.msl(tm), x)}, lc_at(d, tr, tz, tm, x, pr, pz, pm, hx))

def ms_at(+d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +x: Nat, +pr: {A.perfect(U.Nt, d, tr) == True{} : Bool}, +pz: {A.perfect(U.Nt, d, tz) == True{} : Bool}, +pm: {A.perfect(U.Ms, d, tm) == True{} : Bool}, +hx: {Nat.is_lt(x, SC.pow2(d)) == True{} : Bool}) -> {M.ms(clist(d, tr, tz, tm), x) == AR.nthm(AR.msl(tm), x) : List<&2, Nat>}:
  Equal.cong(CL.Cell, List<&2, Nat>, CL.cmembers, M.lc(clist(d, tr, tz, tm), x), CL.Cell{AR.nthn(AR.rsl(tr), x), AR.nthn(AR.rsl(tz), x), AR.nthm(AR.msl(tm), x)}, lc_at(d, tr, tz, tm, x, pr, pz, pm, hx))

# The cell list is exactly the arena capacity long, so the invariant's
# n <= pow2(d) is also "n is within the cell list".
def cl_len(+d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +pr: {A.perfect(U.Nt, d, tr) == True{} : Bool}, +pz: {A.perfect(U.Nt, d, tz) == True{} : Bool}, +pm: {A.perfect(U.Ms, d, tm) == True{} : Bool}) -> {SC.length(CL.Cell, clist(d, tr, tz, tm)) == SC.pow2(d) : Nat}:
  Equal.trans(Nat, SC.length(CL.Cell, clist(d, tr, tz, tm)), SC.length(Nat, AR.rsl(tr)), SC.pow2(d),
    CL.cells_length(AR.rsl(tr), AR.rsl(tz), AR.msl(tm),
      Equal.trans(Nat, SC.length(Nat, AR.rsl(tz)), SC.pow2(d), SC.length(Nat, AR.rsl(tr)), AR.rsl_length(d, tz, pz), Equal.sym(Nat, SC.length(Nat, AR.rsl(tr)), SC.pow2(d), AR.rsl_length(d, tr, pr))),
      Equal.trans(Nat, SC.length(List<&2, Nat>, AR.msl(tm)), SC.pow2(d), SC.length(Nat, AR.rsl(tr)), AR.msl_length(d, tm, pm), Equal.sym(Nat, SC.length(Nat, AR.rsl(tr)), SC.pow2(d), AR.rsl_length(d, tr, pr)))),
    AR.rsl_length(d, tr, pr))

def g_len(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat, +g: {repf(n, d, tr, tz, tm, c) == True{} : Bool}) -> {Nat.is_le(n, SC.length(CL.Cell, clist(d, tr, tz, tm))) == True{} : Bool}:
  L.subst(Nat, k => {Nat.is_le(n, k) == True{} : Bool}, SC.pow2(d), SC.length(CL.Cell, clist(d, tr, tz, tm)),
    Equal.sym(Nat, SC.length(CL.Cell, clist(d, tr, tz, tm)), SC.pow2(d), cl_len(d, tr, tz, tm, g_pr(n, d, tr, tz, tm, c, g), g_pz(n, d, tr, tz, tm, c, g), g_pm(n, d, tr, tz, tm, c, g))),
    g_cap(n, d, tr, tz, tm, c, g))

# ---- the shadow of a live structure is unique ----
#
# Every law says "the real operation lands on the arenas of THIS shadow".
# Because a runtime UnionFind determines its shadow, that pins the abstract
# state: the laws cannot be satisfied by naming a different shadow.

def dispose_ok(+sh: Sh) -> {U.dispose(real(sh)) == Unit{} : Unit}:
  match sh:
    case Sh{n, d, tr, tz, tm, c}:
      {==}

# A runtime structure determines its shadow: `back` reads the shadow off a
# structure (freezing its arenas) and undoes `real`.
def back(s: U.UnionFind) -> Sh:
  match s:
    case U.UF{n, d, r, z, m, c}:
      Sh{n, d, A.freeze(U.Nt, r), A.freeze(U.Nt, z), A.freeze(U.Ms, m), c}

def back_real(+sh: Sh) -> {back(real(sh)) == sh : Sh}:
  match sh:
    case Sh{+n, +d, +tr, +tz, +tm, +c}:
      %Equal.sym(A.Tree<U.Nt>, A.freeze(U.Nt, A.thaw(U.Nt, tr)), tr, A.freeze_thaw(U.Nt, tr)) : {Sh{n, d, _, A.freeze(U.Nt, A.thaw(U.Nt, tz)), A.freeze(U.Ms, A.thaw(U.Ms, tm)), c} == Sh{n, d, tr, tz, tm, c} : Sh}
      %Equal.sym(A.Tree<U.Nt>, A.freeze(U.Nt, A.thaw(U.Nt, tz)), tz, A.freeze_thaw(U.Nt, tz)) : {Sh{n, d, tr, _, A.freeze(U.Ms, A.thaw(U.Ms, tm)), c} == Sh{n, d, tr, tz, tm, c} : Sh}
      %Equal.sym(A.Tree<U.Ms>, A.freeze(U.Ms, A.thaw(U.Ms, tm)), tm, A.freeze_thaw(U.Ms, tm)) : {Sh{n, d, tr, tz, _, c} == Sh{n, d, tr, tz, tm, c} : Sh}
      {==}

def real_inj(+a: Sh, +b: Sh, +e: {real(a) == real(b) : U.UnionFind}) -> {a == b : Sh}:
  Equal.trans(Sh, a, back(real(a)), b,
    Equal.sym(Sh, back(real(a)), a, back_real(a)),
    Equal.trans(Sh, back(real(a)), back(real(b)), b,
      Equal.cong(U.UnionFind, Sh, s => back(s), real(a), real(b), e),
      back_real(b)))
