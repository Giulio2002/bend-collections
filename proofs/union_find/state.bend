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

def burn_nt_any(xs: List<U.Nt>) -> {U.burn_nt(xs) == Unit{} : Unit}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      burn_nt_any(t)

def burn_ms_any(xs: List<U.Ms>) -> {U.burn_ms(xs) == Unit{} : Unit}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      burn_ms_any(t)

def unit2(a: Unit, b: Unit) -> Unit:
  match a b:
    case Unit{} Unit{}:
      Unit{}

def uburn(r: Array<U.Nt>, z: Array<U.Nt>, m: Array<U.Ms>) -> Unit:
  U.unit3(U.burn_nt(Array.to_list(~U.Nt, r)), U.burn_nt(Array.to_list(~U.Nt, z)), U.burn_ms(Array.to_list(~U.Ms, m)))

def uburn_ok(+tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>) -> {uburn(A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm)) == Unit{} : Unit}:
  %Equal.sym(Unit, U.burn_nt(Array.to_list(~U.Nt, A.thaw(U.Nt, tr))), Unit{}, burn_nt_any(Array.to_list(~U.Nt, A.thaw(U.Nt, tr)))) : {U.unit3(_, U.burn_nt(Array.to_list(~U.Nt, A.thaw(U.Nt, tz))), U.burn_ms(Array.to_list(~U.Ms, A.thaw(U.Ms, tm)))) == Unit{} : Unit}
  %Equal.sym(Unit, U.burn_nt(Array.to_list(~U.Nt, A.thaw(U.Nt, tz))), Unit{}, burn_nt_any(Array.to_list(~U.Nt, A.thaw(U.Nt, tz)))) : {U.unit3(Unit{}, _, U.burn_ms(Array.to_list(~U.Ms, A.thaw(U.Ms, tm)))) == Unit{} : Unit}
  %Equal.sym(Unit, U.burn_ms(Array.to_list(~U.Ms, A.thaw(U.Ms, tm))), Unit{}, burn_ms_any(Array.to_list(~U.Ms, A.thaw(U.Ms, tm)))) : {U.unit3(Unit{}, Unit{}, _) == Unit{} : Unit}
  {==}

def dispose_ok(+n: Nat, +d: Nat, +tr: A.Tree<U.Nt>, +tz: A.Tree<U.Nt>, +tm: A.Tree<U.Ms>, +c: Nat) -> {U.dispose(real(Sh{n, d, tr, tz, tm, c})) == Unit{} : Unit}:
  uburn_ok(tr, tz, tm)

def npick(+v: Nat, u: Unit) -> Nat:
  match u:
    case Unit{}:
      v

def tpick(-T: Data, t: A.Tree<T>, u: Unit) -> A.Tree<T>:
  match u:
    case Unit{}:
      t

def u_len(s: U.UnionFind) -> Nat:
  match s:
    case U.UF{+n, d, r, z, m, c}:
      npick(n, uburn(r, z, m))

def u_depth(s: U.UnionFind) -> Nat:
  match s:
    case U.UF{n, +d, r, z, m, c}:
      npick(d, uburn(r, z, m))

def u_cnt(s: U.UnionFind) -> Nat:
  match s:
    case U.UF{n, d, r, z, m, +c}:
      npick(c, uburn(r, z, m))

def u_tr(s: U.UnionFind) -> A.Tree<U.Nt>:
  match s:
    case U.UF{n, d, r, z, m, c}:
      tpick(U.Nt, A.freeze(U.Nt, r), unit2(U.burn_nt(Array.to_list(~U.Nt, z)), U.burn_ms(Array.to_list(~U.Ms, m))))

def u_tz(s: U.UnionFind) -> A.Tree<U.Nt>:
  match s:
    case U.UF{n, d, r, z, m, c}:
      tpick(U.Nt, A.freeze(U.Nt, z), unit2(U.burn_nt(Array.to_list(~U.Nt, r)), U.burn_ms(Array.to_list(~U.Ms, m))))

def u_tm(s: U.UnionFind) -> A.Tree<U.Ms>:
  match s:
    case U.UF{n, d, r, z, m, c}:
      tpick(U.Ms, A.freeze(U.Ms, m), unit2(U.burn_nt(Array.to_list(~U.Nt, r)), U.burn_nt(Array.to_list(~U.Nt, z))))

def sh_n(sh: Sh) -> Nat:
  match sh:
    case Sh{n, d, tr, tz, tm, c}:
      n

def sh_d(sh: Sh) -> Nat:
  match sh:
    case Sh{n, d, tr, tz, tm, c}:
      d

def sh_c(sh: Sh) -> Nat:
  match sh:
    case Sh{n, d, tr, tz, tm, c}:
      c

def sh_tr(sh: Sh) -> A.Tree<U.Nt>:
  match sh:
    case Sh{n, d, tr, tz, tm, c}:
      tr

def sh_tz(sh: Sh) -> A.Tree<U.Nt>:
  match sh:
    case Sh{n, d, tr, tz, tm, c}:
      tz

def sh_tm(sh: Sh) -> A.Tree<U.Ms>:
  match sh:
    case Sh{n, d, tr, tz, tm, c}:
      tm

def real_len(+sh: Sh) -> {u_len(real(sh)) == sh_n(sh) : Nat}:
  match sh:
    case Sh{+n, d, tr, tz, tm, c}:
      Equal.cong(Unit, Nat, u => npick(n, u), uburn(A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm)), Unit{}, uburn_ok(tr, tz, tm))

def real_depth(+sh: Sh) -> {u_depth(real(sh)) == sh_d(sh) : Nat}:
  match sh:
    case Sh{n, +d, tr, tz, tm, c}:
      Equal.cong(Unit, Nat, u => npick(d, u), uburn(A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm)), Unit{}, uburn_ok(tr, tz, tm))

def real_cnt(+sh: Sh) -> {u_cnt(real(sh)) == sh_c(sh) : Nat}:
  match sh:
    case Sh{n, d, tr, tz, tm, +c}:
      Equal.cong(Unit, Nat, u => npick(c, u), uburn(A.thaw(U.Nt, tr), A.thaw(U.Nt, tz), A.thaw(U.Ms, tm)), Unit{}, uburn_ok(tr, tz, tm))

def real_tr(+sh: Sh) -> {u_tr(real(sh)) == sh_tr(sh) : A.Tree<U.Nt>}:
  match sh:
    case Sh{n, d, +tr, tz, tm, c}:
      %Equal.sym(Unit, U.burn_nt(Array.to_list(~U.Nt, A.thaw(U.Nt, tz))), Unit{}, burn_nt_any(Array.to_list(~U.Nt, A.thaw(U.Nt, tz)))) : {tpick(U.Nt, A.freeze(U.Nt, A.thaw(U.Nt, tr)), unit2(_, U.burn_ms(Array.to_list(~U.Ms, A.thaw(U.Ms, tm))))) == tr : A.Tree<U.Nt>}
      %Equal.sym(Unit, U.burn_ms(Array.to_list(~U.Ms, A.thaw(U.Ms, tm))), Unit{}, burn_ms_any(Array.to_list(~U.Ms, A.thaw(U.Ms, tm)))) : {tpick(U.Nt, A.freeze(U.Nt, A.thaw(U.Nt, tr)), unit2(Unit{}, _)) == tr : A.Tree<U.Nt>}
      A.freeze_thaw(U.Nt, tr)

def real_tz(+sh: Sh) -> {u_tz(real(sh)) == sh_tz(sh) : A.Tree<U.Nt>}:
  match sh:
    case Sh{n, d, tr, +tz, tm, c}:
      %Equal.sym(Unit, U.burn_nt(Array.to_list(~U.Nt, A.thaw(U.Nt, tr))), Unit{}, burn_nt_any(Array.to_list(~U.Nt, A.thaw(U.Nt, tr)))) : {tpick(U.Nt, A.freeze(U.Nt, A.thaw(U.Nt, tz)), unit2(_, U.burn_ms(Array.to_list(~U.Ms, A.thaw(U.Ms, tm))))) == tz : A.Tree<U.Nt>}
      %Equal.sym(Unit, U.burn_ms(Array.to_list(~U.Ms, A.thaw(U.Ms, tm))), Unit{}, burn_ms_any(Array.to_list(~U.Ms, A.thaw(U.Ms, tm)))) : {tpick(U.Nt, A.freeze(U.Nt, A.thaw(U.Nt, tz)), unit2(Unit{}, _)) == tz : A.Tree<U.Nt>}
      A.freeze_thaw(U.Nt, tz)

def real_tm(+sh: Sh) -> {u_tm(real(sh)) == sh_tm(sh) : A.Tree<U.Ms>}:
  match sh:
    case Sh{n, d, tr, tz, +tm, c}:
      %Equal.sym(Unit, U.burn_nt(Array.to_list(~U.Nt, A.thaw(U.Nt, tr))), Unit{}, burn_nt_any(Array.to_list(~U.Nt, A.thaw(U.Nt, tr)))) : {tpick(U.Ms, A.freeze(U.Ms, A.thaw(U.Ms, tm)), unit2(_, U.burn_nt(Array.to_list(~U.Nt, A.thaw(U.Nt, tz))))) == tm : A.Tree<U.Ms>}
      %Equal.sym(Unit, U.burn_nt(Array.to_list(~U.Nt, A.thaw(U.Nt, tz))), Unit{}, burn_nt_any(Array.to_list(~U.Nt, A.thaw(U.Nt, tz)))) : {tpick(U.Ms, A.freeze(U.Ms, A.thaw(U.Ms, tm)), unit2(Unit{}, _)) == tm : A.Tree<U.Ms>}
      A.freeze_thaw(U.Ms, tm)

def sh_eta(+sh: Sh) -> {sh == Sh{sh_n(sh), sh_d(sh), sh_tr(sh), sh_tz(sh), sh_tm(sh), sh_c(sh)} : Sh}:
  match sh:
    case Sh{n, d, tr, tz, tm, c}:
      {==}

def real_inj_parts(+a: Sh, +b: Sh, +e: {real(a) == real(b) : U.UnionFind}) -> {Sh{sh_n(a), sh_d(a), sh_tr(a), sh_tz(a), sh_tm(a), sh_c(a)} == Sh{sh_n(b), sh_d(b), sh_tr(b), sh_tz(b), sh_tm(b), sh_c(b)} : Sh}:
  %real_len(a) : {Sh{_, sh_d(a), sh_tr(a), sh_tz(a), sh_tm(a), sh_c(a)} == Sh{sh_n(b), sh_d(b), sh_tr(b), sh_tz(b), sh_tm(b), sh_c(b)} : Sh}
  %real_depth(a) : {Sh{u_len(real(a)), _, sh_tr(a), sh_tz(a), sh_tm(a), sh_c(a)} == Sh{sh_n(b), sh_d(b), sh_tr(b), sh_tz(b), sh_tm(b), sh_c(b)} : Sh}
  %real_tr(a) : {Sh{u_len(real(a)), u_depth(real(a)), _, sh_tz(a), sh_tm(a), sh_c(a)} == Sh{sh_n(b), sh_d(b), sh_tr(b), sh_tz(b), sh_tm(b), sh_c(b)} : Sh}
  %real_tz(a) : {Sh{u_len(real(a)), u_depth(real(a)), u_tr(real(a)), _, sh_tm(a), sh_c(a)} == Sh{sh_n(b), sh_d(b), sh_tr(b), sh_tz(b), sh_tm(b), sh_c(b)} : Sh}
  %real_tm(a) : {Sh{u_len(real(a)), u_depth(real(a)), u_tr(real(a)), u_tz(real(a)), _, sh_c(a)} == Sh{sh_n(b), sh_d(b), sh_tr(b), sh_tz(b), sh_tm(b), sh_c(b)} : Sh}
  %real_cnt(a) : {Sh{u_len(real(a)), u_depth(real(a)), u_tr(real(a)), u_tz(real(a)), u_tm(real(a)), _} == Sh{sh_n(b), sh_d(b), sh_tr(b), sh_tz(b), sh_tm(b), sh_c(b)} : Sh}
  %real_len(b) : {Sh{u_len(real(a)), u_depth(real(a)), u_tr(real(a)), u_tz(real(a)), u_tm(real(a)), u_cnt(real(a))} == Sh{_, sh_d(b), sh_tr(b), sh_tz(b), sh_tm(b), sh_c(b)} : Sh}
  %real_depth(b) : {Sh{u_len(real(a)), u_depth(real(a)), u_tr(real(a)), u_tz(real(a)), u_tm(real(a)), u_cnt(real(a))} == Sh{u_len(real(b)), _, sh_tr(b), sh_tz(b), sh_tm(b), sh_c(b)} : Sh}
  %real_tr(b) : {Sh{u_len(real(a)), u_depth(real(a)), u_tr(real(a)), u_tz(real(a)), u_tm(real(a)), u_cnt(real(a))} == Sh{u_len(real(b)), u_depth(real(b)), _, sh_tz(b), sh_tm(b), sh_c(b)} : Sh}
  %real_tz(b) : {Sh{u_len(real(a)), u_depth(real(a)), u_tr(real(a)), u_tz(real(a)), u_tm(real(a)), u_cnt(real(a))} == Sh{u_len(real(b)), u_depth(real(b)), u_tr(real(b)), _, sh_tm(b), sh_c(b)} : Sh}
  %real_tm(b) : {Sh{u_len(real(a)), u_depth(real(a)), u_tr(real(a)), u_tz(real(a)), u_tm(real(a)), u_cnt(real(a))} == Sh{u_len(real(b)), u_depth(real(b)), u_tr(real(b)), u_tz(real(b)), _, sh_c(b)} : Sh}
  %real_cnt(b) : {Sh{u_len(real(a)), u_depth(real(a)), u_tr(real(a)), u_tz(real(a)), u_tm(real(a)), u_cnt(real(a))} == Sh{u_len(real(b)), u_depth(real(b)), u_tr(real(b)), u_tz(real(b)), u_tm(real(b)), _} : Sh}
  Equal.cong(U.UnionFind, Sh, s => Sh{u_len(s), u_depth(s), u_tr(s), u_tz(s), u_tm(s), u_cnt(s)}, real(a), real(b), e)

def real_inj(+a: Sh, +b: Sh, +e: {real(a) == real(b) : U.UnionFind}) -> {a == b : Sh}:
  Equal.trans(Sh, a, Sh{sh_n(a), sh_d(a), sh_tr(a), sh_tz(a), sh_tm(a), sh_c(a)}, b,
    sh_eta(a),
    Equal.trans(Sh, Sh{sh_n(a), sh_d(a), sh_tr(a), sh_tz(a), sh_tm(a), sh_c(a)}, Sh{sh_n(b), sh_d(b), sh_tr(b), sh_tz(b), sh_tm(b), sh_c(b)}, b,
      real_inj_parts(a, b, e),
      Equal.sym(Sh, b, Sh{sh_n(b), sh_d(b), sh_tr(b), sh_tz(b), sh_tm(b), sh_c(b)}, sh_eta(b))))
