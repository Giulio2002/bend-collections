import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as A
import ../lib/flat.bend as FL
import ../../spec/common.bend as SC
import ../../spec/u32seq.bend as Q
import ../../src/segment_tree.bend as F
import ../../src/internal/vec.bend as V
import ./node.bend as TN
import ./model.bend as MD
import ./arr.bend as AR
import ./walk.bend as W

# The shadow of a segment tree.
#
# `Base.Array` is linear, so -- exactly as in proofs/fenwick_tree,
# proofs/bitset -- every law is stated about
# `real(sh)`, the structure whose two cell arrays are built from Data mirror
# trees, and each law names the shadow the operation lands on.
#
#   abstraction  model(sh)   the first n values of the tree the cells realise
#   invariant    good(sh)    the sum array is a perfect tree of depth d+1 and
#                the tag array one of depth d (so every index is a
#                representable U32), n <= 2^d, and every node of the realised
#                tree stores the sum of its subtree's values.

type Sh is Data:
  Sh{len: Nat, depth: Nat, cells: A.Tree<F.Cel>, tags: A.Tree<F.Cel>}

# `base` is derived, not stored in the shadow: a real tree built by the
# constructors always carries 2^depth there, and every law below is about a
# `real(sh)` that does.
def real(sh: Sh) -> F.SegTree:
  match sh:
    case Sh{+n, +d, c, g}:
      F.ST{n, d, SC.pow2(d), A.thaw(F.Cel, c), A.thaw(F.Cel, g)}

# The model tree the two whole cell arrays realise.
def mtree(+d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>) -> TN.Node:
  W.tree_of(AR.cl(tc), AR.cl(tg), d, d, 0n)

def mt(sh: Sh) -> TN.Node:
  match sh:
    case Sh{n, +d, +c, +g}:
      mtree(d, c, g)

def model(sh: Sh) -> List<&2, U32>:
  match sh:
    case Sh{+n, +d, +c, +g}:
      SC.take(U32, MD.vals(mtree(d, c, g)), n)

def repf(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>) -> Bool:
  Bool.and(A.perfect(F.Cel, 1n+d, tc), Bool.and(A.perfect(F.Cel, d, tg), Bool.and(Nat.is_lt(1n+d, 32n), Bool.and(Nat.is_le(n, SC.pow2(d)), MD.goods(mtree(d, tc, tg))))))

def good(sh: Sh) -> Bool:
  match sh:
    case Sh{+n, +d, +c, +g}:
      repf(n, d, c, g)

def rest1(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>) -> Bool:
  Bool.and(A.perfect(F.Cel, d, tg), Bool.and(Nat.is_lt(1n+d, 32n), Bool.and(Nat.is_le(n, SC.pow2(d)), MD.goods(mtree(d, tc, tg)))))

def rest2(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>) -> Bool:
  Bool.and(Nat.is_lt(1n+d, 32n), Bool.and(Nat.is_le(n, SC.pow2(d)), MD.goods(mtree(d, tc, tg))))

def rest3(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>) -> Bool:
  Bool.and(Nat.is_le(n, SC.pow2(d)), MD.goods(mtree(d, tc, tg)))

def g_pf(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +g: {repf(n, d, tc, tg) == True{} : Bool}) -> {A.perfect(F.Cel, 1n+d, tc) == True{} : Bool}:
  L.and_left(A.perfect(F.Cel, 1n+d, tc), rest1(n, d, tc, tg), g)

def g_r1(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +g: {repf(n, d, tc, tg) == True{} : Bool}) -> {rest1(n, d, tc, tg) == True{} : Bool}:
  L.and_right(A.perfect(F.Cel, 1n+d, tc), rest1(n, d, tc, tg), g)

def g_pg(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +g: {repf(n, d, tc, tg) == True{} : Bool}) -> {A.perfect(F.Cel, d, tg) == True{} : Bool}:
  L.and_left(A.perfect(F.Cel, d, tg), rest2(n, d, tc, tg), g_r1(n, d, tc, tg, g))

def g_r2(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +g: {repf(n, d, tc, tg) == True{} : Bool}) -> {rest2(n, d, tc, tg) == True{} : Bool}:
  L.and_right(A.perfect(F.Cel, d, tg), rest2(n, d, tc, tg), g_r1(n, d, tc, tg, g))

def g_lt(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +g: {repf(n, d, tc, tg) == True{} : Bool}) -> {Nat.is_lt(1n+d, 32n) == True{} : Bool}:
  L.and_left(Nat.is_lt(1n+d, 32n), rest3(n, d, tc, tg), g_r2(n, d, tc, tg, g))

def g_ltg(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +g: {repf(n, d, tc, tg) == True{} : Bool}) -> {Nat.is_lt(d, 32n) == True{} : Bool}:
  N.lt_trans(d, 1n+d, 32n, N.lt_succ(d), g_lt(n, d, tc, tg, g))

def g_r3(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +g: {repf(n, d, tc, tg) == True{} : Bool}) -> {rest3(n, d, tc, tg) == True{} : Bool}:
  L.and_right(Nat.is_lt(1n+d, 32n), rest3(n, d, tc, tg), g_r2(n, d, tc, tg, g))

def g_cap(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +g: {repf(n, d, tc, tg) == True{} : Bool}) -> {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}:
  L.and_left(Nat.is_le(n, SC.pow2(d)), MD.goods(mtree(d, tc, tg)), g_r3(n, d, tc, tg, g))

def g_good(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +g: {repf(n, d, tc, tg) == True{} : Bool}) -> {MD.goods(mtree(d, tc, tg)) == True{} : Bool}:
  L.and_right(Nat.is_le(n, SC.pow2(d)), MD.goods(mtree(d, tc, tg)), g_r3(n, d, tc, tg, g))

def g_mk(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +a: {A.perfect(F.Cel, 1n+d, tc) == True{} : Bool}, +b: {A.perfect(F.Cel, d, tg) == True{} : Bool}, +c: {Nat.is_lt(1n+d, 32n) == True{} : Bool}, +e: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}, +f: {MD.goods(mtree(d, tc, tg)) == True{} : Bool}) -> {repf(n, d, tc, tg) == True{} : Bool}:
  L.and_intro(A.perfect(F.Cel, 1n+d, tc), rest1(n, d, tc, tg), a,
    L.and_intro(A.perfect(F.Cel, d, tg), rest2(n, d, tc, tg), b,
      L.and_intro(Nat.is_lt(1n+d, 32n), rest3(n, d, tc, tg), c,
        L.and_intro(Nat.is_le(n, SC.pow2(d)), MD.goods(mtree(d, tc, tg)), e, f))))

# The whole block [0, 2^d) fits the value region, which is what every walk
# lemma of walk.bend asks for.
def whole(+d: Nat) -> {Nat.is_le(Nat.add(0n, SC.pow2(d)), SC.pow2(d)) == True{} : Bool}:
  N.le_refl(SC.pow2(d))

def cells_len(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +g: {repf(n, d, tc, tg) == True{} : Bool}) -> {SC.length(U32, AR.cl(tc)) == SC.pow2(1n+d) : Nat}:
  AR.cl_length(1n+d, tc, g_pf(n, d, tc, tg, g))

def tags_len(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +g: {repf(n, d, tc, tg) == True{} : Bool}) -> {SC.length(U32, AR.cl(tg)) == SC.pow2(d) : Nat}:
  AR.cl_length(d, tg, g_pg(n, d, tc, tg, g))

def mt_perfect(+d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>) -> {MD.perfect(d, mtree(d, tc, tg)) == True{} : Bool}:
  W.tree_perfect(AR.cl(tc), AR.cl(tg), d, d, 0n)

def vals_len(+d: Nat, +t: TN.Node, +pf: {MD.perfect(d, t) == True{} : Bool}) -> {SC.length(U32, MD.vals(t)) == SC.pow2(d) : Nat}:
  %W.vsc(d) : {SC.length(U32, MD.vals(t)) == _ : Nat}
  MD.vals_length(d, t, pf)

def n_le_len(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +g: {repf(n, d, tc, tg) == True{} : Bool}) -> {Nat.is_le(n, SC.length(U32, MD.vals(mtree(d, tc, tg)))) == True{} : Bool}:
  L.subst(Nat, q => {Nat.is_le(n, q) == True{} : Bool}, SC.pow2(d), SC.length(U32, MD.vals(mtree(d, tc, tg))),
    Equal.sym(Nat, SC.length(U32, MD.vals(mtree(d, tc, tg))), SC.pow2(d), vals_len(d, mtree(d, tc, tg), mt_perfect(d, tc, tg))), g_cap(n, d, tc, tg, g))

def len_model(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>, +g: {repf(n, d, tc, tg) == True{} : Bool}) -> {SC.length(U32, SC.take(U32, MD.vals(mtree(d, tc, tg)), n)) == n : Nat}:
  LL.sc_length_take(U32, MD.vals(mtree(d, tc, tg)), n, n_le_len(n, d, tc, tg, g))

# ---- the shadow of a live tree is unique ----

def burn_any(xs: List<F.Cel>) -> {F.burn_list(xs) == Unit{} : Unit}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      burn_any(t)

def dispose_ok(+n: Nat, +d: Nat, +tc: A.Tree<F.Cel>, +tg: A.Tree<F.Cel>) -> {F.dispose(real(Sh{n, d, tc, tg})) == Unit{} : Unit}:
  {==}

def npick(+v: Nat, u: Unit) -> Nat:
  match u:
    case Unit{}:
      v

def tpick(t: A.Tree<F.Cel>, u: Unit) -> A.Tree<F.Cel>:
  match u:
    case Unit{}:
      t

def f_len(f: F.SegTree) -> Nat:
  match f:
    case F.ST{+n, d, b, c, g}:
      npick(npick(n, F.burn(c)), F.burn(g))

def f_depth(f: F.SegTree) -> Nat:
  match f:
    case F.ST{n, +d, b, c, g}:
      npick(npick(d, F.burn(c)), F.burn(g))

def f_cells(f: F.SegTree) -> A.Tree<F.Cel>:
  match f:
    case F.ST{n, d, b, c, g}:
      tpick(A.freeze(F.Cel, c), F.burn(g))

def f_tags(f: F.SegTree) -> A.Tree<F.Cel>:
  match f:
    case F.ST{n, d, b, c, g}:
      tpick(A.freeze(F.Cel, g), F.burn(c))

def sh_len(sh: Sh) -> Nat:
  match sh:
    case Sh{n, d, c, g}:
      n

def sh_depth(sh: Sh) -> Nat:
  match sh:
    case Sh{n, d, c, g}:
      d

def sh_cells(sh: Sh) -> A.Tree<F.Cel>:
  match sh:
    case Sh{n, d, c, g}:
      c

def sh_tags(sh: Sh) -> A.Tree<F.Cel>:
  match sh:
    case Sh{n, d, c, g}:
      g

def real_len(+sh: Sh) -> {f_len(real(sh)) == sh_len(sh) : Nat}:
  match sh:
    case Sh{+n, d, c, g}:
      {==}

def real_depth(+sh: Sh) -> {f_depth(real(sh)) == sh_depth(sh) : Nat}:
  match sh:
    case Sh{n, +d, c, g}:
      {==}

def real_cells(+sh: Sh) -> {f_cells(real(sh)) == sh_cells(sh) : A.Tree<F.Cel>}:
  match sh:
    case Sh{n, d, +c, g}:
      A.freeze_thaw(F.Cel, c)

def real_tags(+sh: Sh) -> {f_tags(real(sh)) == sh_tags(sh) : A.Tree<F.Cel>}:
  match sh:
    case Sh{n, d, c, +g}:
      A.freeze_thaw(F.Cel, g)

def sh_eta(+sh: Sh) -> {sh == Sh{sh_len(sh), sh_depth(sh), sh_cells(sh), sh_tags(sh)} : Sh}:
  match sh:
    case Sh{n, d, c, g}:
      {==}

def real_inj_parts(+a: Sh, +b: Sh, +e: {real(a) == real(b) : F.SegTree}) -> {Sh{sh_len(a), sh_depth(a), sh_cells(a), sh_tags(a)} == Sh{sh_len(b), sh_depth(b), sh_cells(b), sh_tags(b)} : Sh}:
  %real_len(a) : {Sh{_, sh_depth(a), sh_cells(a), sh_tags(a)} == Sh{sh_len(b), sh_depth(b), sh_cells(b), sh_tags(b)} : Sh}
  %real_depth(a) : {Sh{f_len(real(a)), _, sh_cells(a), sh_tags(a)} == Sh{sh_len(b), sh_depth(b), sh_cells(b), sh_tags(b)} : Sh}
  %real_cells(a) : {Sh{f_len(real(a)), f_depth(real(a)), _, sh_tags(a)} == Sh{sh_len(b), sh_depth(b), sh_cells(b), sh_tags(b)} : Sh}
  %real_tags(a) : {Sh{f_len(real(a)), f_depth(real(a)), f_cells(real(a)), _} == Sh{sh_len(b), sh_depth(b), sh_cells(b), sh_tags(b)} : Sh}
  %real_len(b) : {Sh{f_len(real(a)), f_depth(real(a)), f_cells(real(a)), f_tags(real(a))} == Sh{_, sh_depth(b), sh_cells(b), sh_tags(b)} : Sh}
  %real_depth(b) : {Sh{f_len(real(a)), f_depth(real(a)), f_cells(real(a)), f_tags(real(a))} == Sh{f_len(real(b)), _, sh_cells(b), sh_tags(b)} : Sh}
  %real_cells(b) : {Sh{f_len(real(a)), f_depth(real(a)), f_cells(real(a)), f_tags(real(a))} == Sh{f_len(real(b)), f_depth(real(b)), _, sh_tags(b)} : Sh}
  %real_tags(b) : {Sh{f_len(real(a)), f_depth(real(a)), f_cells(real(a)), f_tags(real(a))} == Sh{f_len(real(b)), f_depth(real(b)), f_cells(real(b)), _} : Sh}
  Equal.cong(F.SegTree, Sh, s => Sh{f_len(s), f_depth(s), f_cells(s), f_tags(s)}, real(a), real(b), e)

def real_inj(+a: Sh, +b: Sh, +e: {real(a) == real(b) : F.SegTree}) -> {a == b : Sh}:
  Equal.trans(Sh, a, Sh{sh_len(a), sh_depth(a), sh_cells(a), sh_tags(a)}, b,
    sh_eta(a),
    Equal.trans(Sh, Sh{sh_len(a), sh_depth(a), sh_cells(a), sh_tags(a)}, Sh{sh_len(b), sh_depth(b), sh_cells(b), sh_tags(b)}, b,
      real_inj_parts(a, b, e),
      Equal.sym(Sh, b, Sh{sh_len(b), sh_depth(b), sh_cells(b), sh_tags(b)}, sh_eta(b))))
