import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as A
import ../lib/flat.bend as FL
import ../../spec/common.bend as SC
import ../../spec/u32seq.bend as Q
import ../../src/fenwick_tree.bend as F
import ./model.bend as M
import ./tree.bend as T
import ./arr.bend as AR
import ./walk.bend as W

# The shadow of a Fenwick tree.
#
# `Base.Array` is linear, so -- exactly as in proofs/dynamic_array,
# proofs/bitset and proofs/union_find -- every law is stated about
# `real(sh)`, the structure whose cell array is built from a Data mirror
# tree, and each law names the shadow the operation lands on.
#
#   abstraction  model(sh)   the first n values of the tree the cells realise
#   invariant    good(sh)    the cell array is a perfect tree of depth d+1
#                (so every index is a representable U32), n <= 2^d, and every
#                internal cell holds the exact sum of its block's left half.

type Sh is Data:
  Sh{len: Nat, depth: Nat, cells: A.Tree<F.Cel>}

# `base` is derived, not stored in the shadow: a real tree built by the
# constructors always carries 2^depth there, and every law below is about a
# `real(sh)` that does.
def real(sh: Sh) -> F.Fenwick:
  match sh:
    case Sh{+n, +d, t}:
      F.FT{n, d, SC.pow2(d), A.thaw(F.Cel, t)}

# The model tree the whole cell array realises.
def mtree(+d: Nat, +t: A.Tree<F.Cel>) -> M.Node:
  W.tree_of(AR.cl(t), d, d, 0n)

def mt(sh: Sh) -> M.Node:
  match sh:
    case Sh{n, +d, +t}:
      mtree(d, t)

def model(sh: Sh) -> List<&2, U32>:
  match sh:
    case Sh{+n, +d, +t}:
      SC.take(U32, T.leaves(mtree(d, t)), n)

def repf(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>) -> Bool:
  Bool.and(A.perfect(F.Cel, 1n+d, t), Bool.and(Nat.is_lt(1n+d, 32n), Bool.and(Nat.is_le(n, SC.pow2(d)), T.goodf(mtree(d, t)))))

def good(sh: Sh) -> Bool:
  match sh:
    case Sh{+n, +d, +t}:
      repf(n, d, t)

def g_pf(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>, +g: {repf(n, d, t) == True{} : Bool}) -> {A.perfect(F.Cel, 1n+d, t) == True{} : Bool}:
  L.and_left(A.perfect(F.Cel, 1n+d, t), Bool.and(Nat.is_lt(1n+d, 32n), Bool.and(Nat.is_le(n, SC.pow2(d)), T.goodf(mtree(d, t)))), g)

def g_rest(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>, +g: {repf(n, d, t) == True{} : Bool}) -> {Bool.and(Nat.is_lt(1n+d, 32n), Bool.and(Nat.is_le(n, SC.pow2(d)), T.goodf(mtree(d, t)))) == True{} : Bool}:
  L.and_right(A.perfect(F.Cel, 1n+d, t), Bool.and(Nat.is_lt(1n+d, 32n), Bool.and(Nat.is_le(n, SC.pow2(d)), T.goodf(mtree(d, t)))), g)

def g_lt(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>, +g: {repf(n, d, t) == True{} : Bool}) -> {Nat.is_lt(1n+d, 32n) == True{} : Bool}:
  L.and_left(Nat.is_lt(1n+d, 32n), Bool.and(Nat.is_le(n, SC.pow2(d)), T.goodf(mtree(d, t))), g_rest(n, d, t, g))

def g_rest2(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>, +g: {repf(n, d, t) == True{} : Bool}) -> {Bool.and(Nat.is_le(n, SC.pow2(d)), T.goodf(mtree(d, t))) == True{} : Bool}:
  L.and_right(Nat.is_lt(1n+d, 32n), Bool.and(Nat.is_le(n, SC.pow2(d)), T.goodf(mtree(d, t))), g_rest(n, d, t, g))

def g_cap(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>, +g: {repf(n, d, t) == True{} : Bool}) -> {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}:
  L.and_left(Nat.is_le(n, SC.pow2(d)), T.goodf(mtree(d, t)), g_rest2(n, d, t, g))

def g_good(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>, +g: {repf(n, d, t) == True{} : Bool}) -> {T.goodf(mtree(d, t)) == True{} : Bool}:
  L.and_right(Nat.is_le(n, SC.pow2(d)), T.goodf(mtree(d, t)), g_rest2(n, d, t, g))

def g_mk(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>, +a: {A.perfect(F.Cel, 1n+d, t) == True{} : Bool}, +b: {Nat.is_lt(1n+d, 32n) == True{} : Bool}, +c: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}, +e: {T.goodf(mtree(d, t)) == True{} : Bool}) -> {repf(n, d, t) == True{} : Bool}:
  L.and_intro(A.perfect(F.Cel, 1n+d, t), Bool.and(Nat.is_lt(1n+d, 32n), Bool.and(Nat.is_le(n, SC.pow2(d)), T.goodf(mtree(d, t)))), a,
    L.and_intro(Nat.is_lt(1n+d, 32n), Bool.and(Nat.is_le(n, SC.pow2(d)), T.goodf(mtree(d, t))), b,
      L.and_intro(Nat.is_le(n, SC.pow2(d)), T.goodf(mtree(d, t)), c, e)))

# The whole block [0, 2^d) fits the value region, which is what every walk
# lemma of walk.bend asks for.
def whole(+d: Nat) -> {Nat.is_le(Nat.add(0n, SC.pow2(d)), SC.pow2(d)) == True{} : Bool}:
  N.le_refl(SC.pow2(d))

def base_ok(+d: Nat) -> {SC.pow2(d) == SC.pow2(d) : Nat}:
  {==}

def root_h(+d: Nat) -> {Nat.div(SC.pow2(d), 2n) == FL.hof(d) : Nat}:
  {==}

def cells_len(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>, +g: {repf(n, d, t) == True{} : Bool}) -> {SC.length(U32, AR.cl(t)) == SC.pow2(1n+d) : Nat}:
  AR.cl_length(1n+d, t, g_pf(n, d, t, g))

def mt_perfect(+d: Nat, +t: A.Tree<F.Cel>) -> {T.perfect(d, mtree(d, t)) == True{} : Bool}:
  W.tree_perfect(AR.cl(t), d, d, 0n)

def n_le_len(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>, +g: {repf(n, d, t) == True{} : Bool}) -> {Nat.is_le(n, SC.length(U32, T.leaves(mtree(d, t)))) == True{} : Bool}:
  L.subst(Nat, q => {Nat.is_le(n, q) == True{} : Bool}, SC.pow2(d), SC.length(U32, T.leaves(mtree(d, t))),
    Equal.sym(Nat, SC.length(U32, T.leaves(mtree(d, t))), SC.pow2(d), T.leaves_length(d, mtree(d, t), mt_perfect(d, t))), g_cap(n, d, t, g))

def len_model(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>, +g: {repf(n, d, t) == True{} : Bool}) -> {SC.length(U32, SC.take(U32, T.leaves(mtree(d, t)), n)) == n : Nat}:
  LL.sc_length_take(U32, T.leaves(mtree(d, t)), n, n_le_len(n, d, t, g))

# ---- the shadow of a live tree is unique ----

def burn_any(xs: List<F.Cel>) -> {F.burn_list(xs) == Unit{} : Unit}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      burn_any(t)

def dispose_ok(+n: Nat, +d: Nat, +t: A.Tree<F.Cel>) -> {F.dispose(real(Sh{n, d, t})) == Unit{} : Unit}:
  {==}

def npick(+v: Nat, u: Unit) -> Nat:
  match u:
    case Unit{}:
      v

def tpick(t: A.Tree<F.Cel>, u: Unit) -> A.Tree<F.Cel>:
  match u:
    case Unit{}:
      t

def f_len(f: F.Fenwick) -> Nat:
  match f:
    case F.FT{+n, d, b, a}:
      npick(n, F.burn(a))

def f_depth(f: F.Fenwick) -> Nat:
  match f:
    case F.FT{n, +d, b, a}:
      npick(d, F.burn(a))

def f_tree(f: F.Fenwick) -> A.Tree<F.Cel>:
  match f:
    case F.FT{n, d, b, a}:
      A.freeze(F.Cel, a)

def sh_len(sh: Sh) -> Nat:
  match sh:
    case Sh{n, d, t}:
      n

def sh_depth(sh: Sh) -> Nat:
  match sh:
    case Sh{n, d, t}:
      d

def sh_tree(sh: Sh) -> A.Tree<F.Cel>:
  match sh:
    case Sh{n, d, t}:
      t

def real_len(+sh: Sh) -> {f_len(real(sh)) == sh_len(sh) : Nat}:
  match sh:
    case Sh{+n, d, t}:
      {==}

def real_depth(+sh: Sh) -> {f_depth(real(sh)) == sh_depth(sh) : Nat}:
  match sh:
    case Sh{n, +d, t}:
      {==}

def real_tree(+sh: Sh) -> {f_tree(real(sh)) == sh_tree(sh) : A.Tree<F.Cel>}:
  match sh:
    case Sh{n, d, +t}:
      A.freeze_thaw(F.Cel, t)

def sh_eta(+sh: Sh) -> {sh == Sh{sh_len(sh), sh_depth(sh), sh_tree(sh)} : Sh}:
  match sh:
    case Sh{n, d, t}:
      {==}

def real_inj_parts(+a: Sh, +b: Sh, +e: {real(a) == real(b) : F.Fenwick}) -> {Sh{sh_len(a), sh_depth(a), sh_tree(a)} == Sh{sh_len(b), sh_depth(b), sh_tree(b)} : Sh}:
  %real_len(a) : {Sh{_, sh_depth(a), sh_tree(a)} == Sh{sh_len(b), sh_depth(b), sh_tree(b)} : Sh}
  %real_depth(a) : {Sh{f_len(real(a)), _, sh_tree(a)} == Sh{sh_len(b), sh_depth(b), sh_tree(b)} : Sh}
  %real_tree(a) : {Sh{f_len(real(a)), f_depth(real(a)), _} == Sh{sh_len(b), sh_depth(b), sh_tree(b)} : Sh}
  %real_len(b) : {Sh{f_len(real(a)), f_depth(real(a)), f_tree(real(a))} == Sh{_, sh_depth(b), sh_tree(b)} : Sh}
  %real_depth(b) : {Sh{f_len(real(a)), f_depth(real(a)), f_tree(real(a))} == Sh{f_len(real(b)), _, sh_tree(b)} : Sh}
  %real_tree(b) : {Sh{f_len(real(a)), f_depth(real(a)), f_tree(real(a))} == Sh{f_len(real(b)), f_depth(real(b)), _} : Sh}
  Equal.cong(F.Fenwick, Sh, s => Sh{f_len(s), f_depth(s), f_tree(s)}, real(a), real(b), e)

def real_inj(+a: Sh, +b: Sh, +e: {real(a) == real(b) : F.Fenwick}) -> {a == b : Sh}:
  Equal.trans(Sh, a, Sh{sh_len(a), sh_depth(a), sh_tree(a)}, b,
    sh_eta(a),
    Equal.trans(Sh, Sh{sh_len(a), sh_depth(a), sh_tree(a)}, Sh{sh_len(b), sh_depth(b), sh_tree(b)}, b,
      real_inj_parts(a, b, e),
      Equal.sym(Sh, b, Sh{sh_len(b), sh_depth(b), sh_tree(b)}, sh_eta(b))))
