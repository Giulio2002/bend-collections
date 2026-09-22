import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as A
import ../spec/common.bend as SC
import ../../src/containers/bitset.bend as B
import ./model.bend as MD
import ./walk.bend as WK
import ./listx.bend as LX
import ./arr.bend as AR
import ./loops.bend as LP

# The word-wise combination loop `zip_go` of src/bitset.bend writes
# `word_op(k, a[q], b[q])` into a[q] for every q, leaving b alone. Three
# steps: the loop follows the mirror tree `ztree`, the slot list of that tree
# is the list-level `zl`, and `zl` over the whole array is exactly
# `MD.zip_words`.

def ztree(m: Nat, +k: B.WordOp, +d: Nat, +ta: A.Tree<B.Wd>, +tb: A.Tree<B.Wd>, +q: Nat) -> A.Tree<B.Wd>:
  match m:
    case 0n:
      ta
    case 1n+ +r:
      ztree(r, k, d, A.upd(B.Wd, d, ta, q, B.W{B.word_op(k, WK.nthw(AR.ws(ta), q), WK.nthw(AR.ws(tb), q))}), tb, 1n+q)

def zl(m: Nat, +k: B.WordOp, +q: Nat, +xs: List<&2, U32>, +ys: List<&2, U32>) -> List<&2, U32>:
  match m:
    case 0n:
      xs
    case 1n+ +r:
      zl(r, k, 1n+q, SC.update(U32, xs, q, B.word_op(k, WK.nthw(xs, q), WK.nthw(ys, q))), ys)

# ---- the loop follows the mirror tree ----

def zip_go_ok(m: Nat, +k: B.WordOp, +d: Nat, +ta: A.Tree<B.Wd>, +tb: A.Tree<B.Wd>, +q: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pa: {A.perfect(B.Wd, d, ta) == True{} : Bool}, +pb: {A.perfect(B.Wd, d, tb) == True{} : Bool}, +hm: {Nat.is_le(Nat.add(q, m), SC.pow2(d)) == True{} : Bool}) -> {B.zip_go(m, (A.thaw(B.Wd, ta), A.thaw(B.Wd, tb)), k, d, q) == (A.thaw(B.Wd, ztree(m, k, d, ta, tb, q)), A.thaw(B.Wd, tb)) : Array<B.Wd> & Array<B.Wd>}:
  match m:
    case 0n:
      {==}
    case 1n+ +r:
      +hq = LP.lt_of_sum(q, r, SC.pow2(d), hm)
      +w = B.word_op(k, WK.nthw(AR.ws(ta), q), WK.nthw(AR.ws(tb), q))
      %Equal.sym(Array<B.Wd> & U32, B.read(A.thaw(B.Wd, ta), d, q), (A.thaw(B.Wd, ta), WK.nthw(AR.ws(ta), q)), AR.read_ok(d, ta, q, hd, hq, pa)) : {B.zip_go(r, B.zip_write(_, B.read(A.thaw(B.Wd, tb), d, q), k, d, q), k, d, 1n+q) == (A.thaw(B.Wd, ztree(1n+r, k, d, ta, tb, q)), A.thaw(B.Wd, tb)) : Array<B.Wd> & Array<B.Wd>}
      %Equal.sym(Array<B.Wd> & U32, B.read(A.thaw(B.Wd, tb), d, q), (A.thaw(B.Wd, tb), WK.nthw(AR.ws(tb), q)), AR.read_ok(d, tb, q, hd, hq, pb)) : {B.zip_go(r, B.zip_write((A.thaw(B.Wd, ta), WK.nthw(AR.ws(ta), q)), _, k, d, q), k, d, 1n+q) == (A.thaw(B.Wd, ztree(1n+r, k, d, ta, tb, q)), A.thaw(B.Wd, tb)) : Array<B.Wd> & Array<B.Wd>}
      %Equal.sym(Array<B.Wd>, B.write(A.thaw(B.Wd, ta), d, q, w), A.thaw(B.Wd, A.upd(B.Wd, d, ta, q, B.W{w})), AR.write_ok(d, ta, q, w, hd, hq, pa)) : {B.zip_go(r, (_, A.thaw(B.Wd, tb)), k, d, 1n+q) == (A.thaw(B.Wd, ztree(1n+r, k, d, ta, tb, q)), A.thaw(B.Wd, tb)) : Array<B.Wd> & Array<B.Wd>}
      zip_go_ok(r, k, d, A.upd(B.Wd, d, ta, q, B.W{w}), tb, 1n+q, hd, AR.upd_perfect(d, ta, q, w, pa), pb, LP.le_of_sum(q, r, SC.pow2(d), hm))

# ---- the slots of the mirror tree are the list-level zl ----

def ztree_ws(m: Nat, +k: B.WordOp, +d: Nat, +ta: A.Tree<B.Wd>, +tb: A.Tree<B.Wd>, +q: Nat, +pa: {A.perfect(B.Wd, d, ta) == True{} : Bool}, +hm: {Nat.is_le(Nat.add(q, m), SC.pow2(d)) == True{} : Bool}) -> {AR.ws(ztree(m, k, d, ta, tb, q)) == zl(m, k, q, AR.ws(ta), AR.ws(tb)) : List<&2, U32>}:
  match m:
    case 0n:
      {==}
    case 1n+ +r:
      +hq = LP.lt_of_sum(q, r, SC.pow2(d), hm)
      +w = B.word_op(k, WK.nthw(AR.ws(ta), q), WK.nthw(AR.ws(tb), q))
      %AR.ws_upd(d, ta, q, w, hq, pa) : {AR.ws(ztree(r, k, d, A.upd(B.Wd, d, ta, q, B.W{w}), tb, 1n+q)) == zl(r, k, 1n+q, _, AR.ws(tb)) : List<&2, U32>}
      ztree_ws(r, k, d, A.upd(B.Wd, d, ta, q, B.W{w}), tb, 1n+q, AR.upd_perfect(d, ta, q, w, pa), LP.le_of_sum(q, r, SC.pow2(d), hm))

def ztree_perfect(m: Nat, +k: B.WordOp, +d: Nat, +ta: A.Tree<B.Wd>, +tb: A.Tree<B.Wd>, +q: Nat, +pa: {A.perfect(B.Wd, d, ta) == True{} : Bool}) -> {A.perfect(B.Wd, d, ztree(m, k, d, ta, tb, q)) == True{} : Bool}:
  match m:
    case 0n:
      pa
    case 1n+ +r:
      +w = B.word_op(k, WK.nthw(AR.ws(ta), q), WK.nthw(AR.ws(tb), q))
      ztree_perfect(r, k, d, A.upd(B.Wd, d, ta, q, B.W{w}), tb, 1n+q, AR.upd_perfect(d, ta, q, w, pa))

# ---- zl is zip_words on the whole list ----

def zl_spec(m: Nat, +k: B.WordOp, +q: Nat, +xs: List<&2, U32>, +ys: List<&2, U32>, +hx: {Nat.add(q, m) == SC.length(U32, xs) : Nat}, +hy: {SC.length(U32, ys) == SC.length(U32, xs) : Nat}) -> {zl(m, k, q, xs, ys) == SC.append(U32, SC.take(U32, xs, q), MD.zip_words(k, SC.drop(U32, xs, q), SC.drop(U32, ys, q))) : List<&2, U32>}:
  match m:
    case 0n:
      +eq = Equal.trans(Nat, q, Nat.add(q, 0n), SC.length(U32, xs), Equal.sym(Nat, Nat.add(q, 0n), q, N.add_zero(q)), hx)
      %Equal.sym(Nat, q, SC.length(U32, xs), eq) : {xs == SC.append(U32, SC.take(U32, xs, _), MD.zip_words(k, SC.drop(U32, xs, _), SC.drop(U32, ys, _))) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, SC.drop(U32, xs, SC.length(U32, xs)), Nil{}, LX.drop_all(U32, xs)) : {xs == SC.append(U32, SC.take(U32, xs, SC.length(U32, xs)), MD.zip_words(k, _, SC.drop(U32, ys, SC.length(U32, xs)))) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, SC.take(U32, xs, SC.length(U32, xs)), xs, LX.take_all(U32, xs)) : {xs == SC.append(U32, _, Nil{}) : List<&2, U32>}
      Equal.sym(List<&2, U32>, SC.append(U32, xs, Nil{}), xs, LL.append_nil(U32, xs))
    case 1n+ +r:
      +hq = LP.lt_of_sum(q, r, SC.length(U32, xs), N.eq_le(Nat.add(q, 1n+r), SC.length(U32, xs), hx))
      +hqy = L.subst(Nat, z => {Nat.is_lt(q, z) == True{} : Bool}, SC.length(U32, xs), SC.length(U32, ys), Equal.sym(Nat, SC.length(U32, ys), SC.length(U32, xs), hy), hq)
      +a = WK.nthw(xs, q)
      +b = WK.nthw(ys, q)
      +w = B.word_op(k, a, b)
      +ex = Equal.sym(List<&2, U32>, SC.drop(U32, xs, q), Con{a, SC.drop(U32, xs, 1n+q)}, LX.drop_cons(U32, xs, q, a, WK.nthw_nth(xs, q, hq)))
      +ey = Equal.sym(List<&2, U32>, SC.drop(U32, ys, q), Con{b, SC.drop(U32, ys, 1n+q)}, LX.drop_cons(U32, ys, q, b, WK.nthw_nth(ys, q, hqy)))
      +len2 = Equal.trans(Nat, SC.length(U32, SC.update(U32, xs, q, w)), SC.length(U32, xs), Nat.add(1n+q, r),
        LL.length_update(U32, xs, q, w),
        Equal.sym(Nat, Nat.add(1n+q, r), SC.length(U32, xs), Equal.trans(Nat, Nat.add(1n+q, r), Nat.add(q, 1n+r), SC.length(U32, xs), Equal.sym(Nat, Nat.add(q, 1n+r), Nat.add(1n+q, r), N.add_succ(q, r)), hx)))
      +ih = zl_spec(r, k, 1n+q, SC.update(U32, xs, q, w), ys, Equal.sym(Nat, SC.length(U32, SC.update(U32, xs, q, w)), Nat.add(1n+q, r), len2),
        Equal.trans(Nat, SC.length(U32, ys), SC.length(U32, xs), SC.length(U32, SC.update(U32, xs, q, w)), hy, Equal.sym(Nat, SC.length(U32, SC.update(U32, xs, q, w)), SC.length(U32, xs), LL.length_update(U32, xs, q, w))))
      %ex : {zl(1n+r, k, q, xs, ys) == SC.append(U32, SC.take(U32, xs, q), MD.zip_words(k, _, SC.drop(U32, ys, q))) : List<&2, U32>}
      %ey : {zl(1n+r, k, q, xs, ys) == SC.append(U32, SC.take(U32, xs, q), MD.zip_words(k, Con{a, SC.drop(U32, xs, 1n+q)}, _)) : List<&2, U32>}
      %LL.snoc_append_cons(U32, SC.take(U32, xs, q), w, MD.zip_words(k, SC.drop(U32, xs, 1n+q), SC.drop(U32, ys, 1n+q))) : {zl(1n+r, k, q, xs, ys) == _ : List<&2, U32>}
      %LX.take_update_succ(U32, xs, q, w, hq) : {zl(1n+r, k, q, xs, ys) == SC.append(U32, _, MD.zip_words(k, SC.drop(U32, xs, 1n+q), SC.drop(U32, ys, 1n+q))) : List<&2, U32>}
      %LX.drop_update(U32, xs, q, w) : {zl(1n+r, k, q, xs, ys) == SC.append(U32, SC.take(U32, SC.update(U32, xs, q, w), 1n+q), MD.zip_words(k, _, SC.drop(U32, ys, 1n+q))) : List<&2, U32>}
      ih

def zl_edges(+k: B.WordOp, +xs: List<&2, U32>, +ys: List<&2, U32>) -> {SC.append(U32, SC.take(U32, xs, 0n), MD.zip_words(k, SC.drop(U32, xs, 0n), SC.drop(U32, ys, 0n))) == MD.zip_words(k, xs, ys) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, SC.take(U32, xs, 0n), Nil{}, LX.take_zero(U32, xs)) : {SC.append(U32, _, MD.zip_words(k, SC.drop(U32, xs, 0n), SC.drop(U32, ys, 0n))) == MD.zip_words(k, xs, ys) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, SC.drop(U32, xs, 0n), xs, LX.drop_zero(U32, xs)) : {MD.zip_words(k, _, SC.drop(U32, ys, 0n)) == MD.zip_words(k, xs, ys) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, SC.drop(U32, ys, 0n), ys, LX.drop_zero(U32, ys)) : {MD.zip_words(k, xs, _) == MD.zip_words(k, xs, ys) : List<&2, U32>}
  {==}

def zl_full(+k: B.WordOp, +xs: List<&2, U32>, +ys: List<&2, U32>, +hy: {SC.length(U32, ys) == SC.length(U32, xs) : Nat}) -> {zl(SC.length(U32, xs), k, 0n, xs, ys) == MD.zip_words(k, xs, ys) : List<&2, U32>}:
  Equal.trans(List<&2, U32>,
    zl(SC.length(U32, xs), k, 0n, xs, ys),
    SC.append(U32, SC.take(U32, xs, 0n), MD.zip_words(k, SC.drop(U32, xs, 0n), SC.drop(U32, ys, 0n))),
    MD.zip_words(k, xs, ys),
    zl_spec(SC.length(U32, xs), k, 0n, xs, ys, {==}, hy),
    zl_edges(k, xs, ys))
