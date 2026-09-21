import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/u32half.bend as H
import ../lib/array.bend as AR
import ../lib/array2.bend as A2
import ../../spec/common.bend as SC
import ../../src/graph.bend as G
import ./state.bend as ST
import ./shift.bend as SH
import ./search.bend as SE
import ./window.bend as W
import ./blk.bend as BK
import ./edge.bend as ED
import ./ops.bend as OP
import ./ext.bend as EX
import ./nbrs.bend as NB
import ../../spec/graph.bend as GS
import ../../types/graph.bend as E
import ../../types/balanced_search_tree.bend as BE

# `vertices_block` (src/graph.bend) is the BLOCK form of `vertices`: instead
# of consing the ascending vertex ids into a `List`, it copies the window
# ids[lo, hi) into slots [0, n) of a fresh block, n = hi - lo. This file
# proves that the block it produces holds exactly the list `vertices`
# returns, and that the graph comes back unchanged -- so the two public
# enumerations denote the same ordered sequence.
#
# The loop copies BACKWARDS: with k values still to place, the value read at
# ids[j] belongs in slot k-1 (because j = lo + k - 1), so the destination is
# the remaining count.

# ---- the mirror of vb_go ----

def wr(m: Nat, +xs: List<&2, U32>, +j: Nat, +d: Nat, bt: AR.Tree<U32>) -> AR.Tree<U32>:
  match m:
    case 0n:
      bt
    case 1n+ +p:
      wr(p, xs, Nat.sub(j, 1n), d, AR.upd(U32, d, bt, p, SH.val_at(xs, j)))

def wr_perfect(m: Nat, +xs: List<&2, U32>, +j: Nat, +d: Nat, +bt: AR.Tree<U32>, +pb: {AR.perfect(U32, d, bt) == True{} : Bool}) -> {AR.perfect(U32, d, wr(m, xs, j, d, bt)) == True{} : Bool}:
  match m:
    case 0n:
      pb
    case 1n+ +p:
      wr_perfect(p, xs, Nat.sub(j, 1n), d, AR.upd(U32, d, bt, p, SH.val_at(xs, j)), AR.upd_perfect(U32, d, bt, p, SH.val_at(xs, j), pb))

# ---- the loop refines the mirror ----

def vb_go0_fin(+blk: AR.Tree<U32>, +j: U32, +t: AR.Tree<U32>, +i: U32, s: Sigma<&1, &1, U32, x => {Array.get(U32, AR.thaw(U32, t), i) == (AR.thaw(U32, t), x) : Array<U32> & U32}>) -> {G.vb_go(0n, AR.thaw(U32, blk), j, Array.get(U32, AR.thaw(U32, t), i)) == (AR.thaw(U32, t), AR.thaw(U32, blk)) : Array<U32> & Array<U32>}:
  (x, e) = s
  %Equal.sym(Array<U32> & U32, Array.get(U32, AR.thaw(U32, t), i), (AR.thaw(U32, t), x), e) : {G.vb_go(0n, AR.thaw(U32, blk), j, _) == (AR.thaw(U32, t), AR.thaw(U32, blk)) : Array<U32> & Array<U32>}
  {==}

def vb_go0(+blk: AR.Tree<U32>, +j: U32, +d: Nat, +t: AR.Tree<U32>, +i: U32, +pf: {AR.perfect(U32, d, t) == True{} : Bool}) -> {G.vb_go(0n, AR.thaw(U32, blk), j, Array.get(U32, AR.thaw(U32, t), i)) == (AR.thaw(U32, t), AR.thaw(U32, blk)) : Array<U32> & Array<U32>}:
  vb_go0_fin(blk, j, t, i, BK.get_any(U32, d, t, i, pf))

# One write: Array.set at the destination slot p is `upd` on the mirror.
def set_step(+d: Nat, +bt: AR.Tree<U32>, +p: Nat, +x: U32, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hp: {Nat.is_lt(p, SC.pow2(d)) == True{} : Bool}, +pb: {AR.perfect(U32, d, bt) == True{} : Bool}) -> {Array.set(U32, AR.thaw(U32, bt), U32.from_nat(p), x) == AR.thaw(U32, AR.upd(U32, d, bt, p, x)) : Array<U32>}:
  +ep = U.to_nat_from_nat(p, d, N.lt_le(d, 32n, hd), hp)
  +hip = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, p, U32.to_nat(U32.from_nat(p)), Equal.sym(Nat, U32.to_nat(U32.from_nat(p)), p, ep), hp)
  +hyp = L.subst(Nat, z => {SC.nth(U32, AR.slots(U32, bt), z) == Some{SH.val_at(AR.slots(U32, bt), p)} : Maybe<&2, U32>}, p, U32.to_nat(U32.from_nat(p)), Equal.sym(Nat, U32.to_nat(U32.from_nat(p)), p, ep), SH.some_at(d, bt, p, pb, hp))
  %ep : {Array.set(U32, AR.thaw(U32, bt), U32.from_nat(p), x) == AR.thaw(U32, AR.upd(U32, d, bt, _, x)) : Array<U32>}
  AR.set(U32, d, bt, U32.from_nat(p), x, SH.val_at(AR.slots(U32, bt), p), hd, hip, hyp, pb)

def VbIH(+p: Nat, +d: Nat, +it: AR.Tree<U32>) -> Type:
  @+bt2: AR.Tree<U32> -> @+j2: Nat ->
  @+h1: {Nat.is_lt(j2, SC.pow2(d)) == True{} : Bool} ->
  @+h2: {Nat.is_le(p, 1n+j2) == True{} : Bool} ->
  @+h3: {Nat.is_le(p, SC.pow2(d)) == True{} : Bool} ->
  @+pb: {AR.perfect(U32, d, bt2) == True{} : Bool} ->
  {G.vb_go(p, AR.thaw(U32, bt2), U32.from_nat(j2), Array.get(U32, AR.thaw(U32, it), U32.from_nat(j2))) == (AR.thaw(U32, it), AR.thaw(U32, wr(p, AR.slots(U32, it), j2, d, bt2))) : Array<U32> & Array<U32>}

# After writing slot p: either nothing is left (the next read is discarded,
# even when j = 0 makes its index wrap), or slot j - 1 is in range.
def vb_go_succ(+p: Nat, +bt: AR.Tree<U32>, +j: Nat, +d: Nat, +it: AR.Tree<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pit: {AR.perfect(U32, d, it) == True{} : Bool}, +pb: {AR.perfect(U32, d, bt) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +hm: {Nat.is_le(1n+p, 1n+j) == True{} : Bool}, +hmd: {Nat.is_le(1n+p, SC.pow2(d)) == True{} : Bool}, ih: VbIH(p, d, it)) -> {G.vb_go(p, AR.thaw(U32, AR.upd(U32, d, bt, p, SH.val_at(AR.slots(U32, it), j))), U32.sub(U32.from_nat(j), 1), Array.get(U32, AR.thaw(U32, it), U32.sub(U32.from_nat(j), 1))) == (AR.thaw(U32, it), AR.thaw(U32, wr(1n+p, AR.slots(U32, it), j, d, bt))) : Array<U32> & Array<U32>}:
  match p:
    case 0n:
      vb_go0(AR.upd(U32, d, bt, 0n, SH.val_at(AR.slots(U32, it), j)), U32.sub(U32.from_nat(j), 1), d, it, U32.sub(U32.from_nat(j), 1), pit)
    case 1n+ +q:
      +nb = AR.upd(U32, d, bt, 1n+q, SH.val_at(AR.slots(U32, it), j))
      +pnb = AR.upd_perfect(U32, d, bt, 1n+q, SH.val_at(AR.slots(U32, it), j), pb)
      +j1 = Nat.sub(j, 1n)
      +h1 = N.le_trans(1n, 1n+q, j, N.le_add_right(1n, q), hm)
      +es = H.sub_bridge(j, 1n, d, N.lt_le(d, 32n, hd), hj, h1)
      +hj1 = N.le_lt_trans(j1, j, SC.pow2(d), H.sub_le(j, 1n), hj)
      +hm1 = N.le_trans(1n+q, j, 1n+j1, hm, SE.le_of_pred_le(j, j1, N.le_refl(j1)))
      +hmd1 = N.le_trans(1n+q, 2n+q, SC.pow2(d), N.le_succ(1n+q), hmd)
      %Equal.sym(U32, U32.sub(U32.from_nat(j), 1), U32.from_nat(j1), es) : {G.vb_go(1n+q, AR.thaw(U32, nb), _, Array.get(U32, AR.thaw(U32, it), _)) == (AR.thaw(U32, it), AR.thaw(U32, wr(2n+q, AR.slots(U32, it), j, d, bt))) : Array<U32> & Array<U32>}
      ih(nb, j1, hj1, hm1, hmd1, pnb)

def vb_go_ok(+m: Nat, +bt: AR.Tree<U32>, +j: Nat, +d: Nat, +it: AR.Tree<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pit: {AR.perfect(U32, d, it) == True{} : Bool}, +pb: {AR.perfect(U32, d, bt) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +hm: {Nat.is_le(m, 1n+j) == True{} : Bool}, +hmd: {Nat.is_le(m, SC.pow2(d)) == True{} : Bool}) -> {G.vb_go(m, AR.thaw(U32, bt), U32.from_nat(j), Array.get(U32, AR.thaw(U32, it), U32.from_nat(j))) == (AR.thaw(U32, it), AR.thaw(U32, wr(m, AR.slots(U32, it), j, d, bt))) : Array<U32> & Array<U32>}:
  match m:
    case 0n:
      vb_go0(bt, U32.from_nat(j), d, it, U32.from_nat(j), pit)
    case 1n+p:
      +hp = N.succ_le_lt(p, SC.pow2(d), hmd)
      %NB.get_at(j, d, it, hd, pit, hj) : {G.vb_go(1n+p, AR.thaw(U32, bt), U32.from_nat(j), _) == (AR.thaw(U32, it), AR.thaw(U32, wr(1n+p, AR.slots(U32, it), j, d, bt))) : Array<U32> & Array<U32>}
      %Equal.sym(Array<U32>, Array.set(U32, AR.thaw(U32, bt), U32.from_nat(p), SH.val_at(AR.slots(U32, it), j)), AR.thaw(U32, AR.upd(U32, d, bt, p, SH.val_at(AR.slots(U32, it), j))), set_step(d, bt, p, SH.val_at(AR.slots(U32, it), j), hd, hp, pb)) : {G.vb_go(p, _, U32.sub(U32.from_nat(j), 1), Array.get(U32, AR.thaw(U32, it), U32.sub(U32.from_nat(j), 1))) == (AR.thaw(U32, it), AR.thaw(U32, wr(1n+p, AR.slots(U32, it), j, d, bt))) : Array<U32> & Array<U32>}
      vb_go_succ(p, bt, j, d, it, hd, pit, pb, hj, hm, hmd, bt2 => j2 => h1 => h2 => h3 => pb2 => vb_go_ok(p, bt2, j2, d, it, hd, pit, pb2, h1, h2, h3))

# ---- what the mirror writes ----

def succ_pred(j: Nat, +h: {Nat.is_le(1n, j) == True{} : Bool}) -> {1n+Nat.sub(j, 1n) == j : Nat}:
  match j:
    case 0n:
      Empty.absurd({1n+Nat.sub(0n, 1n) == 0n : Nat}, L.false_true(h))
    case 1n+ +q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.sub(q, 0n), q, N.sub_zero(q))

# Slots at or above m are untouched: the loop only writes slots m-1 .. 0.
def wr_above(m: Nat, +xs: List<&2, U32>, +j: Nat, +d: Nat, +bt: AR.Tree<U32>, +i: Nat, +h: {Nat.is_le(m, i) == True{} : Bool}, +hmd: {Nat.is_le(m, SC.pow2(d)) == True{} : Bool}, +pb: {AR.perfect(U32, d, bt) == True{} : Bool}) -> {SC.nth(U32, AR.slots(U32, wr(m, xs, j, d, bt)), i) == SC.nth(U32, AR.slots(U32, bt), i) : Maybe<&2, U32>}:
  match m:
    case 0n:
      {==}
    case 1n+ +p:
      +v = SH.val_at(xs, j)
      +hp = N.succ_le_lt(p, SC.pow2(d), hmd)
      +hpi = N.succ_le_lt(p, i, h)
      Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, wr(p, xs, Nat.sub(j, 1n), d, AR.upd(U32, d, bt, p, v))), i), SC.nth(U32, AR.slots(U32, AR.upd(U32, d, bt, p, v)), i), SC.nth(U32, AR.slots(U32, bt), i),
        wr_above(p, xs, Nat.sub(j, 1n), d, AR.upd(U32, d, bt, p, v), i, N.lt_le(p, i, hpi), N.lt_le(p, SC.pow2(d), hp), AR.upd_perfect(U32, d, bt, p, v, pb)),
        Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, AR.upd(U32, d, bt, p, v)), i), SC.nth(U32, SC.update(U32, AR.slots(U32, bt), p, v), i), SC.nth(U32, AR.slots(U32, bt), i),
          Equal.cong(List<&2, U32>, Maybe<&2, U32>, z => SC.nth(U32, z, i), AR.slots(U32, AR.upd(U32, d, bt, p, v)), SC.update(U32, AR.slots(U32, bt), p, v), AR.upd_slots(U32, d, bt, p, v, hp, pb)),
          LL.nth_update_other(U32, AR.slots(U32, bt), p, i, v, N.is_eq_lt(p, i, hpi))))

# Slot p of the block after the last write holds xs[j].
def wr_top(+p: Nat, +xs: List<&2, U32>, +j: Nat, +d: Nat, +bt: AR.Tree<U32>, +hp: {Nat.is_lt(p, SC.pow2(d)) == True{} : Bool}, +pb: {AR.perfect(U32, d, bt) == True{} : Bool}) -> {SC.nth(U32, AR.slots(U32, wr(1n+p, xs, j, d, bt)), p) == Some{SH.val_at(xs, j)} : Maybe<&2, U32>}:
  +v = SH.val_at(xs, j)
  +hlen = L.subst(Nat, z => {Nat.is_lt(p, z) == True{} : Bool}, SC.pow2(d), SC.length(U32, AR.slots(U32, bt)), Equal.sym(Nat, SC.length(U32, AR.slots(U32, bt)), SC.pow2(d), AR.slots_length(U32, d, bt, pb)), hp)
  Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, wr(p, xs, Nat.sub(j, 1n), d, AR.upd(U32, d, bt, p, v))), p), SC.nth(U32, AR.slots(U32, AR.upd(U32, d, bt, p, v)), p), Some{v},
    wr_above(p, xs, Nat.sub(j, 1n), d, AR.upd(U32, d, bt, p, v), p, N.le_refl(p), N.lt_le(p, SC.pow2(d), hp), AR.upd_perfect(U32, d, bt, p, v, pb)),
    Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, AR.upd(U32, d, bt, p, v)), p), SC.nth(U32, SC.update(U32, AR.slots(U32, bt), p, v), p), Some{v},
      Equal.cong(List<&2, U32>, Maybe<&2, U32>, z => SC.nth(U32, z, p), AR.slots(U32, AR.upd(U32, d, bt, p, v)), SC.update(U32, AR.slots(U32, bt), p, v), AR.upd_slots(U32, d, bt, p, v, hp, pb)),
      LL.nth_update_same(U32, AR.slots(U32, bt), p, v, hlen)))

def WrIH(+p: Nat, +xs: List<&2, U32>, +d: Nat) -> Type:
  @+s: Nat -> @+j2: Nat -> @+bt2: AR.Tree<U32> -> @+i: Nat ->
  @+ej: {Nat.add(s, p) == 1n+j2 : Nat} ->
  @+hi: {Nat.is_lt(i, p) == True{} : Bool} ->
  @+hmd: {Nat.is_le(p, SC.pow2(d)) == True{} : Bool} ->
  @+pb: {AR.perfect(U32, d, bt2) == True{} : Bool} ->
  {SC.nth(U32, AR.slots(U32, wr(p, xs, j2, d, bt2)), i) == Some{SH.val_at(xs, Nat.add(s, i))} : Maybe<&2, U32>}

def wr_pick(+p: Nat, +xs: List<&2, U32>, +s: Nat, +j: Nat, +d: Nat, +bt: AR.Tree<U32>, +i: Nat, +es: {Nat.add(s, p) == j : Nat}, +hi: {Nat.is_lt(i, 1n+p) == True{} : Bool}, +hmd: {Nat.is_le(1n+p, SC.pow2(d)) == True{} : Bool}, +pb: {AR.perfect(U32, d, bt) == True{} : Bool}, b: Bool, +eb: {Nat.is_lt(i, p) == b : Bool}, ih: WrIH(p, xs, d)) -> {SC.nth(U32, AR.slots(U32, wr(1n+p, xs, j, d, bt)), i) == Some{SH.val_at(xs, Nat.add(s, i))} : Maybe<&2, U32>}:
  match b:
    case True{}:
      +hp = N.succ_le_lt(p, SC.pow2(d), hmd)
      +hip = eb
      +hp1 = N.le_trans(1n, p, j, N.lt_succ_le_succ(0n, p, N.le_lt_trans(0n, i, p, N.zero_le(i), hip)), L.subst(Nat, z => {Nat.is_le(p, z) == True{} : Bool}, Nat.add(s, p), j, es, L.subst(Nat, z => {Nat.is_le(p, z) == True{} : Bool}, Nat.add(p, s), Nat.add(s, p), N.add_comm(p, s), N.le_add_right(p, s))))
      +ej = L.subst(Nat, z => {Nat.add(s, p) == z : Nat}, j, 1n+Nat.sub(j, 1n), Equal.sym(Nat, 1n+Nat.sub(j, 1n), j, succ_pred(j, hp1)), es)
      ih(s, Nat.sub(j, 1n), AR.upd(U32, d, bt, p, SH.val_at(xs, j)), i, ej, hip, N.lt_le(p, SC.pow2(d), hp), AR.upd_perfect(U32, d, bt, p, SH.val_at(xs, j), pb))
    case False{}:
      +hp = N.succ_le_lt(p, SC.pow2(d), hmd)
      +eip = N.le_antisym(i, p, N.lt_succ_le(i, p, hi), N.not_lt_le(i, p, eb))
      %Equal.sym(Nat, i, p, eip) : {SC.nth(U32, AR.slots(U32, wr(1n+p, xs, j, d, bt)), _) == Some{SH.val_at(xs, Nat.add(s, _))} : Maybe<&2, U32>}
      %Equal.sym(Nat, Nat.add(s, p), j, es) : {SC.nth(U32, AR.slots(U32, wr(1n+p, xs, j, d, bt)), p) == Some{SH.val_at(xs, _)} : Maybe<&2, U32>}
      wr_top(p, xs, j, d, bt, hp, pb)

# Slot i < m of the block holds xs[s + i], where s + m = 1 + j.
def wr_nth(m: Nat, +xs: List<&2, U32>, +s: Nat, +j: Nat, +d: Nat, +bt: AR.Tree<U32>, +i: Nat, +ej: {Nat.add(s, m) == 1n+j : Nat}, +hi: {Nat.is_lt(i, m) == True{} : Bool}, +hmd: {Nat.is_le(m, SC.pow2(d)) == True{} : Bool}, +pb: {AR.perfect(U32, d, bt) == True{} : Bool}) -> {SC.nth(U32, AR.slots(U32, wr(m, xs, j, d, bt)), i) == Some{SH.val_at(xs, Nat.add(s, i))} : Maybe<&2, U32>}:
  match m:
    case 0n:
      Empty.absurd({SC.nth(U32, AR.slots(U32, bt), i) == Some{SH.val_at(xs, Nat.add(s, i))} : Maybe<&2, U32>}, N.lt_zero_absurd(i, hi))
    case 1n+ +p:
      +es = N.succ_inj(Nat.add(s, p), j, Equal.trans(Nat, 1n+Nat.add(s, p), Nat.add(s, 1n+p), 1n+j, Equal.sym(Nat, Nat.add(s, 1n+p), 1n+Nat.add(s, p), N.add_succ(s, p)), ej))
      wr_pick(p, xs, s, j, d, bt, i, es, hi, hmd, pb, Nat.is_lt(i, p), {==},
        s2 => j2 => bt2 => i2 => ej2 => hi2 => hmd2 => pb2 => wr_nth(p, xs, s2, j2, d, bt2, i2, ej2, hi2, hmd2, pb2))

# ---- two windows that agree slot by slot are equal ----

def add_left_succ(+a: Nat, i: Nat) -> {Nat.add(1n+a, i) == 1n+Nat.add(a, i) : Nat}:
  match i:
    case 0n:
      Equal.trans(Nat, Nat.add(1n+a, 0n), 1n+a, 1n+Nat.add(a, 0n),
        N.add_zero(1n+a),
        Equal.cong(Nat, Nat, z => 1n+z, a, Nat.add(a, 0n), Equal.sym(Nat, Nat.add(a, 0n), a, N.add_zero(a))))
    case 1n+ +q:
      Equal.trans(Nat, Nat.add(1n+a, 1n+q), 1n+Nat.add(1n+a, q), 1n+Nat.add(a, 1n+q),
        N.add_succ(1n+a, q),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(1n+a, q), Nat.add(a, 1n+q),
          Equal.trans(Nat, Nat.add(1n+a, q), 1n+Nat.add(a, q), Nat.add(a, 1n+q),
            add_left_succ(a, q),
            Equal.sym(Nat, Nat.add(a, 1n+q), 1n+Nat.add(a, q), N.add_succ(a, q)))))

def zero_add(+k: Nat) -> {Nat.add(0n, k) == k : Nat}:
  Equal.trans(Nat, Nat.add(0n, k), Nat.add(k, 0n), k, N.add_comm(0n, k), N.add_zero(k))

# ---- the window of the produced block is the window of the ids ----

def blk_win_go(m: Nat, +k: Nat, +xs: List<&2, U32>, +lo: Nat, +j: Nat, +d: Nat, +bt: AR.Tree<U32>, +t: Nat, +ej: {Nat.add(lo, k) == 1n+j : Nat}, +hmd: {Nat.is_le(k, SC.pow2(d)) == True{} : Bool}, +pb: {AR.perfect(U32, d, bt) == True{} : Bool}, +hsum: {Nat.add(t, m) == k : Nat}, +hxlen: {Nat.is_le(Nat.add(lo, k), SC.length(U32, xs)) == True{} : Bool}) -> {ST.win(U32, AR.slots(U32, wr(k, xs, j, d, bt)), t, m) == ST.win(U32, xs, Nat.add(lo, t), m) : List<&2, U32>}:
  match m:
    case 0n:
      EX.win_zero2(AR.slots(U32, wr(k, xs, j, d, bt)), xs, t, Nat.add(lo, t))
    case 1n+ +q:
      +ys = AR.slots(U32, wr(k, xs, j, d, bt))
      +htk = L.subst(Nat, z => {Nat.is_lt(t, z) == True{} : Bool}, Nat.add(t, 1n+q), k, hsum, L.subst(Nat, z => {Nat.is_lt(t, z) == True{} : Bool}, 1n+Nat.add(t, q), Nat.add(t, 1n+q), Equal.sym(Nat, Nat.add(t, 1n+q), 1n+Nat.add(t, q), N.add_succ(t, q)), N.le_lt_trans(t, Nat.add(t, q), 1n+Nat.add(t, q), N.le_add_right(t, q), N.lt_succ(Nat.add(t, q)))))
      +hlotk = N.lt_le_trans(Nat.add(lo, t), Nat.add(lo, k), SC.length(U32, xs), N.succ_le_lt(Nat.add(lo, t), Nat.add(lo, k), L.subst(Nat, z => {Nat.is_le(z, Nat.add(lo, k)) == True{} : Bool}, Nat.add(lo, 1n+t), 1n+Nat.add(lo, t), N.add_succ(lo, t), N.le_add_left(1n+t, k, lo, N.lt_succ_le_succ(t, k, htk)))), hxlen)
      +hylen = L.subst(Nat, z => {Nat.is_lt(t, z) == True{} : Bool}, SC.pow2(d), SC.length(U32, ys), Equal.sym(Nat, SC.length(U32, ys), SC.pow2(d), AR.slots_length(U32, d, wr(k, xs, j, d, bt), wr_perfect(k, xs, j, d, bt, pb))), N.lt_le_trans(t, k, SC.pow2(d), htk, hmd))
      +hval = Equal.trans(Maybe<&2, U32>, SC.nth(U32, ys, t), Some{SH.val_at(xs, Nat.add(lo, t))}, SC.nth(U32, xs, Nat.add(lo, t)),
        wr_nth(k, xs, lo, j, d, bt, t, ej, htk, hmd, pb),
        Equal.sym(Maybe<&2, U32>, SC.nth(U32, xs, Nat.add(lo, t)), Some{SH.val_at(xs, Nat.add(lo, t))}, NB.val_some(xs, Nat.add(lo, t), hlotk)))
      +hsum1 = Equal.trans(Nat, Nat.add(1n+t, q), 1n+Nat.add(t, q), k, add_left_succ(t, q), Equal.trans(Nat, 1n+Nat.add(t, q), Nat.add(t, 1n+q), k, Equal.sym(Nat, Nat.add(t, 1n+q), 1n+Nat.add(t, q), N.add_succ(t, q)), hsum))
      EX.win_step(ys, xs, t, Nat.add(lo, t), q, hylen, hlotk, hval,
        L.subst(Nat, z => {ST.win(U32, ys, 1n+t, q) == ST.win(U32, xs, z, q) : List<&2, U32>}, Nat.add(lo, 1n+t), 1n+Nat.add(lo, t), N.add_succ(lo, t),
          blk_win_go(q, k, xs, lo, j, d, bt, 1n+t, ej, hmd, pb, hsum1, hxlen)))

def blk_win(+k: Nat, +xs: List<&2, U32>, +lo: Nat, +j: Nat, +d: Nat, +bt: AR.Tree<U32>, +ej: {Nat.add(lo, k) == 1n+j : Nat}, +hmd: {Nat.is_le(k, SC.pow2(d)) == True{} : Bool}, +pb: {AR.perfect(U32, d, bt) == True{} : Bool}, +hxlen: {Nat.is_le(Nat.add(lo, k), SC.length(U32, xs)) == True{} : Bool}) -> {ST.win(U32, AR.slots(U32, wr(k, xs, j, d, bt)), 0n, k) == ST.win(U32, xs, lo, k) : List<&2, U32>}:
  %N.add_zero(lo) : {ST.win(U32, AR.slots(U32, wr(k, xs, j, d, bt)), 0n, k) == ST.win(U32, xs, _, k) : List<&2, U32>}
  blk_win_go(k, k, xs, lo, j, d, bt, 0n, ej, hmd, pb, zero_add(k), hxlen)

# ---- the public operation ----

def vb_case(+lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +hd: {Nat.is_lt(depth, 32n) == True{} : Bool}, +pf: {AR.perfect(U32, depth, it) == True{} : Bool}, +hlo: {Nat.is_le(lo, hi) == True{} : Bool}, +hcap: {Nat.is_le(hi, SC.pow2(depth)) == True{} : Bool}, k: Nat, +ek: {Nat.sub(hi, lo) == k : Nat}) -> {G.vb_go(k, G.zeros(depth), U32.sub(U32.from_nat(hi), 1), Array.get(U32, AR.thaw(U32, it), U32.sub(U32.from_nat(hi), 1))) == (AR.thaw(U32, it), AR.thaw(U32, wr(k, AR.slots(U32, it), Nat.sub(hi, 1n), depth, AR.trep(U32, depth, 0)))) : Array<U32> & Array<U32>}:
  match k:
    case 0n:
      %Equal.sym(Array<U32>, Array.new(U32, depth, 0), AR.thaw(U32, AR.trep(U32, depth, 0)), AR.new(U32, depth, 0)) : {G.vb_go(0n, _, U32.sub(U32.from_nat(hi), 1), Array.get(U32, AR.thaw(U32, it), U32.sub(U32.from_nat(hi), 1))) == (AR.thaw(U32, it), AR.thaw(U32, AR.trep(U32, depth, 0))) : Array<U32> & Array<U32>}
      vb_go0(AR.trep(U32, depth, 0), U32.sub(U32.from_nat(hi), 1), depth, it, U32.sub(U32.from_nat(hi), 1), pf)
    case 1n+ +p:
      %Equal.sym(Array<U32>, Array.new(U32, depth, 0), AR.thaw(U32, AR.trep(U32, depth, 0)), AR.new(U32, depth, 0)) : {G.vb_go(1n+p, _, U32.sub(U32.from_nat(hi), 1), Array.get(U32, AR.thaw(U32, it), U32.sub(U32.from_nat(hi), 1))) == (AR.thaw(U32, it), AR.thaw(U32, wr(1n+p, AR.slots(U32, it), Nat.sub(hi, 1n), depth, AR.trep(U32, depth, 0)))) : Array<U32> & Array<U32>}
      +j = Nat.add(lo, p)
      +el = NB.last_idx(lo, hi, p, ek, hlo)
      +eh = W.window_end(lo, hi, 1n+p, Equal.sym(Nat, Nat.sub(hi, lo), 1n+p, ek), hlo)
      +h1 = L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, Nat.add(lo, 1n+p), hi, eh, L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, 1n+Nat.add(lo, p), Nat.add(lo, 1n+p), Equal.sym(Nat, Nat.add(lo, 1n+p), 1n+Nat.add(lo, p), N.add_succ(lo, p)), N.le_add_right(1n, Nat.add(lo, p))))
      +hj = N.lt_le_trans(j, hi, SC.pow2(depth), L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, Nat.add(lo, 1n+p), hi, eh, L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, 1n+j, Nat.add(lo, 1n+p), Equal.sym(Nat, Nat.add(lo, 1n+p), 1n+j, N.add_succ(lo, p)), N.lt_succ(j))), hcap)
      +hmd = N.le_trans(1n+p, hi, SC.pow2(depth), L.subst(Nat, z => {Nat.is_le(z, hi) == True{} : Bool}, Nat.sub(hi, lo), 1n+p, ek, H.sub_le(hi, lo)), hcap)
      +hm = L.subst(Nat, z => {Nat.is_le(p, z) == True{} : Bool}, Nat.add(p, lo), Nat.add(lo, p), N.add_comm(p, lo), N.le_add_right(p, lo))
      +es = Equal.trans(U32, U32.sub(U32.from_nat(hi), 1), U32.from_nat(Nat.sub(hi, 1n)), U32.from_nat(j),
        H.sub_bridge(hi, 1n, 1n+depth, N.lt_succ_le_succ(depth, 32n, hd), N.le_lt_trans(hi, SC.pow2(depth), SC.pow2(1n+depth), hcap, N.pow2_lt_succ(depth)), h1),
        Equal.cong(Nat, U32, z => U32.from_nat(z), Nat.sub(hi, 1n), j, el))
      L.subst(U32, z => {G.vb_go(1n+p, AR.thaw(U32, AR.trep(U32, depth, 0)), z, Array.get(U32, AR.thaw(U32, it), z)) == (AR.thaw(U32, it), AR.thaw(U32, wr(1n+p, AR.slots(U32, it), Nat.sub(hi, 1n), depth, AR.trep(U32, depth, 0)))) : Array<U32> & Array<U32>}, U32.from_nat(j), U32.sub(U32.from_nat(hi), 1), Equal.sym(U32, U32.sub(U32.from_nat(hi), 1), U32.from_nat(j), es),
        L.subst(Nat, z => {G.vb_go(1n+p, AR.thaw(U32, AR.trep(U32, depth, 0)), U32.from_nat(j), Array.get(U32, AR.thaw(U32, it), U32.from_nat(j))) == (AR.thaw(U32, it), AR.thaw(U32, wr(1n+p, AR.slots(U32, it), z, depth, AR.trep(U32, depth, 0)))) : Array<U32> & Array<U32>}, j, Nat.sub(hi, 1n), Equal.sym(Nat, Nat.sub(hi, 1n), j, el),
          vb_go_ok(1n+p, AR.trep(U32, depth, 0), j, depth, it, hd, pf, AR.trep_perfect(U32, depth, 0), hj, hm, hmd)))

# vertices_block returns the graph unchanged and the block the mirror builds.
def vertices_block_ok(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {G.vertices_block(ST.real(ST.Sh{dir, lo, hi, depth, it, at})) == G.VB{ST.real(ST.Sh{dir, lo, hi, depth, it, at}), AR.thaw(U32, wr(Nat.sub(hi, lo), AR.slots(U32, it), Nat.sub(hi, 1n), depth, AR.trep(U32, depth, 0))), U32.sub(U32.from_nat(hi), U32.from_nat(lo))} : G.VBlk}:
  +k = Nat.sub(hi, lo)
  +hd = ED.dep32(dir, lo, hi, depth, it, at, h)
  +hlo = OP.g_lohi(dir, lo, hi, depth, it, at, h)
  +hcap = OP.g_cap(dir, lo, hi, depth, it, at, h)
  +hb = N.lt_succ_le_succ(depth, 32n, hd)
  +hhi = N.le_lt_trans(hi, SC.pow2(depth), SC.pow2(1n+depth), hcap, N.pow2_lt_succ(depth))
  +ek = Equal.trans(Nat, U32.to_nat(U32.sub(U32.from_nat(hi), U32.from_nat(lo))), U32.to_nat(U32.from_nat(k)), k,
    Equal.cong(U32, Nat, z => U32.to_nat(z), U32.sub(U32.from_nat(hi), U32.from_nat(lo)), U32.from_nat(k), H.sub_bridge(hi, lo, 1n+depth, hb, hhi, hlo)),
    U.to_nat_from_nat(k, 1n+depth, hb, N.le_lt_trans(k, hi, SC.pow2(1n+depth), H.sub_le(hi, lo), hhi)))
  %Equal.sym(Nat, U32.to_nat(U32.sub(U32.from_nat(hi), U32.from_nat(lo))), k, ek) : {G.vb_fin(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, A2.thaw2(at), U32.sub(U32.from_nat(hi), U32.from_nat(lo)), G.vb_go(_, G.zeros(depth), U32.sub(U32.from_nat(hi), 1), Array.get(U32, AR.thaw(U32, it), U32.sub(U32.from_nat(hi), 1)))) == G.VB{ST.real(ST.Sh{dir, lo, hi, depth, it, at}), AR.thaw(U32, wr(k, AR.slots(U32, it), Nat.sub(hi, 1n), depth, AR.trep(U32, depth, 0))), U32.sub(U32.from_nat(hi), U32.from_nat(lo))} : G.VBlk}
  Equal.cong(Array<U32> & Array<U32>, G.VBlk, z => G.vb_fin(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, A2.thaw2(at), U32.sub(U32.from_nat(hi), U32.from_nat(lo)), z),
    G.vb_go(k, G.zeros(depth), U32.sub(U32.from_nat(hi), 1), Array.get(U32, AR.thaw(U32, it), U32.sub(U32.from_nat(hi), 1))),
    (AR.thaw(U32, it), AR.thaw(U32, wr(k, AR.slots(U32, it), Nat.sub(hi, 1n), depth, AR.trep(U32, depth, 0)))),
    vb_case(lo, hi, depth, it, hd, OP.g_ids(dir, lo, hi, depth, it, at, h), hlo, hcap, k, {==}))

# The block window is the ascending id window.
def vb_seq_case(+lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +hd: {Nat.is_lt(depth, 32n) == True{} : Bool}, +pf: {AR.perfect(U32, depth, it) == True{} : Bool}, +hlo: {Nat.is_le(lo, hi) == True{} : Bool}, +hcap: {Nat.is_le(hi, SC.pow2(depth)) == True{} : Bool}, k: Nat, +ek: {Nat.sub(hi, lo) == k : Nat}) -> {ST.win(U32, AR.slots(U32, wr(k, AR.slots(U32, it), Nat.sub(hi, 1n), depth, AR.trep(U32, depth, 0))), 0n, k) == ST.win(U32, AR.slots(U32, it), lo, k) : List<&2, U32>}:
  match k:
    case 0n:
      EX.win_zero2(AR.slots(U32, AR.trep(U32, depth, 0)), AR.slots(U32, it), 0n, lo)
    case 1n+ +p:
      +j = Nat.add(lo, p)
      +el = NB.last_idx(lo, hi, p, ek, hlo)
      +eh = W.window_end(lo, hi, 1n+p, Equal.sym(Nat, Nat.sub(hi, lo), 1n+p, ek), hlo)
      +ej = Equal.trans(Nat, Nat.add(lo, 1n+p), hi, 1n+Nat.sub(hi, 1n), eh, Equal.sym(Nat, 1n+Nat.sub(hi, 1n), hi, succ_pred(hi, L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, Nat.add(lo, 1n+p), hi, eh, L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, 1n+j, Nat.add(lo, 1n+p), Equal.sym(Nat, Nat.add(lo, 1n+p), 1n+j, N.add_succ(lo, p)), N.le_add_right(1n, j))))))
      +hmd = N.le_trans(1n+p, hi, SC.pow2(depth), L.subst(Nat, z => {Nat.is_le(z, hi) == True{} : Bool}, Nat.sub(hi, lo), 1n+p, ek, H.sub_le(hi, lo)), hcap)
      +hxlen = L.subst(Nat, z => {Nat.is_le(Nat.add(lo, 1n+p), z) == True{} : Bool}, SC.pow2(depth), SC.length(U32, AR.slots(U32, it)), Equal.sym(Nat, SC.length(U32, AR.slots(U32, it)), SC.pow2(depth), AR.slots_length(U32, depth, it, pf)), L.subst(Nat, z => {Nat.is_le(z, SC.pow2(depth)) == True{} : Bool}, hi, Nat.add(lo, 1n+p), Equal.sym(Nat, Nat.add(lo, 1n+p), hi, eh), hcap))
      blk_win(1n+p, AR.slots(U32, it), lo, Nat.sub(hi, 1n), depth, AR.trep(U32, depth, 0), ej, hmd, AR.trep_perfect(U32, depth, 0), hxlen)

# The block enumeration and the list enumeration are the SAME sequence.
def vertices_block_seq(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {ST.win(U32, AR.slots(U32, wr(Nat.sub(hi, lo), AR.slots(U32, it), Nat.sub(hi, 1n), depth, AR.trep(U32, depth, 0))), 0n, Nat.sub(hi, lo)) == Pair.snd(G.Graph, List<&2, U32>, G.vertices(ST.real(ST.Sh{dir, lo, hi, depth, it, at}))) : List<&2, U32>}:
  +k = Nat.sub(hi, lo)
  +xs = AR.slots(U32, it)
  +ks = ST.win(U32, xs, lo, k)
  +bw = ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, k)
  +hd = ED.dep32(dir, lo, hi, depth, it, at, h)
  +hlo = OP.g_lohi(dir, lo, hi, depth, it, at, h)
  +hcap = OP.g_cap(dir, lo, hi, depth, it, at, h)
  +hlen = Equal.trans(Nat, SC.length(U32, ks), k, SC.length(AR.Tree<U32>, bw),
    ED.win_len(U32, xs, lo, k, ED.win_fits(U32, depth, it, lo, hi, OP.g_ids(dir, lo, hi, depth, it, at, h), hlo, hcap)),
    Equal.sym(Nat, SC.length(AR.Tree<U32>, bw), k, ED.win_len(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, k, ED.win_fits(AR.Tree<U32>, depth, at, lo, hi, OP.g_adj(dir, lo, hi, depth, it, at, h), hlo, hcap))))
  Equal.trans(List<&2, U32>, ST.win(U32, AR.slots(U32, wr(k, xs, Nat.sub(hi, 1n), depth, AR.trep(U32, depth, 0))), 0n, k), ks, Pair.snd(G.Graph, List<&2, U32>, G.vertices(ST.real(ST.Sh{dir, lo, hi, depth, it, at}))),
    vb_seq_case(lo, hi, depth, it, hd, OP.g_ids(dir, lo, hi, depth, it, at, h), hlo, hcap, k, {==}),
    Equal.trans(List<&2, U32>, ks, GS.keys(List<&2, BE.Entry<U32, Unit>>, ST.amodel(ks, bw)), Pair.snd(G.Graph, List<&2, U32>, G.vertices(ST.real(ST.Sh{dir, lo, hi, depth, it, at}))),
      Equal.sym(List<&2, U32>, GS.keys(List<&2, BE.Entry<U32, Unit>>, ST.amodel(ks, bw)), ks, NB.gkeys_amodel(ks, bw, hlen)),
      Equal.cong(G.Graph & List<&2, U32>, List<&2, U32>, z => Pair.snd(G.Graph, List<&2, U32>, z), (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.keys(List<&2, BE.Entry<U32, Unit>>, ST.amodel(ks, bw))), G.vertices(ST.real(ST.Sh{dir, lo, hi, depth, it, at})),
        Equal.sym(G.Graph & List<&2, U32>, G.vertices(ST.real(ST.Sh{dir, lo, hi, depth, it, at})), (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.keys(List<&2, BE.Entry<U32, Unit>>, ST.amodel(ks, bw))), NB.vertices_ok(dir, lo, hi, depth, it, at, h)))))

# ---- the two facts as one record, for the public entry point ----

def Built(+sh: ST.Shadow) -> Type:
  match sh:
    case ST.Sh{+dir, +lo, +hi, +depth, +it, +at}:
      Sigma<&1, &1,
        {G.vertices_block(ST.real(ST.Sh{dir, lo, hi, depth, it, at})) == G.VB{ST.real(ST.Sh{dir, lo, hi, depth, it, at}), AR.thaw(U32, wr(Nat.sub(hi, lo), AR.slots(U32, it), Nat.sub(hi, 1n), depth, AR.trep(U32, depth, 0))), U32.sub(U32.from_nat(hi), U32.from_nat(lo))} : G.VBlk},
        _ => {ST.win(U32, AR.slots(U32, wr(Nat.sub(hi, lo), AR.slots(U32, it), Nat.sub(hi, 1n), depth, AR.trep(U32, depth, 0))), 0n, Nat.sub(hi, lo)) == Pair.snd(G.Graph, List<&2, U32>, G.vertices(ST.real(ST.Sh{dir, lo, hi, depth, it, at}))) : List<&2, U32>}>

def built(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> Built(ST.Sh{dir, lo, hi, depth, it, at}):
  (vertices_block_ok(dir, lo, hi, depth, it, at, h), vertices_block_seq(dir, lo, hi, depth, it, at, h))
