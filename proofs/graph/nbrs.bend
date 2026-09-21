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
import ./lb.bend as LB
import ../../spec/graph.bend as GS
import ../../types/graph.bend as E
import ../../types/balanced_search_tree.bend as BE

# The backwards read loop `nb_go` (neighbors, vertices) against the window
# it produces.

# ---- a window grows by one element at its end ----

def take_snoc(-A: Data, +ys: List<&2, A>, +p: Nat, +y: A, +h: {SC.nth(A, ys, p) == Some{y} : Maybe<&2, A>}) -> {SC.take(A, ys, 1n+p) == SC.append(A, SC.take(A, ys, p), Con{y, Nil{}}) : List<&2, A>}:
  match ys p:
    case Nil{} p0:
      Empty.absurd({SC.take(A, Nil{}, 1n+p0) == SC.append(A, SC.take(A, Nil{}, p0), Con{y, Nil{}}) : List<&2, A>}, L.false_true(Equal.cong(Maybe<&2, A>, Bool, mm => Maybe.is_some(&2, A, mm), None{}, Some{y}, h)))
    case Con{+a, +t} 0n:
      +ea = Equal.cong(Maybe<&2, A>, A, m => L.some_value(A, m, a), Some{a}, Some{y}, h)
      Equal.trans(List<&2, A>, Con{a, SC.take(A, t, 0n)}, Con{a, Nil{}}, Con{y, Nil{}},
        LL.cons_cong(A, a, SC.take(A, t, 0n), Nil{}, LL.sc_take_zero(A, t)),
        Equal.cong(A, List<&2, A>, z => Con{z, Nil{}}, a, y, ea))
    case Con{+a, +t} 1n+q:
      LL.cons_cong(A, a, SC.take(A, t, 1n+q), SC.append(A, SC.take(A, t, q), Con{y, Nil{}}), take_snoc(A, t, q, y, h))

def win_snoc(-A: Data, +xs: List<&2, A>, +s: Nat, +p: Nat, +y: A, +h: {SC.nth(A, xs, Nat.add(s, p)) == Some{y} : Maybe<&2, A>}) -> {ST.win(A, xs, s, 1n+p) == SC.append(A, ST.win(A, xs, s, p), Con{y, Nil{}}) : List<&2, A>}:
  take_snoc(A, SC.drop(A, xs, s), p, y, Equal.trans(Maybe<&2, A>, SC.nth(A, SC.drop(A, xs, s), p), SC.nth(A, xs, Nat.add(s, p)), Some{y}, W.nth_drop(A, xs, s, p), h))

# ---- the mirror of the read loop ----

# Read xs[j], xs[j-1], ..., m values, consing each onto acc.
def rd(m: Nat, +xs: List<&2, U32>, +j: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match m:
    case 0n:
      acc
    case 1n+p:
      rd(p, xs, Nat.sub(j, 1n), Con{SH.val_at(xs, j), acc})

def sub_one_add(+s: Nat, +p: Nat) -> {Nat.sub(Nat.add(s, 1n+p), 1n) == Nat.add(s, p) : Nat}:
  %Equal.sym(Nat, Nat.add(s, 1n+p), 1n+Nat.add(s, p), N.add_succ(s, p)) : {Nat.sub(_, 1n) == Nat.add(s, p) : Nat}
  N.sub_zero(Nat.add(s, p))

def val_some(+xs: List<&2, U32>, +i: Nat, +hl: {Nat.is_lt(i, SC.length(U32, xs)) == True{} : Bool}) -> {SC.nth(U32, xs, i) == Some{SH.val_at(xs, i)} : Maybe<&2, U32>}:
  ED.nth_some(U32, xs, i, 0, hl, SC.nth(U32, xs, i), {==})

# Reading m values ending at s + m gives the window [s+1, s+1+m).
def rd_win(+xs: List<&2, U32>, +s: Nat, +m: Nat, +acc: List<&2, U32>, +hl: {Nat.is_le(Nat.add(1n+s, m), SC.length(U32, xs)) == True{} : Bool}) -> {rd(m, xs, Nat.add(s, m), acc) == SC.append(U32, ST.win(U32, xs, 1n+s, m), acc) : List<&2, U32>}:
  match m:
    case 0n:
      L.subst(List<&2, U32>, z => {acc == SC.append(U32, z, acc) : List<&2, U32>}, Nil{}, ST.win(U32, xs, 1n+s, 0n), Equal.sym(List<&2, U32>, ST.win(U32, xs, 1n+s, 0n), Nil{}, LL.sc_take_zero(U32, SC.drop(U32, xs, 1n+s))), {==})
    case 1n+p:
      +x = SH.val_at(xs, Nat.add(s, 1n+p))
      +w = ST.win(U32, xs, 1n+s, p)
      +ex = Equal.trans(Nat, Nat.add(s, 1n+p), 1n+Nat.add(s, p), Nat.add(1n+s, p), N.add_succ(s, p), {==})
      +hle = L.subst(Nat, z => {Nat.is_le(z, SC.length(U32, xs)) == True{} : Bool}, Nat.add(1n+s, 1n+p), 1n+Nat.add(1n+s, p), N.add_succ(1n+s, p), hl)
      +hlp = N.le_trans(Nat.add(1n+s, p), 1n+Nat.add(1n+s, p), SC.length(U32, xs), N.lt_le(Nat.add(1n+s, p), 1n+Nat.add(1n+s, p), N.lt_succ(Nat.add(1n+s, p))), hle)
      +hx = L.subst(Nat, z => {SC.nth(U32, xs, z) == Some{x} : Maybe<&2, U32>}, Nat.add(s, 1n+p), Nat.add(1n+s, p), ex,
        val_some(xs, Nat.add(s, 1n+p), L.subst(Nat, z => {Nat.is_lt(z, SC.length(U32, xs)) == True{} : Bool}, Nat.add(1n+s, p), Nat.add(s, 1n+p), Equal.sym(Nat, Nat.add(s, 1n+p), Nat.add(1n+s, p), ex),
          N.succ_le_lt(Nat.add(1n+s, p), SC.length(U32, xs), hle))))
      %Equal.sym(Nat, Nat.sub(Nat.add(s, 1n+p), 1n), Nat.add(s, p), sub_one_add(s, p)) : {rd(p, xs, _, Con{x, acc}) == SC.append(U32, ST.win(U32, xs, 1n+s, 1n+p), acc) : List<&2, U32>}
      Equal.trans(List<&2, U32>, rd(p, xs, Nat.add(s, p), Con{x, acc}), SC.append(U32, w, Con{x, acc}), SC.append(U32, ST.win(U32, xs, 1n+s, 1n+p), acc),
        rd_win(xs, s, p, Con{x, acc}, hlp),
        Equal.sym(List<&2, U32>, SC.append(U32, ST.win(U32, xs, 1n+s, 1n+p), acc), SC.append(U32, w, Con{x, acc}),
          Equal.trans(List<&2, U32>, SC.append(U32, ST.win(U32, xs, 1n+s, 1n+p), acc), SC.append(U32, SC.append(U32, w, Con{x, Nil{}}), acc), SC.append(U32, w, Con{x, acc}),
            Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.append(U32, z, acc), ST.win(U32, xs, 1n+s, 1n+p), SC.append(U32, w, Con{x, Nil{}}), win_snoc(U32, xs, 1n+s, p, x, hx)),
            LL.append_assoc(U32, w, Con{x, Nil{}}, acc))))

# ---- the runtime loop is the mirror ----

def get_at(+j: Nat, +d: Nat, +t: AR.Tree<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {(AR.thaw(U32, t), SH.val_at(AR.slots(U32, t), j)) == Array.get(U32, AR.thaw(U32, t), U32.from_nat(j)) : Array<U32> & U32}:
  +xs = AR.slots(U32, t)
  +ej = U.to_nat_from_nat(j, d, N.lt_le(d, 32n, hd), hj)
  +hij = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, j, U32.to_nat(U32.from_nat(j)), Equal.sym(Nat, U32.to_nat(U32.from_nat(j)), j, ej), hj)
  +hxj = L.subst(Nat, z => {SC.nth(U32, xs, z) == Some{SH.val_at(xs, j)} : Maybe<&2, U32>}, j, U32.to_nat(U32.from_nat(j)), Equal.sym(Nat, U32.to_nat(U32.from_nat(j)), j, ej), SH.some_at(d, t, j, pf, hj))
  Equal.sym(Array<U32> & U32, Array.get(U32, AR.thaw(U32, t), U32.from_nat(j)), (AR.thaw(U32, t), SH.val_at(xs, j)), AR.get(U32, d, t, U32.from_nat(j), SH.val_at(xs, j), hd, hij, hxj, pf))

# A loop with nothing left to read discards its (possibly out-of-range) read.
def nb_go0_fin(+acc: List<&2, U32>, +j: U32, +t: AR.Tree<U32>, +i: U32, s: Sigma<&1, &1, U32, x => {Array.get(U32, AR.thaw(U32, t), i) == (AR.thaw(U32, t), x) : Array<U32> & U32}>) -> {G.nb_go(0n, acc, j, Array.get(U32, AR.thaw(U32, t), i)) == (AR.thaw(U32, t), acc) : Array<U32> & List<&2, U32>}:
  (x, e) = s
  %Equal.sym(Array<U32> & U32, Array.get(U32, AR.thaw(U32, t), i), (AR.thaw(U32, t), x), e) : {G.nb_go(0n, acc, j, _) == (AR.thaw(U32, t), acc) : Array<U32> & List<&2, U32>}
  {==}

def nb_go0(+acc: List<&2, U32>, +j: U32, +d: Nat, +t: AR.Tree<U32>, +i: U32, +pf: {AR.perfect(U32, d, t) == True{} : Bool}) -> {G.nb_go(0n, acc, j, Array.get(U32, AR.thaw(U32, t), i)) == (AR.thaw(U32, t), acc) : Array<U32> & List<&2, U32>}:
  nb_go0_fin(acc, j, t, i, BK.get_any(U32, d, t, i, pf))

def NbIH(+p: Nat, +d: Nat, +t: AR.Tree<U32>) -> Type:
  @+acc2: List<&2, U32> -> @+j2: Nat ->
  @+h1: {Nat.is_lt(j2, SC.pow2(d)) == True{} : Bool} ->
  @+h2: {Nat.is_le(p, 1n+j2) == True{} : Bool} ->
  {G.nb_go(p, acc2, U32.from_nat(j2), Array.get(U32, AR.thaw(U32, t), U32.from_nat(j2))) == (AR.thaw(U32, t), rd(p, AR.slots(U32, t), j2, acc2)) : Array<U32> & List<&2, U32>}

# After reading slot j: either nothing is left (the next read is discarded,
# even when j = 0 makes its index wrap), or slot j - 1 is in range.
def nb_go_succ(+p: Nat, +acc: List<&2, U32>, +j: Nat, +d: Nat, +t: AR.Tree<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +hm: {Nat.is_le(1n+p, 1n+j) == True{} : Bool}, ih: NbIH(p, d, t)) -> {G.nb_go(p, Con{SH.val_at(AR.slots(U32, t), j), acc}, U32.sub(U32.from_nat(j), 1), Array.get(U32, AR.thaw(U32, t), U32.sub(U32.from_nat(j), 1))) == (AR.thaw(U32, t), rd(1n+p, AR.slots(U32, t), j, acc)) : Array<U32> & List<&2, U32>}:
  match p:
    case 0n:
      nb_go0(Con{SH.val_at(AR.slots(U32, t), j), acc}, U32.sub(U32.from_nat(j), 1), d, t, U32.sub(U32.from_nat(j), 1), pf)
    case 1n+q:
      +j1 = Nat.sub(j, 1n)
      +h1 = N.le_trans(1n, 1n+q, j, N.le_add_right(1n, q), hm)
      +es = H.sub_bridge(j, 1n, d, N.lt_le(d, 32n, hd), hj, h1)
      +hj1 = N.le_lt_trans(j1, j, SC.pow2(d), H.sub_le(j, 1n), hj)
      +hm1 = N.le_trans(1n+q, j, 1n+j1, hm, SE.le_of_pred_le(j, j1, N.le_refl(j1)))
      %Equal.sym(U32, U32.sub(U32.from_nat(j), 1), U32.from_nat(j1), es) : {G.nb_go(1n+q, Con{SH.val_at(AR.slots(U32, t), j), acc}, _, Array.get(U32, AR.thaw(U32, t), _)) == (AR.thaw(U32, t), rd(2n+q, AR.slots(U32, t), j, acc)) : Array<U32> & List<&2, U32>}
      ih(Con{SH.val_at(AR.slots(U32, t), j), acc}, j1, hj1, hm1)

# The loop reads slots j, j-1, ..., j-m+1 (and discards one more read).
def nb_go_ok(+m: Nat, +acc: List<&2, U32>, +j: Nat, +d: Nat, +t: AR.Tree<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +hm: {Nat.is_le(m, 1n+j) == True{} : Bool}) -> {G.nb_go(m, acc, U32.from_nat(j), Array.get(U32, AR.thaw(U32, t), U32.from_nat(j))) == (AR.thaw(U32, t), rd(m, AR.slots(U32, t), j, acc)) : Array<U32> & List<&2, U32>}:
  match m:
    case 0n:
      nb_go0(acc, U32.from_nat(j), d, t, U32.from_nat(j), pf)
    case 1n+p:
      %get_at(j, d, t, hd, pf, hj) : {G.nb_go(1n+p, acc, U32.from_nat(j), _) == (AR.thaw(U32, t), rd(1n+p, AR.slots(U32, t), j, acc)) : Array<U32> & List<&2, U32>}
      nb_go_succ(p, acc, j, d, t, hd, pf, hj, hm, acc2 => j2 => hj2 => hm2 => nb_go_ok(p, acc2, j2, d, t, hd, pf, hj2, hm2))

# Array.get at an in-range Nat index.
# ---- neighbors ----

def gkeys_uset(+ws: List<&2, U32>) -> {GS.keys(Unit, ST.uset(ws)) == ws : List<&2, U32>}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => Con{w, ys}, GS.keys(Unit, ST.uset(t)), t, gkeys_uset(t))

# The entries of a block, read backwards from the last one.
def nb_start_ok(+bt: AR.Tree<U32>, +bd: {Nat.is_lt(ST.blcap(bt), 32n) == True{} : Bool}, +bp: {AR.perfect(U32, ST.blcap(bt), bt) == True{} : Bool}, +bcap: {Nat.is_le(Nat.add(3n, ST.bdeg(bt)), SC.pow2(ST.blcap(bt))) == True{} : Bool}) -> {G.nb_start(AR.thaw(U32, bt), BK.v0(bt)) == (AR.thaw(U32, bt), ST.bents(bt)) : Array<U32> & List<&2, U32>}:
  +lc = ST.blcap(bt)
  +dg = ST.bdeg(bt)
  +xs = AR.slots(U32, bt)
  +h2 = N.lt_le_trans(Nat.add(2n, dg), Nat.add(3n, dg), SC.pow2(lc), N.lt_succ(Nat.add(2n, dg)), bcap)
  +e0 = BK.from_to(BK.v0(bt), lc, N.lt_le(lc, 32n, bd), N.lt_le_trans(dg, Nat.add(3n, dg), SC.pow2(lc), N.le_lt_trans(dg, Nat.add(2n, dg), Nat.add(3n, dg), BK.le_plus(2n, dg), N.lt_succ(Nat.add(2n, dg))), bcap))
  +el = Equal.cong(U32, U32, z => U32.inc(U32.inc(z)), U32.from_nat(dg), BK.v0(bt), e0)
  %el : {G.nb_go(dg, Nil{}, _, Array.get(U32, AR.thaw(U32, bt), _)) == (AR.thaw(U32, bt), ST.bents(bt)) : Array<U32> & List<&2, U32>}
  Equal.trans(Array<U32> & List<&2, U32>, G.nb_go(dg, Nil{}, U32.from_nat(Nat.add(2n, dg)), Array.get(U32, AR.thaw(U32, bt), U32.from_nat(Nat.add(2n, dg)))), (AR.thaw(U32, bt), rd(dg, xs, Nat.add(2n, dg), Nil{})), (AR.thaw(U32, bt), ST.bents(bt)),
    nb_go_ok(dg, Nil{}, Nat.add(2n, dg), lc, bt, bd, bp, h2, BK.le_plus(3n, dg)),
    Equal.cong(List<&2, U32>, Array<U32> & List<&2, U32>, z => (AR.thaw(U32, bt), z), rd(dg, xs, Nat.add(2n, dg), Nil{}), ST.bents(bt),
      Equal.trans(List<&2, U32>, rd(dg, xs, Nat.add(2n, dg), Nil{}), SC.append(U32, ST.bents(bt), Nil{}), ST.bents(bt),
        rd_win(xs, 2n, dg, Nil{}, L.subst(Nat, z => {Nat.is_le(Nat.add(3n, dg), z) == True{} : Bool}, SC.pow2(lc), SC.length(U32, xs), Equal.sym(Nat, SC.length(U32, xs), SC.pow2(lc), AR.slots_length(U32, lc, bt, bp)), bcap)),
        LL.append_nil(U32, ST.bents(bt)))))

def nbrs_ok(+d: Nat, +at: AR.Tree<AR.Tree<U32>>, +i: U32, +bt: AR.Tree<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}, +hx: {SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), U32.to_nat(i)) == Some{bt} : Maybe<&2, AR.Tree<U32>>}, +pf: {AR.perfect(AR.Tree<U32>, d, at) == True{} : Bool}, +bd: {Nat.is_lt(ST.blcap(bt), 32n) == True{} : Bool}, +b2: {Nat.is_le(2n, ST.blcap(bt)) == True{} : Bool}, +bp: {AR.perfect(U32, ST.blcap(bt), bt) == True{} : Bool}, +bcap: {Nat.is_le(Nat.add(3n, ST.bdeg(bt)), SC.pow2(ST.blcap(bt))) == True{} : Bool}) -> {G.nbrs(A2.thaw2(at), i) == G.NBR{A2.thaw2(at), ST.bents(bt)} : G.Nbr}:
  +at1 = AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), BK.leaf0())
  %Equal.sym(Array<Array<U32>> & Array<U32>, Array.swap(Array<U32>, A2.thaw2(at), i, AR.thaw(U32, BK.leaf0())), (A2.thaw2(at1), AR.thaw(U32, bt)), A2.swap2(d, at, i, BK.leaf0(), bt, hd, hi, hx, pf)) : {G.nb_take(i, _) == G.NBR{A2.thaw2(at), ST.bents(bt)} : G.Nbr}
  %Equal.sym(G.Hdr, G.header(AR.thaw(U32, bt)), G.HD{AR.thaw(U32, bt), BK.v0(bt), BK.v1(bt), BK.v2(bt)}, BK.header_ok(bt, bd, b2, bp)) : {G.nb_hdr(A2.thaw2(at1), i, _) == G.NBR{A2.thaw2(at), ST.bents(bt)} : G.Nbr}
  %Equal.sym(Array<U32> & List<&2, U32>, G.nb_start(AR.thaw(U32, bt), BK.v0(bt)), (AR.thaw(U32, bt), ST.bents(bt)), nb_start_ok(bt, bd, bp, bcap)) : {G.nb_fin(A2.thaw2(at1), i, _) == G.NBR{A2.thaw2(at), ST.bents(bt)} : G.Nbr}
  Equal.cong(Array<Array<U32>>, G.Nbr, z => G.NBR{z, ST.bents(bt)}, Array.set(Array<U32>, A2.thaw2(at1), i, AR.thaw(U32, bt)), A2.thaw2(at), BK.swap_back(d, at, i, bt, hd, hi, hx, pf))

def nb_case(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, fv: Bool, +efv: {SE.found_of(it, OP.lbv(lo, hi, it, v), hi, v) == fv : Bool}) -> {G.nbr_pick(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), U32.from_nat(OP.lbv(lo, hi, it, v)), fv) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.neighbors_at(LB.pickv(List<&2, BE.Entry<U32, Unit>>, fv, ST.uset(ST.bents(ED.blk_of(dir, lo, hi, depth, it, at, v)))))) : G.Graph & Result<&2, &2, E.Error, List<&2, U32>>}:
  match fv:
    case False{}:
      {==}
    case True{}:
      +bt = ED.blk_of(dir, lo, hi, depth, it, at, v)
      +hin = ED.found_lt(it, OP.lbv(lo, hi, it, v), hi, v, Nat.is_lt(OP.lbv(lo, hi, it, v), hi), {==}, efv)
      +bk = ED.blk_ok_of(dir, lo, hi, depth, it, at, v, h, hin)
      +iv = U32.from_nat(OP.lbv(lo, hi, it, v))
      %Equal.sym(G.Nbr, G.nbrs(A2.thaw2(at), iv), G.NBR{A2.thaw2(at), ST.bents(bt)},
        nbrs_ok(depth, at, iv, bt, ED.dep32(dir, lo, hi, depth, it, at, h),
          L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(depth)) == True{} : Bool}, OP.lbv(lo, hi, it, v), U32.to_nat(iv), Equal.sym(Nat, U32.to_nat(iv), OP.lbv(lo, hi, it, v), ED.slot_nat(dir, lo, hi, depth, it, at, v, h, hin)), ED.lbv_lt_cap(dir, lo, hi, depth, it, at, v, h, hin)),
          ED.blk_at(dir, lo, hi, depth, it, at, v, h, hin),
          OP.g_adj(dir, lo, hi, depth, it, at, h),
          ED.bk_lt32(bt, bk), ED.bk_two(bt, bk), ED.bk_perfect(bt, bk), ED.bk_cap(bt, bk))) : {G.nbr_done(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), _) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), Done{GS.keys(Unit, ST.uset(ST.bents(bt)))}) : G.Graph & Result<&2, &2, E.Error, List<&2, U32>>}
      Equal.cong(List<&2, U32>, G.Graph & Result<&2, &2, E.Error, List<&2, U32>>, z => (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), Done{z}), ST.bents(bt), GS.keys(Unit, ST.uset(ST.bents(bt))),
        Equal.sym(List<&2, U32>, GS.keys(Unit, ST.uset(ST.bents(bt))), ST.bents(bt), gkeys_uset(ST.bents(bt))))

# neighbors refines the specification and returns the state unchanged.
def neighbors_ok(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {G.neighbors(ST.real(ST.Sh{dir, lo, hi, depth, it, at}), v) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.neighbors_at(GS.find(v, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))))) : G.Graph & Result<&2, &2, E.Error, List<&2, U32>>}:
  +am = ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))
  +fv = SE.found_of(it, OP.lbv(lo, hi, it, v), hi, v)
  %Equal.sym(G.Loc, G.locate(depth, v, U32.from_nat(lo), U32.from_nat(hi), AR.thaw(U32, it)), G.LC{AR.thaw(U32, it), U32.from_nat(OP.lbv(lo, hi, it, v)), fv}, OP.hv_locate(dir, lo, hi, depth, it, at, v, h)) : {G.nbr_fin(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, A2.thaw2(at), _) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.neighbors_at(GS.find(v, am))) : G.Graph & Result<&2, &2, E.Error, List<&2, U32>>}
  %Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(v, am), LB.pickv(List<&2, BE.Entry<U32, Unit>>, fv, ST.uset(ST.bents(ED.blk_of(dir, lo, hi, depth, it, at, v)))), ED.gfind(dir, lo, hi, depth, it, at, v, h)) : {G.nbr_pick(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), U32.from_nat(OP.lbv(lo, hi, it, v)), fv) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.neighbors_at(_)) : G.Graph & Result<&2, &2, E.Error, List<&2, U32>>}
  nb_case(dir, lo, hi, depth, it, at, v, h, fv, {==})

# Reading 1+p values ending at st + p gives the window [st, st+1+p); any st.
def rd_win1(+xs: List<&2, U32>, +st: Nat, +p: Nat, +acc: List<&2, U32>, +hl: {Nat.is_le(Nat.add(st, 1n+p), SC.length(U32, xs)) == True{} : Bool}) -> {rd(1n+p, xs, Nat.add(st, p), acc) == SC.append(U32, ST.win(U32, xs, st, 1n+p), acc) : List<&2, U32>}:
  match p:
    case 0n:
      +x = SH.val_at(xs, Nat.add(st, 0n))
      +hle = L.subst(Nat, z => {Nat.is_le(z, SC.length(U32, xs)) == True{} : Bool}, Nat.add(st, 1n), 1n+Nat.add(st, 0n), N.add_succ(st, 0n), hl)
      +hx = val_some(xs, Nat.add(st, 0n), N.succ_le_lt(Nat.add(st, 0n), SC.length(U32, xs), hle))
      Equal.sym(List<&2, U32>, SC.append(U32, ST.win(U32, xs, st, 1n), acc), Con{x, acc},
        Equal.trans(List<&2, U32>, SC.append(U32, ST.win(U32, xs, st, 1n), acc), SC.append(U32, SC.append(U32, ST.win(U32, xs, st, 0n), Con{x, Nil{}}), acc), Con{x, acc},
          Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.append(U32, z, acc), ST.win(U32, xs, st, 1n), SC.append(U32, ST.win(U32, xs, st, 0n), Con{x, Nil{}}), win_snoc(U32, xs, st, 0n, x, hx)),
          L.subst(List<&2, U32>, z => {SC.append(U32, SC.append(U32, z, Con{x, Nil{}}), acc) == Con{x, acc} : List<&2, U32>}, Nil{}, ST.win(U32, xs, st, 0n), Equal.sym(List<&2, U32>, ST.win(U32, xs, st, 0n), Nil{}, LL.sc_take_zero(U32, SC.drop(U32, xs, st))), {==})))
    case 1n+q:
      +x = SH.val_at(xs, Nat.add(st, 1n+q))
      +hle = L.subst(Nat, z => {Nat.is_le(z, SC.length(U32, xs)) == True{} : Bool}, Nat.add(st, 2n+q), 1n+Nat.add(st, 1n+q), N.add_succ(st, 1n+q), hl)
      +hx = val_some(xs, Nat.add(st, 1n+q), N.succ_le_lt(Nat.add(st, 1n+q), SC.length(U32, xs), hle))
      +hlq = N.le_trans(Nat.add(st, 1n+q), 1n+Nat.add(st, 1n+q), SC.length(U32, xs), N.lt_le(Nat.add(st, 1n+q), 1n+Nat.add(st, 1n+q), N.lt_succ(Nat.add(st, 1n+q))), hle)
      %Equal.sym(Nat, Nat.sub(Nat.add(st, 1n+q), 1n), Nat.add(st, q), sub_one_add(st, q)) : {rd(1n+q, xs, _, Con{x, acc}) == SC.append(U32, ST.win(U32, xs, st, 2n+q), acc) : List<&2, U32>}
      Equal.trans(List<&2, U32>, rd(1n+q, xs, Nat.add(st, q), Con{x, acc}), SC.append(U32, ST.win(U32, xs, st, 1n+q), Con{x, acc}), SC.append(U32, ST.win(U32, xs, st, 2n+q), acc),
        rd_win1(xs, st, q, Con{x, acc}, hlq),
        Equal.sym(List<&2, U32>, SC.append(U32, ST.win(U32, xs, st, 2n+q), acc), SC.append(U32, ST.win(U32, xs, st, 1n+q), Con{x, acc}),
          Equal.trans(List<&2, U32>, SC.append(U32, ST.win(U32, xs, st, 2n+q), acc), SC.append(U32, SC.append(U32, ST.win(U32, xs, st, 1n+q), Con{x, Nil{}}), acc), SC.append(U32, ST.win(U32, xs, st, 1n+q), Con{x, acc}),
            Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.append(U32, z, acc), ST.win(U32, xs, st, 2n+q), SC.append(U32, ST.win(U32, xs, st, 1n+q), Con{x, Nil{}}), win_snoc(U32, xs, st, 1n+q, x, hx)),
            LL.append_assoc(U32, ST.win(U32, xs, st, 1n+q), Con{x, Nil{}}, acc))))

# ---- vertices ----

def gkeys_amodel(+ks: List<&2, U32>, +bs: List<&2, AR.Tree<U32>>, +hlen: {SC.length(U32, ks) == SC.length(AR.Tree<U32>, bs) : Nat}) -> {GS.keys(List<&2, BE.Entry<U32, Unit>>, ST.amodel(ks, bs)) == ks : List<&2, U32>}:
  match ks bs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, bt}:
      Empty.absurd({GS.keys(List<&2, BE.Entry<U32, Unit>>, ST.amodel(Nil{}, Con{b, bt})) == Nil{} : List<&2, U32>}, N.zero_succ(SC.length(AR.Tree<U32>, bt), hlen))
    case Con{k, kt} Nil{}:
      Empty.absurd({GS.keys(List<&2, BE.Entry<U32, Unit>>, ST.amodel(Con{k, kt}, Nil{})) == Con{k, kt} : List<&2, U32>}, N.succ_zero(SC.length(U32, kt), hlen))
    case Con{+k, +kt} Con{+b, +bt}:
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => Con{k, ys}, GS.keys(List<&2, BE.Entry<U32, Unit>>, ST.amodel(kt, bt)), kt, gkeys_amodel(kt, bt, N.succ_inj(SC.length(U32, kt), SC.length(AR.Tree<U32>, bt), hlen)))

# hi - lo = 1 + p  gives  hi - 1 = lo + p.
def last_idx(+lo: Nat, +hi: Nat, +p: Nat, +ek: {Nat.sub(hi, lo) == 1n+p : Nat}, +hlo: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Nat.sub(hi, 1n) == Nat.add(lo, p) : Nat}:
  +eh = W.window_end(lo, hi, 1n+p, Equal.sym(Nat, Nat.sub(hi, lo), 1n+p, ek), hlo)
  L.subst(Nat, z => {Nat.sub(z, 1n) == Nat.add(lo, p) : Nat}, Nat.add(lo, 1n+p), hi, eh, sub_one_add(lo, p))

def vs_case(+lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +hd: {Nat.is_lt(depth, 32n) == True{} : Bool}, +pf: {AR.perfect(U32, depth, it) == True{} : Bool}, +hlo: {Nat.is_le(lo, hi) == True{} : Bool}, +hcap: {Nat.is_le(hi, SC.pow2(depth)) == True{} : Bool}, k: Nat, +ek: {Nat.sub(hi, lo) == k : Nat}) -> {G.nb_go(k, Nil{}, U32.sub(U32.from_nat(hi), 1), Array.get(U32, AR.thaw(U32, it), U32.sub(U32.from_nat(hi), 1))) == (AR.thaw(U32, it), ST.win(U32, AR.slots(U32, it), lo, k)) : Array<U32> & List<&2, U32>}:
  match k:
    case 0n:
      L.subst(List<&2, U32>, z => {G.nb_go(0n, Nil{}, U32.sub(U32.from_nat(hi), 1), Array.get(U32, AR.thaw(U32, it), U32.sub(U32.from_nat(hi), 1))) == (AR.thaw(U32, it), z) : Array<U32> & List<&2, U32>}, Nil{}, ST.win(U32, AR.slots(U32, it), lo, 0n), Equal.sym(List<&2, U32>, ST.win(U32, AR.slots(U32, it), lo, 0n), Nil{}, LL.sc_take_zero(U32, SC.drop(U32, AR.slots(U32, it), lo))),
        nb_go0(Nil{}, U32.sub(U32.from_nat(hi), 1), depth, it, U32.sub(U32.from_nat(hi), 1), pf))
    case 1n+ +p:
      +xs = AR.slots(U32, it)
      +j = Nat.add(lo, p)
      +el = last_idx(lo, hi, p, ek, hlo)
      +eh = W.window_end(lo, hi, 1n+p, Equal.sym(Nat, Nat.sub(hi, lo), 1n+p, ek), hlo)
      +h1 = L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, Nat.add(lo, 1n+p), hi, eh, L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, 1n+Nat.add(lo, p), Nat.add(lo, 1n+p), Equal.sym(Nat, Nat.add(lo, 1n+p), 1n+Nat.add(lo, p), N.add_succ(lo, p)), N.le_add_right(1n, Nat.add(lo, p))))
      +hj = N.lt_le_trans(j, hi, SC.pow2(depth), L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, Nat.add(lo, 1n+p), hi, eh, L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, 1n+j, Nat.add(lo, 1n+p), Equal.sym(Nat, Nat.add(lo, 1n+p), 1n+j, N.add_succ(lo, p)), N.lt_succ(j))), hcap)
      +es = Equal.trans(U32, U32.sub(U32.from_nat(hi), 1), U32.from_nat(Nat.sub(hi, 1n)), U32.from_nat(j),
        H.sub_bridge(hi, 1n, 1n+depth, N.lt_succ_le_succ(depth, 32n, hd), N.le_lt_trans(hi, SC.pow2(depth), SC.pow2(1n+depth), hcap, N.pow2_lt_succ(depth)), h1),
        Equal.cong(Nat, U32, z => U32.from_nat(z), Nat.sub(hi, 1n), j, el))
      %Equal.sym(U32, U32.sub(U32.from_nat(hi), 1), U32.from_nat(j), es) : {G.nb_go(1n+p, Nil{}, _, Array.get(U32, AR.thaw(U32, it), _)) == (AR.thaw(U32, it), ST.win(U32, xs, lo, 1n+p)) : Array<U32> & List<&2, U32>}
      Equal.trans(Array<U32> & List<&2, U32>, G.nb_go(1n+p, Nil{}, U32.from_nat(j), Array.get(U32, AR.thaw(U32, it), U32.from_nat(j))), (AR.thaw(U32, it), rd(1n+p, xs, j, Nil{})), (AR.thaw(U32, it), ST.win(U32, xs, lo, 1n+p)),
        nb_go_ok(1n+p, Nil{}, j, depth, it, hd, pf, hj, N.lt_succ_le_succ(p, 1n+j, N.le_lt_succ(p, j, BK.le_plus(lo, p)))),
        Equal.cong(List<&2, U32>, Array<U32> & List<&2, U32>, z => (AR.thaw(U32, it), z), rd(1n+p, xs, j, Nil{}), ST.win(U32, xs, lo, 1n+p),
          Equal.trans(List<&2, U32>, rd(1n+p, xs, j, Nil{}), SC.append(U32, ST.win(U32, xs, lo, 1n+p), Nil{}), ST.win(U32, xs, lo, 1n+p),
            rd_win1(xs, lo, p, Nil{}, L.subst(Nat, z => {Nat.is_le(z, SC.length(U32, xs)) == True{} : Bool}, hi, Nat.add(lo, 1n+p), Equal.sym(Nat, Nat.add(lo, 1n+p), hi, eh),
              L.subst(Nat, z => {Nat.is_le(hi, z) == True{} : Bool}, SC.pow2(depth), SC.length(U32, xs), Equal.sym(Nat, SC.length(U32, xs), SC.pow2(depth), AR.slots_length(U32, depth, it, pf)), hcap))),
            LL.append_nil(U32, ST.win(U32, xs, lo, 1n+p)))))

# vertices refines the specification and returns the state unchanged.
def vertices_ok(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {G.vertices(ST.real(ST.Sh{dir, lo, hi, depth, it, at})) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.keys(List<&2, BE.Entry<U32, Unit>>, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo))))) : G.Graph & List<&2, U32>}:
  +k = Nat.sub(hi, lo)
  +xs = AR.slots(U32, it)
  +ks = ST.win(U32, xs, lo, k)
  +bw = ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, k)
  +hd = ED.dep32(dir, lo, hi, depth, it, at, h)
  +hlo = OP.g_lohi(dir, lo, hi, depth, it, at, h)
  +hcap = OP.g_cap(dir, lo, hi, depth, it, at, h)
  +hb = N.lt_succ_le_succ(depth, 32n, hd)
  +hhi = N.le_lt_trans(hi, SC.pow2(depth), SC.pow2(1n+depth), hcap, N.pow2_lt_succ(depth))
  +ek = Equal.trans(Nat, U32.to_nat(U32.sub(U32.from_nat(hi), U32.from_nat(lo))), U32.to_nat(U32.from_nat(k)), k,
    Equal.cong(U32, Nat, z => U32.to_nat(z), U32.sub(U32.from_nat(hi), U32.from_nat(lo)), U32.from_nat(k), H.sub_bridge(hi, lo, 1n+depth, hb, hhi, hlo)),
    U.to_nat_from_nat(k, 1n+depth, hb, N.le_lt_trans(k, hi, SC.pow2(1n+depth), H.sub_le(hi, lo), hhi)))
  +hlen = Equal.trans(Nat, SC.length(U32, ks), k, SC.length(AR.Tree<U32>, bw),
    ED.win_len(U32, xs, lo, k, ED.win_fits(U32, depth, it, lo, hi, OP.g_ids(dir, lo, hi, depth, it, at, h), hlo, hcap)),
    Equal.sym(Nat, SC.length(AR.Tree<U32>, bw), k, ED.win_len(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, k, ED.win_fits(AR.Tree<U32>, depth, at, lo, hi, OP.g_adj(dir, lo, hi, depth, it, at, h), hlo, hcap))))
  %Equal.sym(Nat, U32.to_nat(U32.sub(U32.from_nat(hi), U32.from_nat(lo))), k, ek) : {G.vs_fin(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, A2.thaw2(at), G.nb_go(_, Nil{}, U32.sub(U32.from_nat(hi), 1), Array.get(U32, AR.thaw(U32, it), U32.sub(U32.from_nat(hi), 1)))) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.keys(List<&2, BE.Entry<U32, Unit>>, ST.amodel(ks, bw))) : G.Graph & List<&2, U32>}
  %Equal.sym(Array<U32> & List<&2, U32>, G.nb_go(k, Nil{}, U32.sub(U32.from_nat(hi), 1), Array.get(U32, AR.thaw(U32, it), U32.sub(U32.from_nat(hi), 1))), (AR.thaw(U32, it), ks), vs_case(lo, hi, depth, it, hd, OP.g_ids(dir, lo, hi, depth, it, at, h), hlo, hcap, k, {==})) : {G.vs_fin(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, A2.thaw2(at), _) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.keys(List<&2, BE.Entry<U32, Unit>>, ST.amodel(ks, bw))) : G.Graph & List<&2, U32>}
  Equal.cong(List<&2, U32>, G.Graph & List<&2, U32>, z => (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), z), ks, GS.keys(List<&2, BE.Entry<U32, Unit>>, ST.amodel(ks, bw)), Equal.sym(List<&2, U32>, GS.keys(List<&2, BE.Entry<U32, Unit>>, ST.amodel(ks, bw)), ks, gkeys_amodel(ks, bw, hlen)))
