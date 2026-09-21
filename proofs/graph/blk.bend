import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../lib/array2.bend as A2
import ../../spec/common.bend as SC
import ../../reference/lru/spec/numeric.bend as NS
import ../../src/graph.bend as G
import ./search.bend as SE
import ./shift.bend as SH
import ./state.bend as ST
import ./window.bend as W

# Tree-update identities used when an operation takes a block out of the
# adjacency array (Array.swap with a placeholder) and puts it back.

# Writing the value that is already stored changes nothing.
def tupd_self(-T: Data, +d: Nat, +t: AR.Tree<T>, +j: Nat, +x: T, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(T, d, t) == True{} : Bool}, +hx: {SC.nth(T, AR.slots(T, t), j) == Some{x} : Maybe<&2, T>}, +b: Bool, +eb: {AR.ndec(d, j) == b : Bool}) -> {AR.tupd(T, d, t, j, x, b) == t : AR.Tree<T>}:
  match d t b:
    case 0n AR.TLeaf{+y} _:
      Equal.cong(T, AR.Tree<T>, z => AR.TLeaf{z}, x, y, Equal.sym(T, y, x, AR.leaf_value(T, y, j, x, hj, hx)))
    case 0n AR.TNode{l, r} _:
      Empty.absurd({AR.tupd(T, 0n, AR.TNode{l, r}, j, x, b) == AR.TNode{l, r} : AR.Tree<T>}, L.false_true(pf))
    case 1n+p AR.TLeaf{y} _:
      Empty.absurd({AR.tupd(T, 1n+p, AR.TLeaf{y}, j, x, b) == AR.TLeaf{y} : AR.Tree<T>}, L.false_true(pf))
    case 1n+ +p AR.TNode{+l, +r} True{}:
      +pl = AR.pf_left(T, p, l, r, pf)
      +hjl = eb
      +hxl = Equal.trans(Maybe<&2, T>, SC.nth(T, AR.slots(T, l), j), SC.nth(T, SC.append(T, AR.slots(T, l), AR.slots(T, r)), j), Some{x},
        Equal.sym(Maybe<&2, T>, SC.nth(T, SC.append(T, AR.slots(T, l), AR.slots(T, r)), j), SC.nth(T, AR.slots(T, l), j), LL.nth_append_left(T, AR.slots(T, l), AR.slots(T, r), j, AR.len_lt(T, p, l, j, pl, hjl))), hx)
      %Equal.sym(AR.Tree<T>, AR.tupd(T, p, l, j, x, AR.ndec(p, j)), l, tupd_self(T, p, l, j, x, hjl, pl, hxl, AR.ndec(p, j), {==})) : {AR.TNode{_, r} == AR.TNode{l, r} : AR.Tree<T>}
      {==}
    case 1n+ +p AR.TNode{+l, +r} False{}:
      +pl = AR.pf_left(T, p, l, r, pf)
      +pr = AR.pf_right(T, p, l, r, pf)
      +le = N.not_lt_le(j, SC.pow2(p), eb)
      +k = Nat.sub(j, SC.pow2(p))
      +hjr = AR.upper_lt(j, p, hj, le)
      +hxr = Equal.trans(Maybe<&2, T>, SC.nth(T, AR.slots(T, r), k), SC.nth(T, SC.append(T, AR.slots(T, l), AR.slots(T, r)), j), Some{x},
        Equal.sym(Maybe<&2, T>, SC.nth(T, SC.append(T, AR.slots(T, l), AR.slots(T, r)), j), SC.nth(T, AR.slots(T, r), k), AR.right_nth(T, p, l, r, j, pl, le)), hx)
      %Equal.sym(AR.Tree<T>, AR.tupd(T, p, r, k, x, AR.ndec(p, k)), r, tupd_self(T, p, r, k, x, hjr, pr, hxr, AR.ndec(p, k), {==})) : {AR.TNode{l, _} == AR.TNode{l, r} : AR.Tree<T>}
      {==}

# Two writes at the same index: the second wins.
def tupd_tupd(-T: Data, +d: Nat, +t: AR.Tree<T>, +j: Nat, +a: T, +x: T, +b: Bool) -> {AR.tupd(T, d, AR.tupd(T, d, t, j, a, b), j, x, b) == AR.tupd(T, d, t, j, x, b) : AR.Tree<T>}:
  match d t b:
    case 0n AR.TLeaf{y} _:
      {==}
    case 0n AR.TNode{l, r} _:
      {==}
    case 1n+p AR.TLeaf{y} _:
      {==}
    case 1n+ +p AR.TNode{+l, +r} True{}:
      %Equal.sym(AR.Tree<T>, AR.tupd(T, p, AR.tupd(T, p, l, j, a, AR.ndec(p, j)), j, x, AR.ndec(p, j)), AR.tupd(T, p, l, j, x, AR.ndec(p, j)), tupd_tupd(T, p, l, j, a, x, AR.ndec(p, j))) : {AR.TNode{_, r} == AR.TNode{AR.tupd(T, p, l, j, x, AR.ndec(p, j)), r} : AR.Tree<T>}
      {==}
    case 1n+ +p AR.TNode{+l, +r} False{}:
      +k = Nat.sub(j, SC.pow2(p))
      %Equal.sym(AR.Tree<T>, AR.tupd(T, p, AR.tupd(T, p, r, k, a, AR.ndec(p, k)), k, x, AR.ndec(p, k)), AR.tupd(T, p, r, k, x, AR.ndec(p, k)), tupd_tupd(T, p, r, k, a, x, AR.ndec(p, k))) : {AR.TNode{l, _} == AR.TNode{l, AR.tupd(T, p, r, k, x, AR.ndec(p, k))} : AR.Tree<T>}
      {==}

# Take the value out (replacing it by `a`) and put the same value back.
def upd_back(-T: Data, +d: Nat, +t: AR.Tree<T>, +j: Nat, +a: T, +x: T, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(T, d, t) == True{} : Bool}, +hx: {SC.nth(T, AR.slots(T, t), j) == Some{x} : Maybe<&2, T>}) -> {AR.upd(T, d, AR.upd(T, d, t, j, a), j, x) == t : AR.Tree<T>}:
  Equal.trans(AR.Tree<T>, AR.tupd(T, d, AR.tupd(T, d, t, j, a, AR.ndec(d, j)), j, x, AR.ndec(d, j)), AR.tupd(T, d, t, j, x, AR.ndec(d, j)), t,
    tupd_tupd(T, d, t, j, a, x, AR.ndec(d, j)),
    tupd_self(T, d, t, j, x, hj, pf, hx, AR.ndec(d, j), {==}))

# ---- U32 round trip under a symbolic bound ----

def from_to(+x: U32, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +h: {Nat.is_lt(U32.to_nat(x), SC.pow2(k)) == True{} : Bool}) -> {U32.from_nat(U32.to_nat(x)) == x : U32}:
  match x:
    case U32{+w}:
      Equal.trans(U32, U32.from_nat(U32.to_nat(U32{w})), U32{NS.from_nat(32n, U32.to_nat(U32{w}))}, U32{w},
        U.from_nat_word(U32.to_nat(U32{w}), k, hk, h),
        Equal.cong(Word(32n), U32, z => U32{z}, NS.from_nat(32n, U32.to_nat(U32{w})), w,
          Equal.trans(Word(32n), NS.from_nat(32n, U32.to_nat(U32{w})), NS.from_nat(32n, NS.unsigned(32n, w)), w,
            Equal.cong(Nat, Word(32n), n => NS.from_nat(32n, n), U32.to_nat(U32{w}), NS.unsigned(32n, w), U.to_nat_word(w)),
            U.word_from_unsigned(w))))

# ---- search of a sorted window [lo, hi) of any perfect tree ----

def win_locate(+d: Nat, +t: AR.Tree<U32>, +v: U32, +lo: Nat, +hi: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hlo: {Nat.is_le(lo, hi) == True{} : Bool}, +hcap: {Nat.is_le(hi, SC.pow2(d)) == True{} : Bool}, +hs: {SE.asc_at(Nat.sub(hi, lo), AR.slots(U32, t), lo) == True{} : Bool}) -> {G.locate(d, v, U32.from_nat(lo), U32.from_nat(hi), AR.thaw(U32, t)) == G.LC{AR.thaw(U32, t), U32.from_nat(Nat.add(lo, W.lbs(v, AR.slots(U32, t), Nat.sub(hi, lo), lo))), SE.found_of(t, Nat.add(lo, W.lbs(v, AR.slots(U32, t), Nat.sub(hi, lo), lo)), hi, v)} : G.Loc}:
  +k = Nat.sub(hi, lo)
  +l = W.lbs(v, AR.slots(U32, t), k, lo)
  SE.locate_ok(d, t, v, lo, hi, Nat.add(lo, l), hd, pf,
    N.le_add_right(lo, l),
    L.subst(Nat, z => {Nat.is_le(Nat.add(lo, l), z) == True{} : Bool}, Nat.add(lo, k), hi, W.window_end(lo, hi, k, {==}, hlo),
      W.add_mono(lo, l, k, W.lbs_le(v, AR.slots(U32, t), k, lo))),
    hcap,
    L.subst(Nat, z => {SE.alllt(z, AR.slots(U32, t), lo, v) == True{} : Bool}, l, Nat.sub(Nat.add(lo, l), lo),
      Equal.sym(Nat, Nat.sub(Nat.add(lo, l), lo), l, N.add_sub_cancel(lo, l)),
      W.lbs_alllt(v, AR.slots(U32, t), k, lo)),
    L.subst(Nat, z => {SE.allge(z, AR.slots(U32, t), Nat.add(lo, l), v) == True{} : Bool}, Nat.sub(k, l), Nat.sub(hi, Nat.add(lo, l)),
      SE.sub_add_eq(hi, lo, l),
      W.lbs_allge(v, AR.slots(U32, t), k, lo, hs)))

# b <= a + b
def le_plus(+a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(b, z) == True{} : Bool}, Nat.add(b, a), Nat.add(a, b), N.add_comm(b, a), N.le_add_right(b, a))

# ---- one adjacency block ----

def v0(+bt: AR.Tree<U32>) -> U32:
  SH.val_at(AR.slots(U32, bt), 0n)

def v1(+bt: AR.Tree<U32>) -> U32:
  SH.val_at(AR.slots(U32, bt), 1n)

def v2(+bt: AR.Tree<U32>) -> U32:
  SH.val_at(AR.slots(U32, bt), 2n)

# The lower bound of w among the block's entries, as an absolute index.
def lbb(+bt: AR.Tree<U32>, +w: U32) -> Nat:
  Nat.add(3n, W.lbs(w, AR.slots(U32, bt), ST.bdeg(bt), 3n))

def blk_find_ok(+bt: AR.Tree<U32>, +w: U32, +hd: {Nat.is_lt(ST.blcap(bt), 32n) == True{} : Bool}, +pf: {AR.perfect(U32, ST.blcap(bt), bt) == True{} : Bool}, +hcap: {Nat.is_le(Nat.add(3n, ST.bdeg(bt)), SC.pow2(ST.blcap(bt))) == True{} : Bool}, +hs: {SE.asc_at(ST.bdeg(bt), AR.slots(U32, bt), 3n) == True{} : Bool}) -> {G.blk_find(AR.thaw(U32, bt), v0(bt), v2(bt), w) == G.LC{AR.thaw(U32, bt), U32.from_nat(lbb(bt, w)), SE.found_of(bt, lbb(bt, w), Nat.add(3n, ST.bdeg(bt)), w)} : G.Loc}:
  +lc = ST.blcap(bt)
  +dg = ST.bdeg(bt)
  +ehi = Equal.sym(Nat, Nat.sub(dg, 0n), dg, LL.sub_zero_eq(dg))
  %from_to(v0(bt), lc, N.lt_le(lc, 32n, hd), N.lt_le_trans(dg, Nat.add(3n, dg), SC.pow2(lc), N.le_lt_trans(dg, Nat.add(2n, dg), Nat.add(3n, dg), le_plus(2n, dg), N.lt_succ(Nat.add(2n, dg))), hcap)) : {G.blk_find(AR.thaw(U32, bt), _, v2(bt), w) == G.LC{AR.thaw(U32, bt), U32.from_nat(lbb(bt, w)), SE.found_of(bt, lbb(bt, w), Nat.add(3n, dg), w)} : G.Loc}
  L.subst(Nat, z => {G.locate(lc, w, 3, U32.from_nat(Nat.add(3n, dg)), AR.thaw(U32, bt)) == G.LC{AR.thaw(U32, bt), U32.from_nat(Nat.add(3n, W.lbs(w, AR.slots(U32, bt), z, 3n))), SE.found_of(bt, Nat.add(3n, W.lbs(w, AR.slots(U32, bt), z, 3n)), Nat.add(3n, dg), w)} : G.Loc}, Nat.sub(dg, 0n), dg, LL.sub_zero_eq(dg),
    win_locate(lc, bt, w, 3n, Nat.add(3n, dg), hd, pf, N.le_add_right(3n, dg), hcap,
      L.subst(Nat, z => {SE.asc_at(z, AR.slots(U32, bt), 3n) == True{} : Bool}, dg, Nat.sub(dg, 0n), ehi, hs)))

# Words 0, 1, 2 exist in a block of lcap >= 2.
def hdr_lt(+lc: Nat, +i: Nat, +h2: {Nat.is_le(2n, lc) == True{} : Bool}, +hi: {Nat.is_lt(i, 4n) == True{} : Bool}) -> {Nat.is_lt(i, SC.pow2(lc)) == True{} : Bool}:
  N.lt_le_trans(i, 4n, SC.pow2(lc), hi, N.pow2_mono(2n, lc, h2))

# Reading the three header words of a block.
def header_ok(+bt: AR.Tree<U32>, +hd: {Nat.is_lt(ST.blcap(bt), 32n) == True{} : Bool}, +h2: {Nat.is_le(2n, ST.blcap(bt)) == True{} : Bool}, +pf: {AR.perfect(U32, ST.blcap(bt), bt) == True{} : Bool}) -> {G.header(AR.thaw(U32, bt)) == G.HD{AR.thaw(U32, bt), v0(bt), v1(bt), v2(bt)} : G.Hdr}:
  +lc = ST.blcap(bt)
  +l0 = hdr_lt(lc, 0n, h2, {==})
  +l1 = hdr_lt(lc, 1n, h2, {==})
  +l2 = hdr_lt(lc, 2n, h2, {==})
  %Equal.sym(Array<U32> & U32, Array.get(U32, AR.thaw(U32, bt), 0), (AR.thaw(U32, bt), v0(bt)), AR.get(U32, lc, bt, 0, v0(bt), hd, l0, SH.some_at(lc, bt, 0n, pf, l0), pf)) : {G.hdr1(_) == G.HD{AR.thaw(U32, bt), v0(bt), v1(bt), v2(bt)} : G.Hdr}
  %Equal.sym(Array<U32> & U32, Array.get(U32, AR.thaw(U32, bt), 1), (AR.thaw(U32, bt), v1(bt)), AR.get(U32, lc, bt, 1, v1(bt), hd, l1, SH.some_at(lc, bt, 1n, pf, l1), pf)) : {G.hdr2(v0(bt), _) == G.HD{AR.thaw(U32, bt), v0(bt), v1(bt), v2(bt)} : G.Hdr}
  %Equal.sym(Array<U32> & U32, Array.get(U32, AR.thaw(U32, bt), 2), (AR.thaw(U32, bt), v2(bt)), AR.get(U32, lc, bt, 2, v2(bt), hd, l2, SH.some_at(lc, bt, 2n, pf, l2), pf)) : {G.hdr3(v0(bt), v1(bt), _) == G.HD{AR.thaw(U32, bt), v0(bt), v1(bt), v2(bt)} : G.Hdr}
  {==}

# ---- taking a block out of the adjacency array and putting it back ----

def leaf0() -> AR.Tree<U32>:
  AR.TLeaf{0}

def upd_nth_same(-T: Data, +d: Nat, +t: AR.Tree<T>, +j: Nat, +v: T, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(T, d, t) == True{} : Bool}) -> {SC.nth(T, AR.slots(T, AR.upd(T, d, t, j, v)), j) == Some{v} : Maybe<&2, T>}:
  L.subst(List<&2, T>, ys => {SC.nth(T, ys, j) == Some{v} : Maybe<&2, T>}, SC.update(T, AR.slots(T, t), j, v), AR.slots(T, AR.upd(T, d, t, j, v)),
    Equal.sym(List<&2, T>, AR.slots(T, AR.upd(T, d, t, j, v)), SC.update(T, AR.slots(T, t), j, v), AR.upd_slots(T, d, t, j, v, hj, pf)),
    LL.nth_update_same(T, AR.slots(T, t), j, v,
      L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, SC.pow2(d), SC.length(T, AR.slots(T, t)), Equal.sym(Nat, SC.length(T, AR.slots(T, t)), SC.pow2(d), AR.slots_length(T, d, t, pf)), hj)))

# Swap the block at i for a placeholder, then store b back at i.
def swap_back(+d: Nat, +at: AR.Tree<AR.Tree<U32>>, +i: U32, +bt: AR.Tree<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}, +hx: {SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), U32.to_nat(i)) == Some{bt} : Maybe<&2, AR.Tree<U32>>}, +pf: {AR.perfect(AR.Tree<U32>, d, at) == True{} : Bool}) -> {Array.set(Array<U32>, A2.thaw2(AR.upd(AR.Tree<U32>, d, at, U32.to_nat(i), leaf0())), i, AR.thaw(U32, bt)) == A2.thaw2(at) : Array<Array<U32>>}:
  +j = U32.to_nat(i)
  +at1 = AR.upd(AR.Tree<U32>, d, at, j, leaf0())
  Equal.trans(Array<Array<U32>>, Array.set(Array<U32>, A2.thaw2(at1), i, AR.thaw(U32, bt)), A2.thaw2(AR.upd(AR.Tree<U32>, d, at1, j, bt)), A2.thaw2(at),
    A2.set2(d, at1, i, bt, leaf0(), hd, hi, upd_nth_same(AR.Tree<U32>, d, at, j, leaf0(), hi, pf), AR.upd_perfect(AR.Tree<U32>, d, at, j, leaf0(), pf)),
    Equal.cong(AR.Tree<AR.Tree<U32>>, Array<Array<U32>>, z => A2.thaw2(z), AR.upd(AR.Tree<U32>, d, at1, j, bt), at, upd_back(AR.Tree<U32>, d, at, j, leaf0(), bt, hi, pf, hx)))

# Membership of w in the block of slot i leaves the adjacency unchanged.
def mem_nbr_ok(+d: Nat, +at: AR.Tree<AR.Tree<U32>>, +i: U32, +bt: AR.Tree<U32>, +w: U32, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}, +hx: {SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), U32.to_nat(i)) == Some{bt} : Maybe<&2, AR.Tree<U32>>}, +pf: {AR.perfect(AR.Tree<U32>, d, at) == True{} : Bool}, +bd: {Nat.is_lt(ST.blcap(bt), 32n) == True{} : Bool}, +b2: {Nat.is_le(2n, ST.blcap(bt)) == True{} : Bool}, +bp: {AR.perfect(U32, ST.blcap(bt), bt) == True{} : Bool}, +bcap: {Nat.is_le(Nat.add(3n, ST.bdeg(bt)), SC.pow2(ST.blcap(bt))) == True{} : Bool}, +bs: {SE.asc_at(ST.bdeg(bt), AR.slots(U32, bt), 3n) == True{} : Bool}) -> {G.mem_nbr(A2.thaw2(at), i, w) == G.UP{A2.thaw2(at), SE.found_of(bt, lbb(bt, w), Nat.add(3n, ST.bdeg(bt)), w)} : G.Upd}:
  +j = U32.to_nat(i)
  +at1 = AR.upd(AR.Tree<U32>, d, at, j, leaf0())
  +fd = SE.found_of(bt, lbb(bt, w), Nat.add(3n, ST.bdeg(bt)), w)
  %Equal.sym(Array<Array<U32>> & Array<U32>, Array.swap(Array<U32>, A2.thaw2(at), i, AR.thaw(U32, leaf0())), (A2.thaw2(at1), AR.thaw(U32, bt)), A2.swap2(d, at, i, leaf0(), bt, hd, hi, hx, pf)) : {G.mem_read(i, w, _) == G.UP{A2.thaw2(at), fd} : G.Upd}
  %Equal.sym(G.Hdr, G.header(AR.thaw(U32, bt)), G.HD{AR.thaw(U32, bt), v0(bt), v1(bt), v2(bt)}, header_ok(bt, bd, b2, bp)) : {G.mem_hdr(A2.thaw2(at1), i, w, _) == G.UP{A2.thaw2(at), fd} : G.Upd}
  %Equal.sym(G.Loc, G.blk_find(AR.thaw(U32, bt), v0(bt), v2(bt), w), G.LC{AR.thaw(U32, bt), U32.from_nat(lbb(bt, w)), fd}, blk_find_ok(bt, w, bd, bp, bcap, bs)) : {G.mem_loc(A2.thaw2(at1), i, _) == G.UP{A2.thaw2(at), fd} : G.Upd}
  Equal.cong(Array<Array<U32>>, G.Upd, z => G.UP{z, fd}, Array.set(Array<U32>, A2.thaw2(at1), i, AR.thaw(U32, bt)), A2.thaw2(at), swap_back(d, at, i, bt, hd, hi, hx, pf))

# ---- a read at ANY index returns the array unchanged and some element ----
#
# Base masks the index, so even a read that the algorithm discards (the
# loops that read one slot past their last element) is well defined; the
# proofs only need that it leaves the array as it was.

def GetAny(-T: Data, +t: AR.Tree<T>, +n: U32, +i: U32) -> Type:
  Sigma<&1, &1, T, x => {Array.get.go(T, AR.thaw(T, t), n, i) == (AR.thaw(T, t), x) : Array<T> & T}>

def get_if_pick(-T: Data, +l: AR.Tree<T>, +r: AR.Tree<T>, +h: U32, +i: U32, b: Bool, sl: GetAny(T, l, h, i), sr: GetAny(T, r, h, U32.sub(i, h))) -> Sigma<&1, &1, T, x => {Array.get.if(T, AR.thaw(T, l), AR.thaw(T, r), h, i, b) == (ANode{AR.thaw(T, l), AR.thaw(T, r)}, x) : Array<T> & T}>:
  match b:
    case True{}:
      (xl, el) = sl
      (xl, %Equal.sym(Array<T> & T, Array.get.go(T, AR.thaw(T, l), h, i), (AR.thaw(T, l), xl), el) : {Array.swap.lo(T, AR.thaw(T, r), _) == (ANode{AR.thaw(T, l), AR.thaw(T, r)}, xl) : Array<T> & T}
        {==})
    case False{}:
      (xr, er) = sr
      (xr, %Equal.sym(Array<T> & T, Array.get.go(T, AR.thaw(T, r), h, U32.sub(i, h)), (AR.thaw(T, r), xr), er) : {Array.swap.hi(T, AR.thaw(T, l), _) == (ANode{AR.thaw(T, l), AR.thaw(T, r)}, xr) : Array<T> & T}
        {==})

def get_go_any(-T: Data, +t: AR.Tree<T>, +n: U32, +i: U32) -> GetAny(T, t, n, i):
  match t:
    case AR.TLeaf{+x}:
      (x, {==})
    case AR.TNode{+l, +r}:
      get_if_pick(T, l, r, U32.shr(n), i, U32.is_lt(i, U32.shr(n)), get_go_any(T, l, U32.shr(n), i), get_go_any(T, r, U32.shr(n), U32.sub(i, U32.shr(n))))

def get_any_fin(-T: Data, +d: Nat, +t: AR.Tree<T>, +i: U32, +pf: {AR.perfect(T, d, t) == True{} : Bool}, s: GetAny(T, t, U.pow2u(d), U32.and(i, U32.sub(U.pow2u(d), 1)))) -> Sigma<&1, &1, T, x => {Array.get(T, AR.thaw(T, t), i) == (AR.thaw(T, t), x) : Array<T> & T}>:
  (x, e) = s
  (x, %Equal.sym(Array<T> & U32, Array.size(T, AR.thaw(T, t)), (AR.thaw(T, t), U.pow2u(d)), AR.size_thaw(T, d, t, pf)) : {Array.get.at(T, i, _) == (AR.thaw(T, t), x) : Array<T> & T}
    e)

def get_any(-T: Data, +d: Nat, +t: AR.Tree<T>, +i: U32, +pf: {AR.perfect(T, d, t) == True{} : Bool}) -> Sigma<&1, &1, T, x => {Array.get(T, AR.thaw(T, t), i) == (AR.thaw(T, t), x) : Array<T> & T}>:
  get_any_fin(T, d, t, i, pf, get_go_any(T, t, U.pow2u(d), U32.and(i, U32.sub(U.pow2u(d), 1))))
