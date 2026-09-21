import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/u32half.bend as H
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../src/graph.bend as G
import ./state.bend as ST
import ./shift.bend as SH
import ./search.bend as SE
import ./window.bend as W
import ./blk.bend as BK
import ./edge.bend as ED
import ./nbrs.bend as NB
import ./lists.bend as LS
import ./ext.bend as X
import ./asc.bend as AS

# Deleting and inserting one entry of an adjacency block: the mirror trees,
# the runtime equalities, the new entry lists and block well-formedness.

def shl_perfect(+k: Nat, +d: Nat, +t: AR.Tree<U32>, +j: Nat, +pf: {AR.perfect(U32, d, t) == True{} : Bool}) -> {AR.perfect(U32, d, SH.shl_tree(k, d, t, j)) == True{} : Bool}:
  match k:
    case 0n:
      pf
    case 1n+m:
      shl_perfect(m, d, AR.upd(U32, d, t, j, SH.val_at(AR.slots(U32, t), 1n+j)), 1n+j, AR.upd_perfect(U32, d, t, j, SH.val_at(AR.slots(U32, t), 1n+j), pf))

def shr_perfect(+k: Nat, +d: Nat, +t: AR.Tree<U32>, +j: Nat, +pf: {AR.perfect(U32, d, t) == True{} : Bool}) -> {AR.perfect(U32, d, SH.shr_tree(k, d, t, j)) == True{} : Bool}:
  match k:
    case 0n:
      pf
    case 1n+m:
      shr_perfect(m, d, AR.upd(U32, d, t, j, SH.val_at(AR.slots(U32, t), Nat.sub(j, 1n))), Nat.sub(j, 1n), AR.upd_perfect(U32, d, t, j, SH.val_at(AR.slots(U32, t), Nat.sub(j, 1n)), pf))

def ne_zero(+i: Nat, +h: {Nat.is_le(1n, i) == True{} : Bool}) -> {Nat.is_eq(i, 0n) == False{} : Bool}:
  match i:
    case 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, L.false_true(h))
    case 1n+p:
      {==}

def val_eq(+ys: List<&2, U32>, +xs: List<&2, U32>, +i: Nat, +j: Nat, +h: {SC.nth(U32, ys, i) == SC.nth(U32, xs, j) : Maybe<&2, U32>}) -> {SH.val_at(ys, i) == SH.val_at(xs, j) : U32}:
  Equal.cong(Maybe<&2, U32>, U32, m => L.some_value(U32, m, 0), SC.nth(U32, ys, i), SC.nth(U32, xs, j), h)

# ---- deletion ----

def kdel(+bt: AR.Tree<U32>, +l: Nat) -> Nat:
  Nat.sub(ST.bdeg(bt), 1n+l)

def tdel(+bt: AR.Tree<U32>, +l: Nat) -> AR.Tree<U32>:
  SH.shl_tree(kdel(bt, l), ST.blcap(bt), bt, Nat.add(3n, l))

def bdel(+bt: AR.Tree<U32>, +l: Nat) -> AR.Tree<U32>:
  AR.upd(U32, ST.blcap(bt), tdel(bt, l), 0n, U32.sub(BK.v0(bt), 1))

def del_end(+bt: AR.Tree<U32>, +l: Nat, +hl: {Nat.is_lt(l, ST.bdeg(bt)) == True{} : Bool}) -> {Nat.add(Nat.add(3n, l), kdel(bt, l)) == Nat.add(2n, ST.bdeg(bt)) : Nat}:
  Equal.cong(Nat, Nat, z => 2n+z, Nat.add(1n+l, Nat.sub(ST.bdeg(bt), 1n+l)), ST.bdeg(bt), N.sub_add(ST.bdeg(bt), 1n+l, N.lt_succ_le_succ(l, ST.bdeg(bt), hl)))

def del_hjk(+bt: AR.Tree<U32>, +l: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_lt(l, ST.bdeg(bt)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(Nat.add(3n, l), kdel(bt, l)), SC.pow2(ST.blcap(bt))) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(ST.blcap(bt))) == True{} : Bool}, Nat.add(2n, ST.bdeg(bt)), Nat.add(Nat.add(3n, l), kdel(bt, l)), Equal.sym(Nat, Nat.add(Nat.add(3n, l), kdel(bt, l)), Nat.add(2n, ST.bdeg(bt)), del_end(bt, l, hl)),
    N.lt_le_trans(Nat.add(2n, ST.bdeg(bt)), Nat.add(3n, ST.bdeg(bt)), SC.pow2(ST.blcap(bt)), N.lt_succ(Nat.add(2n, ST.bdeg(bt))), ED.bk_cap(bt, bk)))

def lt_cap(+bt: AR.Tree<U32>, +i: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +h: {Nat.is_lt(i, 4n) == True{} : Bool}) -> {Nat.is_lt(i, SC.pow2(ST.blcap(bt))) == True{} : Bool}:
  BK.hdr_lt(ST.blcap(bt), i, ED.bk_two(bt, bk), h)

# The runtime deletion is the mirror.
def blk_del_ok(+bt: AR.Tree<U32>, +l: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_lt(l, ST.bdeg(bt)) == True{} : Bool}) -> {G.blk_del(AR.thaw(U32, bt), BK.v0(bt), U32.from_nat(Nat.add(3n, l))) == AR.thaw(U32, bdel(bt, l)) : Array<U32>}:
  +lc = ST.blcap(bt)
  +dg = ST.bdeg(bt)
  +hd = ED.bk_lt32(bt, bk)
  +pf = ED.bk_perfect(bt, bk)
  +bcap = ED.bk_cap(bt, bk)
  +q = Nat.add(3n, l)
  +k = kdel(bt, l)
  +h2 = N.lt_le_trans(Nat.add(2n, dg), Nat.add(3n, dg), SC.pow2(lc), N.lt_succ(Nat.add(2n, dg)), bcap)
  +e0 = BK.from_to(BK.v0(bt), lc, N.lt_le(lc, 32n, hd), N.lt_le_trans(dg, Nat.add(3n, dg), SC.pow2(lc), N.le_lt_trans(dg, Nat.add(2n, dg), Nat.add(3n, dg), BK.le_plus(2n, dg), N.lt_succ(Nat.add(2n, dg))), bcap))
  +hq = N.lt_succ_le_succ(Nat.add(2n, l), Nat.add(2n, dg), N.le_lt_trans(Nat.add(2n, l), Nat.add(2n, l), Nat.add(2n, dg), N.le_refl(Nat.add(2n, l)), W.add_lt(2n, l, dg, hl)))
  +es = Equal.trans(Nat, U32.to_nat(U32.sub(U32.from_nat(Nat.add(2n, dg)), U32.from_nat(q))), U32.to_nat(U32.from_nat(k)), k,
    Equal.cong(U32, Nat, z => U32.to_nat(z), U32.sub(U32.from_nat(Nat.add(2n, dg)), U32.from_nat(q)), U32.from_nat(k), H.sub_bridge(Nat.add(2n, dg), q, lc, N.lt_le(lc, 32n, hd), h2, hq)),
    U.to_nat_from_nat(k, lc, N.lt_le(lc, 32n, hd), N.le_lt_trans(k, Nat.add(2n, dg), SC.pow2(lc), N.le_trans(k, dg, Nat.add(2n, dg), H.sub_le(dg, 1n+l), BK.le_plus(2n, dg)), h2)))
  %Equal.cong(U32, U32, z => U32.inc(U32.inc(z)), U32.from_nat(dg), BK.v0(bt), e0) : {Array.set(U32, G.shl_go(U32.to_nat(U32.sub(_, U32.from_nat(q))), U32.from_nat(q), AR.thaw(U32, bt)), 0, U32.sub(BK.v0(bt), 1)) == AR.thaw(U32, bdel(bt, l)) : Array<U32>}
  %Equal.sym(Nat, U32.to_nat(U32.sub(U32.from_nat(Nat.add(2n, dg)), U32.from_nat(q))), k, es) : {Array.set(U32, G.shl_go(_, U32.from_nat(q), AR.thaw(U32, bt)), 0, U32.sub(BK.v0(bt), 1)) == AR.thaw(U32, bdel(bt, l)) : Array<U32>}
  %Equal.sym(Array<U32>, G.shl_go(k, U32.from_nat(q), AR.thaw(U32, bt)), AR.thaw(U32, tdel(bt, l)), SH.shl_run(k, lc, bt, q, hd, pf, del_hjk(bt, l, bk, hl))) : {Array.set(U32, _, 0, U32.sub(BK.v0(bt), 1)) == AR.thaw(U32, bdel(bt, l)) : Array<U32>}
  SH.set_at(lc, tdel(bt, l), 0n, U32.sub(BK.v0(bt), 1), hd, shl_perfect(k, lc, bt, q, pf), lt_cap(bt, 0n, bk, {==}), {==})

# Index facts about the new block.
def del_other(+bt: AR.Tree<U32>, +l: Nat, +i: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hi: {Nat.is_le(1n, i) == True{} : Bool}) -> {SC.nth(U32, AR.slots(U32, bdel(bt, l)), i) == SC.nth(U32, AR.slots(U32, tdel(bt, l)), i) : Maybe<&2, U32>}:
  SH.upd_other(ST.blcap(bt), tdel(bt, l), 0n, U32.sub(BK.v0(bt), 1), i, shl_perfect(kdel(bt, l), ST.blcap(bt), bt, Nat.add(3n, l), ED.bk_perfect(bt, bk)), lt_cap(bt, 0n, bk, {==}), ne_zero(i, hi))

def del_below(+bt: AR.Tree<U32>, +l: Nat, +i: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_lt(l, ST.bdeg(bt)) == True{} : Bool}, +hi1: {Nat.is_le(1n, i) == True{} : Bool}, +hi: {Nat.is_lt(i, Nat.add(3n, l)) == True{} : Bool}) -> {SC.nth(U32, AR.slots(U32, bdel(bt, l)), i) == SC.nth(U32, AR.slots(U32, bt), i) : Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, bdel(bt, l)), i), SC.nth(U32, AR.slots(U32, tdel(bt, l)), i), SC.nth(U32, AR.slots(U32, bt), i),
    del_other(bt, l, i, bk, hi1),
    SH.shl_below(kdel(bt, l), ST.blcap(bt), bt, Nat.add(3n, l), i, ED.bk_perfect(bt, bk), del_hjk(bt, l, bk, hl), hi))

def del_moved(+bt: AR.Tree<U32>, +l: Nat, +i: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_lt(l, ST.bdeg(bt)) == True{} : Bool}, +h1: {Nat.is_le(Nat.add(3n, l), i) == True{} : Bool}, +h2: {Nat.is_lt(i, Nat.add(Nat.add(3n, l), kdel(bt, l))) == True{} : Bool}) -> {SC.nth(U32, AR.slots(U32, bdel(bt, l)), i) == SC.nth(U32, AR.slots(U32, bt), 1n+i) : Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, bdel(bt, l)), i), SC.nth(U32, AR.slots(U32, tdel(bt, l)), i), SC.nth(U32, AR.slots(U32, bt), 1n+i),
    del_other(bt, l, i, bk, N.le_trans(1n, Nat.add(3n, l), i, N.le_add_right(1n, Nat.add(2n, l)), h1)),
    SH.shl_moved(kdel(bt, l), ST.blcap(bt), bt, Nat.add(3n, l), i, ED.bk_perfect(bt, bk), del_hjk(bt, l, bk, hl), h1, h2))

def del_len(+bt: AR.Tree<U32>, +l: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}) -> {SC.length(U32, AR.slots(U32, bdel(bt, l))) == SC.length(U32, AR.slots(U32, bt)) : Nat}:
  +lc = ST.blcap(bt)
  +pf = ED.bk_perfect(bt, bk)
  Equal.trans(Nat, SC.length(U32, AR.slots(U32, bdel(bt, l))), SC.pow2(lc), SC.length(U32, AR.slots(U32, bt)),
    AR.slots_length(U32, lc, bdel(bt, l), AR.upd_perfect(U32, lc, tdel(bt, l), 0n, U32.sub(BK.v0(bt), 1), shl_perfect(kdel(bt, l), lc, bt, Nat.add(3n, l), pf))),
    Equal.sym(Nat, SC.length(U32, AR.slots(U32, bt)), SC.pow2(lc), AR.slots_length(U32, lc, bt, pf)))

def len_cap(+bt: AR.Tree<U32>, +bk: {ST.blk_ok(bt) == True{} : Bool}) -> {SC.length(U32, AR.slots(U32, bt)) == SC.pow2(ST.blcap(bt)) : Nat}:
  AR.slots_length(U32, ST.blcap(bt), bt, ED.bk_perfect(bt, bk))

# The unshifted prefix [a, a+m) with 1 <= a and a+m <= 3+l.
def pre_del(+m: Nat, +bt: AR.Tree<U32>, +l: Nat, +a: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_lt(l, ST.bdeg(bt)) == True{} : Bool}, +ha: {Nat.is_le(1n, a) == True{} : Bool}, +hq: {Nat.is_le(Nat.add(a, m), Nat.add(3n, l)) == True{} : Bool}) -> {ST.win(U32, AR.slots(U32, bdel(bt, l)), a, m) == ST.win(U32, AR.slots(U32, bt), a, m) : List<&2, U32>}:
  match m:
    case 0n:
      X.win_zero2(AR.slots(U32, bdel(bt, l)), AR.slots(U32, bt), a, a)
    case 1n+r:
      +xs = AR.slots(U32, bt)
      +ys = AR.slots(U32, bdel(bt, l))
      +hle = L.subst(Nat, z => {Nat.is_le(z, Nat.add(3n, l)) == True{} : Bool}, Nat.add(a, 1n+r), 1n+Nat.add(a, r), N.add_succ(a, r), hq)
      +haq = N.lt_le_trans(a, 1n+a, Nat.add(3n, l), N.lt_succ(a), N.le_trans(1n+a, 1n+Nat.add(a, r), Nat.add(3n, l), N.le_add_right(1n+a, r), hle))
      +hqd = N.lt_le(Nat.add(3n, l), Nat.add(3n, ST.bdeg(bt)), W.add_lt(3n, l, ST.bdeg(bt), hl))
      +hax = N.lt_le_trans(a, Nat.add(3n, ST.bdeg(bt)), SC.length(U32, xs), N.lt_le_trans(a, Nat.add(3n, l), Nat.add(3n, ST.bdeg(bt)), haq, hqd), L.subst(Nat, z => {Nat.is_le(Nat.add(3n, ST.bdeg(bt)), z) == True{} : Bool}, SC.pow2(ST.blcap(bt)), SC.length(U32, xs), Equal.sym(Nat, SC.length(U32, xs), SC.pow2(ST.blcap(bt)), len_cap(bt, bk)), ED.bk_cap(bt, bk)))
      +hay = L.subst(Nat, z => {Nat.is_lt(a, z) == True{} : Bool}, SC.length(U32, xs), SC.length(U32, ys), Equal.sym(Nat, SC.length(U32, ys), SC.length(U32, xs), del_len(bt, l, bk)), hax)
      X.win_step(ys, xs, a, a, r, hay, hax, del_below(bt, l, a, bk, hl, ha, haq),
        pre_del(r, bt, l, 1n+a, bk, hl, N.le_trans(1n, a, 1n+a, ha, N.lt_le(a, 1n+a, N.lt_succ(a))), hle))

# The shifted part: new [a, a+m) is old [1+a, 1+a+m), for 3+l <= a and a+m <= 3+l+k.
def sh_del(+m: Nat, +bt: AR.Tree<U32>, +l: Nat, +a: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_lt(l, ST.bdeg(bt)) == True{} : Bool}, +hqa: {Nat.is_le(Nat.add(3n, l), a) == True{} : Bool}, +hm: {Nat.is_le(Nat.add(a, m), Nat.add(Nat.add(3n, l), kdel(bt, l))) == True{} : Bool}) -> {ST.win(U32, AR.slots(U32, bdel(bt, l)), a, m) == ST.win(U32, AR.slots(U32, bt), 1n+a, m) : List<&2, U32>}:
  match m:
    case 0n:
      X.win_zero2(AR.slots(U32, bdel(bt, l)), AR.slots(U32, bt), a, 1n+a)
    case 1n+r:
      +xs = AR.slots(U32, bt)
      +ys = AR.slots(U32, bdel(bt, l))
      +qk = Nat.add(Nat.add(3n, l), kdel(bt, l))
      +hle = L.subst(Nat, z => {Nat.is_le(z, qk) == True{} : Bool}, Nat.add(a, 1n+r), 1n+Nat.add(a, r), N.add_succ(a, r), hm)
      +ha1 = N.le_trans(1n+a, 1n+Nat.add(a, r), qk, N.le_add_right(1n+a, r), hle)
      +hak = N.lt_le_trans(a, 1n+a, qk, N.lt_succ(a), ha1)
      +hqlen = L.subst(Nat, z => {Nat.is_lt(qk, z) == True{} : Bool}, SC.pow2(ST.blcap(bt)), SC.length(U32, xs), Equal.sym(Nat, SC.length(U32, xs), SC.pow2(ST.blcap(bt)), len_cap(bt, bk)), del_hjk(bt, l, bk, hl))
      +hax = N.le_lt_trans(1n+a, qk, SC.length(U32, xs), ha1, hqlen)
      +hay = L.subst(Nat, z => {Nat.is_lt(a, z) == True{} : Bool}, SC.length(U32, xs), SC.length(U32, ys), Equal.sym(Nat, SC.length(U32, ys), SC.length(U32, xs), del_len(bt, l, bk)), N.lt_trans(a, 1n+a, SC.length(U32, xs), N.lt_succ(a), hax))
      X.win_step(ys, xs, a, 1n+a, r, hay, hax, del_moved(bt, l, a, bk, hl, hqa, hak),
        sh_del(r, bt, l, 1n+a, bk, hl, N.le_trans(Nat.add(3n, l), a, 1n+a, hqa, N.lt_le(a, 1n+a, N.lt_succ(a))), hle))

# ---- the header of the new block ----

def del_perfect(+bt: AR.Tree<U32>, +l: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}) -> {AR.perfect(U32, ST.blcap(bt), bdel(bt, l)) == True{} : Bool}:
  AR.upd_perfect(U32, ST.blcap(bt), tdel(bt, l), 0n, U32.sub(BK.v0(bt), 1), shl_perfect(kdel(bt, l), ST.blcap(bt), bt, Nat.add(3n, l), ED.bk_perfect(bt, bk)))

def del_deg(+bt: AR.Tree<U32>, +l: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_lt(l, ST.bdeg(bt)) == True{} : Bool}) -> {ST.bdeg(bdel(bt, l)) == Nat.sub(ST.bdeg(bt), 1n) : Nat}:
  +lc = ST.blcap(bt)
  +x = U32.sub(BK.v0(bt), 1)
  +ev = val_eq(AR.slots(U32, bdel(bt, l)), Con{x, Nil{}}, 0n, 0n, SH.upd_same(lc, tdel(bt, l), 0n, x, shl_perfect(kdel(bt, l), lc, bt, Nat.add(3n, l), ED.bk_perfect(bt, bk)), lt_cap(bt, 0n, bk, {==})))
  Equal.trans(Nat, U32.to_nat(SH.val_at(AR.slots(U32, bdel(bt, l)), 0n)), U32.to_nat(x), Nat.sub(ST.bdeg(bt), 1n),
    Equal.cong(U32, Nat, z => U32.to_nat(z), SH.val_at(AR.slots(U32, bdel(bt, l)), 0n), x, ev),
    U.sub_nat(BK.v0(bt), 1, N.le_trans(1n, 1n+l, ST.bdeg(bt), N.le_add_right(1n, l), N.lt_succ_le_succ(l, ST.bdeg(bt), hl))))

def del_word(+bt: AR.Tree<U32>, +l: Nat, +i: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_lt(l, ST.bdeg(bt)) == True{} : Bool}, +hi1: {Nat.is_le(1n, i) == True{} : Bool}, +hi: {Nat.is_lt(i, 3n) == True{} : Bool}) -> {SH.val_at(AR.slots(U32, bdel(bt, l)), i) == SH.val_at(AR.slots(U32, bt), i) : U32}:
  val_eq(AR.slots(U32, bdel(bt, l)), AR.slots(U32, bt), i, i, del_below(bt, l, i, bk, hl, hi1, N.lt_le_trans(i, 3n, Nat.add(3n, l), hi, N.le_add_right(3n, l))))

def del_cap(+bt: AR.Tree<U32>, +l: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_lt(l, ST.bdeg(bt)) == True{} : Bool}) -> {ST.blcap(bdel(bt, l)) == ST.blcap(bt) : Nat}:
  Equal.cong(U32, Nat, z => U32.to_nat(z), SH.val_at(AR.slots(U32, bdel(bt, l)), 2n), SH.val_at(AR.slots(U32, bt), 2n), del_word(bt, l, 2n, bk, hl, {==}, {==}))

def del_size(+bt: AR.Tree<U32>, +l: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_lt(l, ST.bdeg(bt)) == True{} : Bool}) -> {ST.bsize(bdel(bt, l)) == ST.bsize(bt) : Nat}:
  Equal.cong(U32, Nat, z => U32.to_nat(z), SH.val_at(AR.slots(U32, bdel(bt, l)), 1n), SH.val_at(AR.slots(U32, bt), 1n), del_word(bt, l, 1n, bk, hl, {==}, {==}))

# ---- the new entries ----

def sub_split1(+a: Nat, +l: Nat, +h: {Nat.is_lt(l, a) == True{} : Bool}) -> {Nat.sub(a, l) == 1n+Nat.sub(a, 1n+l) : Nat}:
  +x = Nat.sub(a, l)
  Equal.trans(Nat, x, Nat.add(1n, Nat.sub(x, 1n)), 1n+Nat.sub(a, 1n+l),
    Equal.sym(Nat, Nat.add(1n, Nat.sub(x, 1n)), x, N.sub_add(x, 1n, N.lt_succ_le_succ(0n, x, SE.sub_pos(a, l, h)))),
    Equal.cong(Nat, Nat, z => 1n+z, Nat.sub(x, 1n), Nat.sub(a, 1n+l), Equal.sym(Nat, Nat.sub(a, 1n+l), Nat.sub(x, 1n), SE.sub_succ_right(a, l))))

def fits(+bt: AR.Tree<U32>, +n: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +h: {Nat.is_le(n, Nat.add(3n, ST.bdeg(bt))) == True{} : Bool}) -> {Nat.is_le(n, SC.length(U32, AR.slots(U32, bt))) == True{} : Bool}:
  N.le_trans(n, Nat.add(3n, ST.bdeg(bt)), SC.length(U32, AR.slots(U32, bt)), h,
    L.subst(Nat, z => {Nat.is_le(Nat.add(3n, ST.bdeg(bt)), z) == True{} : Bool}, SC.pow2(ST.blcap(bt)), SC.length(U32, AR.slots(U32, bt)), Equal.sym(Nat, SC.length(U32, AR.slots(U32, bt)), SC.pow2(ST.blcap(bt)), len_cap(bt, bk)), ED.bk_cap(bt, bk)))

def del_bents(+bt: AR.Tree<U32>, +l: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_lt(l, ST.bdeg(bt)) == True{} : Bool}) -> {ST.bents(bdel(bt, l)) == LS.dl(ST.bents(bt), l) : List<&2, U32>}:
  +dg = ST.bdeg(bt)
  +xs = AR.slots(U32, bt)
  +ys = AR.slots(U32, bdel(bt, l))
  +q = Nat.add(3n, l)
  +k = kdel(bt, l)
  +as = ST.win(U32, xs, 3n, l)
  +x = SH.val_at(xs, q)
  +bs = ST.win(U32, xs, 1n+q, k)
  +hld = N.lt_le(l, dg, hl)
  +hql = N.lt_le_trans(q, Nat.add(3n, dg), SC.length(U32, xs), W.add_lt(3n, l, dg, hl), fits(bt, Nat.add(3n, dg), bk, N.le_refl(Nat.add(3n, dg))))
  +ek = Equal.sym(Nat, Nat.sub(Nat.sub(dg, 1n), l), k, SE.sub_add_eq(dg, 1n, l))
  +er1 = Equal.trans(List<&2, U32>, ST.win(U32, xs, 3n, dg), SC.append(U32, as, ST.win(U32, xs, q, Nat.sub(dg, l))), SC.append(U32, as, Con{x, bs}),
    X.win_split(U32, xs, 3n, l, dg, hld),
    Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.append(U32, as, z), ST.win(U32, xs, q, Nat.sub(dg, l)), Con{x, bs},
      Equal.trans(List<&2, U32>, ST.win(U32, xs, q, Nat.sub(dg, l)), ST.win(U32, xs, q, 1n+k), Con{x, bs},
        Equal.cong(Nat, List<&2, U32>, z => ST.win(U32, xs, q, z), Nat.sub(dg, l), 1n+k, sub_split1(dg, l, hl)),
        X.win_cons(xs, q, k, hql))))
  +er2 = L.subst(Nat, z => {LS.dl(SC.append(U32, as, Con{x, bs}), z) == SC.append(U32, as, bs) : List<&2, U32>}, SC.length(U32, as), l,
    W.win_length(xs, 3n, l, fits(bt, Nat.add(3n, l), bk, N.le_add_left(l, dg, 3n, hld))),
    X.dl_app(as, x, bs))
  +el = Equal.trans(List<&2, U32>, ST.win(U32, ys, 3n, Nat.sub(dg, 1n)), SC.append(U32, ST.win(U32, ys, 3n, l), ST.win(U32, ys, q, Nat.sub(Nat.sub(dg, 1n), l))), SC.append(U32, as, bs),
    X.win_split(U32, ys, 3n, l, Nat.sub(dg, 1n), SH.le_pred(l, dg, N.lt_succ_le_succ(l, dg, hl))),
    Equal.trans(List<&2, U32>, SC.append(U32, ST.win(U32, ys, 3n, l), ST.win(U32, ys, q, Nat.sub(Nat.sub(dg, 1n), l))), SC.append(U32, as, ST.win(U32, ys, q, Nat.sub(Nat.sub(dg, 1n), l))), SC.append(U32, as, bs),
      Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.append(U32, z, ST.win(U32, ys, q, Nat.sub(Nat.sub(dg, 1n), l))), ST.win(U32, ys, 3n, l), as, pre_del(l, bt, l, 3n, bk, hl, {==}, N.le_refl(q))),
      Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.append(U32, as, z), ST.win(U32, ys, q, Nat.sub(Nat.sub(dg, 1n), l)), bs,
        L.subst(Nat, z => {ST.win(U32, ys, q, z) == ST.win(U32, xs, 1n+q, k) : List<&2, U32>}, k, Nat.sub(Nat.sub(dg, 1n), l), ek,
          sh_del(k, bt, l, q, bk, hl, N.le_refl(q), N.le_refl(Nat.add(q, k)))))))
  Equal.trans(List<&2, U32>, ST.win(U32, ys, 3n, ST.bdeg(bdel(bt, l))), ST.win(U32, ys, 3n, Nat.sub(dg, 1n)), LS.dl(ST.win(U32, xs, 3n, dg), l),
    Equal.cong(Nat, List<&2, U32>, z => ST.win(U32, ys, 3n, z), ST.bdeg(bdel(bt, l)), Nat.sub(dg, 1n), del_deg(bt, l, bk, hl)),
    Equal.trans(List<&2, U32>, ST.win(U32, ys, 3n, Nat.sub(dg, 1n)), SC.append(U32, as, bs), LS.dl(ST.win(U32, xs, 3n, dg), l),
      el,
      Equal.sym(List<&2, U32>, LS.dl(ST.win(U32, xs, 3n, dg), l), SC.append(U32, as, bs),
        Equal.trans(List<&2, U32>, LS.dl(ST.win(U32, xs, 3n, dg), l), LS.dl(SC.append(U32, as, Con{x, bs}), l), SC.append(U32, as, bs),
          Equal.cong(List<&2, U32>, List<&2, U32>, z => LS.dl(z, l), ST.win(U32, xs, 3n, dg), SC.append(U32, as, Con{x, bs}), er1),
          er2))))

# ---- block well-formedness from its parts ----

def blk_ok_mk(+b: AR.Tree<U32>, +pf: {AR.perfect(U32, ST.blcap(b), b) == True{} : Bool}, +h2: {Nat.is_le(2n, ST.blcap(b)) == True{} : Bool}, +h31: {Nat.is_le(ST.blcap(b), 31n) == True{} : Bool}, +hs: {Nat.is_eq(ST.bsize(b), SC.pow2(ST.blcap(b))) == True{} : Bool}, +hf: {Nat.is_le(Nat.add(3n, ST.bdeg(b)), ST.bsize(b)) == True{} : Bool}, +ha: {SE.asc_at(ST.bdeg(b), AR.slots(U32, b), 3n) == True{} : Bool}) -> {ST.blk_ok(b) == True{} : Bool}:
  L.and_intro(AR.perfect(U32, ST.blcap(b), b), ED.b1(b), pf,
    L.and_intro(Nat.is_le(2n, ST.blcap(b)), ED.b2(b), h2,
      L.and_intro(Nat.is_le(ST.blcap(b), 31n), ED.b3(b), h31,
        L.and_intro(Nat.is_eq(ST.bsize(b), SC.pow2(ST.blcap(b))), ED.b4(b), hs,
          L.and_intro(Nat.is_le(Nat.add(3n, ST.bdeg(b)), ST.bsize(b)), SE.asc_at(ST.bdeg(b), AR.slots(U32, b), 3n), hf, ha)))))

def del_ok(+bt: AR.Tree<U32>, +l: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_lt(l, ST.bdeg(bt)) == True{} : Bool}) -> {ST.blk_ok(bdel(bt, l)) == True{} : Bool}:
  +b = bdel(bt, l)
  +dg = ST.bdeg(bt)
  +ec = Equal.sym(Nat, ST.blcap(b), ST.blcap(bt), del_cap(bt, l, bk, hl))
  +es = Equal.sym(Nat, ST.bsize(b), ST.bsize(bt), del_size(bt, l, bk, hl))
  +ed = Equal.sym(Nat, ST.bdeg(b), Nat.sub(dg, 1n), del_deg(bt, l, bk, hl))
  +hld = SH.le_pred(l, dg, N.lt_succ_le_succ(l, dg, hl))
  +hdd = N.le_trans(Nat.sub(dg, 1n), dg, dg, H.sub_le(dg, 1n), N.le_refl(dg))
  +hwin = AS.asc_dl(ST.bents(bt), l, W.asc_win(dg, AR.slots(U32, bt), 3n, ED.bk_asc(bt, bk)))
  +hwin2 = L.subst(List<&2, U32>, z => {ST.asc(z) == True{} : Bool}, LS.dl(ST.bents(bt), l), ST.bents(b), Equal.sym(List<&2, U32>, ST.bents(b), LS.dl(ST.bents(bt), l), del_bents(bt, l, bk, hl)), hwin)
  +hlen = L.subst(Nat, z => {Nat.is_le(Nat.add(3n, z), SC.length(U32, AR.slots(U32, b))) == True{} : Bool}, Nat.sub(dg, 1n), ST.bdeg(b), ed,
    L.subst(Nat, z => {Nat.is_le(Nat.add(3n, Nat.sub(dg, 1n)), z) == True{} : Bool}, SC.length(U32, AR.slots(U32, bt)), SC.length(U32, AR.slots(U32, b)), Equal.sym(Nat, SC.length(U32, AR.slots(U32, b)), SC.length(U32, AR.slots(U32, bt)), del_len(bt, l, bk)),
      fits(bt, Nat.add(3n, Nat.sub(dg, 1n)), bk, N.le_add_left(Nat.sub(dg, 1n), dg, 3n, hdd))))
  blk_ok_mk(b,
    L.subst(Nat, z => {AR.perfect(U32, z, b) == True{} : Bool}, ST.blcap(bt), ST.blcap(b), ec, del_perfect(bt, l, bk)),
    L.subst(Nat, z => {Nat.is_le(2n, z) == True{} : Bool}, ST.blcap(bt), ST.blcap(b), ec, ED.bk_two(bt, bk)),
    L.subst(Nat, z => {Nat.is_le(z, 31n) == True{} : Bool}, ST.blcap(bt), ST.blcap(b), ec, ED.bk_le31(bt, bk)),
    L.subst(Nat, z => {Nat.is_eq(ST.bsize(b), SC.pow2(z)) == True{} : Bool}, ST.blcap(bt), ST.blcap(b), ec,
      L.subst(Nat, z => {Nat.is_eq(z, SC.pow2(ST.blcap(bt))) == True{} : Bool}, ST.bsize(bt), ST.bsize(b), es, ED.bk_size(bt, bk))),
    L.subst(Nat, z => {Nat.is_le(Nat.add(3n, z), ST.bsize(b)) == True{} : Bool}, Nat.sub(dg, 1n), ST.bdeg(b), ed,
      L.subst(Nat, z => {Nat.is_le(Nat.add(3n, Nat.sub(dg, 1n)), z) == True{} : Bool}, ST.bsize(bt), ST.bsize(b), es,
        N.le_trans(Nat.add(3n, Nat.sub(dg, 1n)), Nat.add(3n, dg), ST.bsize(bt), N.le_add_left(Nat.sub(dg, 1n), dg, 3n, hdd), ED.bk_fit(bt, bk)))),
    AS.asc_at_of_win(ST.bdeg(b), AR.slots(U32, b), 3n, hlen, hwin2))

# ---- insertion ----

def sub_shift(+c: Nat, +x: Nat, +y: Nat, +h: {Nat.is_le(y, x) == True{} : Bool}) -> {Nat.sub(Nat.add(c, x), y) == Nat.add(c, Nat.sub(x, y)) : Nat}:
  match x y:
    case x0 0n:
      Equal.trans(Nat, Nat.sub(Nat.add(c, x0), 0n), Nat.add(c, x0), Nat.add(c, Nat.sub(x0, 0n)), N.sub_zero(Nat.add(c, x0)), Equal.cong(Nat, Nat, z => Nat.add(c, z), x0, Nat.sub(x0, 0n), Equal.sym(Nat, Nat.sub(x0, 0n), x0, N.sub_zero(x0))))
    case 0n 1n+q:
      Empty.absurd({Nat.sub(Nat.add(c, 0n), 1n+q) == Nat.add(c, Nat.sub(0n, 1n+q)) : Nat}, L.false_true(h))
    case 1n+p 1n+q:
      %Equal.sym(Nat, Nat.add(c, 1n+p), 1n+Nat.add(c, p), N.add_succ(c, p)) : {Nat.sub(_, 1n+q) == Nat.add(c, Nat.sub(p, q)) : Nat}
      sub_shift(c, p, q, h)

def sub_succ_l(+a: Nat, +b: Nat, +h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.sub(1n+a, b) == 1n+Nat.sub(a, b) : Nat}:
  sub_shift(1n, a, b, h)

def kput(+bt: AR.Tree<U32>, +l: Nat) -> Nat:
  Nat.sub(ST.bdeg(bt), l)

def tput(+bt: AR.Tree<U32>, +l: Nat) -> AR.Tree<U32>:
  SH.shr_tree(kput(bt, l), ST.blcap(bt), bt, Nat.add(3n, ST.bdeg(bt)))

def uput(+bt: AR.Tree<U32>, +l: Nat, +w: U32) -> AR.Tree<U32>:
  AR.upd(U32, ST.blcap(bt), tput(bt, l), Nat.add(3n, l), w)

def bput(+bt: AR.Tree<U32>, +l: Nat, +w: U32) -> AR.Tree<U32>:
  AR.upd(U32, ST.blcap(bt), uput(bt, l, w), 0n, U32.inc(BK.v0(bt)))

def room_cap(+bt: AR.Tree<U32>, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hr: {Nat.is_lt(Nat.add(3n, ST.bdeg(bt)), ST.bsize(bt)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(3n, ST.bdeg(bt)), SC.pow2(ST.blcap(bt))) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(Nat.add(3n, ST.bdeg(bt)), z) == True{} : Bool}, ST.bsize(bt), SC.pow2(ST.blcap(bt)), N.eq_from_is_eq(ST.bsize(bt), SC.pow2(ST.blcap(bt)), ED.bk_size(bt, bk)), hr)

def put_bound(+bt: AR.Tree<U32>, +l: Nat, +hl: {Nat.is_le(l, ST.bdeg(bt)) == True{} : Bool}) -> {Nat.sub(Nat.add(3n, ST.bdeg(bt)), kput(bt, l)) == Nat.add(3n, l) : Nat}:
  Equal.trans(Nat, Nat.sub(Nat.add(3n, ST.bdeg(bt)), kput(bt, l)), Nat.add(3n, Nat.sub(ST.bdeg(bt), kput(bt, l))), Nat.add(3n, l),
    sub_shift(3n, ST.bdeg(bt), kput(bt, l), H.sub_le(ST.bdeg(bt), l)),
    Equal.cong(Nat, Nat, z => Nat.add(3n, z), Nat.sub(ST.bdeg(bt), kput(bt, l)), l, SE.sub_sub_cancel(ST.bdeg(bt), l, hl)))

def tput_perfect(+bt: AR.Tree<U32>, +l: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}) -> {AR.perfect(U32, ST.blcap(bt), tput(bt, l)) == True{} : Bool}:
  shr_perfect(kput(bt, l), ST.blcap(bt), bt, Nat.add(3n, ST.bdeg(bt)), ED.bk_perfect(bt, bk))

def uput_perfect(+bt: AR.Tree<U32>, +l: Nat, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}) -> {AR.perfect(U32, ST.blcap(bt), uput(bt, l, w)) == True{} : Bool}:
  AR.upd_perfect(U32, ST.blcap(bt), tput(bt, l), Nat.add(3n, l), w, tput_perfect(bt, l, bk))

def put_perfect(+bt: AR.Tree<U32>, +l: Nat, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}) -> {AR.perfect(U32, ST.blcap(bt), bput(bt, l, w)) == True{} : Bool}:
  AR.upd_perfect(U32, ST.blcap(bt), uput(bt, l, w), 0n, U32.inc(BK.v0(bt)), uput_perfect(bt, l, w, bk))

def q_lt_cap(+bt: AR.Tree<U32>, +l: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_le(l, ST.bdeg(bt)) == True{} : Bool}, +hr: {Nat.is_lt(Nat.add(3n, ST.bdeg(bt)), ST.bsize(bt)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(3n, l), SC.pow2(ST.blcap(bt))) == True{} : Bool}:
  N.le_lt_trans(Nat.add(3n, l), Nat.add(3n, ST.bdeg(bt)), SC.pow2(ST.blcap(bt)), N.le_add_left(l, ST.bdeg(bt), 3n, hl), room_cap(bt, bk, hr))

# The runtime insertion is the mirror.
def blk_put_ok(+bt: AR.Tree<U32>, +l: Nat, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_le(l, ST.bdeg(bt)) == True{} : Bool}, +hr: {Nat.is_lt(Nat.add(3n, ST.bdeg(bt)), ST.bsize(bt)) == True{} : Bool}) -> {G.blk_put(AR.thaw(U32, bt), BK.v0(bt), U32.from_nat(Nat.add(3n, l)), w) == AR.thaw(U32, bput(bt, l, w)) : Array<U32>}:
  +lc = ST.blcap(bt)
  +dg = ST.bdeg(bt)
  +hd = ED.bk_lt32(bt, bk)
  +pf = ED.bk_perfect(bt, bk)
  +bcap = ED.bk_cap(bt, bk)
  +q = Nat.add(3n, l)
  +j = Nat.add(3n, dg)
  +k = kput(bt, l)
  +hj = room_cap(bt, bk, hr)
  +hql = N.le_add_left(l, dg, 3n, hl)
  +e0 = BK.from_to(BK.v0(bt), lc, N.lt_le(lc, 32n, hd), N.lt_le_trans(dg, Nat.add(3n, dg), SC.pow2(lc), N.le_lt_trans(dg, Nat.add(2n, dg), Nat.add(3n, dg), BK.le_plus(2n, dg), N.lt_succ(Nat.add(2n, dg))), bcap))
  +es = Equal.trans(Nat, U32.to_nat(U32.sub(U32.from_nat(j), U32.from_nat(q))), U32.to_nat(U32.from_nat(k)), k,
    Equal.cong(U32, Nat, z => U32.to_nat(z), U32.sub(U32.from_nat(j), U32.from_nat(q)), U32.from_nat(k), H.sub_bridge(j, q, lc, N.lt_le(lc, 32n, hd), hj, hql)),
    U.to_nat_from_nat(k, lc, N.lt_le(lc, 32n, hd), N.le_lt_trans(k, j, SC.pow2(lc), N.le_trans(k, dg, j, H.sub_le(dg, l), BK.le_plus(3n, dg)), hj)))
  +hq = q_lt_cap(bt, l, bk, hl, hr)
  +rq = U.to_nat_from_nat(q, lc, N.lt_le(lc, 32n, hd), hq)
  %Equal.cong(U32, U32, z => U32.inc(U32.inc(U32.inc(z))), U32.from_nat(dg), BK.v0(bt), e0) : {Array.set(U32, Array.set(U32, G.shr_go(U32.to_nat(U32.sub(_, U32.from_nat(q))), _, AR.thaw(U32, bt)), U32.from_nat(q), w), 0, U32.inc(BK.v0(bt))) == AR.thaw(U32, bput(bt, l, w)) : Array<U32>}
  %Equal.sym(Nat, U32.to_nat(U32.sub(U32.from_nat(j), U32.from_nat(q))), k, es) : {Array.set(U32, Array.set(U32, G.shr_go(_, U32.from_nat(j), AR.thaw(U32, bt)), U32.from_nat(q), w), 0, U32.inc(BK.v0(bt))) == AR.thaw(U32, bput(bt, l, w)) : Array<U32>}
  %Equal.sym(Array<U32>, G.shr_go(k, U32.from_nat(j), AR.thaw(U32, bt)), AR.thaw(U32, tput(bt, l)), SH.shr_run(k, lc, bt, j, hd, pf, hj, N.le_trans(k, dg, j, H.sub_le(dg, l), BK.le_plus(3n, dg)))) : {Array.set(U32, Array.set(U32, _, U32.from_nat(q), w), 0, U32.inc(BK.v0(bt))) == AR.thaw(U32, bput(bt, l, w)) : Array<U32>}
  %Equal.sym(Array<U32>, Array.set(U32, AR.thaw(U32, tput(bt, l)), U32.from_nat(q), w), AR.thaw(U32, uput(bt, l, w)), SH.set_at(lc, tput(bt, l), q, w, hd, tput_perfect(bt, l, bk), hq, rq)) : {Array.set(U32, _, 0, U32.inc(BK.v0(bt))) == AR.thaw(U32, bput(bt, l, w)) : Array<U32>}
  SH.set_at(lc, uput(bt, l, w), 0n, U32.inc(BK.v0(bt)), hd, uput_perfect(bt, l, w, bk), lt_cap(bt, 0n, bk, {==}), {==})

def put_other(+bt: AR.Tree<U32>, +l: Nat, +w: U32, +i: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hi: {Nat.is_le(1n, i) == True{} : Bool}) -> {SC.nth(U32, AR.slots(U32, bput(bt, l, w)), i) == SC.nth(U32, AR.slots(U32, uput(bt, l, w)), i) : Maybe<&2, U32>}:
  SH.upd_other(ST.blcap(bt), uput(bt, l, w), 0n, U32.inc(BK.v0(bt)), i, uput_perfect(bt, l, w, bk), lt_cap(bt, 0n, bk, {==}), ne_zero(i, hi))

def put_q(+bt: AR.Tree<U32>, +l: Nat, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_le(l, ST.bdeg(bt)) == True{} : Bool}, +hr: {Nat.is_lt(Nat.add(3n, ST.bdeg(bt)), ST.bsize(bt)) == True{} : Bool}) -> {SC.nth(U32, AR.slots(U32, bput(bt, l, w)), Nat.add(3n, l)) == Some{w} : Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, bput(bt, l, w)), Nat.add(3n, l)), SC.nth(U32, AR.slots(U32, uput(bt, l, w)), Nat.add(3n, l)), Some{w},
    put_other(bt, l, w, Nat.add(3n, l), bk, N.le_add_right(1n, Nat.add(2n, l))),
    SH.upd_same(ST.blcap(bt), tput(bt, l), Nat.add(3n, l), w, tput_perfect(bt, l, bk), q_lt_cap(bt, l, bk, hl, hr)))

def put_below(+bt: AR.Tree<U32>, +l: Nat, +w: U32, +i: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_le(l, ST.bdeg(bt)) == True{} : Bool}, +hr: {Nat.is_lt(Nat.add(3n, ST.bdeg(bt)), ST.bsize(bt)) == True{} : Bool}, +hi1: {Nat.is_le(1n, i) == True{} : Bool}, +hi: {Nat.is_lt(i, Nat.add(3n, l)) == True{} : Bool}) -> {SC.nth(U32, AR.slots(U32, bput(bt, l, w)), i) == SC.nth(U32, AR.slots(U32, bt), i) : Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, bput(bt, l, w)), i), SC.nth(U32, AR.slots(U32, uput(bt, l, w)), i), SC.nth(U32, AR.slots(U32, bt), i),
    put_other(bt, l, w, i, bk, hi1),
    Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, uput(bt, l, w)), i), SC.nth(U32, AR.slots(U32, tput(bt, l)), i), SC.nth(U32, AR.slots(U32, bt), i),
      SH.upd_other(ST.blcap(bt), tput(bt, l), Nat.add(3n, l), w, i, tput_perfect(bt, l, bk), q_lt_cap(bt, l, bk, hl, hr), SH.ne_of_lt(i, Nat.add(3n, l), hi)),
      SH.shr_below(kput(bt, l), ST.blcap(bt), bt, Nat.add(3n, ST.bdeg(bt)), i, ED.bk_perfect(bt, bk), room_cap(bt, bk, hr), N.le_trans(kput(bt, l), ST.bdeg(bt), Nat.add(3n, ST.bdeg(bt)), H.sub_le(ST.bdeg(bt), l), BK.le_plus(3n, ST.bdeg(bt))),
        L.subst(Nat, z => {Nat.is_le(i, z) == True{} : Bool}, Nat.add(3n, l), Nat.sub(Nat.add(3n, ST.bdeg(bt)), kput(bt, l)), Equal.sym(Nat, Nat.sub(Nat.add(3n, ST.bdeg(bt)), kput(bt, l)), Nat.add(3n, l), put_bound(bt, l, hl)), N.lt_le(i, Nat.add(3n, l), hi)))))

def put_moved(+bt: AR.Tree<U32>, +l: Nat, +w: U32, +i: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_le(l, ST.bdeg(bt)) == True{} : Bool}, +hr: {Nat.is_lt(Nat.add(3n, ST.bdeg(bt)), ST.bsize(bt)) == True{} : Bool}, +h1: {Nat.is_lt(Nat.add(3n, l), i) == True{} : Bool}, +h2: {Nat.is_le(i, Nat.add(3n, ST.bdeg(bt))) == True{} : Bool}) -> {SC.nth(U32, AR.slots(U32, bput(bt, l, w)), i) == SC.nth(U32, AR.slots(U32, bt), Nat.sub(i, 1n)) : Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, bput(bt, l, w)), i), SC.nth(U32, AR.slots(U32, uput(bt, l, w)), i), SC.nth(U32, AR.slots(U32, bt), Nat.sub(i, 1n)),
    put_other(bt, l, w, i, bk, N.le_trans(1n, Nat.add(3n, l), i, N.le_add_right(1n, Nat.add(2n, l)), N.lt_le(Nat.add(3n, l), i, h1))),
    Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, uput(bt, l, w)), i), SC.nth(U32, AR.slots(U32, tput(bt, l)), i), SC.nth(U32, AR.slots(U32, bt), Nat.sub(i, 1n)),
      SH.upd_other(ST.blcap(bt), tput(bt, l), Nat.add(3n, l), w, i, tput_perfect(bt, l, bk), q_lt_cap(bt, l, bk, hl, hr), SH.ne_flip(Nat.add(3n, l), i, SH.ne_of_lt(Nat.add(3n, l), i, h1))),
      SH.shr_moved(kput(bt, l), ST.blcap(bt), bt, Nat.add(3n, ST.bdeg(bt)), i, ED.bk_perfect(bt, bk), room_cap(bt, bk, hr), N.le_trans(kput(bt, l), ST.bdeg(bt), Nat.add(3n, ST.bdeg(bt)), H.sub_le(ST.bdeg(bt), l), BK.le_plus(3n, ST.bdeg(bt))),
        L.subst(Nat, z => {Nat.is_lt(z, i) == True{} : Bool}, Nat.add(3n, l), Nat.sub(Nat.add(3n, ST.bdeg(bt)), kput(bt, l)), Equal.sym(Nat, Nat.sub(Nat.add(3n, ST.bdeg(bt)), kput(bt, l)), Nat.add(3n, l), put_bound(bt, l, hl)), h1),
        h2)))

def put_len(+bt: AR.Tree<U32>, +l: Nat, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}) -> {SC.length(U32, AR.slots(U32, bput(bt, l, w))) == SC.length(U32, AR.slots(U32, bt)) : Nat}:
  Equal.trans(Nat, SC.length(U32, AR.slots(U32, bput(bt, l, w))), SC.pow2(ST.blcap(bt)), SC.length(U32, AR.slots(U32, bt)),
    AR.slots_length(U32, ST.blcap(bt), bput(bt, l, w), put_perfect(bt, l, w, bk)),
    Equal.sym(Nat, SC.length(U32, AR.slots(U32, bt)), SC.pow2(ST.blcap(bt)), len_cap(bt, bk)))

def pre_put(+m: Nat, +bt: AR.Tree<U32>, +l: Nat, +w: U32, +a: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_le(l, ST.bdeg(bt)) == True{} : Bool}, +hr: {Nat.is_lt(Nat.add(3n, ST.bdeg(bt)), ST.bsize(bt)) == True{} : Bool}, +ha: {Nat.is_le(1n, a) == True{} : Bool}, +hq: {Nat.is_le(Nat.add(a, m), Nat.add(3n, l)) == True{} : Bool}) -> {ST.win(U32, AR.slots(U32, bput(bt, l, w)), a, m) == ST.win(U32, AR.slots(U32, bt), a, m) : List<&2, U32>}:
  match m:
    case 0n:
      X.win_zero2(AR.slots(U32, bput(bt, l, w)), AR.slots(U32, bt), a, a)
    case 1n+r:
      +xs = AR.slots(U32, bt)
      +ys = AR.slots(U32, bput(bt, l, w))
      +hle = L.subst(Nat, z => {Nat.is_le(z, Nat.add(3n, l)) == True{} : Bool}, Nat.add(a, 1n+r), 1n+Nat.add(a, r), N.add_succ(a, r), hq)
      +haq = N.lt_le_trans(a, 1n+a, Nat.add(3n, l), N.lt_succ(a), N.le_trans(1n+a, 1n+Nat.add(a, r), Nat.add(3n, l), N.le_add_right(1n+a, r), hle))
      +hax = N.lt_le_trans(a, Nat.add(3n, l), SC.length(U32, xs), haq, fits(bt, Nat.add(3n, l), bk, N.le_add_left(l, ST.bdeg(bt), 3n, hl)))
      +hay = L.subst(Nat, z => {Nat.is_lt(a, z) == True{} : Bool}, SC.length(U32, xs), SC.length(U32, ys), Equal.sym(Nat, SC.length(U32, ys), SC.length(U32, xs), put_len(bt, l, w, bk)), hax)
      X.win_step(ys, xs, a, a, r, hay, hax, put_below(bt, l, w, a, bk, hl, hr, ha, haq),
        pre_put(r, bt, l, w, 1n+a, bk, hl, hr, N.le_trans(1n, a, 1n+a, ha, N.lt_le(a, 1n+a, N.lt_succ(a))), hle))

def sh_put(+m: Nat, +bt: AR.Tree<U32>, +l: Nat, +w: U32, +a: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_le(l, ST.bdeg(bt)) == True{} : Bool}, +hr: {Nat.is_lt(Nat.add(3n, ST.bdeg(bt)), ST.bsize(bt)) == True{} : Bool}, +hqa: {Nat.is_le(Nat.add(3n, l), a) == True{} : Bool}, +hm: {Nat.is_le(Nat.add(a, m), Nat.add(3n, ST.bdeg(bt))) == True{} : Bool}) -> {ST.win(U32, AR.slots(U32, bput(bt, l, w)), 1n+a, m) == ST.win(U32, AR.slots(U32, bt), a, m) : List<&2, U32>}:
  match m:
    case 0n:
      X.win_zero2(AR.slots(U32, bput(bt, l, w)), AR.slots(U32, bt), 1n+a, a)
    case 1n+r:
      +xs = AR.slots(U32, bt)
      +ys = AR.slots(U32, bput(bt, l, w))
      +j = Nat.add(3n, ST.bdeg(bt))
      +hle = L.subst(Nat, z => {Nat.is_le(z, j) == True{} : Bool}, Nat.add(a, 1n+r), 1n+Nat.add(a, r), N.add_succ(a, r), hm)
      +ha1 = N.le_trans(1n+a, 1n+Nat.add(a, r), j, N.le_add_right(1n+a, r), hle)
      +hjl = L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, SC.pow2(ST.blcap(bt)), SC.length(U32, xs), Equal.sym(Nat, SC.length(U32, xs), SC.pow2(ST.blcap(bt)), len_cap(bt, bk)), room_cap(bt, bk, hr))
      +hax = N.lt_le_trans(a, 1n+a, SC.length(U32, xs), N.lt_succ(a), N.lt_le(1n+a, SC.length(U32, xs), N.le_lt_trans(1n+a, j, SC.length(U32, xs), ha1, hjl)))
      +hay = L.subst(Nat, z => {Nat.is_lt(1n+a, z) == True{} : Bool}, SC.length(U32, xs), SC.length(U32, ys), Equal.sym(Nat, SC.length(U32, ys), SC.length(U32, xs), put_len(bt, l, w, bk)), N.le_lt_trans(1n+a, j, SC.length(U32, xs), ha1, hjl))
      +hv = L.subst(Nat, z => {SC.nth(U32, ys, 1n+a) == SC.nth(U32, xs, z) : Maybe<&2, U32>}, Nat.sub(1n+a, 1n), a, N.sub_zero(a),
        put_moved(bt, l, w, 1n+a, bk, hl, hr, N.le_lt_succ(Nat.add(3n, l), a, hqa), ha1))
      X.win_step(ys, xs, 1n+a, a, r, hay, hax, hv,
        sh_put(r, bt, l, w, 1n+a, bk, hl, hr, N.le_trans(Nat.add(3n, l), a, 1n+a, hqa, N.lt_le(a, 1n+a, N.lt_succ(a))), hle))

def put_word(+bt: AR.Tree<U32>, +l: Nat, +w: U32, +i: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_le(l, ST.bdeg(bt)) == True{} : Bool}, +hr: {Nat.is_lt(Nat.add(3n, ST.bdeg(bt)), ST.bsize(bt)) == True{} : Bool}, +hi1: {Nat.is_le(1n, i) == True{} : Bool}, +hi: {Nat.is_lt(i, 3n) == True{} : Bool}) -> {SH.val_at(AR.slots(U32, bput(bt, l, w)), i) == SH.val_at(AR.slots(U32, bt), i) : U32}:
  val_eq(AR.slots(U32, bput(bt, l, w)), AR.slots(U32, bt), i, i, put_below(bt, l, w, i, bk, hl, hr, hi1, N.lt_le_trans(i, 3n, Nat.add(3n, l), hi, N.le_add_right(3n, l))))

def put_cap(+bt: AR.Tree<U32>, +l: Nat, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_le(l, ST.bdeg(bt)) == True{} : Bool}, +hr: {Nat.is_lt(Nat.add(3n, ST.bdeg(bt)), ST.bsize(bt)) == True{} : Bool}) -> {ST.blcap(bput(bt, l, w)) == ST.blcap(bt) : Nat}:
  Equal.cong(U32, Nat, z => U32.to_nat(z), SH.val_at(AR.slots(U32, bput(bt, l, w)), 2n), SH.val_at(AR.slots(U32, bt), 2n), put_word(bt, l, w, 2n, bk, hl, hr, {==}, {==}))

def put_size(+bt: AR.Tree<U32>, +l: Nat, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_le(l, ST.bdeg(bt)) == True{} : Bool}, +hr: {Nat.is_lt(Nat.add(3n, ST.bdeg(bt)), ST.bsize(bt)) == True{} : Bool}) -> {ST.bsize(bput(bt, l, w)) == ST.bsize(bt) : Nat}:
  Equal.cong(U32, Nat, z => U32.to_nat(z), SH.val_at(AR.slots(U32, bput(bt, l, w)), 1n), SH.val_at(AR.slots(U32, bt), 1n), put_word(bt, l, w, 1n, bk, hl, hr, {==}, {==}))

def put_deg(+bt: AR.Tree<U32>, +l: Nat, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hr: {Nat.is_lt(Nat.add(3n, ST.bdeg(bt)), ST.bsize(bt)) == True{} : Bool}) -> {ST.bdeg(bput(bt, l, w)) == 1n+ST.bdeg(bt) : Nat}:
  +lc = ST.blcap(bt)
  +dg = ST.bdeg(bt)
  +hd = ED.bk_lt32(bt, bk)
  +x = U32.inc(BK.v0(bt))
  +ev = val_eq(AR.slots(U32, bput(bt, l, w)), Con{x, Nil{}}, 0n, 0n, SH.upd_same(lc, uput(bt, l, w), 0n, x, uput_perfect(bt, l, w, bk), lt_cap(bt, 0n, bk, {==})))
  +hcap = room_cap(bt, bk, hr)
  +e0 = BK.from_to(BK.v0(bt), lc, N.lt_le(lc, 32n, hd), N.le_lt_trans(dg, Nat.add(3n, dg), SC.pow2(lc), BK.le_plus(3n, dg), hcap))
  Equal.trans(Nat, U32.to_nat(SH.val_at(AR.slots(U32, bput(bt, l, w)), 0n)), U32.to_nat(x), 1n+dg,
    Equal.cong(U32, Nat, z => U32.to_nat(z), SH.val_at(AR.slots(U32, bput(bt, l, w)), 0n), x, ev),
    Equal.trans(Nat, U32.to_nat(x), U32.to_nat(U32.from_nat(1n+dg)), 1n+dg,
      Equal.cong(U32, Nat, z => U32.to_nat(U32.inc(z)), BK.v0(bt), U32.from_nat(dg), Equal.sym(U32, U32.from_nat(dg), BK.v0(bt), e0)),
      U.to_nat_from_nat(1n+dg, lc, N.lt_le(lc, 32n, hd), N.le_lt_trans(1n+dg, Nat.add(3n, dg), SC.pow2(lc), BK.le_plus(2n, 1n+dg), hcap))))

def put_bents(+bt: AR.Tree<U32>, +l: Nat, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_le(l, ST.bdeg(bt)) == True{} : Bool}, +hr: {Nat.is_lt(Nat.add(3n, ST.bdeg(bt)), ST.bsize(bt)) == True{} : Bool}) -> {ST.bents(bput(bt, l, w)) == LS.il(ST.bents(bt), l, w) : List<&2, U32>}:
  +dg = ST.bdeg(bt)
  +xs = AR.slots(U32, bt)
  +ys = AR.slots(U32, bput(bt, l, w))
  +q = Nat.add(3n, l)
  +k = kput(bt, l)
  +as = ST.win(U32, xs, 3n, l)
  +bs = ST.win(U32, xs, q, k)
  +hj = room_cap(bt, bk, hr)
  +hqy = L.subst(Nat, z => {Nat.is_lt(q, z) == True{} : Bool}, SC.pow2(ST.blcap(bt)), SC.length(U32, ys), Equal.sym(Nat, SC.length(U32, ys), SC.pow2(ST.blcap(bt)), AR.slots_length(U32, ST.blcap(bt), bput(bt, l, w), put_perfect(bt, l, w, bk))), q_lt_cap(bt, l, bk, hl, hr))
  +ew = val_eq(ys, Con{w, Nil{}}, q, 0n, put_q(bt, l, w, bk, hl, hr))
  +eqk = Equal.trans(Nat, Nat.add(q, k), Nat.add(3n, Nat.add(l, k)), Nat.add(3n, dg), N.add_assoc(3n, l, k), Equal.cong(Nat, Nat, z => Nat.add(3n, z), Nat.add(l, k), dg, N.sub_add(dg, l, hl)))
  +el = Equal.trans(List<&2, U32>, ST.win(U32, ys, 3n, 1n+dg), SC.append(U32, ST.win(U32, ys, 3n, l), ST.win(U32, ys, q, Nat.sub(1n+dg, l))), SC.append(U32, as, Con{w, bs}),
    X.win_split(U32, ys, 3n, l, 1n+dg, N.le_trans(l, dg, 1n+dg, hl, N.lt_le(dg, 1n+dg, N.lt_succ(dg)))),
    Equal.trans(List<&2, U32>, SC.append(U32, ST.win(U32, ys, 3n, l), ST.win(U32, ys, q, Nat.sub(1n+dg, l))), SC.append(U32, as, ST.win(U32, ys, q, Nat.sub(1n+dg, l))), SC.append(U32, as, Con{w, bs}),
      Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.append(U32, z, ST.win(U32, ys, q, Nat.sub(1n+dg, l))), ST.win(U32, ys, 3n, l), as, pre_put(l, bt, l, w, 3n, bk, hl, hr, {==}, N.le_refl(q))),
      Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.append(U32, as, z), ST.win(U32, ys, q, Nat.sub(1n+dg, l)), Con{w, bs},
        Equal.trans(List<&2, U32>, ST.win(U32, ys, q, Nat.sub(1n+dg, l)), ST.win(U32, ys, q, 1n+k), Con{w, bs},
          Equal.cong(Nat, List<&2, U32>, z => ST.win(U32, ys, q, z), Nat.sub(1n+dg, l), 1n+k, sub_succ_l(dg, l, hl)),
          Equal.trans(List<&2, U32>, ST.win(U32, ys, q, 1n+k), Con{SH.val_at(ys, q), ST.win(U32, ys, 1n+q, k)}, Con{w, bs},
            X.win_cons(ys, q, k, hqy),
            Equal.trans(List<&2, U32>, Con{SH.val_at(ys, q), ST.win(U32, ys, 1n+q, k)}, Con{w, ST.win(U32, ys, 1n+q, k)}, Con{w, bs},
              Equal.cong(U32, List<&2, U32>, z => Con{z, ST.win(U32, ys, 1n+q, k)}, SH.val_at(ys, q), w, ew),
              LL.cons_cong(U32, w, ST.win(U32, ys, 1n+q, k), bs, sh_put(k, bt, l, w, q, bk, hl, hr, N.le_refl(q), L.subst(Nat, z => {Nat.is_le(z, Nat.add(3n, dg)) == True{} : Bool}, Nat.add(3n, dg), Nat.add(q, k), Equal.sym(Nat, Nat.add(q, k), Nat.add(3n, dg), eqk), N.le_refl(Nat.add(3n, dg)))))))))))
  +er = Equal.trans(List<&2, U32>, LS.il(ST.win(U32, xs, 3n, dg), l, w), LS.il(SC.append(U32, as, bs), l, w), SC.append(U32, as, Con{w, bs}),
    Equal.cong(List<&2, U32>, List<&2, U32>, z => LS.il(z, l, w), ST.win(U32, xs, 3n, dg), SC.append(U32, as, bs), X.win_split(U32, xs, 3n, l, dg, hl)),
    L.subst(Nat, z => {LS.il(SC.append(U32, as, bs), z, w) == SC.append(U32, as, Con{w, bs}) : List<&2, U32>}, SC.length(U32, as), l,
      W.win_length(xs, 3n, l, fits(bt, Nat.add(3n, l), bk, N.le_add_left(l, dg, 3n, hl))),
      X.il_app(as, w, bs)))
  Equal.trans(List<&2, U32>, ST.win(U32, ys, 3n, ST.bdeg(bput(bt, l, w))), ST.win(U32, ys, 3n, 1n+dg), LS.il(ST.win(U32, xs, 3n, dg), l, w),
    Equal.cong(Nat, List<&2, U32>, z => ST.win(U32, ys, 3n, z), ST.bdeg(bput(bt, l, w)), 1n+dg, put_deg(bt, l, w, bk, hr)),
    Equal.trans(List<&2, U32>, ST.win(U32, ys, 3n, 1n+dg), SC.append(U32, as, Con{w, bs}), LS.il(ST.win(U32, xs, 3n, dg), l, w), el, Equal.sym(List<&2, U32>, LS.il(ST.win(U32, xs, 3n, dg), l, w), SC.append(U32, as, Con{w, bs}), er)))

def put_ok(+bt: AR.Tree<U32>, +l: Nat, +w: U32, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hl: {Nat.is_le(l, ST.bdeg(bt)) == True{} : Bool}, +hr: {Nat.is_lt(Nat.add(3n, ST.bdeg(bt)), ST.bsize(bt)) == True{} : Bool}, +ha: {ST.asc(LS.il(ST.bents(bt), l, w)) == True{} : Bool}) -> {ST.blk_ok(bput(bt, l, w)) == True{} : Bool}:
  +b = bput(bt, l, w)
  +dg = ST.bdeg(bt)
  +ec = Equal.sym(Nat, ST.blcap(b), ST.blcap(bt), put_cap(bt, l, w, bk, hl, hr))
  +es = Equal.sym(Nat, ST.bsize(b), ST.bsize(bt), put_size(bt, l, w, bk, hl, hr))
  +ed = Equal.sym(Nat, ST.bdeg(b), 1n+dg, put_deg(bt, l, w, bk, hr))
  +hwin2 = L.subst(List<&2, U32>, z => {ST.asc(z) == True{} : Bool}, LS.il(ST.bents(bt), l, w), ST.bents(b), Equal.sym(List<&2, U32>, ST.bents(b), LS.il(ST.bents(bt), l, w), put_bents(bt, l, w, bk, hl, hr)), ha)
  +h4 = N.lt_succ_le_succ(Nat.add(3n, dg), ST.bsize(bt), hr)
  +hlen = L.subst(Nat, z => {Nat.is_le(Nat.add(3n, z), SC.length(U32, AR.slots(U32, b))) == True{} : Bool}, 1n+dg, ST.bdeg(b), ed,
    L.subst(Nat, z => {Nat.is_le(Nat.add(3n, 1n+dg), z) == True{} : Bool}, SC.pow2(ST.blcap(bt)), SC.length(U32, AR.slots(U32, b)), Equal.sym(Nat, SC.length(U32, AR.slots(U32, b)), SC.pow2(ST.blcap(bt)), AR.slots_length(U32, ST.blcap(bt), b, put_perfect(bt, l, w, bk))),
      L.subst(Nat, z => {Nat.is_le(Nat.add(3n, 1n+dg), z) == True{} : Bool}, ST.bsize(bt), SC.pow2(ST.blcap(bt)), N.eq_from_is_eq(ST.bsize(bt), SC.pow2(ST.blcap(bt)), ED.bk_size(bt, bk)), L.subst(Nat, z => {Nat.is_le(z, ST.bsize(bt)) == True{} : Bool}, 1n+Nat.add(3n, dg), Nat.add(3n, 1n+dg), Equal.sym(Nat, Nat.add(3n, 1n+dg), 1n+Nat.add(3n, dg), N.add_succ(3n, dg)), h4))))
  blk_ok_mk(b,
    L.subst(Nat, z => {AR.perfect(U32, z, b) == True{} : Bool}, ST.blcap(bt), ST.blcap(b), ec, put_perfect(bt, l, w, bk)),
    L.subst(Nat, z => {Nat.is_le(2n, z) == True{} : Bool}, ST.blcap(bt), ST.blcap(b), ec, ED.bk_two(bt, bk)),
    L.subst(Nat, z => {Nat.is_le(z, 31n) == True{} : Bool}, ST.blcap(bt), ST.blcap(b), ec, ED.bk_le31(bt, bk)),
    L.subst(Nat, z => {Nat.is_eq(ST.bsize(b), SC.pow2(z)) == True{} : Bool}, ST.blcap(bt), ST.blcap(b), ec,
      L.subst(Nat, z => {Nat.is_eq(z, SC.pow2(ST.blcap(bt))) == True{} : Bool}, ST.bsize(bt), ST.bsize(b), es, ED.bk_size(bt, bk))),
    L.subst(Nat, z => {Nat.is_le(Nat.add(3n, z), ST.bsize(b)) == True{} : Bool}, 1n+dg, ST.bdeg(b), ed,
      L.subst(Nat, z => {Nat.is_le(Nat.add(3n, 1n+dg), z) == True{} : Bool}, ST.bsize(bt), ST.bsize(b), es, L.subst(Nat, z => {Nat.is_le(z, ST.bsize(bt)) == True{} : Bool}, 1n+Nat.add(3n, dg), Nat.add(3n, 1n+dg), Equal.sym(Nat, Nat.add(3n, 1n+dg), 1n+Nat.add(3n, dg), N.add_succ(3n, dg)), h4))),
    AS.asc_at_of_win(ST.bdeg(b), AR.slots(U32, b), 3n, hlen, hwin2))

# ---- growth: the old block becomes the lower half ----

def tgrow(+bt: AR.Tree<U32>) -> AR.Tree<U32>:
  AR.TNode{bt, AR.trep(U32, ST.blcap(bt), 0)}

def ggrow(+bt: AR.Tree<U32>) -> AR.Tree<U32>:
  AR.upd(U32, 1n+ST.blcap(bt), tgrow(bt), 1n, U32.shl(BK.v1(bt)))

def bgrow(+bt: AR.Tree<U32>) -> AR.Tree<U32>:
  AR.upd(U32, 1n+ST.blcap(bt), ggrow(bt), 2n, U32.inc(BK.v2(bt)))

def tgrow_perfect(+bt: AR.Tree<U32>, +bk: {ST.blk_ok(bt) == True{} : Bool}) -> {AR.perfect(U32, 1n+ST.blcap(bt), tgrow(bt)) == True{} : Bool}:
  L.and_intro(AR.perfect(U32, ST.blcap(bt), bt), AR.perfect(U32, ST.blcap(bt), AR.trep(U32, ST.blcap(bt), 0)), ED.bk_perfect(bt, bk), AR.trep_perfect(U32, ST.blcap(bt), 0))

def ggrow_perfect(+bt: AR.Tree<U32>, +bk: {ST.blk_ok(bt) == True{} : Bool}) -> {AR.perfect(U32, 1n+ST.blcap(bt), ggrow(bt)) == True{} : Bool}:
  AR.upd_perfect(U32, 1n+ST.blcap(bt), tgrow(bt), 1n, U32.shl(BK.v1(bt)), tgrow_perfect(bt, bk))

def grow_perfect(+bt: AR.Tree<U32>, +bk: {ST.blk_ok(bt) == True{} : Bool}) -> {AR.perfect(U32, 1n+ST.blcap(bt), bgrow(bt)) == True{} : Bool}:
  AR.upd_perfect(U32, 1n+ST.blcap(bt), ggrow(bt), 2n, U32.inc(BK.v2(bt)), ggrow_perfect(bt, bk))

def g_lt(+bt: AR.Tree<U32>, +i: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +h: {Nat.is_lt(i, 4n) == True{} : Bool}) -> {Nat.is_lt(i, SC.pow2(1n+ST.blcap(bt))) == True{} : Bool}:
  N.lt_trans(i, SC.pow2(ST.blcap(bt)), SC.pow2(1n+ST.blcap(bt)), lt_cap(bt, i, bk, h), N.pow2_lt_succ(ST.blcap(bt)))

def g32(+bt: AR.Tree<U32>, +h30: {Nat.is_le(ST.blcap(bt), 30n) == True{} : Bool}) -> {Nat.is_lt(1n+ST.blcap(bt), 32n) == True{} : Bool}:
  N.le_lt_succ(1n+ST.blcap(bt), 31n, h30)

# The runtime growth is the mirror.
def blk_grow_ok(+bt: AR.Tree<U32>, +bk: {ST.blk_ok(bt) == True{} : Bool}, +h30: {Nat.is_le(ST.blcap(bt), 30n) == True{} : Bool}) -> {G.blk_grow(AR.thaw(U32, bt), BK.v1(bt), BK.v2(bt)) == AR.thaw(U32, bgrow(bt)) : Array<U32>}:
  +lc = ST.blcap(bt)
  %Equal.sym(Array<U32>, Array.new(U32, lc, 0), AR.thaw(U32, AR.trep(U32, lc, 0)), AR.new(U32, lc, 0)) : {Array.set(U32, Array.set(U32, ANode{AR.thaw(U32, bt), _}, 1, U32.shl(BK.v1(bt))), 2, U32.inc(BK.v2(bt))) == AR.thaw(U32, bgrow(bt)) : Array<U32>}
  %Equal.sym(Array<U32>, Array.set(U32, AR.thaw(U32, tgrow(bt)), U32.from_nat(1n), U32.shl(BK.v1(bt))), AR.thaw(U32, ggrow(bt)), SH.set_at(1n+lc, tgrow(bt), 1n, U32.shl(BK.v1(bt)), g32(bt, h30), tgrow_perfect(bt, bk), g_lt(bt, 1n, bk, {==}), {==})) : {Array.set(U32, _, 2, U32.inc(BK.v2(bt))) == AR.thaw(U32, bgrow(bt)) : Array<U32>}
  SH.set_at(1n+lc, ggrow(bt), 2n, U32.inc(BK.v2(bt)), g32(bt, h30), ggrow_perfect(bt, bk), g_lt(bt, 2n, bk, {==}), {==})

# Every old index outside the two rewritten header words is unchanged.
def grow_keep(+bt: AR.Tree<U32>, +i: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +hn1: {Nat.is_eq(i, 1n) == False{} : Bool}, +hn2: {Nat.is_eq(i, 2n) == False{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(ST.blcap(bt))) == True{} : Bool}) -> {SC.nth(U32, AR.slots(U32, bgrow(bt)), i) == SC.nth(U32, AR.slots(U32, bt), i) : Maybe<&2, U32>}:
  +lc = ST.blcap(bt)
  Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, bgrow(bt)), i), SC.nth(U32, AR.slots(U32, ggrow(bt)), i), SC.nth(U32, AR.slots(U32, bt), i),
    SH.upd_other(1n+lc, ggrow(bt), 2n, U32.inc(BK.v2(bt)), i, ggrow_perfect(bt, bk), g_lt(bt, 2n, bk, {==}), hn2),
    Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, ggrow(bt)), i), SC.nth(U32, AR.slots(U32, tgrow(bt)), i), SC.nth(U32, AR.slots(U32, bt), i),
      SH.upd_other(1n+lc, tgrow(bt), 1n, U32.shl(BK.v1(bt)), i, tgrow_perfect(bt, bk), g_lt(bt, 1n, bk, {==}), hn1),
      LL.nth_append_left(U32, AR.slots(U32, bt), AR.slots(U32, AR.trep(U32, lc, 0)), i, L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, SC.pow2(lc), SC.length(U32, AR.slots(U32, bt)), Equal.sym(Nat, SC.length(U32, AR.slots(U32, bt)), SC.pow2(lc), len_cap(bt, bk)), hi))))

def ge3_ne1(+i: Nat, +h: {Nat.is_le(3n, i) == True{} : Bool}) -> {Nat.is_eq(i, 1n) == False{} : Bool}:
  SH.ne_flip(1n, i, SH.ne_of_lt(1n, i, N.lt_le_trans(1n, 3n, i, {==}, h)))

def ge3_ne2(+i: Nat, +h: {Nat.is_le(3n, i) == True{} : Bool}) -> {Nat.is_eq(i, 2n) == False{} : Bool}:
  SH.ne_flip(2n, i, SH.ne_of_lt(2n, i, N.lt_le_trans(2n, 3n, i, {==}, h)))

def grow_len(+bt: AR.Tree<U32>, +bk: {ST.blk_ok(bt) == True{} : Bool}) -> {SC.length(U32, AR.slots(U32, bgrow(bt))) == SC.pow2(1n+ST.blcap(bt)) : Nat}:
  AR.slots_length(U32, 1n+ST.blcap(bt), bgrow(bt), grow_perfect(bt, bk))

def pre_grow(+m: Nat, +bt: AR.Tree<U32>, +a: Nat, +bk: {ST.blk_ok(bt) == True{} : Bool}, +ha: {Nat.is_le(3n, a) == True{} : Bool}, +hm: {Nat.is_le(Nat.add(a, m), SC.pow2(ST.blcap(bt))) == True{} : Bool}) -> {ST.win(U32, AR.slots(U32, bgrow(bt)), a, m) == ST.win(U32, AR.slots(U32, bt), a, m) : List<&2, U32>}:
  match m:
    case 0n:
      X.win_zero2(AR.slots(U32, bgrow(bt)), AR.slots(U32, bt), a, a)
    case 1n+r:
      +xs = AR.slots(U32, bt)
      +ys = AR.slots(U32, bgrow(bt))
      +lc = ST.blcap(bt)
      +hle = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(lc)) == True{} : Bool}, Nat.add(a, 1n+r), 1n+Nat.add(a, r), N.add_succ(a, r), hm)
      +hac = N.lt_le_trans(a, 1n+a, SC.pow2(lc), N.lt_succ(a), N.le_trans(1n+a, 1n+Nat.add(a, r), SC.pow2(lc), N.le_add_right(1n+a, r), hle))
      +hax = L.subst(Nat, z => {Nat.is_lt(a, z) == True{} : Bool}, SC.pow2(lc), SC.length(U32, xs), Equal.sym(Nat, SC.length(U32, xs), SC.pow2(lc), len_cap(bt, bk)), hac)
      +hay = L.subst(Nat, z => {Nat.is_lt(a, z) == True{} : Bool}, SC.pow2(1n+lc), SC.length(U32, ys), Equal.sym(Nat, SC.length(U32, ys), SC.pow2(1n+lc), grow_len(bt, bk)), N.lt_trans(a, SC.pow2(lc), SC.pow2(1n+lc), hac, N.pow2_lt_succ(lc)))
      X.win_step(ys, xs, a, a, r, hay, hax, grow_keep(bt, a, bk, ge3_ne1(a, ha), ge3_ne2(a, ha), hac),
        pre_grow(r, bt, 1n+a, bk, N.le_trans(3n, a, 1n+a, ha, N.lt_le(a, 1n+a, N.lt_succ(a))), hle))

def grow_v0(+bt: AR.Tree<U32>, +bk: {ST.blk_ok(bt) == True{} : Bool}) -> {BK.v0(bgrow(bt)) == BK.v0(bt) : U32}:
  val_eq(AR.slots(U32, bgrow(bt)), AR.slots(U32, bt), 0n, 0n, grow_keep(bt, 0n, bk, {==}, {==}, lt_cap(bt, 0n, bk, {==})))

def grow_deg(+bt: AR.Tree<U32>, +bk: {ST.blk_ok(bt) == True{} : Bool}) -> {ST.bdeg(bgrow(bt)) == ST.bdeg(bt) : Nat}:
  Equal.cong(U32, Nat, z => U32.to_nat(z), BK.v0(bgrow(bt)), BK.v0(bt), grow_v0(bt, bk))

def grow_cap(+bt: AR.Tree<U32>, +bk: {ST.blk_ok(bt) == True{} : Bool}, +h30: {Nat.is_le(ST.blcap(bt), 30n) == True{} : Bool}) -> {ST.blcap(bgrow(bt)) == 1n+ST.blcap(bt) : Nat}:
  +lc = ST.blcap(bt)
  +x = U32.inc(BK.v2(bt))
  +ev = val_eq(AR.slots(U32, bgrow(bt)), Con{x, Nil{}}, 2n, 0n, SH.upd_same(1n+lc, ggrow(bt), 2n, x, ggrow_perfect(bt, bk), g_lt(bt, 2n, bk, {==})))
  +h31 = N.le_lt_succ(lc, 31n, ED.bk_le31(bt, bk))
  +e2 = BK.from_to(BK.v2(bt), 5n, {==}, N.lt_le_trans(lc, 32n, SC.pow2(5n), h31, {==}))
  Equal.trans(Nat, U32.to_nat(SH.val_at(AR.slots(U32, bgrow(bt)), 2n)), U32.to_nat(x), 1n+lc,
    Equal.cong(U32, Nat, z => U32.to_nat(z), SH.val_at(AR.slots(U32, bgrow(bt)), 2n), x, ev),
    Equal.trans(Nat, U32.to_nat(x), U32.to_nat(U32.from_nat(1n+lc)), 1n+lc,
      Equal.cong(U32, Nat, z => U32.to_nat(U32.inc(z)), BK.v2(bt), U32.from_nat(lc), Equal.sym(U32, U32.from_nat(lc), BK.v2(bt), e2)),
      U.to_nat_from_nat(1n+lc, 5n, {==}, N.lt_le_trans(1n+lc, 32n, SC.pow2(5n), g32(bt, h30), {==}))))

def grow_size(+bt: AR.Tree<U32>, +bk: {ST.blk_ok(bt) == True{} : Bool}, +h30: {Nat.is_le(ST.blcap(bt), 30n) == True{} : Bool}) -> {ST.bsize(bgrow(bt)) == SC.pow2(1n+ST.blcap(bt)) : Nat}:
  +lc = ST.blcap(bt)
  +x = U32.shl(BK.v1(bt))
  +ev = val_eq(AR.slots(U32, bgrow(bt)), AR.slots(U32, ggrow(bt)), 1n, 1n, SH.upd_other(1n+lc, ggrow(bt), 2n, U32.inc(BK.v2(bt)), 1n, ggrow_perfect(bt, bk), g_lt(bt, 2n, bk, {==}), {==}))
  +ev1 = val_eq(AR.slots(U32, ggrow(bt)), Con{x, Nil{}}, 1n, 0n, SH.upd_same(1n+lc, tgrow(bt), 1n, x, tgrow_perfect(bt, bk), g_lt(bt, 1n, bk, {==})))
  +es = N.eq_from_is_eq(ST.bsize(bt), SC.pow2(lc), ED.bk_size(bt, bk))
  Equal.trans(Nat, U32.to_nat(SH.val_at(AR.slots(U32, bgrow(bt)), 1n)), U32.to_nat(x), SC.pow2(1n+lc),
    Equal.cong(U32, Nat, z => U32.to_nat(z), SH.val_at(AR.slots(U32, bgrow(bt)), 1n), x, Equal.trans(U32, SH.val_at(AR.slots(U32, bgrow(bt)), 1n), SH.val_at(AR.slots(U32, ggrow(bt)), 1n), x, ev, ev1)),
    Equal.trans(Nat, U32.to_nat(x), Nat.double(ST.bsize(bt)), SC.pow2(1n+lc),
      U.shl_value(BK.v1(bt), 2n+lc, N.lt_succ_le_succ(1n+lc, 32n, g32(bt, h30)),
        L.subst(Nat, z => {Nat.is_lt(Nat.double(z), SC.pow2(2n+lc)) == True{} : Bool}, SC.pow2(lc), ST.bsize(bt), Equal.sym(Nat, ST.bsize(bt), SC.pow2(lc), es), N.pow2_lt_succ(1n+lc))),
      Equal.cong(Nat, Nat, z => Nat.double(z), ST.bsize(bt), SC.pow2(lc), es)))

def grow_bents(+bt: AR.Tree<U32>, +bk: {ST.blk_ok(bt) == True{} : Bool}) -> {ST.bents(bgrow(bt)) == ST.bents(bt) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, ST.win(U32, AR.slots(U32, bgrow(bt)), 3n, ST.bdeg(bgrow(bt))), ST.win(U32, AR.slots(U32, bgrow(bt)), 3n, ST.bdeg(bt)), ST.bents(bt),
    Equal.cong(Nat, List<&2, U32>, z => ST.win(U32, AR.slots(U32, bgrow(bt)), 3n, z), ST.bdeg(bgrow(bt)), ST.bdeg(bt), grow_deg(bt, bk)),
    pre_grow(ST.bdeg(bt), bt, 3n, bk, {==}, ED.bk_cap(bt, bk)))

def grow_ok(+bt: AR.Tree<U32>, +bk: {ST.blk_ok(bt) == True{} : Bool}, +h30: {Nat.is_le(ST.blcap(bt), 30n) == True{} : Bool}) -> {ST.blk_ok(bgrow(bt)) == True{} : Bool}:
  +b = bgrow(bt)
  +lc = ST.blcap(bt)
  +dg = ST.bdeg(bt)
  +ec = Equal.sym(Nat, ST.blcap(b), 1n+lc, grow_cap(bt, bk, h30))
  +es = Equal.sym(Nat, ST.bsize(b), SC.pow2(1n+lc), grow_size(bt, bk, h30))
  +ed = Equal.sym(Nat, ST.bdeg(b), dg, grow_deg(bt, bk))
  +hfit = N.le_trans(Nat.add(3n, dg), SC.pow2(lc), SC.pow2(1n+lc), ED.bk_cap(bt, bk), N.lt_le(SC.pow2(lc), SC.pow2(1n+lc), N.pow2_lt_succ(lc)))
  +hwin = L.subst(List<&2, U32>, z => {ST.asc(z) == True{} : Bool}, ST.bents(bt), ST.bents(b), Equal.sym(List<&2, U32>, ST.bents(b), ST.bents(bt), grow_bents(bt, bk)), W.asc_win(dg, AR.slots(U32, bt), 3n, ED.bk_asc(bt, bk)))
  +hlen = L.subst(Nat, z => {Nat.is_le(Nat.add(3n, z), SC.length(U32, AR.slots(U32, b))) == True{} : Bool}, dg, ST.bdeg(b), ed,
    L.subst(Nat, z => {Nat.is_le(Nat.add(3n, dg), z) == True{} : Bool}, SC.pow2(1n+lc), SC.length(U32, AR.slots(U32, b)), Equal.sym(Nat, SC.length(U32, AR.slots(U32, b)), SC.pow2(1n+lc), grow_len(bt, bk)), hfit))
  blk_ok_mk(b,
    L.subst(Nat, z => {AR.perfect(U32, z, b) == True{} : Bool}, 1n+lc, ST.blcap(b), ec, grow_perfect(bt, bk)),
    L.subst(Nat, z => {Nat.is_le(2n, z) == True{} : Bool}, 1n+lc, ST.blcap(b), ec, N.le_trans(2n, lc, 1n+lc, ED.bk_two(bt, bk), N.lt_le(lc, 1n+lc, N.lt_succ(lc)))),
    L.subst(Nat, z => {Nat.is_le(z, 31n) == True{} : Bool}, 1n+lc, ST.blcap(b), ec, h30),
    L.subst(Nat, z => {Nat.is_eq(ST.bsize(b), SC.pow2(z)) == True{} : Bool}, 1n+lc, ST.blcap(b), ec,
      L.subst(Nat, z => {Nat.is_eq(z, SC.pow2(1n+lc)) == True{} : Bool}, SC.pow2(1n+lc), ST.bsize(b), es, N.is_eq_refl(SC.pow2(1n+lc)))),
    L.subst(Nat, z => {Nat.is_le(Nat.add(3n, z), ST.bsize(b)) == True{} : Bool}, dg, ST.bdeg(b), ed,
      L.subst(Nat, z => {Nat.is_le(Nat.add(3n, dg), z) == True{} : Bool}, SC.pow2(1n+lc), ST.bsize(b), es, hfit)),
    AS.asc_at_of_win(ST.bdeg(b), AR.slots(U32, b), 3n, hlen, hwin))
