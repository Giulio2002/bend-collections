import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/u32half.bend as H
import ../lib/array.bend as AR
import ../binary_heap/u32idx.bend as IX
import ../../spec/common.bend as SC
import ../../src/graph.bend as G
import ./search.bend as SE

# The two shift loops of src/graph.bend, against their effect on the block.
#
# `shr_go(k, j, a)` performs a[j] = a[j-1], a[j-1] = a[j-2], ... k times: the
# entries of (j - k, j] become the entries of (j - k - 1, j - 1], which is
# what an insertion at j - k does after the caller writes the new entry
# there. `shl_go(k, j, a)` is the mirror image, which is what a deletion at j
# does. Both are proved against the REAL Base.Array algorithms through the
# mirror tree, and then characterised index by index.

# The value stored at index i (0 when the index is out of range; the callers
# always stay in range).
def val_at(xs: List<&2, U32>, +i: Nat) -> U32:
  L.some_value(U32, SC.nth(U32, xs, i), 0)

def shr_tree(+k: Nat, +d: Nat, +t: AR.Tree<U32>, +j: Nat) -> AR.Tree<U32>:
  match k:
    case 0n:
      t
    case 1n+m:
      shr_tree(m, d, AR.upd(U32, d, t, j, val_at(AR.slots(U32, t), Nat.sub(j, 1n))), Nat.sub(j, 1n))

def shl_tree(+k: Nat, +d: Nat, +t: AR.Tree<U32>, +j: Nat) -> AR.Tree<U32>:
  match k:
    case 0n:
      t
    case 1n+m:
      shl_tree(m, d, AR.upd(U32, d, t, j, val_at(AR.slots(U32, t), 1n+j)), 1n+j)

# ---- the array loops are the mirror loops ----

def some_at_go(+d: Nat, +t: AR.Tree<U32>, +i: Nat, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, mb: Maybe<&2, U32>, +hmb: {SC.nth(U32, AR.slots(U32, t), i) == mb : Maybe<&2, U32>}) -> {SC.nth(U32, AR.slots(U32, t), i) == Some{val_at(AR.slots(U32, t), i)} : Maybe<&2, U32>}:
  match mb:
    case None{}:
      Empty.absurd({SC.nth(U32, AR.slots(U32, t), i) == Some{val_at(AR.slots(U32, t), i)} : Maybe<&2, U32>},
        LL.sc_nth_some(U32, AR.slots(U32, t), i, SE.slot_some(d, t, i, pf, hi), hmb))
    case Some{+x}:
      L.subst(U32, z => {SC.nth(U32, AR.slots(U32, t), i) == Some{z} : Maybe<&2, U32>}, x, val_at(AR.slots(U32, t), i),
        Equal.sym(U32, val_at(AR.slots(U32, t), i), x,
          Equal.cong(Maybe<&2, U32>, U32, mm => L.some_value(U32, mm, 0), SC.nth(U32, AR.slots(U32, t), i), Some{x}, hmb)),
        hmb)

# Base.Array.set at an index given as a Nat.
def some_at(+d: Nat, +t: AR.Tree<U32>, +i: Nat, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}) -> {SC.nth(U32, AR.slots(U32, t), i) == Some{val_at(AR.slots(U32, t), i)} : Maybe<&2, U32>}:
  some_at_go(d, t, i, pf, hi, SC.nth(U32, AR.slots(U32, t), i), {==})

def set_at(+d: Nat, +t: AR.Tree<U32>, +i: Nat, +x: U32, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +ri: {U32.to_nat(U32.from_nat(i)) == i : Nat}) -> {Array.set(U32, AR.thaw(U32, t), U32.from_nat(i), x) == AR.thaw(U32, AR.upd(U32, d, t, i, x)) : Array<U32>}:
  L.subst(Nat, z => {Array.set(U32, AR.thaw(U32, t), U32.from_nat(i), x) == AR.thaw(U32, AR.upd(U32, d, t, z, x)) : Array<U32>}, U32.to_nat(U32.from_nat(i)), i, ri,
    AR.set(U32, d, t, U32.from_nat(i), x, val_at(AR.slots(U32, t), i), hd,
      L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, ri), hi),
      L.subst(Nat, z => {SC.nth(U32, AR.slots(U32, t), z) == Some{val_at(AR.slots(U32, t), i)} : Maybe<&2, U32>}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, ri), some_at(d, t, i, pf, hi)),
      pf))

def le_pred(+m: Nat, +j: Nat, +h: {Nat.is_le(1n+m, j) == True{} : Bool}) -> {Nat.is_le(m, Nat.sub(j, 1n)) == True{} : Bool}:
  match j:
    case 0n:
      Empty.absurd({Nat.is_le(m, Nat.sub(0n, 1n)) == True{} : Bool}, L.false_true(h))
    case 1n+q:
      L.subst(Nat, z => {Nat.is_le(m, z) == True{} : Bool}, q, Nat.sub(1n+q, 1n), Equal.sym(Nat, Nat.sub(1n+q, 1n), q, N.sub_zero(q)), h)

# The slot at an in-range index has a value.
def shr_run(+k: Nat, +d: Nat, +t: AR.Tree<U32>, +j: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +hk: {Nat.is_le(k, j) == True{} : Bool}) -> {G.shr_go(k, U32.from_nat(j), AR.thaw(U32, t)) == AR.thaw(U32, shr_tree(k, d, t, j)) : Array<U32>}:
  match k:
    case 0n:
      {==}
    case 1n+m:
      +hk1 = N.le_trans(1n, 1n+m, j, N.lt_succ_le_succ(0n, 1n+m, {==}), hk)
      +hjm = N.le_lt_trans(Nat.sub(j, 1n), j, SC.pow2(d), IX.sub_le(j), hj)
      +e1 = IX.sub_one(j, d, N.lt_le(d, 32n, hd), hj, hk1)
      +x = val_at(AR.slots(U32, t), Nat.sub(j, 1n))
      +hx = some_at(d, t, Nat.sub(j, 1n), pf, hjm)
      +rj = IX.nat_round(j, d, N.lt_le(d, 32n, hd), hj)
      +rm = IX.nat_round(Nat.sub(j, 1n), d, N.lt_le(d, 32n, hd), hjm)
      # read a[j - 1]
      %Equal.sym(U32, U32.sub(U32.from_nat(j), 1), U32.from_nat(Nat.sub(j, 1n)), e1) : {G.shr_go(m, _, G.shr_put(U32.from_nat(j), Array.get(U32, AR.thaw(U32, t), _))) == AR.thaw(U32, shr_tree(1n+m, d, t, j)) : Array<U32>}
      %Equal.sym(Array<U32> & U32, Array.get(U32, AR.thaw(U32, t), U32.from_nat(Nat.sub(j, 1n))), (AR.thaw(U32, t), x),
        AR.get(U32, d, t, U32.from_nat(Nat.sub(j, 1n)), x, hd,
          L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, Nat.sub(j, 1n), U32.to_nat(U32.from_nat(Nat.sub(j, 1n))), Equal.sym(Nat, U32.to_nat(U32.from_nat(Nat.sub(j, 1n))), Nat.sub(j, 1n), rm), hjm),
          L.subst(Nat, z => {SC.nth(U32, AR.slots(U32, t), z) == Some{x} : Maybe<&2, U32>}, Nat.sub(j, 1n), U32.to_nat(U32.from_nat(Nat.sub(j, 1n))), Equal.sym(Nat, U32.to_nat(U32.from_nat(Nat.sub(j, 1n))), Nat.sub(j, 1n), rm), hx),
          pf)) : {G.shr_go(m, U32.from_nat(Nat.sub(j, 1n)), G.shr_put(U32.from_nat(j), _)) == AR.thaw(U32, shr_tree(1n+m, d, t, j)) : Array<U32>}
      # write a[j]
      %Equal.sym(Array<U32>, Array.set(U32, AR.thaw(U32, t), U32.from_nat(j), x), AR.thaw(U32, AR.upd(U32, d, t, j, x)),
        set_at(d, t, j, x, hd, pf, hj, rj)) : {G.shr_go(m, U32.from_nat(Nat.sub(j, 1n)), _) == AR.thaw(U32, shr_tree(1n+m, d, t, j)) : Array<U32>}
      shr_run(m, d, AR.upd(U32, d, t, j, x), Nat.sub(j, 1n), hd,
        AR.upd_perfect(U32, d, t, j, x, pf), hjm,
        N.le_trans(m, Nat.sub(j, 1n), Nat.sub(j, 1n), le_pred(m, j, hk), N.le_refl(Nat.sub(j, 1n))))

# m + 1 <= j gives m <= j - 1.
# add(j, 1 + m) = add(1 + j, m)
def add_shift(+j: Nat, +m: Nat) -> {Nat.add(j, 1n+m) == Nat.add(1n+j, m) : Nat}:
  N.add_succ(j, m)

def shl_run(+k: Nat, +d: Nat, +t: AR.Tree<U32>, +j: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hjk: {Nat.is_lt(Nat.add(j, k), SC.pow2(d)) == True{} : Bool}) -> {G.shl_go(k, U32.from_nat(j), AR.thaw(U32, t)) == AR.thaw(U32, shl_tree(k, d, t, j)) : Array<U32>}:
  match k:
    case 0n:
      {==}
    case 1n+m:
      +hjs = N.le_lt_trans(1n+j, Nat.add(j, 1n+m), SC.pow2(d),
               L.subst(Nat, z => {Nat.is_le(1n+j, z) == True{} : Bool}, 1n+Nat.add(j, m), Nat.add(j, 1n+m), Equal.sym(Nat, Nat.add(j, 1n+m), 1n+Nat.add(j, m), N.add_succ(j, m)),
                 N.lt_succ_le_succ(j, 1n+Nat.add(j, m), N.le_lt_trans(j, Nat.add(j, m), 1n+Nat.add(j, m), N.le_add_right(j, m), N.lt_succ(Nat.add(j, m))))),
               hjk)
      +hj = N.le_lt_trans(j, 1n+j, SC.pow2(d), N.le_succ(j), hjs)
      +x = val_at(AR.slots(U32, t), 1n+j)
      +rj = IX.nat_round(j, d, N.lt_le(d, 32n, hd), hj)
      +rs = IX.nat_round(1n+j, d, N.lt_le(d, 32n, hd), hjs)
      %Equal.sym(Array<U32> & U32, Array.get(U32, AR.thaw(U32, t), U32.from_nat(1n+j)), (AR.thaw(U32, t), x),
        AR.get(U32, d, t, U32.from_nat(1n+j), x, hd,
          L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, 1n+j, U32.to_nat(U32.from_nat(1n+j)), Equal.sym(Nat, U32.to_nat(U32.from_nat(1n+j)), 1n+j, rs), hjs),
          L.subst(Nat, z => {SC.nth(U32, AR.slots(U32, t), z) == Some{x} : Maybe<&2, U32>}, 1n+j, U32.to_nat(U32.from_nat(1n+j)), Equal.sym(Nat, U32.to_nat(U32.from_nat(1n+j)), 1n+j, rs), some_at(d, t, 1n+j, pf, hjs)),
          pf)) : {G.shl_go(m, U32.from_nat(1n+j), G.shl_put(U32.from_nat(j), _)) == AR.thaw(U32, shl_tree(1n+m, d, t, j)) : Array<U32>}
      %Equal.sym(Array<U32>, Array.set(U32, AR.thaw(U32, t), U32.from_nat(j), x), AR.thaw(U32, AR.upd(U32, d, t, j, x)),
        set_at(d, t, j, x, hd, pf, hj, rj)) : {G.shl_go(m, U32.from_nat(1n+j), _) == AR.thaw(U32, shl_tree(1n+m, d, t, j)) : Array<U32>}
      shl_run(m, d, AR.upd(U32, d, t, j, x), 1n+j, hd, AR.upd_perfect(U32, d, t, j, x, pf),
        L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, Nat.add(j, 1n+m), Nat.add(1n+j, m), add_shift(j, m), hjk))

# ---- index-wise effect of the mirror loops ----

# i < j implies is_eq(i, j) is False.
def ne_of_lt_go(+i: Nat, +j: Nat, +h: {Nat.is_lt(i, j) == True{} : Bool}, e: Bool, +ee: {Nat.is_eq(i, j) == e : Bool}) -> {Nat.is_eq(i, j) == False{} : Bool}:
  match e:
    case False{}:
      ee
    case True{}:
      Empty.absurd({Nat.is_eq(i, j) == False{} : Bool}, N.lt_ne(i, j, h, N.eq_from_is_eq(i, j, ee)))

# One mirror update, seen through `nth`.
def ne_of_lt(+i: Nat, +j: Nat, +h: {Nat.is_lt(i, j) == True{} : Bool}) -> {Nat.is_eq(i, j) == False{} : Bool}:
  ne_of_lt_go(i, j, h, Nat.is_eq(i, j), {==})

def ne_flip(+i: Nat, +j: Nat, +h: {Nat.is_eq(i, j) == False{} : Bool}) -> {Nat.is_eq(j, i) == False{} : Bool}:
  match i j:
    case 0n 0n:
      h
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ne_flip(p, q, h)

def upd_other(+d: Nat, +t: AR.Tree<U32>, +j: Nat, +x: U32, +i: Nat, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +hne: {Nat.is_eq(i, j) == False{} : Bool}) -> {SC.nth(U32, AR.slots(U32, AR.upd(U32, d, t, j, x)), i) == SC.nth(U32, AR.slots(U32, t), i) : Maybe<&2, U32>}:
  L.subst(List<&2, U32>, ys => {SC.nth(U32, ys, i) == SC.nth(U32, AR.slots(U32, t), i) : Maybe<&2, U32>}, SC.update(U32, AR.slots(U32, t), j, x), AR.slots(U32, AR.upd(U32, d, t, j, x)),
    Equal.sym(List<&2, U32>, AR.slots(U32, AR.upd(U32, d, t, j, x)), SC.update(U32, AR.slots(U32, t), j, x), AR.upd_slots(U32, d, t, j, x, hj, pf)),
    LL.nth_update_other(U32, AR.slots(U32, t), j, i, x, ne_flip(i, j, hne)))

def upd_same(+d: Nat, +t: AR.Tree<U32>, +j: Nat, +x: U32, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {SC.nth(U32, AR.slots(U32, AR.upd(U32, d, t, j, x)), j) == Some{x} : Maybe<&2, U32>}:
  L.subst(List<&2, U32>, ys => {SC.nth(U32, ys, j) == Some{x} : Maybe<&2, U32>}, SC.update(U32, AR.slots(U32, t), j, x), AR.slots(U32, AR.upd(U32, d, t, j, x)),
    Equal.sym(List<&2, U32>, AR.slots(U32, AR.upd(U32, d, t, j, x)), SC.update(U32, AR.slots(U32, t), j, x), AR.upd_slots(U32, d, t, j, x, hj, pf)),
    LL.nth_update_same(U32, AR.slots(U32, t), j, x, SE.slot_some(d, t, j, pf, hj)))

# Above the shifted region nothing changes.
def shr_above(+k: Nat, +d: Nat, +t: AR.Tree<U32>, +j: Nat, +i: Nat, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +hk: {Nat.is_le(k, j) == True{} : Bool}, +hi: {Nat.is_lt(j, i) == True{} : Bool}) -> {SC.nth(U32, AR.slots(U32, shr_tree(k, d, t, j)), i) == SC.nth(U32, AR.slots(U32, t), i) : Maybe<&2, U32>}:
  match k:
    case 0n:
      {==}
    case 1n+m:
      +x = val_at(AR.slots(U32, t), Nat.sub(j, 1n))
      +hjm = N.le_lt_trans(Nat.sub(j, 1n), j, SC.pow2(d), IX.sub_le(j), hj)
      Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, shr_tree(m, d, AR.upd(U32, d, t, j, x), Nat.sub(j, 1n))), i), SC.nth(U32, AR.slots(U32, AR.upd(U32, d, t, j, x)), i), SC.nth(U32, AR.slots(U32, t), i),
        shr_above(m, d, AR.upd(U32, d, t, j, x), Nat.sub(j, 1n), i, AR.upd_perfect(U32, d, t, j, x, pf), hjm,
          le_pred(m, j, hk), N.le_lt_trans(Nat.sub(j, 1n), j, i, IX.sub_le(j), hi)),
        upd_other(d, t, j, x, i, pf, hj, ne_flip(j, i, ne_of_lt(j, i, hi))))

# Below the shifted region nothing changes.
def shr_below(+k: Nat, +d: Nat, +t: AR.Tree<U32>, +j: Nat, +i: Nat, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +hk: {Nat.is_le(k, j) == True{} : Bool}, +hi: {Nat.is_le(i, Nat.sub(j, k)) == True{} : Bool}) -> {SC.nth(U32, AR.slots(U32, shr_tree(k, d, t, j)), i) == SC.nth(U32, AR.slots(U32, t), i) : Maybe<&2, U32>}:
  match k:
    case 0n:
      {==}
    case 1n+m:
      +x = val_at(AR.slots(U32, t), Nat.sub(j, 1n))
      +hjm = N.le_lt_trans(Nat.sub(j, 1n), j, SC.pow2(d), IX.sub_le(j), hj)
      +hij = N.le_lt_trans(i, Nat.sub(j, 1n+m), j, N.le_trans(i, Nat.sub(j, 1n+m), Nat.sub(j, 1n+m), hi, N.le_refl(Nat.sub(j, 1n+m))),
              SE.sub_lt_self(j, 1n+m, {==}, N.lt_le_trans(0n, 1n+m, j, {==}, hk)))
      Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, shr_tree(m, d, AR.upd(U32, d, t, j, x), Nat.sub(j, 1n))), i), SC.nth(U32, AR.slots(U32, AR.upd(U32, d, t, j, x)), i), SC.nth(U32, AR.slots(U32, t), i),
        shr_below(m, d, AR.upd(U32, d, t, j, x), Nat.sub(j, 1n), i, AR.upd_perfect(U32, d, t, j, x, pf), hjm, le_pred(m, j, hk),
          L.subst(Nat, z => {Nat.is_le(i, z) == True{} : Bool}, Nat.sub(j, 1n+m), Nat.sub(Nat.sub(j, 1n), m),
            Equal.sym(Nat, Nat.sub(Nat.sub(j, 1n), m), Nat.sub(j, 1n+m),
              Equal.trans(Nat, Nat.sub(Nat.sub(j, 1n), m), Nat.sub(j, Nat.add(1n, m)), Nat.sub(j, 1n+m),
                SE.sub_add_eq(j, 1n, m), {==})),
            hi)),
        upd_other(d, t, j, x, i, pf, hj, ne_of_lt(i, j, hij)))

# Inside the shifted region every entry comes from one slot below.
def ne_lt(+i: Nat, +j: Nat, +h2: {Nat.is_le(i, j) == True{} : Bool}, +hs: {Nat.is_eq(i, j) == False{} : Bool}) -> {Nat.is_le(j, i) == False{} : Bool}:
  match i j:
    case 0n 0n:
      Empty.absurd({Nat.is_le(0n, 0n) == False{} : Bool}, L.true_false(hs))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(0n, 1n+p) == False{} : Bool}, L.false_true(h2))
    case 1n+p 1n+q:
      ne_lt(p, q, h2, hs)

def shr_moved_split(+m: Nat, +d: Nat, +t: AR.Tree<U32>, +j: Nat, +i: Nat, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +hk: {Nat.is_le(1n+m, j) == True{} : Bool}, +h1: {Nat.is_lt(Nat.sub(j, 1n+m), i) == True{} : Bool}, +h2: {Nat.is_le(i, j) == True{} : Bool}, same: Bool, +hs: {Nat.is_eq(i, j) == same : Bool}, ih: @+hh: {Nat.is_le(i, Nat.sub(j, 1n)) == True{} : Bool} -> {SC.nth(U32, AR.slots(U32, shr_tree(m, d, AR.upd(U32, d, t, j, val_at(AR.slots(U32, t), Nat.sub(j, 1n))), Nat.sub(j, 1n))), i) == SC.nth(U32, AR.slots(U32, AR.upd(U32, d, t, j, val_at(AR.slots(U32, t), Nat.sub(j, 1n)))), Nat.sub(i, 1n)) : Maybe<&2, U32>}) -> {SC.nth(U32, AR.slots(U32, shr_tree(1n+m, d, t, j)), i) == SC.nth(U32, AR.slots(U32, t), Nat.sub(i, 1n)) : Maybe<&2, U32>}:
  match same:
    case True{}:
      +x = val_at(AR.slots(U32, t), Nat.sub(j, 1n))
      +hjm = N.le_lt_trans(Nat.sub(j, 1n), j, SC.pow2(d), IX.sub_le(j), hj)
      # i is the slot just written; the rest of the loop stays strictly below it
      L.subst(Nat, z => {SC.nth(U32, AR.slots(U32, shr_tree(1n+m, d, t, j)), z) == SC.nth(U32, AR.slots(U32, t), Nat.sub(z, 1n)) : Maybe<&2, U32>}, j, i, Equal.sym(Nat, i, j, N.eq_from_is_eq(i, j, hs)),
        Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, shr_tree(m, d, AR.upd(U32, d, t, j, x), Nat.sub(j, 1n))), j), SC.nth(U32, AR.slots(U32, AR.upd(U32, d, t, j, x)), j), SC.nth(U32, AR.slots(U32, t), Nat.sub(j, 1n)),
          shr_above(m, d, AR.upd(U32, d, t, j, x), Nat.sub(j, 1n), j, AR.upd_perfect(U32, d, t, j, x, pf), hjm, le_pred(m, j, hk),
            SE.sub_lt_self(j, 1n, {==}, N.lt_le_trans(0n, 1n+m, j, {==}, hk))),
          Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, AR.upd(U32, d, t, j, x)), j), Some{x}, SC.nth(U32, AR.slots(U32, t), Nat.sub(j, 1n)),
            upd_same(d, t, j, x, pf, hj),
            Equal.sym(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, t), Nat.sub(j, 1n)), Some{x}, some_at(d, t, Nat.sub(j, 1n), pf, hjm)))))
    case False{}:
      +x = val_at(AR.slots(U32, t), Nat.sub(j, 1n))
      +hjm = N.le_lt_trans(Nat.sub(j, 1n), j, SC.pow2(d), IX.sub_le(j), hj)
      # i is strictly below j: the remaining loop moves it
      Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, shr_tree(m, d, AR.upd(U32, d, t, j, x), Nat.sub(j, 1n))), i), SC.nth(U32, AR.slots(U32, AR.upd(U32, d, t, j, x)), Nat.sub(i, 1n)), SC.nth(U32, AR.slots(U32, t), Nat.sub(i, 1n)),
        ih(le_pred(i, j, N.lt_succ_le_succ(i, j, N.not_le_lt(j, i, ne_lt(i, j, h2, hs))))),
        upd_other(d, t, j, x, Nat.sub(i, 1n), pf, hj,
          ne_of_lt(Nat.sub(i, 1n), j, N.le_lt_trans(Nat.sub(i, 1n), i, j, IX.sub_le(i), N.not_le_lt(j, i, ne_lt(i, j, h2, hs))))))

# i <= j and i /= j give NOT (j <= i).
def shr_moved(+k: Nat, +d: Nat, +t: AR.Tree<U32>, +j: Nat, +i: Nat, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +hk: {Nat.is_le(k, j) == True{} : Bool}, +h1: {Nat.is_lt(Nat.sub(j, k), i) == True{} : Bool}, +h2: {Nat.is_le(i, j) == True{} : Bool}) -> {SC.nth(U32, AR.slots(U32, shr_tree(k, d, t, j)), i) == SC.nth(U32, AR.slots(U32, t), Nat.sub(i, 1n)) : Maybe<&2, U32>}:
  match k:
    case 0n:
      Empty.absurd({SC.nth(U32, AR.slots(U32, shr_tree(0n, d, t, j)), i) == SC.nth(U32, AR.slots(U32, t), Nat.sub(i, 1n)) : Maybe<&2, U32>},
        L.true_not_false(Nat.is_le(i, j), h2, N.lt_not_le(j, i, L.subst(Nat, z => {Nat.is_lt(z, i) == True{} : Bool}, Nat.sub(j, 0n), j, N.sub_zero(j), h1))))
    case 1n+m:
      shr_moved_split(m, d, t, j, i, pf, hj, hk, h1, h2, Nat.is_eq(i, j), {==},
        hh => shr_moved(m, d, AR.upd(U32, d, t, j, val_at(AR.slots(U32, t), Nat.sub(j, 1n))), Nat.sub(j, 1n), i,
                AR.upd_perfect(U32, d, t, j, val_at(AR.slots(U32, t), Nat.sub(j, 1n)), pf),
                N.le_lt_trans(Nat.sub(j, 1n), j, SC.pow2(d), IX.sub_le(j), hj),
                le_pred(m, j, hk),
                L.subst(Nat, z => {Nat.is_lt(z, i) == True{} : Bool}, Nat.sub(j, 1n+m), Nat.sub(Nat.sub(j, 1n), m),
                  Equal.sym(Nat, Nat.sub(Nat.sub(j, 1n), m), Nat.sub(j, 1n+m), Equal.trans(Nat, Nat.sub(Nat.sub(j, 1n), m), Nat.sub(j, Nat.add(1n, m)), Nat.sub(j, 1n+m), SE.sub_add_eq(j, 1n, m), {==})),
                  h1),
                hh))

# ---- the same three facts for the left shift ----

def shl_below(+k: Nat, +d: Nat, +t: AR.Tree<U32>, +j: Nat, +i: Nat, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hjk: {Nat.is_lt(Nat.add(j, k), SC.pow2(d)) == True{} : Bool}, +hi: {Nat.is_lt(i, j) == True{} : Bool}) -> {SC.nth(U32, AR.slots(U32, shl_tree(k, d, t, j)), i) == SC.nth(U32, AR.slots(U32, t), i) : Maybe<&2, U32>}:
  match k:
    case 0n:
      {==}
    case 1n+m:
      +x = val_at(AR.slots(U32, t), 1n+j)
      +hj = N.le_lt_trans(j, Nat.add(j, 1n+m), SC.pow2(d), N.le_add_right(j, 1n+m), hjk)
      Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, shl_tree(m, d, AR.upd(U32, d, t, j, x), 1n+j)), i), SC.nth(U32, AR.slots(U32, AR.upd(U32, d, t, j, x)), i), SC.nth(U32, AR.slots(U32, t), i),
        shl_below(m, d, AR.upd(U32, d, t, j, x), 1n+j, i, AR.upd_perfect(U32, d, t, j, x, pf),
          L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, Nat.add(j, 1n+m), Nat.add(1n+j, m), add_shift(j, m), hjk),
          N.lt_trans(i, j, 1n+j, hi, N.lt_succ(j))),
        upd_other(d, t, j, x, i, pf, hj, ne_of_lt(i, j, hi)))

def shl_above(+k: Nat, +d: Nat, +t: AR.Tree<U32>, +j: Nat, +i: Nat, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hjk: {Nat.is_lt(Nat.add(j, k), SC.pow2(d)) == True{} : Bool}, +hi: {Nat.is_le(Nat.add(j, k), i) == True{} : Bool}) -> {SC.nth(U32, AR.slots(U32, shl_tree(k, d, t, j)), i) == SC.nth(U32, AR.slots(U32, t), i) : Maybe<&2, U32>}:
  match k:
    case 0n:
      {==}
    case 1n+m:
      +x = val_at(AR.slots(U32, t), 1n+j)
      +hj = N.le_lt_trans(j, Nat.add(j, 1n+m), SC.pow2(d), N.le_add_right(j, 1n+m), hjk)
      +hji = N.lt_le_trans(j, Nat.add(j, 1n+m), i,
               L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, 1n+Nat.add(j, m), Nat.add(j, 1n+m), Equal.sym(Nat, Nat.add(j, 1n+m), 1n+Nat.add(j, m), N.add_succ(j, m)),
                 N.le_lt_trans(j, Nat.add(j, m), 1n+Nat.add(j, m), N.le_add_right(j, m), N.lt_succ(Nat.add(j, m)))),
               hi)
      Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, shl_tree(m, d, AR.upd(U32, d, t, j, x), 1n+j)), i), SC.nth(U32, AR.slots(U32, AR.upd(U32, d, t, j, x)), i), SC.nth(U32, AR.slots(U32, t), i),
        shl_above(m, d, AR.upd(U32, d, t, j, x), 1n+j, i, AR.upd_perfect(U32, d, t, j, x, pf),
          L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, Nat.add(j, 1n+m), Nat.add(1n+j, m), add_shift(j, m), hjk),
          L.subst(Nat, z => {Nat.is_le(z, i) == True{} : Bool}, Nat.add(j, 1n+m), Nat.add(1n+j, m), add_shift(j, m), hi)),
        upd_other(d, t, j, x, i, pf, hj, ne_flip(j, i, ne_of_lt(j, i, hji))))

def ne_lt_flip(+i: Nat, +j: Nat, +h1: {Nat.is_le(j, i) == True{} : Bool}, +hs: {Nat.is_eq(i, j) == False{} : Bool}) -> {Nat.is_le(i, j) == False{} : Bool}:
  match i j:
    case 0n 0n:
      Empty.absurd({Nat.is_le(0n, 0n) == False{} : Bool}, L.true_false(hs))
    case 0n 1n+q:
      Empty.absurd({Nat.is_le(0n, 1n+q) == False{} : Bool}, L.false_true(h1))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ne_lt_flip(p, q, h1, hs)

def shl_moved_split(+m: Nat, +d: Nat, +t: AR.Tree<U32>, +j: Nat, +i: Nat, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hjk: {Nat.is_lt(Nat.add(j, 1n+m), SC.pow2(d)) == True{} : Bool}, +h1: {Nat.is_le(j, i) == True{} : Bool}, +h2: {Nat.is_lt(i, Nat.add(j, 1n+m)) == True{} : Bool}, same: Bool, +hs: {Nat.is_eq(i, j) == same : Bool}, ih: @+hh: {Nat.is_le(1n+j, i) == True{} : Bool} -> {SC.nth(U32, AR.slots(U32, shl_tree(m, d, AR.upd(U32, d, t, j, val_at(AR.slots(U32, t), 1n+j)), 1n+j)), i) == SC.nth(U32, AR.slots(U32, AR.upd(U32, d, t, j, val_at(AR.slots(U32, t), 1n+j))), 1n+i) : Maybe<&2, U32>}) -> {SC.nth(U32, AR.slots(U32, shl_tree(1n+m, d, t, j)), i) == SC.nth(U32, AR.slots(U32, t), 1n+i) : Maybe<&2, U32>}:
  match same:
    case True{}:
      +x = val_at(AR.slots(U32, t), 1n+j)
      +hj = N.le_lt_trans(j, Nat.add(j, 1n+m), SC.pow2(d), N.le_add_right(j, 1n+m), hjk)
      +hjs = N.le_lt_trans(1n+j, Nat.add(j, 1n+m), SC.pow2(d), L.subst(Nat, z => {Nat.is_le(1n+j, z) == True{} : Bool}, 1n+Nat.add(j, m), Nat.add(j, 1n+m), Equal.sym(Nat, Nat.add(j, 1n+m), 1n+Nat.add(j, m), N.add_succ(j, m)), N.lt_succ_le_succ(j, 1n+Nat.add(j, m), N.le_lt_trans(j, Nat.add(j, m), 1n+Nat.add(j, m), N.le_add_right(j, m), N.lt_succ(Nat.add(j, m))))), hjk)
      L.subst(Nat, z => {SC.nth(U32, AR.slots(U32, shl_tree(1n+m, d, t, j)), z) == SC.nth(U32, AR.slots(U32, t), 1n+z) : Maybe<&2, U32>}, j, i, Equal.sym(Nat, i, j, N.eq_from_is_eq(i, j, hs)),
        Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, shl_tree(m, d, AR.upd(U32, d, t, j, x), 1n+j)), j), SC.nth(U32, AR.slots(U32, AR.upd(U32, d, t, j, x)), j), SC.nth(U32, AR.slots(U32, t), 1n+j),
          shl_below(m, d, AR.upd(U32, d, t, j, x), 1n+j, j, AR.upd_perfect(U32, d, t, j, x, pf),
            L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, Nat.add(j, 1n+m), Nat.add(1n+j, m), add_shift(j, m), hjk),
            N.lt_succ(j)),
          Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, AR.upd(U32, d, t, j, x)), j), Some{x}, SC.nth(U32, AR.slots(U32, t), 1n+j),
            upd_same(d, t, j, x, pf, hj),
            Equal.sym(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, t), 1n+j), Some{x}, some_at(d, t, 1n+j, pf, hjs)))))
    case False{}:
      +x = val_at(AR.slots(U32, t), 1n+j)
      +hj = N.le_lt_trans(j, Nat.add(j, 1n+m), SC.pow2(d), N.le_add_right(j, 1n+m), hjk)
      Equal.trans(Maybe<&2, U32>, SC.nth(U32, AR.slots(U32, shl_tree(m, d, AR.upd(U32, d, t, j, x), 1n+j)), i), SC.nth(U32, AR.slots(U32, AR.upd(U32, d, t, j, x)), 1n+i), SC.nth(U32, AR.slots(U32, t), 1n+i),
        ih(N.lt_succ_le_succ(j, i, N.not_le_lt(i, j, ne_lt_flip(i, j, h1, hs)))),
        upd_other(d, t, j, x, 1n+i, pf, hj, ne_flip(j, 1n+i, ne_of_lt(j, 1n+i, N.le_lt_trans(j, i, 1n+i, h1, N.lt_succ(i))))))

# j <= i and i /= j give NOT (i <= j).
def shl_moved(+k: Nat, +d: Nat, +t: AR.Tree<U32>, +j: Nat, +i: Nat, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hjk: {Nat.is_lt(Nat.add(j, k), SC.pow2(d)) == True{} : Bool}, +h1: {Nat.is_le(j, i) == True{} : Bool}, +h2: {Nat.is_lt(i, Nat.add(j, k)) == True{} : Bool}) -> {SC.nth(U32, AR.slots(U32, shl_tree(k, d, t, j)), i) == SC.nth(U32, AR.slots(U32, t), 1n+i) : Maybe<&2, U32>}:
  match k:
    case 0n:
      Empty.absurd({SC.nth(U32, AR.slots(U32, shl_tree(0n, d, t, j)), i) == SC.nth(U32, AR.slots(U32, t), 1n+i) : Maybe<&2, U32>},
        L.true_not_false(Nat.is_le(j, i), h1, N.lt_not_le(i, j, L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, Nat.add(j, 0n), j, N.add_zero(j), h2))))
    case 1n+m:
      shl_moved_split(m, d, t, j, i, pf, hjk, h1, h2, Nat.is_eq(i, j), {==},
        hh => shl_moved(m, d, AR.upd(U32, d, t, j, val_at(AR.slots(U32, t), 1n+j)), 1n+j, i,
                AR.upd_perfect(U32, d, t, j, val_at(AR.slots(U32, t), 1n+j), pf),
                L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, Nat.add(j, 1n+m), Nat.add(1n+j, m), add_shift(j, m), hjk),
                hh,
                L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, Nat.add(j, 1n+m), Nat.add(1n+j, m), add_shift(j, m), h2)))
