import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../lib/array2.bend as A2
import ../binary_heap/u32idx.bend as IX
import ../../spec/common.bend as SC
import ../../src/graph.bend as G
import ./shift.bend as SH
import ./blk.bend as BK
import ./blkops.bend as BO
import ./zip.bend as ZP

# The vertex-table shift loops against the list-level shifts of zip.bend.
# The id table (U32 words) is copied slot by slot; the adjacency table swaps
# each block out, leaving a one-word placeholder behind, so no block is ever
# duplicated.

# ---- generic slot facts ----

def sat(-T: Data, +xs: List<&2, T>, +i: Nat, +d: T, +h: {Nat.is_lt(i, SC.length(T, xs)) == True{} : Bool}) -> {SC.nth(T, xs, i) == Some{ZP.vget(T, d, xs, i)} : Maybe<&2, T>}:
  match xs i:
    case Nil{} i0:
      Empty.absurd({SC.nth(T, Nil{}, i0) == Some{ZP.vget(T, d, Nil{}, i0)} : Maybe<&2, T>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(i0, 0n), True{}, Equal.sym(Bool, Nat.is_lt(i0, 0n), False{}, N.not_lt_zero(i0)), h)))
    case Con{+hh, +t} 0n:
      {==}
    case Con{+hh, +t} 1n+p:
      sat(T, t, p, d, h)

def tsat(-T: Data, +dp: Nat, +t: AR.Tree<T>, +i: Nat, +d: T, +pf: {AR.perfect(T, dp, t) == True{} : Bool}, +h: {Nat.is_lt(i, SC.pow2(dp)) == True{} : Bool}) -> {SC.nth(T, AR.slots(T, t), i) == Some{ZP.vget(T, d, AR.slots(T, t), i)} : Maybe<&2, T>}:
  sat(T, AR.slots(T, t), i, d, AR.len_lt(T, dp, t, i, pf, h))

# ---- the id table ----

def sl_slots(+k: Nat, +d: Nat, +t: AR.Tree<U32>, +j: Nat, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hjk: {Nat.is_lt(Nat.add(j, k), SC.pow2(d)) == True{} : Bool}) -> {AR.slots(U32, SH.shl_tree(k, d, t, j)) == ZP.lsl(U32, False{}, 0, 0, k, AR.slots(U32, t), j) : List<&2, U32>}:
  match k:
    case 0n:
      {==}
    case 1n+m:
      +x = SH.val_at(AR.slots(U32, t), 1n+j)
      +hj = N.le_lt_trans(j, Nat.add(j, 1n+m), SC.pow2(d), N.le_add_right(j, 1n+m), hjk)
      +ih = sl_slots(m, d, AR.upd(U32, d, t, j, x), 1n+j, AR.upd_perfect(U32, d, t, j, x, pf), L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, Nat.add(j, 1n+m), Nat.add(1n+j, m), SH.add_shift(j, m), hjk))
      Equal.trans(List<&2, U32>, AR.slots(U32, SH.shl_tree(m, d, AR.upd(U32, d, t, j, x), 1n+j)), ZP.lsl(U32, False{}, 0, 0, m, AR.slots(U32, AR.upd(U32, d, t, j, x)), 1n+j), ZP.lsl(U32, False{}, 0, 0, m, SC.update(U32, AR.slots(U32, t), j, x), 1n+j),
        ih, Equal.cong(List<&2, U32>, List<&2, U32>, z => ZP.lsl(U32, False{}, 0, 0, m, z, 1n+j), AR.slots(U32, AR.upd(U32, d, t, j, x)), SC.update(U32, AR.slots(U32, t), j, x), AR.upd_slots(U32, d, t, j, x, hj, pf)))

def sr_slots(+k: Nat, +d: Nat, +t: AR.Tree<U32>, +j: Nat, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +hk: {Nat.is_le(k, j) == True{} : Bool}) -> {AR.slots(U32, SH.shr_tree(k, d, t, j)) == ZP.lsr(U32, False{}, 0, 0, k, AR.slots(U32, t), j) : List<&2, U32>}:
  match k:
    case 0n:
      {==}
    case 1n+m:
      +x = SH.val_at(AR.slots(U32, t), Nat.sub(j, 1n))
      +hjm = N.le_lt_trans(Nat.sub(j, 1n), j, SC.pow2(d), IX.sub_le(j), hj)
      +ih = sr_slots(m, d, AR.upd(U32, d, t, j, x), Nat.sub(j, 1n), AR.upd_perfect(U32, d, t, j, x, pf), hjm, SH.le_pred(m, j, hk))
      Equal.trans(List<&2, U32>, AR.slots(U32, SH.shr_tree(m, d, AR.upd(U32, d, t, j, x), Nat.sub(j, 1n))), ZP.lsr(U32, False{}, 0, 0, m, AR.slots(U32, AR.upd(U32, d, t, j, x)), Nat.sub(j, 1n)), ZP.lsr(U32, False{}, 0, 0, m, SC.update(U32, AR.slots(U32, t), j, x), Nat.sub(j, 1n)),
        ih, Equal.cong(List<&2, U32>, List<&2, U32>, z => ZP.lsr(U32, False{}, 0, 0, m, z, Nat.sub(j, 1n)), AR.slots(U32, AR.upd(U32, d, t, j, x)), SC.update(U32, AR.slots(U32, t), j, x), AR.upd_slots(U32, d, t, j, x, hj, pf)))

# ---- the adjacency table ----

def shla_tree(+k: Nat, +d: Nat, +t: AR.Tree<AR.Tree<U32>>, +j: Nat) -> AR.Tree<AR.Tree<U32>>:
  match k:
    case 0n:
      t
    case 1n+m:
      shla_tree(m, d, AR.upd(AR.Tree<U32>, d, AR.upd(AR.Tree<U32>, d, t, 1n+j, BK.leaf0()), j, ZP.vget(AR.Tree<U32>, BK.leaf0(), AR.slots(AR.Tree<U32>, t), 1n+j)), 1n+j)

def shra_tree(+k: Nat, +d: Nat, +t: AR.Tree<AR.Tree<U32>>, +j: Nat) -> AR.Tree<AR.Tree<U32>>:
  match k:
    case 0n:
      t
    case 1n+m:
      shra_tree(m, d, AR.upd(AR.Tree<U32>, d, AR.upd(AR.Tree<U32>, d, t, Nat.sub(j, 1n), BK.leaf0()), j, ZP.vget(AR.Tree<U32>, BK.leaf0(), AR.slots(AR.Tree<U32>, t), Nat.sub(j, 1n))), Nat.sub(j, 1n))

def shla_perfect(+k: Nat, +d: Nat, +t: AR.Tree<AR.Tree<U32>>, +j: Nat, +pf: {AR.perfect(AR.Tree<U32>, d, t) == True{} : Bool}) -> {AR.perfect(AR.Tree<U32>, d, shla_tree(k, d, t, j)) == True{} : Bool}:
  match k:
    case 0n:
      pf
    case 1n+m:
      +t1 = AR.upd(AR.Tree<U32>, d, t, 1n+j, BK.leaf0())
      +x = ZP.vget(AR.Tree<U32>, BK.leaf0(), AR.slots(AR.Tree<U32>, t), 1n+j)
      shla_perfect(m, d, AR.upd(AR.Tree<U32>, d, t1, j, x), 1n+j, AR.upd_perfect(AR.Tree<U32>, d, t1, j, x, AR.upd_perfect(AR.Tree<U32>, d, t, 1n+j, BK.leaf0(), pf)))

def shra_perfect(+k: Nat, +d: Nat, +t: AR.Tree<AR.Tree<U32>>, +j: Nat, +pf: {AR.perfect(AR.Tree<U32>, d, t) == True{} : Bool}) -> {AR.perfect(AR.Tree<U32>, d, shra_tree(k, d, t, j)) == True{} : Bool}:
  match k:
    case 0n:
      pf
    case 1n+m:
      +t1 = AR.upd(AR.Tree<U32>, d, t, Nat.sub(j, 1n), BK.leaf0())
      +x = ZP.vget(AR.Tree<U32>, BK.leaf0(), AR.slots(AR.Tree<U32>, t), Nat.sub(j, 1n))
      shra_perfect(m, d, AR.upd(AR.Tree<U32>, d, t1, j, x), Nat.sub(j, 1n), AR.upd_perfect(AR.Tree<U32>, d, t1, j, x, AR.upd_perfect(AR.Tree<U32>, d, t, Nat.sub(j, 1n), BK.leaf0(), pf)))

def sla_slots(+k: Nat, +d: Nat, +t: AR.Tree<AR.Tree<U32>>, +j: Nat, +pf: {AR.perfect(AR.Tree<U32>, d, t) == True{} : Bool}, +hjk: {Nat.is_lt(Nat.add(j, k), SC.pow2(d)) == True{} : Bool}) -> {AR.slots(AR.Tree<U32>, shla_tree(k, d, t, j)) == ZP.lsl(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), k, AR.slots(AR.Tree<U32>, t), j) : List<&2, AR.Tree<U32>>}:
  match k:
    case 0n:
      {==}
    case 1n+m:
      +xs = AR.slots(AR.Tree<U32>, t)
      +t1 = AR.upd(AR.Tree<U32>, d, t, 1n+j, BK.leaf0())
      +x = ZP.vget(AR.Tree<U32>, BK.leaf0(), xs, 1n+j)
      +hj1 = N.le_lt_trans(1n+j, Nat.add(j, 1n+m), SC.pow2(d), L.subst(Nat, z => {Nat.is_le(1n+j, z) == True{} : Bool}, Nat.add(1n+j, m), Nat.add(j, 1n+m), Equal.sym(Nat, Nat.add(j, 1n+m), Nat.add(1n+j, m), SH.add_shift(j, m)), N.le_add_right(1n+j, m)), hjk)
      +hj = N.le_lt_trans(j, 1n+j, SC.pow2(d), N.le_succ(j), hj1)
      +pf1 = AR.upd_perfect(AR.Tree<U32>, d, t, 1n+j, BK.leaf0(), pf)
      +ih = sla_slots(m, d, AR.upd(AR.Tree<U32>, d, t1, j, x), 1n+j, AR.upd_perfect(AR.Tree<U32>, d, t1, j, x, pf1), L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, Nat.add(j, 1n+m), Nat.add(1n+j, m), SH.add_shift(j, m), hjk))
      +es = Equal.trans(List<&2, AR.Tree<U32>>, AR.slots(AR.Tree<U32>, AR.upd(AR.Tree<U32>, d, t1, j, x)), SC.update(AR.Tree<U32>, AR.slots(AR.Tree<U32>, t1), j, x), SC.update(AR.Tree<U32>, SC.update(AR.Tree<U32>, xs, 1n+j, BK.leaf0()), j, x),
        AR.upd_slots(AR.Tree<U32>, d, t1, j, x, hj, pf1),
        Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => SC.update(AR.Tree<U32>, z, j, x), AR.slots(AR.Tree<U32>, t1), SC.update(AR.Tree<U32>, xs, 1n+j, BK.leaf0()), AR.upd_slots(AR.Tree<U32>, d, t, 1n+j, BK.leaf0(), hj1, pf)))
      Equal.trans(List<&2, AR.Tree<U32>>, AR.slots(AR.Tree<U32>, shla_tree(m, d, AR.upd(AR.Tree<U32>, d, t1, j, x), 1n+j)), ZP.lsl(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), m, AR.slots(AR.Tree<U32>, AR.upd(AR.Tree<U32>, d, t1, j, x)), 1n+j), ZP.lsl(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), m, SC.update(AR.Tree<U32>, SC.update(AR.Tree<U32>, xs, 1n+j, BK.leaf0()), j, x), 1n+j),
        ih, Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => ZP.lsl(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), m, z, 1n+j), AR.slots(AR.Tree<U32>, AR.upd(AR.Tree<U32>, d, t1, j, x)), SC.update(AR.Tree<U32>, SC.update(AR.Tree<U32>, xs, 1n+j, BK.leaf0()), j, x), es))

def sra_slots(+k: Nat, +d: Nat, +t: AR.Tree<AR.Tree<U32>>, +j: Nat, +pf: {AR.perfect(AR.Tree<U32>, d, t) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +hk: {Nat.is_le(k, j) == True{} : Bool}) -> {AR.slots(AR.Tree<U32>, shra_tree(k, d, t, j)) == ZP.lsr(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), k, AR.slots(AR.Tree<U32>, t), j) : List<&2, AR.Tree<U32>>}:
  match k:
    case 0n:
      {==}
    case 1n+m:
      +xs = AR.slots(AR.Tree<U32>, t)
      +j1 = Nat.sub(j, 1n)
      +t1 = AR.upd(AR.Tree<U32>, d, t, j1, BK.leaf0())
      +x = ZP.vget(AR.Tree<U32>, BK.leaf0(), xs, j1)
      +hjm = N.le_lt_trans(j1, j, SC.pow2(d), IX.sub_le(j), hj)
      +pf1 = AR.upd_perfect(AR.Tree<U32>, d, t, j1, BK.leaf0(), pf)
      +ih = sra_slots(m, d, AR.upd(AR.Tree<U32>, d, t1, j, x), j1, AR.upd_perfect(AR.Tree<U32>, d, t1, j, x, pf1), hjm, SH.le_pred(m, j, hk))
      +es = Equal.trans(List<&2, AR.Tree<U32>>, AR.slots(AR.Tree<U32>, AR.upd(AR.Tree<U32>, d, t1, j, x)), SC.update(AR.Tree<U32>, AR.slots(AR.Tree<U32>, t1), j, x), SC.update(AR.Tree<U32>, SC.update(AR.Tree<U32>, xs, j1, BK.leaf0()), j, x),
        AR.upd_slots(AR.Tree<U32>, d, t1, j, x, hj, pf1),
        Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => SC.update(AR.Tree<U32>, z, j, x), AR.slots(AR.Tree<U32>, t1), SC.update(AR.Tree<U32>, xs, j1, BK.leaf0()), AR.upd_slots(AR.Tree<U32>, d, t, j1, BK.leaf0(), hjm, pf)))
      Equal.trans(List<&2, AR.Tree<U32>>, AR.slots(AR.Tree<U32>, shra_tree(m, d, AR.upd(AR.Tree<U32>, d, t1, j, x), j1)), ZP.lsr(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), m, AR.slots(AR.Tree<U32>, AR.upd(AR.Tree<U32>, d, t1, j, x)), j1), ZP.lsr(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), m, SC.update(AR.Tree<U32>, SC.update(AR.Tree<U32>, xs, j1, BK.leaf0()), j, x), j1),
        ih, Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => ZP.lsr(AR.Tree<U32>, True{}, BK.leaf0(), BK.leaf0(), m, z, j1), AR.slots(AR.Tree<U32>, AR.upd(AR.Tree<U32>, d, t1, j, x)), SC.update(AR.Tree<U32>, SC.update(AR.Tree<U32>, xs, j1, BK.leaf0()), j, x), es))

# ---- the runtime loops are the mirror trees ----

def zeros0() -> {G.zeros(0n) == AR.thaw(U32, BK.leaf0()) : Array<U32>}:
  AR.new(U32, 0n, 0)

def sw_pair(+d: Nat, +t: AR.Tree<AR.Tree<U32>>, +i: Nat, +x: AR.Tree<U32>) -> Array<Array<U32>> & Array<U32>:
  (A2.thaw2(AR.upd(AR.Tree<U32>, d, t, i, BK.leaf0())), AR.thaw(U32, x))

# Swap the block at i (in range) for the placeholder.
def swap_out(+d: Nat, +t: AR.Tree<AR.Tree<U32>>, +i: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(AR.Tree<U32>, d, t) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}) -> {Array.swap(Array<U32>, A2.thaw2(t), U32.from_nat(i), G.zeros(0n)) == (A2.thaw2(AR.upd(AR.Tree<U32>, d, t, i, BK.leaf0())), AR.thaw(U32, ZP.vget(AR.Tree<U32>, BK.leaf0(), AR.slots(AR.Tree<U32>, t), i))) : Array<Array<U32>> & Array<U32>}:
  +x = ZP.vget(AR.Tree<U32>, BK.leaf0(), AR.slots(AR.Tree<U32>, t), i)
  +ri = IX.nat_round(i, d, N.lt_le(d, 32n, hd), hi)
  Equal.trans(Array<Array<U32>> & Array<U32>, Array.swap(Array<U32>, A2.thaw2(t), U32.from_nat(i), G.zeros(0n)), Array.swap(Array<U32>, A2.thaw2(t), U32.from_nat(i), AR.thaw(U32, BK.leaf0())), (A2.thaw2(AR.upd(AR.Tree<U32>, d, t, i, BK.leaf0())), AR.thaw(U32, x)),
    Equal.cong(Array<U32>, Array<Array<U32>> & Array<U32>, z => Array.swap(Array<U32>, A2.thaw2(t), U32.from_nat(i), z), G.zeros(0n), AR.thaw(U32, BK.leaf0()), zeros0()),
    Equal.trans(Array<Array<U32>> & Array<U32>, Array.swap(Array<U32>, A2.thaw2(t), U32.from_nat(i), AR.thaw(U32, BK.leaf0())), (A2.thaw2(AR.upd(AR.Tree<U32>, d, t, U32.to_nat(U32.from_nat(i)), BK.leaf0())), AR.thaw(U32, x)), (A2.thaw2(AR.upd(AR.Tree<U32>, d, t, i, BK.leaf0())), AR.thaw(U32, x)),
      A2.swap2(d, t, U32.from_nat(i), BK.leaf0(), x, hd,
        L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, ri), hi),
        L.subst(Nat, z => {SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, t), z) == Some{x} : Maybe<&2, AR.Tree<U32>>}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, ri), tsat(AR.Tree<U32>, d, t, i, BK.leaf0(), pf, hi)),
        pf),
      Equal.cong(Nat, Array<Array<U32>> & Array<U32>, z => sw_pair(d, t, z, x), U32.to_nat(U32.from_nat(i)), i, ri)))

# Store a block at i (in range).
def put_in(+d: Nat, +t: AR.Tree<AR.Tree<U32>>, +i: Nat, +b: AR.Tree<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(AR.Tree<U32>, d, t) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}) -> {Array.set(Array<U32>, A2.thaw2(t), U32.from_nat(i), AR.thaw(U32, b)) == A2.thaw2(AR.upd(AR.Tree<U32>, d, t, i, b)) : Array<Array<U32>>}:
  +ri = IX.nat_round(i, d, N.lt_le(d, 32n, hd), hi)
  Equal.trans(Array<Array<U32>>, Array.set(Array<U32>, A2.thaw2(t), U32.from_nat(i), AR.thaw(U32, b)), A2.thaw2(AR.upd(AR.Tree<U32>, d, t, U32.to_nat(U32.from_nat(i)), b)), A2.thaw2(AR.upd(AR.Tree<U32>, d, t, i, b)),
    A2.set2(d, t, U32.from_nat(i), b, ZP.vget(AR.Tree<U32>, BK.leaf0(), AR.slots(AR.Tree<U32>, t), i), hd,
      L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, ri), hi),
      L.subst(Nat, z => {SC.nth(AR.Tree<U32>, AR.slots(AR.Tree<U32>, t), z) == Some{ZP.vget(AR.Tree<U32>, BK.leaf0(), AR.slots(AR.Tree<U32>, t), i)} : Maybe<&2, AR.Tree<U32>>}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, ri), tsat(AR.Tree<U32>, d, t, i, BK.leaf0(), pf, hi)),
      pf),
    Equal.cong(Nat, Array<Array<U32>>, z => A2.thaw2(AR.upd(AR.Tree<U32>, d, t, z, b)), U32.to_nat(U32.from_nat(i)), i, ri))

def sla_run(+k: Nat, +d: Nat, +t: AR.Tree<AR.Tree<U32>>, +j: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(AR.Tree<U32>, d, t) == True{} : Bool}, +hjk: {Nat.is_lt(Nat.add(j, k), SC.pow2(d)) == True{} : Bool}) -> {G.shla_go(k, U32.from_nat(j), A2.thaw2(t)) == A2.thaw2(shla_tree(k, d, t, j)) : Array<Array<U32>>}:
  match k:
    case 0n:
      {==}
    case 1n+m:
      +t1 = AR.upd(AR.Tree<U32>, d, t, 1n+j, BK.leaf0())
      +x = ZP.vget(AR.Tree<U32>, BK.leaf0(), AR.slots(AR.Tree<U32>, t), 1n+j)
      +hj1 = N.le_lt_trans(1n+j, Nat.add(j, 1n+m), SC.pow2(d), L.subst(Nat, z => {Nat.is_le(1n+j, z) == True{} : Bool}, Nat.add(1n+j, m), Nat.add(j, 1n+m), Equal.sym(Nat, Nat.add(j, 1n+m), Nat.add(1n+j, m), SH.add_shift(j, m)), N.le_add_right(1n+j, m)), hjk)
      +hj = N.le_lt_trans(j, 1n+j, SC.pow2(d), N.le_succ(j), hj1)
      +pf1 = AR.upd_perfect(AR.Tree<U32>, d, t, 1n+j, BK.leaf0(), pf)
      +ea = Equal.cong(Array<Array<U32>> & Array<U32>, Array<Array<U32>>, z => G.shla_go(m, U32.from_nat(1n+j), G.shla_put(U32.from_nat(j), z)), Array.swap(Array<U32>, A2.thaw2(t), U32.from_nat(1n+j), G.zeros(0n)), sw_pair(d, t, 1n+j, x), swap_out(d, t, 1n+j, hd, pf, hj1))
      +eb = Equal.cong(Array<Array<U32>>, Array<Array<U32>>, z => G.shla_go(m, U32.from_nat(1n+j), z), Array.set(Array<U32>, A2.thaw2(t1), U32.from_nat(j), AR.thaw(U32, x)), A2.thaw2(AR.upd(AR.Tree<U32>, d, t1, j, x)), put_in(d, t1, j, x, hd, pf1, hj))
      +ih = sla_run(m, d, AR.upd(AR.Tree<U32>, d, t1, j, x), 1n+j, hd, AR.upd_perfect(AR.Tree<U32>, d, t1, j, x, pf1), L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, Nat.add(j, 1n+m), Nat.add(1n+j, m), SH.add_shift(j, m), hjk))
      Equal.trans(Array<Array<U32>>, G.shla_go(m, U32.from_nat(1n+j), G.shla_put(U32.from_nat(j), Array.swap(Array<U32>, A2.thaw2(t), U32.from_nat(1n+j), G.zeros(0n)))), G.shla_go(m, U32.from_nat(1n+j), G.shla_put(U32.from_nat(j), sw_pair(d, t, 1n+j, x))), A2.thaw2(shla_tree(m, d, AR.upd(AR.Tree<U32>, d, t1, j, x), 1n+j)), ea,
        Equal.trans(Array<Array<U32>>, G.shla_go(m, U32.from_nat(1n+j), G.shla_put(U32.from_nat(j), sw_pair(d, t, 1n+j, x))), G.shla_go(m, U32.from_nat(1n+j), A2.thaw2(AR.upd(AR.Tree<U32>, d, t1, j, x))), A2.thaw2(shla_tree(m, d, AR.upd(AR.Tree<U32>, d, t1, j, x), 1n+j)), eb, ih))

def sra_run(+k: Nat, +d: Nat, +t: AR.Tree<AR.Tree<U32>>, +j: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(AR.Tree<U32>, d, t) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +hk: {Nat.is_le(k, j) == True{} : Bool}) -> {G.shra_go(k, U32.from_nat(j), A2.thaw2(t)) == A2.thaw2(shra_tree(k, d, t, j)) : Array<Array<U32>>}:
  match k:
    case 0n:
      {==}
    case 1n+m:
      +j1 = Nat.sub(j, 1n)
      +t1 = AR.upd(AR.Tree<U32>, d, t, j1, BK.leaf0())
      +x = ZP.vget(AR.Tree<U32>, BK.leaf0(), AR.slots(AR.Tree<U32>, t), j1)
      +hk1 = N.le_trans(1n, 1n+m, j, N.lt_succ_le_succ(0n, 1n+m, {==}), hk)
      +hjm = N.le_lt_trans(j1, j, SC.pow2(d), IX.sub_le(j), hj)
      +pf1 = AR.upd_perfect(AR.Tree<U32>, d, t, j1, BK.leaf0(), pf)
      +e0 = Equal.cong(U32, Array<Array<U32>>, z => G.shra_go(m, z, G.shra_put(U32.from_nat(j), Array.swap(Array<U32>, A2.thaw2(t), z, G.zeros(0n)))), U32.sub(U32.from_nat(j), 1), U32.from_nat(j1), IX.sub_one(j, d, N.lt_le(d, 32n, hd), hj, hk1))
      +ea = Equal.cong(Array<Array<U32>> & Array<U32>, Array<Array<U32>>, z => G.shra_go(m, U32.from_nat(j1), G.shra_put(U32.from_nat(j), z)), Array.swap(Array<U32>, A2.thaw2(t), U32.from_nat(j1), G.zeros(0n)), sw_pair(d, t, j1, x), swap_out(d, t, j1, hd, pf, hjm))
      +eb = Equal.cong(Array<Array<U32>>, Array<Array<U32>>, z => G.shra_go(m, U32.from_nat(j1), z), Array.set(Array<U32>, A2.thaw2(t1), U32.from_nat(j), AR.thaw(U32, x)), A2.thaw2(AR.upd(AR.Tree<U32>, d, t1, j, x)), put_in(d, t1, j, x, hd, pf1, hj))
      +ih = sra_run(m, d, AR.upd(AR.Tree<U32>, d, t1, j, x), j1, hd, AR.upd_perfect(AR.Tree<U32>, d, t1, j, x, pf1), hjm, SH.le_pred(m, j, hk))
      Equal.trans(Array<Array<U32>>, G.shra_go(m, U32.sub(U32.from_nat(j), 1), G.shra_put(U32.from_nat(j), Array.swap(Array<U32>, A2.thaw2(t), U32.sub(U32.from_nat(j), 1), G.zeros(0n)))), G.shra_go(m, U32.from_nat(j1), G.shra_put(U32.from_nat(j), Array.swap(Array<U32>, A2.thaw2(t), U32.from_nat(j1), G.zeros(0n)))), A2.thaw2(shra_tree(m, d, AR.upd(AR.Tree<U32>, d, t1, j, x), j1)), e0,
        Equal.trans(Array<Array<U32>>, G.shra_go(m, U32.from_nat(j1), G.shra_put(U32.from_nat(j), Array.swap(Array<U32>, A2.thaw2(t), U32.from_nat(j1), G.zeros(0n)))), G.shra_go(m, U32.from_nat(j1), G.shra_put(U32.from_nat(j), sw_pair(d, t, j1, x))), A2.thaw2(shra_tree(m, d, AR.upd(AR.Tree<U32>, d, t1, j, x), j1)), ea,
          Equal.trans(Array<Array<U32>>, G.shra_go(m, U32.from_nat(j1), G.shra_put(U32.from_nat(j), sw_pair(d, t, j1, x))), G.shra_go(m, U32.from_nat(j1), A2.thaw2(AR.upd(AR.Tree<U32>, d, t1, j, x))), A2.thaw2(shra_tree(m, d, AR.upd(AR.Tree<U32>, d, t1, j, x), j1)), eb, ih)))
