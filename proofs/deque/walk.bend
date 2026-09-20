import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../src/deque.bend as DQ
import ../dynamic_array/layout.bend as LY
import ./layout.bend as WN
import ./state.bend as ST

# `to_list` reads the len slots of the window, last one first, and conses
# them: this file proves that the indexed read walk of src/deque.bend
# produces exactly LY.somes of the slot list, which is the model.

def unwrap(-T: Data, m: Maybe<&2, Maybe<&2, T>>) -> Maybe<&2, T>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      s

# the content of slot j
def slot(-T: Data, +xs: List<&2, Maybe<&2, T>>, +j: Nat) -> Maybe<&2, T>:
  unwrap(T, SC.nth(Maybe<&2, T>, xs, j))

def nth_slot(-T: Data, +xs: List<&2, Maybe<&2, T>>, +j: Nat, +hj: {Nat.is_lt(j, SC.length(Maybe<&2, T>, xs)) == True{} : Bool}) -> {SC.nth(Maybe<&2, T>, xs, j) == Some{slot(T, xs, j)} : Maybe<&2, Maybe<&2, T>>}:
  match xs j:
    case Nil{} _:
      Empty.absurd({None{} == Some{None{}} : Maybe<&2, Maybe<&2, T>>}, N.lt_zero_absurd(j, hj))
    case Con{x, r} 0n:
      {==}
    case Con{x, +r} 1n+k:
      nth_slot(T, r, k, hj)

# ---- the walk on the slot list ----

def tvals(k: Nat, -T: Data, +xs: List<&2, Maybe<&2, T>>, +lo: Nat, acc: List<&2, T>) -> List<&2, T>:
  match k:
    case 0n:
      acc
    case 1n+ +m:
      tvals(m, T, xs, lo, DQ.cons_mb(T, slot(T, xs, Nat.add(lo, m)), acc))

# ---- the source walk is the walk on the slot list ----

def dec1_le(+m: Nat) -> {Nat.is_le(DQ.dec1(m), m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      N.le_succ(p)

def add_le(+a: Nat, +x: Nat, +y: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, x), Nat.add(a, y)) == True{} : Bool}:
  match a:
    case 0n:
      h
    case 1n+p:
      add_le(p, x, y, h)

def get_slot(-T: Data, +d: Nat, +t: AR.Tree<Maybe<&2, T>>, +j: Nat, +hd: {Nat.is_le(d, 31n) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, T>, d, t) == True{} : Bool}) -> {Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(j)) == (AR.thaw(Maybe<&2, T>, t), slot(T, AR.slots(Maybe<&2, T>, t), j)) : Array<Maybe<&2, T>> & Maybe<&2, T>}:
  +ss = AR.slots(Maybe<&2, T>, t)
  +ej = U.to_nat_from_nat(j, d, ST.le32(d, hd), hj)
  AR.get(Maybe<&2, T>, d, t, U32.from_nat(j), slot(T, ss, j), ST.lt32(d, hd),
    L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, j, U32.to_nat(U32.from_nat(j)), Equal.sym(Nat, U32.to_nat(U32.from_nat(j)), j, ej), hj),
    L.subst(Nat, z => {SC.nth(Maybe<&2, T>, ss, z) == Some{slot(T, ss, j)} : Maybe<&2, Maybe<&2, T>>}, j, U32.to_nat(U32.from_nat(j)), Equal.sym(Nat, U32.to_nat(U32.from_nat(j)), j, ej),
      nth_slot(T, ss, j, L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, SC.pow2(d), SC.length(Maybe<&2, T>, ss), Equal.sym(Nat, SC.length(Maybe<&2, T>, ss), SC.pow2(d), AR.slots_length(Maybe<&2, T>, d, t, pf)), hj))),
    pf)

def tl_thaw(k: Nat, -T: Data, +d: Nat, +t: AR.Tree<Maybe<&2, T>>, +lo: Nat, acc: List<&2, T>, +hd: {Nat.is_le(d, 31n) == True{} : Bool}, +hb: {Nat.is_lt(Nat.add(lo, DQ.dec1(k)), SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, T>, d, t) == True{} : Bool}) -> {DQ.tl_go(k, T, lo, acc, (AR.thaw(Maybe<&2, T>, t), slot(T, AR.slots(Maybe<&2, T>, t), Nat.add(lo, DQ.dec1(k))))) == (AR.thaw(Maybe<&2, T>, t), tvals(k, T, AR.slots(Maybe<&2, T>, t), lo, acc)) : Array<Maybe<&2, T>> & List<&2, T>}:
  match k:
    case 0n:
      {==}
    case 1n+ +m:
      +ss = AR.slots(Maybe<&2, T>, t)
      +hj = N.le_lt_trans(Nat.add(lo, DQ.dec1(m)), Nat.add(lo, m), SC.pow2(d), add_le(lo, DQ.dec1(m), m, dec1_le(m)), hb)
      %Equal.sym(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(Nat.add(lo, DQ.dec1(m)))), (AR.thaw(Maybe<&2, T>, t), slot(T, ss, Nat.add(lo, DQ.dec1(m)))), get_slot(T, d, t, Nat.add(lo, DQ.dec1(m)), hd, hj, pf)) : {DQ.tl_go(m, T, lo, DQ.cons_mb(T, slot(T, ss, Nat.add(lo, m)), acc), _) == (AR.thaw(Maybe<&2, T>, t), tvals(1n+m, T, ss, lo, acc)) : Array<Maybe<&2, T>> & List<&2, T>}
      tl_thaw(m, T, d, t, lo, DQ.cons_mb(T, slot(T, ss, Nat.add(lo, m)), acc), hd, hj, pf)

# ---- the walk on the slot list is the model ----

def take_all(-T: Data, +ys: List<&2, T>, +n: Nat, +h: {SC.length(T, ys) == n : Nat}) -> {SC.take(T, ys, n) == ys : List<&2, T>}:
  match ys n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+m:
      Empty.absurd({Nil{} == Nil{} : List<&2, T>}, N.zero_succ(m, h))
    case Con{y, r} 0n:
      Empty.absurd({Nil{} == Con{y, r} : List<&2, T>}, N.succ_zero(SC.length(T, r), h))
    case Con{+y, +r} 1n+m:
      LL.cons_cong(T, y, SC.take(T, r, m), r, take_all(T, r, m, N.succ_inj(SC.length(T, r), m, h)))

def take_cons_mb(-T: Data, +ys: List<&2, T>, +m: Nat, +acc: List<&2, T>, +hm: {Nat.is_lt(m, SC.length(T, ys)) == True{} : Bool}) -> {SC.append(T, SC.take(T, ys, m), DQ.cons_mb(T, SC.nth(T, ys, m), acc)) == SC.append(T, SC.take(T, ys, 1n+m), acc) : List<&2, T>}:
  match ys m:
    case Nil{} _:
      Empty.absurd({DQ.cons_mb(T, None{}, acc) == acc : List<&2, T>}, N.lt_zero_absurd(m, hm))
    case Con{y, +r} 0n:
      %Equal.sym(List<&2, T>, SC.take(T, r, 0n), Nil{}, LL.sc_take_zero(T, r)) : {Con{y, acc} == SC.append(T, Con{y, _}, acc) : List<&2, T>}
      {==}
    case Con{+y, +r} 1n+k:
      LL.cons_cong(T, y, SC.append(T, SC.take(T, r, k), DQ.cons_mb(T, SC.nth(T, r, k), acc)), SC.append(T, SC.take(T, r, 1n+k), acc), take_cons_mb(T, r, k, acc, hm))

def slot_nth(-T: Data, +xs: List<&2, Maybe<&2, T>>, +lo: Nat, +n: Nat, +m: Nat, +h: {WN.win(T, xs, lo, n) == True{} : Bool}, +hm: {Nat.is_lt(m, n) == True{} : Bool}) -> {slot(T, xs, Nat.add(lo, m)) == SC.nth(T, LY.somes(T, xs), m) : Maybe<&2, T>}:
  %Equal.sym(Maybe<&2, Maybe<&2, T>>, SC.nth(Maybe<&2, T>, xs, Nat.add(lo, m)), Some{SC.nth(T, LY.somes(T, xs), m)}, WN.win_nth(T, xs, lo, n, m, h, hm)) : {unwrap(T, _) == SC.nth(T, LY.somes(T, xs), m) : Maybe<&2, T>}
  {==}

def tvals_take(k: Nat, -T: Data, +xs: List<&2, Maybe<&2, T>>, +lo: Nat, +n: Nat, +acc: List<&2, T>, +h: {WN.win(T, xs, lo, n) == True{} : Bool}, +hk: {Nat.is_le(k, n) == True{} : Bool}) -> {tvals(k, T, xs, lo, acc) == SC.append(T, SC.take(T, LY.somes(T, xs), k), acc) : List<&2, T>}:
  match k:
    case 0n:
      %Equal.sym(List<&2, T>, SC.take(T, LY.somes(T, xs), 0n), Nil{}, LL.sc_take_zero(T, LY.somes(T, xs))) : {acc == SC.append(T, _, acc) : List<&2, T>}
      {==}
    case 1n+ +m:
      +ys = LY.somes(T, xs)
      +hm = N.succ_le_lt(m, n, hk)
      +hlen = N.lt_le_trans(m, n, SC.length(T, ys), hm, N.eq_le(n, SC.length(T, ys), Equal.sym(Nat, SC.length(T, ys), n, WN.win_len(T, xs, lo, n, h))))
      %Equal.sym(Maybe<&2, T>, slot(T, xs, Nat.add(lo, m)), SC.nth(T, ys, m), slot_nth(T, xs, lo, n, m, h, hm)) : {tvals(m, T, xs, lo, DQ.cons_mb(T, _, acc)) == SC.append(T, SC.take(T, ys, 1n+m), acc) : List<&2, T>}
      %take_cons_mb(T, ys, m, acc, hlen) : {tvals(m, T, xs, lo, DQ.cons_mb(T, SC.nth(T, ys, m), acc)) == _ : List<&2, T>}
      tvals_take(m, T, xs, lo, n, DQ.cons_mb(T, SC.nth(T, ys, m), acc), h, N.lt_le(m, n, hm))

# the whole window: the walk produces the model
def tvals_model(-T: Data, +xs: List<&2, Maybe<&2, T>>, +lo: Nat, +n: Nat, +h: {WN.win(T, xs, lo, n) == True{} : Bool}) -> {tvals(n, T, xs, lo, Nil{}) == LY.somes(T, xs) : List<&2, T>}:
  %take_all(T, LY.somes(T, xs), n, WN.win_len(T, xs, lo, n, h)) : {tvals(n, T, xs, lo, Nil{}) == _ : List<&2, T>}
  %LL.append_nil(T, SC.take(T, LY.somes(T, xs), n)) : {tvals(n, T, xs, lo, Nil{}) == _ : List<&2, T>}
  tvals_take(n, T, xs, lo, n, Nil{}, h, N.le_refl(n))
