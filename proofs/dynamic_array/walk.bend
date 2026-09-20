import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../src/dynamic_array.bend as DA
import ./layout.bend as LY
import ./state.bend as ST

# `to_list_at` reads the `length` occupied slots by index, last one first, and
# conses them. This file proves that this indexed read walk produces exactly
# `LY.somes` of the slot list -- the same list the parametric `to_list`
# produces by cloning and flattening -- without cloning the array and without
# a structural traversal.

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

def get_slot(-T: Data, +l: Nat, +d: Nat, +t: AR.Tree<Maybe<&2, T>>, +j: Nat, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, T>, d, t) == True{} : Bool}) -> {Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(j)) == (AR.thaw(Maybe<&2, T>, t), slot(T, AR.slots(Maybe<&2, T>, t), j)) : Array<Maybe<&2, T>> & Maybe<&2, T>}:
  +ss = AR.slots(Maybe<&2, T>, t)
  +ej = U.to_nat_from_nat(j, d, ST.le32(d, l, hd, hl), hj)
  AR.get(Maybe<&2, T>, d, t, U32.from_nat(j), slot(T, ss, j), ST.lt32(d, l, hd, hl),
    L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, j, U32.to_nat(U32.from_nat(j)), Equal.sym(Nat, U32.to_nat(U32.from_nat(j)), j, ej), hj),
    L.subst(Nat, z => {SC.nth(Maybe<&2, T>, ss, z) == Some{slot(T, ss, j)} : Maybe<&2, Maybe<&2, T>>}, j, U32.to_nat(U32.from_nat(j)), Equal.sym(Nat, U32.to_nat(U32.from_nat(j)), j, ej),
      nth_slot(T, ss, j, L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, SC.pow2(d), SC.length(Maybe<&2, T>, ss), Equal.sym(Nat, SC.length(Maybe<&2, T>, ss), SC.pow2(d), AR.slots_length(Maybe<&2, T>, d, t, pf)), hj))),
    pf)

# ---- the walk on the slot list ----

def tvals(k: Nat, -T: Data, +xs: List<&2, Maybe<&2, T>>, acc: List<&2, T>) -> List<&2, T>:
  match k:
    case 0n:
      acc
    case 1n+ +m:
      tvals(m, T, xs, DA.cons_some(T, slot(T, xs, m), acc))

def dec1_le(+m: Nat) -> {Nat.is_le(DA.dec1(m), m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      N.le_succ(p)

def tl_thaw(k: Nat, -T: Data, +l: Nat, +d: Nat, +t: AR.Tree<Maybe<&2, T>>, acc: List<&2, T>, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hb: {Nat.is_lt(DA.dec1(k), SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, T>, d, t) == True{} : Bool}) -> {DA.tl_go(k, T, acc, (AR.thaw(Maybe<&2, T>, t), slot(T, AR.slots(Maybe<&2, T>, t), DA.dec1(k)))) == (AR.thaw(Maybe<&2, T>, t), tvals(k, T, AR.slots(Maybe<&2, T>, t), acc)) : Array<Maybe<&2, T>> & List<&2, T>}:
  match k:
    case 0n:
      {==}
    case 1n+ +m:
      +ss = AR.slots(Maybe<&2, T>, t)
      +hj = N.le_lt_trans(DA.dec1(m), m, SC.pow2(d), dec1_le(m), hb)
      %Equal.sym(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(DA.dec1(m))), (AR.thaw(Maybe<&2, T>, t), slot(T, ss, DA.dec1(m))), get_slot(T, l, d, t, DA.dec1(m), hd, hl, hj, pf)) : {DA.tl_go(m, T, DA.cons_some(T, slot(T, ss, m), acc), _) == (AR.thaw(Maybe<&2, T>, t), tvals(1n+m, T, ss, acc)) : Array<Maybe<&2, T>> & List<&2, T>}
      tl_thaw(m, T, l, d, t, DA.cons_some(T, slot(T, ss, m), acc), hd, hl, hj, pf)

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

def take_cons_some(-T: Data, +ys: List<&2, T>, +m: Nat, +acc: List<&2, T>, +hm: {Nat.is_lt(m, SC.length(T, ys)) == True{} : Bool}) -> {SC.append(T, SC.take(T, ys, m), DA.cons_some(T, SC.nth(T, ys, m), acc)) == SC.append(T, SC.take(T, ys, 1n+m), acc) : List<&2, T>}:
  match ys m:
    case Nil{} _:
      Empty.absurd({DA.cons_some(T, None{}, acc) == acc : List<&2, T>}, N.lt_zero_absurd(m, hm))
    case Con{y, +r} 0n:
      %Equal.sym(List<&2, T>, SC.take(T, r, 0n), Nil{}, LL.sc_take_zero(T, r)) : {Con{y, acc} == SC.append(T, Con{y, _}, acc) : List<&2, T>}
      {==}
    case Con{+y, +r} 1n+k:
      LL.cons_cong(T, y, SC.append(T, SC.take(T, r, k), DA.cons_some(T, SC.nth(T, r, k), acc)), SC.append(T, SC.take(T, r, 1n+k), acc), take_cons_some(T, r, k, acc, hm))

def slot_nth(-T: Data, +xs: List<&2, Maybe<&2, T>>, +n: Nat, +m: Nat, +h: {LY.lay(T, xs, n) == True{} : Bool}, +hm: {Nat.is_lt(m, n) == True{} : Bool}) -> {slot(T, xs, m) == SC.nth(T, LY.somes(T, xs), m) : Maybe<&2, T>}:
  %Equal.sym(Maybe<&2, Maybe<&2, T>>, SC.nth(Maybe<&2, T>, xs, m), Some{SC.nth(T, LY.somes(T, xs), m)}, LY.lay_nth(T, xs, n, m, h, hm)) : {unwrap(T, _) == SC.nth(T, LY.somes(T, xs), m) : Maybe<&2, T>}
  {==}

def tvals_take(k: Nat, -T: Data, +xs: List<&2, Maybe<&2, T>>, +n: Nat, +acc: List<&2, T>, +h: {LY.lay(T, xs, n) == True{} : Bool}, +hk: {Nat.is_le(k, n) == True{} : Bool}) -> {tvals(k, T, xs, acc) == SC.append(T, SC.take(T, LY.somes(T, xs), k), acc) : List<&2, T>}:
  match k:
    case 0n:
      %Equal.sym(List<&2, T>, SC.take(T, LY.somes(T, xs), 0n), Nil{}, LL.sc_take_zero(T, LY.somes(T, xs))) : {acc == SC.append(T, _, acc) : List<&2, T>}
      {==}
    case 1n+ +m:
      +ys = LY.somes(T, xs)
      +hm = N.succ_le_lt(m, n, hk)
      +hlen = N.lt_le_trans(m, n, SC.length(T, ys), hm, N.eq_le(n, SC.length(T, ys), Equal.sym(Nat, SC.length(T, ys), n, LY.lay_len(T, xs, n, h))))
      %Equal.sym(Maybe<&2, T>, slot(T, xs, m), SC.nth(T, ys, m), slot_nth(T, xs, n, m, h, hm)) : {tvals(m, T, xs, DA.cons_some(T, _, acc)) == SC.append(T, SC.take(T, ys, 1n+m), acc) : List<&2, T>}
      %take_cons_some(T, ys, m, acc, hlen) : {tvals(m, T, xs, DA.cons_some(T, SC.nth(T, ys, m), acc)) == _ : List<&2, T>}
      tvals_take(m, T, xs, n, DA.cons_some(T, SC.nth(T, ys, m), acc), h, N.lt_le(m, n, hm))

def tvals_model(-T: Data, +xs: List<&2, Maybe<&2, T>>, +n: Nat, +h: {LY.lay(T, xs, n) == True{} : Bool}) -> {tvals(n, T, xs, Nil{}) == LY.somes(T, xs) : List<&2, T>}:
  %take_all(T, LY.somes(T, xs), n, LY.lay_len(T, xs, n, h)) : {tvals(n, T, xs, Nil{}) == _ : List<&2, T>}
  %LL.append_nil(T, SC.take(T, LY.somes(T, xs), n)) : {tvals(n, T, xs, Nil{}) == _ : List<&2, T>}
  tvals_take(n, T, xs, n, Nil{}, h, N.le_refl(n))
