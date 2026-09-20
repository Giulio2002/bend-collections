import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../../spec/common.bend as SC
import ../../spec/binary_heap.bend as S
import ./multiset.bend as M
import ./idx.bend as IX
import ./slots.bend as SL

# The multiset of an array heap: the values of the slots [0, n), sorted by
# insertion. Sorting is what the specification calls a priority queue, and
# `M.ins_comm` says the order the values are inserted in does not matter --
# which is exactly why every swap a sift performs is invisible here.

def cons_slot(~A: Data, m: Maybe<&2, A>, acc: List<&2, A>) -> List<&2, A>:
  match m:
    case None{}:
      acc
    case Some{v}:
      Con{v, acc}

def vals(~A: Data, +ss: List<&2, Maybe<&2, A>>, n: Nat) -> List<&2, A>:
  match n:
    case 0n:
      Nil{}
    case 1n+ +m:
      cons_slot(~A, SL.slot(~A, ss, m), vals(~A, ss, m))

def msort(~A: Data, ~cmp: A -> A -> Cmp, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      S.ins(~A, ~cmp, h, msort(~A, ~cmp, t))

# ---- the slots below an update are untouched ----

def vals_above(~A: Data, +ss: List<&2, Maybe<&2, A>>, +i: Nat, +v: Maybe<&2, A>, m: Nat, +h: {Nat.is_le(m, i) == True{} : Bool}) -> {vals(~A, SC.update(Maybe<&2, A>, ss, i, v), m) == vals(~A, ss, m) : List<&2, A>}:
  match m:
    case 0n:
      {==}
    case 1n+ +k:
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, SC.update(Maybe<&2, A>, ss, i, v), k), SL.slot(~A, ss, k), SL.slot_other(~A, ss, i, k, v, SL.ne_sym(i, k, N.is_eq_lt(k, i, N.succ_le_lt(k, i, h))))) : {cons_slot(~A, _, vals(~A, SC.update(Maybe<&2, A>, ss, i, v), k)) == vals(~A, ss, 1n+k) : List<&2, A>}
      Equal.cong(List<&2, A>, List<&2, A>, ys => cons_slot(~A, SL.slot(~A, ss, k), ys), vals(~A, SC.update(Maybe<&2, A>, ss, i, v), k), vals(~A, ss, k), vals_above(~A, ss, i, v, k, N.lt_le(k, i, N.succ_le_lt(k, i, h))))

# ---- sorting a list with one slot replaced ----

def none_not_some(~A: Data, +old: A, +h: {None{} == Some{old} : Maybe<&2, A>}) -> Empty:
  L.true_not_false(Maybe.is_some(&2, A, None{}), Equal.cong(Maybe<&2, A>, Bool, z => Maybe.is_some(&2, A, z), None{}, Some{old}, h), {==})

def nth_of_slot_go(~A: Data, +old: A, m: Maybe<&2, Maybe<&2, A>>, +hold: {SL.unwrap(~A, m) == Some{old} : Maybe<&2, A>}) -> {m == Some{Some{old}} : Maybe<&2, Maybe<&2, A>>}:
  match m:
    case None{}:
      Empty.absurd({None{} == Some{Some{old}} : Maybe<&2, Maybe<&2, A>>}, none_not_some(~A, old, hold))
    case Some{s}:
      Equal.cong(Maybe<&2, A>, Maybe<&2, Maybe<&2, A>>, z => Some{z}, s, Some{old}, hold)

def nth_of_slot(~A: Data, +ss: List<&2, Maybe<&2, A>>, +i: Nat, +old: A, +hold: {SL.slot(~A, ss, i) == Some{old} : Maybe<&2, A>}) -> {SC.nth(Maybe<&2, A>, ss, i) == Some{Some{old}} : Maybe<&2, Maybe<&2, A>>}:
  nth_of_slot_go(~A, old, SC.nth(Maybe<&2, A>, ss, i), hold)

def slot_in_range(~A: Data, +ss: List<&2, Maybe<&2, A>>, +i: Nat, +old: A, +hold: {SL.slot(~A, ss, i) == Some{old} : Maybe<&2, A>}) -> {Nat.is_lt(i, SC.length(Maybe<&2, A>, ss)) == True{} : Bool}:
  LL.nth_lt_length(Maybe<&2, A>, ss, i, Some{old}, nth_of_slot(~A, ss, i, old, hold))

def ins_set_same(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ss: List<&2, Maybe<&2, A>>, +i: Nat, +old: A, +v: A, +hold: {SL.slot(~A, ss, i) == Some{old} : Maybe<&2, A>}) -> {S.ins(~A, ~cmp, old, msort(~A, ~cmp, vals(~A, SC.update(Maybe<&2, A>, ss, i, Some{v}), 1n+i))) == S.ins(~A, ~cmp, v, msort(~A, ~cmp, vals(~A, ss, 1n+i))) : List<&2, A>}:
  +up = SC.update(Maybe<&2, A>, ss, i, Some{v})
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, SC.update(Maybe<&2, A>, ss, i, Some{v}), i), Some{v}, SL.slot_same(~A, ss, i, Some{v}, slot_in_range(~A, ss, i, old, hold))) : {S.ins(~A, ~cmp, old, msort(~A, ~cmp, cons_slot(~A, _, vals(~A, up, i)))) == S.ins(~A, ~cmp, v, msort(~A, ~cmp, vals(~A, ss, 1n+i))) : List<&2, A>}
  %Equal.sym(List<&2, A>, vals(~A, SC.update(Maybe<&2, A>, ss, i, Some{v}), i), vals(~A, ss, i), vals_above(~A, ss, i, Some{v}, i, N.le_refl(i))) : {S.ins(~A, ~cmp, old, msort(~A, ~cmp, cons_slot(~A, Some{v}, _))) == S.ins(~A, ~cmp, v, msort(~A, ~cmp, vals(~A, ss, 1n+i))) : List<&2, A>}
  %Equal.sym(Maybe<&2, A>, SL.slot(~A, ss, i), Some{old}, hold) : {S.ins(~A, ~cmp, old, S.ins(~A, ~cmp, v, msort(~A, ~cmp, vals(~A, ss, i)))) == S.ins(~A, ~cmp, v, msort(~A, ~cmp, cons_slot(~A, _, vals(~A, ss, i)))) : List<&2, A>}
  M.ins_comm(~A, ~cmp, ~o, old, v, msort(~A, ~cmp, vals(~A, ss, i)))

def ins_set_top(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ss: List<&2, Maybe<&2, A>>, +m: Nat, +i: Nat, +old: A, +v: A, +ei: {i == m : Nat}, +hold: {SL.slot(~A, ss, i) == Some{old} : Maybe<&2, A>}) -> {S.ins(~A, ~cmp, old, msort(~A, ~cmp, vals(~A, SC.update(Maybe<&2, A>, ss, i, Some{v}), 1n+m))) == S.ins(~A, ~cmp, v, msort(~A, ~cmp, vals(~A, ss, 1n+m))) : List<&2, A>}:
  %ei : {S.ins(~A, ~cmp, old, msort(~A, ~cmp, vals(~A, SC.update(Maybe<&2, A>, ss, i, Some{v}), 1n+_))) == S.ins(~A, ~cmp, v, msort(~A, ~cmp, vals(~A, ss, 1n+_))) : List<&2, A>}
  ins_set_same(~A, ~cmp, ~o, ss, i, old, v, hold)

def ins_set_cons(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), s: Maybe<&2, A>, +old: A, +v: A, +xs: List<&2, A>, +ys: List<&2, A>, +ih: {S.ins(~A, ~cmp, old, msort(~A, ~cmp, xs)) == S.ins(~A, ~cmp, v, msort(~A, ~cmp, ys)) : List<&2, A>}) -> {S.ins(~A, ~cmp, old, msort(~A, ~cmp, cons_slot(~A, s, xs))) == S.ins(~A, ~cmp, v, msort(~A, ~cmp, cons_slot(~A, s, ys))) : List<&2, A>}:
  match s:
    case None{}:
      ih
    case Some{+w}:
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, old, S.ins(~A, ~cmp, w, msort(~A, ~cmp, xs))), S.ins(~A, ~cmp, w, S.ins(~A, ~cmp, old, msort(~A, ~cmp, xs))), M.ins_comm(~A, ~cmp, ~o, old, w, msort(~A, ~cmp, xs))) : {_ == S.ins(~A, ~cmp, v, S.ins(~A, ~cmp, w, msort(~A, ~cmp, ys))) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, v, S.ins(~A, ~cmp, w, msort(~A, ~cmp, ys))), S.ins(~A, ~cmp, w, S.ins(~A, ~cmp, v, msort(~A, ~cmp, ys))), M.ins_comm(~A, ~cmp, ~o, v, w, msort(~A, ~cmp, ys))) : {S.ins(~A, ~cmp, w, S.ins(~A, ~cmp, old, msort(~A, ~cmp, xs))) == _ : List<&2, A>}
      Equal.cong(List<&2, A>, List<&2, A>, zs => S.ins(~A, ~cmp, w, zs), S.ins(~A, ~cmp, old, msort(~A, ~cmp, xs)), S.ins(~A, ~cmp, v, msort(~A, ~cmp, ys)), ih)

def ins_set(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ss: List<&2, Maybe<&2, A>>, n: Nat, +i: Nat, +old: A, +v: A, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hold: {SL.slot(~A, ss, i) == Some{old} : Maybe<&2, A>}, b: Bool, +eb: {Nat.is_eq(i, N.pred(n)) == b : Bool}) -> {S.ins(~A, ~cmp, old, msort(~A, ~cmp, vals(~A, SC.update(Maybe<&2, A>, ss, i, Some{v}), n))) == S.ins(~A, ~cmp, v, msort(~A, ~cmp, vals(~A, ss, n))) : List<&2, A>}:
  match n b:
    case 0n _:
      Empty.absurd({S.ins(~A, ~cmp, old, msort(~A, ~cmp, vals(~A, SC.update(Maybe<&2, A>, ss, i, Some{v}), 0n))) == S.ins(~A, ~cmp, v, msort(~A, ~cmp, vals(~A, ss, 0n))) : List<&2, A>}, N.lt_zero_absurd(i, hi))
    case 1n+m True{}:
      ins_set_top(~A, ~cmp, ~o, ss, m, i, old, v, N.eq_from_is_eq(i, m, eb), hold)
    case 1n+ +m False{}:
      +up = SC.update(Maybe<&2, A>, ss, i, Some{v})
      +hi2 = N.lt_or_eq(i, m, N.lt_succ_le(i, m, hi), eb)
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, up, m), SL.slot(~A, ss, m), SL.slot_other(~A, ss, i, m, Some{v}, N.is_eq_lt(i, m, hi2))) : {S.ins(~A, ~cmp, old, msort(~A, ~cmp, cons_slot(~A, _, vals(~A, up, m)))) == S.ins(~A, ~cmp, v, msort(~A, ~cmp, vals(~A, ss, 1n+m))) : List<&2, A>}
      ins_set_cons(~A, ~cmp, ~o, SL.slot(~A, ss, m), old, v, vals(~A, up, m), vals(~A, ss, m), ins_set(~A, ~cmp, ~o, ss, m, i, old, v, hi2, hold, Nat.is_eq(i, N.pred(m)), {==}))
