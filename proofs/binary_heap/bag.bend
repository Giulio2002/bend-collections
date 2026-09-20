import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../../spec/common.bend as SC
import ../../spec/binary_heap.bend as S
import ./multiset.bend as M
import ./slots.bend as SL
import ./vals.bend as V

# Cancellation for sorted insertion, and what it gives: swapping the values of
# two slots does not change the sorted multiset. That is the whole reason a
# sift may move values along a path -- every step is a swap.

# The first element that compares EQ to z is removed. `b` is "does the head
# compare EQ to z": a loop that branches on a computed value has to carry the
# decision in its arguments (Bend matches only on parameters).
def eq_head(~A: Data, ~cmp: A -> A -> Cmp, +z: A, xs: List<&2, A>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Cmp.is_eq(cmp(z, h))

def del(~A: Data, ~cmp: A -> A -> Cmp, +z: A, xs: List<&2, A>, b: Bool) -> List<&2, A>:
  match xs b:
    case Nil{} _:
      Nil{}
    case Con{h, t} True{}:
      t
    case Con{h, +t} False{}:
      Con{h, del(~A, ~cmp, z, t, eq_head(~A, ~cmp, z, t))}

def delf(~A: Data, ~cmp: A -> A -> Cmp, +z: A, +xs: List<&2, A>) -> List<&2, A>:
  del(~A, ~cmp, z, xs, eq_head(~A, ~cmp, z, xs))

# z is removed from a list it was just inserted into.
def del_head(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +z: A, +xs: List<&2, A>) -> {delf(~A, ~cmp, z, Con{z, xs}) == xs : List<&2, A>}:
  %Equal.sym(Cmp, cmp(z, z), EQ{}, O.refl(~A, ~cmp, ~o, z)) : {del(~A, ~cmp, z, Con{z, xs}, Cmp.is_eq(_)) == xs : List<&2, A>}
  {==}

def not_le_not_eq(~A: Data, ~cmp: A -> A -> Cmp, +z: A, +h: A, +e: {S.le(~A, ~cmp, z, h) == False{} : Bool}) -> {Cmp.is_eq(cmp(z, h)) == False{} : Bool}:
  not_le_not_eq_c(cmp(z, h), e)

def not_le_not_eq_c(c: Cmp, +e: {Cmp.is_le(c) == False{} : Bool}) -> {Cmp.is_eq(c) == False{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Cmp.is_eq(LT{}) == False{} : Bool}, L.true_false(e))
    case EQ{}:
      Empty.absurd({Cmp.is_eq(EQ{}) == False{} : Bool}, L.true_false(e))
    case GT{}:
      {==}

def del_ins_cons(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +z: A, +h: A, +t: List<&2, A>, b: Bool, +eb: {S.le(~A, ~cmp, z, h) == b : Bool}, +ih: {delf(~A, ~cmp, z, S.ins(~A, ~cmp, z, t)) == t : List<&2, A>}) -> {delf(~A, ~cmp, z, S.ins(~A, ~cmp, z, Con{h, t})) == Con{h, t} : List<&2, A>}:
  match b:
    case True{}:
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, z, Con{h, t}), Con{z, Con{h, t}}, M.ins_cons(~A, ~cmp, z, h, t, True{}, eb)) : {delf(~A, ~cmp, z, _) == Con{h, t} : List<&2, A>}
      del_head(~A, ~cmp, ~o, z, Con{h, t})
    case False{}:
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, z, Con{h, t}), Con{h, S.ins(~A, ~cmp, z, t)}, M.ins_cons(~A, ~cmp, z, h, t, False{}, eb)) : {delf(~A, ~cmp, z, _) == Con{h, t} : List<&2, A>}
      %Equal.sym(Bool, Cmp.is_eq(cmp(z, h)), False{}, not_le_not_eq(~A, ~cmp, z, h, eb)) : {del(~A, ~cmp, z, Con{h, S.ins(~A, ~cmp, z, t)}, _) == Con{h, t} : List<&2, A>}
      LL.cons_cong(A, h, delf(~A, ~cmp, z, S.ins(~A, ~cmp, z, t)), t, ih)

def del_ins(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +z: A, xs: List<&2, A>) -> {delf(~A, ~cmp, z, S.ins(~A, ~cmp, z, xs)) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      del_head(~A, ~cmp, ~o, z, Nil{})
    case Con{+h, +t}:
      del_ins_cons(~A, ~cmp, ~o, z, h, t, S.le(~A, ~cmp, z, h), {==}, del_ins(~A, ~cmp, ~o, z, t))

# Insertion is injective in the list: the sorted multiset is determined.
def ins_inj(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +z: A, +xs: List<&2, A>, +ys: List<&2, A>, +e: {S.ins(~A, ~cmp, z, xs) == S.ins(~A, ~cmp, z, ys) : List<&2, A>}) -> {xs == ys : List<&2, A>}:
  Equal.trans(List<&2, A>, xs, delf(~A, ~cmp, z, S.ins(~A, ~cmp, z, xs)), ys,
    Equal.sym(List<&2, A>, delf(~A, ~cmp, z, S.ins(~A, ~cmp, z, xs)), xs, del_ins(~A, ~cmp, ~o, z, xs)),
    Equal.trans(List<&2, A>, delf(~A, ~cmp, z, S.ins(~A, ~cmp, z, xs)), delf(~A, ~cmp, z, S.ins(~A, ~cmp, z, ys)), ys,
      Equal.cong(List<&2, A>, List<&2, A>, l => delf(~A, ~cmp, z, l), S.ins(~A, ~cmp, z, xs), S.ins(~A, ~cmp, z, ys), e),
      del_ins(~A, ~cmp, ~o, z, ys)))

# ---- swapping two slots ----

def upd_upd_same(~A: Data, +ss: List<&2, Maybe<&2, A>>, +i: Nat, +u: Maybe<&2, A>, +v: Maybe<&2, A>) -> {SC.update(Maybe<&2, A>, SC.update(Maybe<&2, A>, ss, i, u), i, v) == SC.update(Maybe<&2, A>, ss, i, v) : List<&2, Maybe<&2, A>>}:
  match ss i:
    case Nil{} _:
      {==}
    case Con{x, r} 0n:
      {==}
    case Con{+x, +r} 1n+k:
      LL.cons_cong(Maybe<&2, A>, x, SC.update(Maybe<&2, A>, SC.update(Maybe<&2, A>, r, k, u), k, v), SC.update(Maybe<&2, A>, r, k, v), upd_upd_same(~A, r, k, u, v))

def slot_l1(~A: Data, +ss: List<&2, Maybe<&2, A>>, +i: Nat, +p: Nat, +b: A, +hne: {Nat.is_eq(i, p) == False{} : Bool}, +hb: {SL.slot(~A, ss, p) == Some{b} : Maybe<&2, A>}) -> {SL.slot(~A, SC.update(Maybe<&2, A>, ss, i, Some{b}), p) == Some{b} : Maybe<&2, A>}:
  Equal.trans(Maybe<&2, A>, SL.slot(~A, SC.update(Maybe<&2, A>, ss, i, Some{b}), p), SL.slot(~A, ss, p), Some{b}, SL.slot_other(~A, ss, i, p, Some{b}, hne), hb)

# ---- a value below every slot is below every element of the multiset ----

def all_ge_cons(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +z: A, +m: Maybe<&2, A>, +xs: List<&2, A>, +hm: {SL.mle(~A, ~cmp, Some{z}, m) == True{} : Bool}, +hxs: {M.all_ge(~A, ~cmp, z, V.msort(~A, ~cmp, xs)) == True{} : Bool}) -> {M.all_ge(~A, ~cmp, z, V.msort(~A, ~cmp, V.cons_slot(~A, m, xs))) == True{} : Bool}:
  match m:
    case None{}:
      hxs
    case Some{+w}:
      %M.all_ge_ins(~A, ~cmp, ~o, z, w, V.msort(~A, ~cmp, xs)) : {_ == True{} : Bool}
      L.and_intro(S.le(~A, ~cmp, z, w), M.all_ge(~A, ~cmp, z, V.msort(~A, ~cmp, xs)), hm, hxs)

def low_all(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +z: A, k: Nat) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+ +m:
      Bool.and(SL.mle(~A, ~cmp, Some{z}, SL.slot(~A, ss, m)), low_all(~A, ~cmp, ss, z, m))

def all_ge_vals(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ss: List<&2, Maybe<&2, A>>, +z: A, k: Nat, +h: {low_all(~A, ~cmp, ss, z, k) == True{} : Bool}) -> {M.all_ge(~A, ~cmp, z, V.msort(~A, ~cmp, V.vals(~A, ss, k))) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +m:
      all_ge_cons(~A, ~cmp, ~o, z, SL.slot(~A, ss, m), V.vals(~A, ss, m),
        L.and_left(SL.mle(~A, ~cmp, Some{z}, SL.slot(~A, ss, m)), low_all(~A, ~cmp, ss, z, m), h),
        all_ge_vals(~A, ~cmp, ~o, ss, z, m, L.and_right(SL.mle(~A, ~cmp, Some{z}, SL.slot(~A, ss, m)), low_all(~A, ~cmp, ss, z, m), h)))

# Exchanging the values of two occupied slots leaves the sorted multiset
# unchanged: two applications of `ins_set` and one cancellation.
def vals_swap(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ss: List<&2, Maybe<&2, A>>, +n: Nat, +i: Nat, +p: Nat, +a: A, +b: A, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hp: {Nat.is_lt(p, n) == True{} : Bool}, +hne: {Nat.is_eq(i, p) == False{} : Bool}, +ha: {SL.slot(~A, ss, i) == Some{a} : Maybe<&2, A>}, +hb: {SL.slot(~A, ss, p) == Some{b} : Maybe<&2, A>}) -> {V.msort(~A, ~cmp, V.vals(~A, SC.update(Maybe<&2, A>, SC.update(Maybe<&2, A>, ss, i, Some{b}), p, Some{a}), n)) == V.msort(~A, ~cmp, V.vals(~A, ss, n)) : List<&2, A>}:
  +l1 = SC.update(Maybe<&2, A>, ss, i, Some{b})
  +e1 = V.ins_set(~A, ~cmp, ~o, ss, n, i, a, b, hi, ha, Nat.is_eq(i, N.pred(n)), {==})
  +e2 = V.ins_set(~A, ~cmp, ~o, l1, n, p, b, a, hp, slot_l1(~A, ss, i, p, b, hne, hb), Nat.is_eq(p, N.pred(n)), {==})
  ins_inj(~A, ~cmp, ~o, b, V.msort(~A, ~cmp, V.vals(~A, SC.update(Maybe<&2, A>, l1, p, Some{a}), n)), V.msort(~A, ~cmp, V.vals(~A, ss, n)),
    Equal.trans(List<&2, A>, S.ins(~A, ~cmp, b, V.msort(~A, ~cmp, V.vals(~A, SC.update(Maybe<&2, A>, l1, p, Some{a}), n))), S.ins(~A, ~cmp, a, V.msort(~A, ~cmp, V.vals(~A, l1, n))), S.ins(~A, ~cmp, b, V.msort(~A, ~cmp, V.vals(~A, ss, n))), e2, e1))
