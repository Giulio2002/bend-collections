import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../graph/shift.bend as SH
import ../../spec/common.bend as SC
import ../../spec/doubly_linked_list.bend as DS
import ../../src/doubly_linked_list.bend as D
import ../../types/doubly_linked_list.bend as E
import ./state.bend as ST
import ./facts.bend as F
import ./links.bend as LK
import ./items.bend as IT
import ./core.bend as K

# Every id of the order holds a value, so the items follow the order exactly.

def alive(-T: Data, +xs: List<&2, Maybe<&2, T>>, ys: List<&2, Nat>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, t}:
      Bool.and(ST.is_some(T, ST.vat(T, xs, y)), alive(T, xs, t))

def sub_in(ys: List<&2, Nat>, +full: List<&2, Nat>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, t}:
      Bool.and(ST.lmem(y, full), sub_in(t, full))

def or_true_r(a: Bool, +b: Bool, +h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def lmem_cons(+i: Nat, +y: Nat, +full: List<&2, Nat>, +h: {ST.lmem(i, full) == True{} : Bool}) -> {ST.lmem(i, Con{y, full}) == True{} : Bool}:
  or_true_r(Nat.is_eq(y, i), ST.lmem(i, full), h)

def sub_in_cons(+ys: List<&2, Nat>, +y: Nat, +full: List<&2, Nat>, +h: {sub_in(ys, full) == True{} : Bool}) -> {sub_in(ys, Con{y, full}) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+z, +t}:
      L.and_intro(ST.lmem(z, Con{y, full}), sub_in(t, Con{y, full}), lmem_cons(z, y, full, L.and_left(ST.lmem(z, full), sub_in(t, full), h)), sub_in_cons(t, y, full, L.and_right(ST.lmem(z, full), sub_in(t, full), h)))

def lmem_self(+y: Nat) -> {Nat.is_eq(y, y) == True{} : Bool}:
  N.is_eq_refl(y)

def sub_in_self(+ys: List<&2, Nat>) -> {sub_in(ys, ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      L.and_intro(ST.lmem(y, Con{y, t}), sub_in(t, Con{y, t}),
        L.subst(Bool, b => {Bool.or(b, ST.lmem(y, t)) == True{} : Bool}, True{}, Nat.is_eq(y, y), Equal.sym(Bool, Nat.is_eq(y, y), True{}, lmem_self(y)), {==}),
        sub_in_cons(t, y, t, sub_in_self(t)))

def beq_true(-T: Data, m: Maybe<&2, T>, +h: {ST.beq(ST.is_some(T, m), True{}) == True{} : Bool}) -> {ST.is_some(T, m) == True{} : Bool}:
  match m:
    case None{}:
      h
    case Some{v}:
      {==}

def alive_of(-T: Data, +xs: List<&2, Maybe<&2, T>>, +fresh: Nat, +full: List<&2, Nat>, +ys: List<&2, Nat>, +hlv: {ST.lv(T, fresh, xs, 0n, full) == True{} : Bool}, +hs: {sub_in(ys, full) == True{} : Bool}, +hl: {ST.alllt(ys, fresh) == True{} : Bool}) -> {alive(T, xs, ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +hm = L.and_left(ST.lmem(y, full), sub_in(t, full), hs)
      +hb = L.subst(Nat, z => {ST.beq(ST.is_some(T, ST.vat(T, xs, z)), ST.lmem(z, full)) == True{} : Bool}, Nat.add(y, 0n), y, N.add_zero(y), K.lv_get(T, fresh, xs, 0n, full, hlv, y, IT.lt_head(y, t, fresh, hl)))
      +hb2 = L.subst(Bool, b => {ST.beq(ST.is_some(T, ST.vat(T, xs, y)), b) == True{} : Bool}, ST.lmem(y, full), True{}, hm, hb)
      L.and_intro(ST.is_some(T, ST.vat(T, xs, y)), alive(T, xs, t), beq_true(T, ST.vat(T, xs, y), hb2),
        alive_of(T, xs, fresh, full, t, hlv, L.and_right(ST.lmem(y, full), sub_in(t, full), hs), IT.lt_tail(y, t, fresh, hl)))

def g_alive(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> {alive(T, AR.slots(Maybe<&2, T>, tv), ord) == True{} : Bool}:
  alive_of(T, AR.slots(Maybe<&2, T>, tv), fresh, ord, ord, F.g_lv(~T, tag, fresh, depth, tv, tp, tn, ord, h), sub_in_self(ord), F.g_lt(~T, tag, fresh, depth, tv, tp, tn, ord, h))

# ---- the items of a live order ----

def val_of(-T: Data, m: Maybe<&2, T>, +h: {ST.is_some(T, m) == True{} : Bool}) -> T:
  match m:
    case None{}:
      Empty.absurd(T, L.false_true(h))
    case Some{v}:
      v

def some_val(-T: Data, m: Maybe<&2, T>, +h: {ST.is_some(T, m) == True{} : Bool}) -> {m == Some{val_of(T, m, h)} : Maybe<&2, T>}:
  match m:
    case None{}:
      Empty.absurd({None{} == Some{val_of(T, None{}, h)} : Maybe<&2, T>}, L.false_true(h))
    case Some{v}:
      {==}

def itm_some(-T: Data, m: Maybe<&2, T>, +p: Nat, +rest: List<&2, E.Item<T>>, +h: {ST.is_some(T, m) == True{} : Bool}) -> {ST.itm(T, m, p, rest) == Con{E.Item{U32.from_nat(p), val_of(T, m, h)}, rest} : List<&2, E.Item<T>>}:
  match m:
    case None{}:
      Empty.absurd({ST.itm(T, None{}, p, rest) == Con{E.Item{U32.from_nat(p), val_of(T, None{}, h)}, rest} : List<&2, E.Item<T>>}, L.false_true(h))
    case Some{v}:
      {==}

def items_len(-T: Data, +xs: List<&2, Maybe<&2, T>>, +ys: List<&2, Nat>, +h: {alive(T, xs, ys) == True{} : Bool}) -> {SC.length(E.Item<T>, ST.items(T, xs, ys)) == SC.length(Nat, ys) : Nat}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +hy = L.and_left(ST.is_some(T, ST.vat(T, xs, y)), alive(T, xs, t), h)
      Equal.trans(Nat, SC.length(E.Item<T>, ST.itm(T, ST.vat(T, xs, y), y, ST.items(T, xs, t))), SC.length(E.Item<T>, Con{E.Item{U32.from_nat(y), val_of(T, ST.vat(T, xs, y), hy)}, ST.items(T, xs, t)}), 1n+SC.length(Nat, t),
        Equal.cong(List<&2, E.Item<T>>, Nat, z => SC.length(E.Item<T>, z), ST.itm(T, ST.vat(T, xs, y), y, ST.items(T, xs, t)), Con{E.Item{U32.from_nat(y), val_of(T, ST.vat(T, xs, y), hy)}, ST.items(T, xs, t)}, itm_some(T, ST.vat(T, xs, y), y, ST.items(T, xs, t), hy)),
        Equal.cong(Nat, Nat, z => 1n+z, SC.length(E.Item<T>, ST.items(T, xs, t)), SC.length(Nat, t), items_len(T, xs, t, L.and_right(ST.is_some(T, ST.vat(T, xs, y)), alive(T, xs, t), h))))

def alive_app(-T: Data, +xs: List<&2, Maybe<&2, T>>, +a: List<&2, Nat>, +b: List<&2, Nat>, +h: {alive(T, xs, SC.append(Nat, a, b)) == True{} : Bool}) -> {alive(T, xs, a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      L.and_intro(ST.is_some(T, ST.vat(T, xs, y)), alive(T, xs, t), L.and_left(ST.is_some(T, ST.vat(T, xs, y)), alive(T, xs, SC.append(Nat, t, b)), h), alive_app(T, xs, t, b, L.and_right(ST.is_some(T, ST.vat(T, xs, y)), alive(T, xs, SC.append(Nat, t, b)), h)))

def alive_app_r(-T: Data, +xs: List<&2, Maybe<&2, T>>, +a: List<&2, Nat>, +b: List<&2, Nat>, +h: {alive(T, xs, SC.append(Nat, a, b)) == True{} : Bool}) -> {alive(T, xs, b) == True{} : Bool}:
  match a:
    case Nil{}:
      h
    case Con{+y, +t}:
      alive_app_r(T, xs, t, b, L.and_right(ST.is_some(T, ST.vat(T, xs, y)), alive(T, xs, SC.append(Nat, t, b)), h))

def items_app_c(-T: Data, +xs: List<&2, Maybe<&2, T>>, +y: Nat, +t: List<&2, Nat>, +b: List<&2, Nat>, m: Maybe<&2, T>, +ih: {ST.items(T, xs, SC.append(Nat, t, b)) == SC.append(E.Item<T>, ST.items(T, xs, t), ST.items(T, xs, b)) : List<&2, E.Item<T>>}) -> {ST.itm(T, m, y, ST.items(T, xs, SC.append(Nat, t, b))) == SC.append(E.Item<T>, ST.itm(T, m, y, ST.items(T, xs, t)), ST.items(T, xs, b)) : List<&2, E.Item<T>>}:
  match m:
    case None{}:
      ih
    case Some{v}:
      LL.cons_cong(E.Item<T>, E.Item{U32.from_nat(y), v}, ST.items(T, xs, SC.append(Nat, t, b)), SC.append(E.Item<T>, ST.items(T, xs, t), ST.items(T, xs, b)), ih)

def items_app(-T: Data, +xs: List<&2, Maybe<&2, T>>, +a: List<&2, Nat>, +b: List<&2, Nat>) -> {ST.items(T, xs, SC.append(Nat, a, b)) == SC.append(E.Item<T>, ST.items(T, xs, a), ST.items(T, xs, b)) : List<&2, E.Item<T>>}:
  match a:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      items_app_c(T, xs, y, t, b, ST.vat(T, xs, y), items_app(T, xs, t, b))

