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

# The model's items against the value arena.

def gv(-T: Data, b: Bool, m: Maybe<&2, T>) -> Maybe<&2, T>:
  match b:
    case True{}:
      m
    case False{}:
      None{}

# Every id of the order is below 2^depth.
def allp(xs: List<&2, Nat>, +n: Nat) -> Bool:
  ST.alllt(xs, n)

def lt_head(+x: Nat, +t: List<&2, Nat>, +n: Nat, +h: {ST.alllt(Con{x, t}, n) == True{} : Bool}) -> {Nat.is_lt(x, n) == True{} : Bool}:
  L.and_left(Nat.is_lt(x, n), ST.alllt(t, n), h)

def lt_tail(+x: Nat, +t: List<&2, Nat>, +n: Nat, +h: {ST.alllt(Con{x, t}, n) == True{} : Bool}) -> {ST.alllt(t, n) == True{} : Bool}:
  L.and_right(Nat.is_lt(x, n), ST.alllt(t, n), h)

# The spec compares ids as U32: exact below 2^depth.
def ueq(+p: Nat, +i: U32, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hp: {Nat.is_lt(p, SC.pow2(depth)) == True{} : Bool}) -> {U32.is_eq(U32.from_nat(p), i) == Nat.is_eq(p, U32.to_nat(i)) : Bool}:
  Equal.trans(Bool, U32.is_eq(U32.from_nat(p), i), Nat.is_eq(U32.to_nat(U32.from_nat(p)), U32.to_nat(i)), Nat.is_eq(p, U32.to_nat(i)),
    F.u32_eq_nat(U32.from_nat(p), i),
    Equal.cong(Nat, Bool, z => Nat.is_eq(z, U32.to_nat(i)), U32.to_nat(U32.from_nat(p)), p, F.id_nat(p, depth, hd, hp)))

def eq_nat_true(+a: Nat, +b: Nat, +h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  N.eq_from_is_eq(a, b, h)

def gv_none(-T: Data, b: Bool) -> {gv(T, b, None{}) == None{} : Maybe<&2, T>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def getv_none_c(~T: Data, +p: Nat, +t: List<&2, Nat>, +xs: List<&2, Maybe<&2, T>>, +i: U32, +hv: {ST.vat(T, xs, p) == None{} : Maybe<&2, T>}, c: Bool, +ec: {Nat.is_eq(p, U32.to_nat(i)) == c : Bool}, +ih: {DS.getv(T, ST.items(T, xs, t), i) == gv(T, ST.lmem(U32.to_nat(i), t), ST.vat(T, xs, U32.to_nat(i))) : Maybe<&2, T>}) -> {DS.getv(T, ST.items(T, xs, t), i) == gv(T, Bool.or(Nat.is_eq(p, U32.to_nat(i)), ST.lmem(U32.to_nat(i), t)), ST.vat(T, xs, U32.to_nat(i))) : Maybe<&2, T>}:
  match c:
    case False{}:
      L.subst(Bool, b => {DS.getv(T, ST.items(T, xs, t), i) == gv(T, Bool.or(b, ST.lmem(U32.to_nat(i), t)), ST.vat(T, xs, U32.to_nat(i))) : Maybe<&2, T>}, False{}, Nat.is_eq(p, U32.to_nat(i)), Equal.sym(Bool, Nat.is_eq(p, U32.to_nat(i)), False{}, ec), ih)
    case True{}:
      +en = eq_nat_true(p, U32.to_nat(i), ec)
      +hv2 = L.subst(Nat, z => {ST.vat(T, xs, z) == None{} : Maybe<&2, T>}, p, U32.to_nat(i), en, hv)
      +l1 = Equal.trans(Maybe<&2, T>, DS.getv(T, ST.items(T, xs, t), i), gv(T, ST.lmem(U32.to_nat(i), t), None{}), None{},
        L.subst(Maybe<&2, T>, m => {DS.getv(T, ST.items(T, xs, t), i) == gv(T, ST.lmem(U32.to_nat(i), t), m) : Maybe<&2, T>}, ST.vat(T, xs, U32.to_nat(i)), None{}, hv2, ih),
        gv_none(T, ST.lmem(U32.to_nat(i), t)))
      Equal.trans(Maybe<&2, T>, DS.getv(T, ST.items(T, xs, t), i), None{}, gv(T, Bool.or(Nat.is_eq(p, U32.to_nat(i)), ST.lmem(U32.to_nat(i), t)), ST.vat(T, xs, U32.to_nat(i))),
        l1,
        Equal.sym(Maybe<&2, T>, gv(T, Bool.or(Nat.is_eq(p, U32.to_nat(i)), ST.lmem(U32.to_nat(i), t)), ST.vat(T, xs, U32.to_nat(i))), None{},
          L.subst(Maybe<&2, T>, m => {gv(T, Bool.or(Nat.is_eq(p, U32.to_nat(i)), ST.lmem(U32.to_nat(i), t)), m) == None{} : Maybe<&2, T>}, None{}, ST.vat(T, xs, U32.to_nat(i)), Equal.sym(Maybe<&2, T>, ST.vat(T, xs, U32.to_nat(i)), None{}, hv2), gv_none(T, Bool.or(Nat.is_eq(p, U32.to_nat(i)), ST.lmem(U32.to_nat(i), t))))))

def getv_some_c(~T: Data, +p: Nat, +v: T, +t: List<&2, Nat>, +xs: List<&2, Maybe<&2, T>>, +i: U32, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hp: {Nat.is_lt(p, SC.pow2(depth)) == True{} : Bool}, +hv: {ST.vat(T, xs, p) == Some{v} : Maybe<&2, T>}, c: Bool, +ec: {Nat.is_eq(p, U32.to_nat(i)) == c : Bool}, +ih: {DS.getv(T, ST.items(T, xs, t), i) == gv(T, ST.lmem(U32.to_nat(i), t), ST.vat(T, xs, U32.to_nat(i))) : Maybe<&2, T>}) -> {DS.getv(T, Con{E.Item{U32.from_nat(p), v}, ST.items(T, xs, t)}, i) == gv(T, Bool.or(Nat.is_eq(p, U32.to_nat(i)), ST.lmem(U32.to_nat(i), t)), ST.vat(T, xs, U32.to_nat(i))) : Maybe<&2, T>}:
  match c:
    case False{}:
      +eu = Equal.trans(Bool, U32.is_eq(U32.from_nat(p), i), Nat.is_eq(p, U32.to_nat(i)), False{}, ueq(p, i, depth, hd, hp), ec)
      L.subst(Bool, b => {DS.getv_at(T, b, v, DS.getv(T, ST.items(T, xs, t), i)) == gv(T, Bool.or(Nat.is_eq(p, U32.to_nat(i)), ST.lmem(U32.to_nat(i), t)), ST.vat(T, xs, U32.to_nat(i))) : Maybe<&2, T>}, False{}, U32.is_eq(U32.from_nat(p), i), Equal.sym(Bool, U32.is_eq(U32.from_nat(p), i), False{}, eu),
        L.subst(Bool, b => {DS.getv(T, ST.items(T, xs, t), i) == gv(T, Bool.or(b, ST.lmem(U32.to_nat(i), t)), ST.vat(T, xs, U32.to_nat(i))) : Maybe<&2, T>}, False{}, Nat.is_eq(p, U32.to_nat(i)), Equal.sym(Bool, Nat.is_eq(p, U32.to_nat(i)), False{}, ec), ih))
    case True{}:
      +eu = Equal.trans(Bool, U32.is_eq(U32.from_nat(p), i), Nat.is_eq(p, U32.to_nat(i)), True{}, ueq(p, i, depth, hd, hp), ec)
      +en = eq_nat_true(p, U32.to_nat(i), ec)
      +hv2 = L.subst(Nat, z => {ST.vat(T, xs, z) == Some{v} : Maybe<&2, T>}, p, U32.to_nat(i), en, hv)
      L.subst(Bool, b => {DS.getv_at(T, b, v, DS.getv(T, ST.items(T, xs, t), i)) == gv(T, Bool.or(Nat.is_eq(p, U32.to_nat(i)), ST.lmem(U32.to_nat(i), t)), ST.vat(T, xs, U32.to_nat(i))) : Maybe<&2, T>}, True{}, U32.is_eq(U32.from_nat(p), i), Equal.sym(Bool, U32.is_eq(U32.from_nat(p), i), True{}, eu),
        L.subst(Bool, b => {Some{v} == gv(T, Bool.or(b, ST.lmem(U32.to_nat(i), t)), ST.vat(T, xs, U32.to_nat(i))) : Maybe<&2, T>}, True{}, Nat.is_eq(p, U32.to_nat(i)), Equal.sym(Bool, Nat.is_eq(p, U32.to_nat(i)), True{}, ec),
          Equal.sym(Maybe<&2, T>, ST.vat(T, xs, U32.to_nat(i)), Some{v}, hv2)))

def getv_items_c(~T: Data, +p: Nat, +t: List<&2, Nat>, +xs: List<&2, Maybe<&2, T>>, +i: U32, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hp: {Nat.is_lt(p, SC.pow2(depth)) == True{} : Bool}, m: Maybe<&2, T>, +em: {ST.vat(T, xs, p) == m : Maybe<&2, T>}, +ih: {DS.getv(T, ST.items(T, xs, t), i) == gv(T, ST.lmem(U32.to_nat(i), t), ST.vat(T, xs, U32.to_nat(i))) : Maybe<&2, T>}) -> {DS.getv(T, ST.itm(T, m, p, ST.items(T, xs, t)), i) == gv(T, Bool.or(Nat.is_eq(p, U32.to_nat(i)), ST.lmem(U32.to_nat(i), t)), ST.vat(T, xs, U32.to_nat(i))) : Maybe<&2, T>}:
  match m:
    case None{}:
      getv_none_c(~T, p, t, xs, i, em, Nat.is_eq(p, U32.to_nat(i)), {==}, ih)
    case Some{v}:
      getv_some_c(~T, p, v, t, xs, i, depth, hd, hp, em, Nat.is_eq(p, U32.to_nat(i)), {==}, ih)

# Looking an id up in the model reads the value arena, if the id is in the order.
def getv_items(~T: Data, +xs: List<&2, Maybe<&2, T>>, +ord: List<&2, Nat>, +i: U32, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {ST.alllt(ord, SC.pow2(depth)) == True{} : Bool}) -> {DS.getv(T, ST.items(T, xs, ord), i) == gv(T, ST.lmem(U32.to_nat(i), ord), ST.vat(T, xs, U32.to_nat(i))) : Maybe<&2, T>}:
  match ord:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      getv_items_c(~T, p, t, xs, i, depth, hd, lt_head(p, t, SC.pow2(depth), hl), ST.vat(T, xs, p), {==}, getv_items(~T, xs, t, i, depth, hd, lt_tail(p, t, SC.pow2(depth), hl)))

def eq_some(-A: Data, +a: A, +b: A, +h: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  Equal.cong(Maybe<&2, A>, A, m => L.some_value(A, m, a), Some{a}, Some{b}, h)
