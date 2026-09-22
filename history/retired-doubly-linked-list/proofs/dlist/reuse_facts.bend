import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../../spec/common.bend as SC
import ../graph/shift.bend as SH
import ./state.bend as ST
import ./alive.bend as AL
import ./links.bend as LK
import ./split.bend as SP
import ./insfacts.bend as IF

# An insertion at ANY unused slot, including an issued-and-retired slot.
# Unlike fresh insertion, the upper bound does not increase.
def bounds_insert(+x: List<&2, Nat>, +y: List<&2, Nat>, +i: Nat, +limit: Nat, +hi: {Nat.is_lt(i, limit) == True{} : Bool}, +h: {ST.alllt(SC.append(Nat, x, y), limit) == True{} : Bool}) -> {ST.alllt(SC.append(Nat, x, Con{i, y}), limit) == True{} : Bool}:
  match x:
    case Nil{}:
      L.and_intro(Nat.is_lt(i, limit), ST.alllt(y, limit), hi, h)
    case Con{+a, +rest}:
      L.and_intro(Nat.is_lt(a, limit), ST.alllt(SC.append(Nat, rest, Con{i, y}), limit), L.and_left(Nat.is_lt(a, limit), ST.alllt(SC.append(Nat, rest, y), limit), h), bounds_insert(rest, y, i, limit, hi, L.and_right(Nat.is_lt(a, limit), ST.alllt(SC.append(Nat, rest, y), limit), h)))

def inserted_member(+x: List<&2, Nat>, +y: List<&2, Nat>, +i: Nat) -> {ST.lmem(i, SC.append(Nat, x, Con{i, y})) == True{} : Bool}:
  match x:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(i, i), True{}, N.is_eq_refl(i)) : {Bool.or(_, ST.lmem(i, y)) == True{} : Bool}
      {==}
    case Con{+a, +rest}:
      AL.or_true_r(Nat.is_eq(a, i), ST.lmem(i, SC.append(Nat, rest, Con{i, y})), inserted_member(rest, y, i))

def value_at_insert(-T: Data, +xs: List<&2, Maybe<&2, T>>, +x: List<&2, Nat>, +y: List<&2, Nat>, +i: Nat, +v: T, +q: Nat, +hi: {Nat.is_lt(i, SC.length(Maybe<&2, T>, xs)) == True{} : Bool}, +hold: {ST.beq(ST.is_some(T, ST.vat(T, xs, q)), ST.lmem(q, SC.append(Nat, x, y))) == True{} : Bool}, same: Bool, +hsame: {Nat.is_eq(i, q) == same : Bool}) -> {ST.beq(ST.is_some(T, ST.vat(T, SC.update(Maybe<&2, T>, xs, i, Some{v}), q)), ST.lmem(q, SC.append(Nat, x, Con{i, y}))) == True{} : Bool}:
  match same:
    case False{}:
      IF.lvi_pos(T, xs, x, y, i, Some{v}, q, hsame, hold)
    case True{}:
      +eq = N.eq_from_is_eq(i, q, hsame)
      %eq : {ST.beq(ST.is_some(T, ST.vat(T, SC.update(Maybe<&2, T>, xs, i, Some{v}), _)), ST.lmem(_, SC.append(Nat, x, Con{i, y}))) == True{} : Bool}
      %Equal.sym(Maybe<&2, T>, ST.vat(T, SC.update(Maybe<&2, T>, xs, i, Some{v}), i), Some{v}, LK.vat_same(T, xs, i, Some{v}, hi)) : {ST.beq(ST.is_some(T, _), ST.lmem(i, SC.append(Nat, x, Con{i, y}))) == True{} : Bool}
      %Equal.sym(Bool, ST.lmem(i, SC.append(Nat, x, Con{i, y})), True{}, inserted_member(x, y, i)) : {ST.beq(True{}, _) == True{} : Bool}
      {==}

def values_insert(-T: Data, k: Nat, +xs: List<&2, Maybe<&2, T>>, +p: Nat, +x: List<&2, Nat>, +y: List<&2, Nat>, +i: Nat, +v: T, +hi: {Nat.is_lt(i, SC.length(Maybe<&2, T>, xs)) == True{} : Bool}, +h: {ST.lv(T, k, xs, p, SC.append(Nat, x, y)) == True{} : Bool}) -> {ST.lv(T, k, SC.update(Maybe<&2, T>, xs, i, Some{v}), p, SC.append(Nat, x, Con{i, y})) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +rest:
      +head = L.and_left(ST.beq(ST.is_some(T, ST.vat(T, xs, p)), ST.lmem(p, SC.append(Nat, x, y))), ST.lv(T, rest, xs, 1n+p, SC.append(Nat, x, y)), h)
      +tail = L.and_right(ST.beq(ST.is_some(T, ST.vat(T, xs, p)), ST.lmem(p, SC.append(Nat, x, y))), ST.lv(T, rest, xs, 1n+p, SC.append(Nat, x, y)), h)
      L.and_intro(ST.beq(ST.is_some(T, ST.vat(T, SC.update(Maybe<&2, T>, xs, i, Some{v}), p)), ST.lmem(p, SC.append(Nat, x, Con{i, y}))), ST.lv(T, rest, SC.update(Maybe<&2, T>, xs, i, Some{v}), 1n+p, SC.append(Nat, x, Con{i, y})), value_at_insert(T, xs, x, y, i, v, p, hi, head, Nat.is_eq(i, p), {==}), values_insert(T, rest, xs, 1n+p, x, y, i, v, hi, tail))
