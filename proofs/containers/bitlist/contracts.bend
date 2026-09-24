import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../lib/spec_common.bend as SC
import ../../../src/containers/types/bitlist.bend as E
import ../bitset/spec.bend as BSP
import ../bitset/lists.bend as BL
import ./spec.bend as S

# Contracts of the specification, in the style of the SPARK formal vector
# postconditions (Replace_Element: Element(Container, I) = New_Item and every
# other element unchanged; Append: Length + 1 and Last_Element = New_Item)
# and of the Lean 4 List lemmas (List.getElem_set_self / getElem_set_ne,
# List.length_concat, List.dropLast_concat): each law is about the model
# S.step, and proofs/containers/bitlist/steps.bend makes the implementation
# step equal to S.step on every good bitlist, so each law holds for the
# implementation.
# (source: proofs/containers/bitlist/contracts.src)


def bits(m: S.Model) -> List<&2, Bool>:
  match m:
    case S.M{l, c, xs}:
      xs

# ---- assign: the written bit reads back, every other bit is unchanged ----

def assign_in(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}, +y: Maybe<&2, Bool>, +hy: {SC.nth(Bool, xs, i) == y : Maybe<&2, Bool>}) -> {S.assign_at(y, l, c, xs, i, v) == (S.M{l, c, SC.update(Bool, xs, i, v)}, E.OUnit{Done{Unit{}}}) : S.Model & E.Obs}:
  match y:
    case None{}:
      Empty.absurd({S.assign_at(None{}, l, c, xs, i, v) == (S.M{l, c, SC.update(Bool, xs, i, v)}, E.OUnit{Done{Unit{}}}) : S.Model & E.Obs}, LL.sc_nth_some(Bool, xs, i, h, hy))
    case Some{b}:
      {==}

def assign_step(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> {S.step(S.M{l, c, xs}, E.Assign{i, v}) == (S.M{l, c, SC.update(Bool, xs, i, v)}, E.OUnit{Done{Unit{}}}) : S.Model & E.Obs}:
  assign_in(l, c, xs, i, v, h, SC.nth(Bool, xs, i), {==})

def get_assign_same(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> {Pair.snd(S.Model, E.Obs, S.step(Pair.fst(S.Model, E.Obs, S.step(S.M{l, c, xs}, E.Assign{i, v})), E.Get{i})) == E.OBit{Done{v}} : E.Obs}:
  %Equal.sym(S.Model & E.Obs, S.step(S.M{l, c, xs}, E.Assign{i, v}), (S.M{l, c, SC.update(Bool, xs, i, v)}, E.OUnit{Done{Unit{}}}), assign_step(l, c, xs, i, v, h)) : {Pair.snd(S.Model, E.Obs, S.step(Pair.fst(S.Model, E.Obs, _), E.Get{i})) == E.OBit{Done{v}} : E.Obs}
  %Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, SC.update(Bool, xs, i, v), i), Some{v}, LL.nth_update_same(Bool, xs, i, v, h)) : {E.OBit{S.bit(_)} == E.OBit{Done{v}} : E.Obs}
  {==}

def get_assign_other(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +j: Nat, +v: Bool, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}, +ne: {Nat.is_eq(i, j) == False{} : Bool}) -> {Pair.snd(S.Model, E.Obs, S.step(Pair.fst(S.Model, E.Obs, S.step(S.M{l, c, xs}, E.Assign{i, v})), E.Get{j})) == Pair.snd(S.Model, E.Obs, S.step(S.M{l, c, xs}, E.Get{j})) : E.Obs}:
  %Equal.sym(S.Model & E.Obs, S.step(S.M{l, c, xs}, E.Assign{i, v}), (S.M{l, c, SC.update(Bool, xs, i, v)}, E.OUnit{Done{Unit{}}}), assign_step(l, c, xs, i, v, h)) : {Pair.snd(S.Model, E.Obs, S.step(Pair.fst(S.Model, E.Obs, _), E.Get{j})) == E.OBit{S.bit(SC.nth(Bool, xs, j))} : E.Obs}
  %Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, SC.update(Bool, xs, i, v), j), SC.nth(Bool, xs, j), LL.nth_update_other(Bool, xs, i, j, v, ne)) : {E.OBit{S.bit(_)} == E.OBit{S.bit(SC.nth(Bool, xs, j))} : E.Obs}
  {==}

def length_assign(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> {SC.length(Bool, bits(Pair.fst(S.Model, E.Obs, S.step(S.M{l, c, xs}, E.Assign{i, v})))) == SC.length(Bool, xs) : Nat}:
  %Equal.sym(S.Model & E.Obs, S.step(S.M{l, c, xs}, E.Assign{i, v}), (S.M{l, c, SC.update(Bool, xs, i, v)}, E.OUnit{Done{Unit{}}}), assign_step(l, c, xs, i, v, h)) : {SC.length(Bool, bits(Pair.fst(S.Model, E.Obs, _))) == SC.length(Bool, xs) : Nat}
  LL.length_update(Bool, xs, i, v)

def nth_snoc_end(+xs: List<&2, Bool>, +v: Bool) -> {SC.nth(Bool, SC.snoc(Bool, xs, v), SC.length(Bool, xs)) == Some{v} : Maybe<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      nth_snoc_end(t, v)

def pop_snoc(+l: Maybe<&2, Nat>, +c: Nat, +ys: List<&2, Bool>, +b: Bool) -> {S.pop(l, c, SC.snoc(Bool, ys, b)) == (S.M{l, c, ys}, E.OBit{Done{b}}) : S.Model & E.Obs}:
  match ys:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(List<&2, Bool>, SC.init(Bool, SC.snoc(Bool, Con{h, t}, b)), Con{h, t}, LL.init_snoc(Bool, Con{h, t}, b)) : {(S.M{l, c, _}, E.OBit{S.last_bit(SC.last(Bool, SC.snoc(Bool, Con{h, t}, b)))}) == (S.M{l, c, Con{h, t}}, E.OBit{Done{b}}) : S.Model & E.Obs}
      %Equal.sym(Maybe<&2, Bool>, SC.last(Bool, SC.snoc(Bool, Con{h, t}, b)), Some{b}, LL.last_snoc(Bool, Con{h, t}, b)) : {(S.M{l, c, Con{h, t}}, E.OBit{S.last_bit(_)}) == (S.M{l, c, Con{h, t}}, E.OBit{Done{b}}) : S.Model & E.Obs}
      {==}

# ---- push / pop: append one bit, pop returns it and restores the list ----

def push_step(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {S.room(l, c, SC.length(Bool, xs)) == True{} : Bool}) -> {S.step(S.M{l, c, xs}, E.Push{v}) == (S.M{l, c, SC.snoc(Bool, xs, v)}, E.OUnit{Done{Unit{}}}) : S.Model & E.Obs}:
  %Equal.sym(Bool, S.room(l, c, SC.length(Bool, xs)), True{}, h) : {S.push_if(_, l, c, xs, v) == (S.M{l, c, SC.snoc(Bool, xs, v)}, E.OUnit{Done{Unit{}}}) : S.Model & E.Obs}
  {==}

def length_push(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {S.room(l, c, SC.length(Bool, xs)) == True{} : Bool}) -> {SC.length(Bool, bits(Pair.fst(S.Model, E.Obs, S.step(S.M{l, c, xs}, E.Push{v})))) == 1n+SC.length(Bool, xs) : Nat}:
  %Equal.sym(S.Model & E.Obs, S.step(S.M{l, c, xs}, E.Push{v}), (S.M{l, c, SC.snoc(Bool, xs, v)}, E.OUnit{Done{Unit{}}}), push_step(l, c, xs, v, h)) : {SC.length(Bool, bits(Pair.fst(S.Model, E.Obs, _))) == 1n+SC.length(Bool, xs) : Nat}
  LL.length_snoc(Bool, xs, v)

def get_push_last(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {S.room(l, c, SC.length(Bool, xs)) == True{} : Bool}) -> {Pair.snd(S.Model, E.Obs, S.step(Pair.fst(S.Model, E.Obs, S.step(S.M{l, c, xs}, E.Push{v})), E.Get{SC.length(Bool, xs)})) == E.OBit{Done{v}} : E.Obs}:
  %Equal.sym(S.Model & E.Obs, S.step(S.M{l, c, xs}, E.Push{v}), (S.M{l, c, SC.snoc(Bool, xs, v)}, E.OUnit{Done{Unit{}}}), push_step(l, c, xs, v, h)) : {Pair.snd(S.Model, E.Obs, S.step(Pair.fst(S.Model, E.Obs, _), E.Get{SC.length(Bool, xs)})) == E.OBit{Done{v}} : E.Obs}
  %Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, SC.snoc(Bool, xs, v), SC.length(Bool, xs)), Some{v}, nth_snoc_end(xs, v)) : {E.OBit{S.bit(_)} == E.OBit{Done{v}} : E.Obs}
  {==}

def pop_push(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {S.room(l, c, SC.length(Bool, xs)) == True{} : Bool}) -> {S.step(Pair.fst(S.Model, E.Obs, S.step(S.M{l, c, xs}, E.Push{v})), E.Pop{}) == (S.M{l, c, xs}, E.OBit{Done{v}}) : S.Model & E.Obs}:
  %Equal.sym(S.Model & E.Obs, S.step(S.M{l, c, xs}, E.Push{v}), (S.M{l, c, SC.snoc(Bool, xs, v)}, E.OUnit{Done{Unit{}}}), push_step(l, c, xs, v, h)) : {S.step(Pair.fst(S.Model, E.Obs, _), E.Pop{}) == (S.M{l, c, xs}, E.OBit{Done{v}}) : S.Model & E.Obs}
  pop_snoc(l, c, xs, v)

def count_push(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {S.room(l, c, SC.length(Bool, xs)) == True{} : Bool}) -> {S.count(bits(Pair.fst(S.Model, E.Obs, S.step(S.M{l, c, xs}, E.Push{v})))) == Nat.add(S.count(xs), S.count(Con{v, Nil{}})) : Nat}:
  %Equal.sym(S.Model & E.Obs, S.step(S.M{l, c, xs}, E.Push{v}), (S.M{l, c, SC.snoc(Bool, xs, v)}, E.OUnit{Done{Unit{}}}), push_step(l, c, xs, v, h)) : {S.count(bits(Pair.fst(S.Model, E.Obs, _))) == Nat.add(S.count(xs), S.count(Con{v, Nil{}})) : Nat}
  %Equal.sym(List<&2, Bool>, SC.snoc(Bool, xs, v), SC.append(Bool, xs, Con{v, Nil{}}), LL.snoc_append(Bool, xs, v)) : {S.count(_) == Nat.add(S.count(xs), S.count(Con{v, Nil{}})) : Nat}
  BL.count_append(xs, Con{v, Nil{}})

# ---- from_bools spells its input ----

def room_of(+c: Nat, +xs: List<&2, Bool>, +b: Bool, +t: List<&2, Bool>, +h: {Nat.is_le(Nat.add(SC.length(Bool, xs), SC.length(Bool, Con{b, t})), Nat.mul(SC.pow2(c), 32n)) == True{} : Bool}) -> {S.room(None{}, c, SC.length(Bool, xs)) == True{} : Bool}:
  +h1 = L.subst(Nat, z => {Nat.is_le(z, Nat.mul(SC.pow2(c), 32n)) == True{} : Bool}, Nat.add(SC.length(Bool, xs), 1n+SC.length(Bool, t)), 1n+Nat.add(SC.length(Bool, xs), SC.length(Bool, t)), N.add_succ(SC.length(Bool, xs), SC.length(Bool, t)), h)
  N.lt_le_trans(SC.length(Bool, xs), 1n+Nat.add(SC.length(Bool, xs), SC.length(Bool, t)), Nat.mul(SC.pow2(c), 32n), N.le_lt_succ(SC.length(Bool, xs), Nat.add(SC.length(Bool, xs), SC.length(Bool, t)), N.le_add_right(SC.length(Bool, xs), SC.length(Bool, t))), h1)

def fits_tail(+c: Nat, +xs: List<&2, Bool>, +b: Bool, +t: List<&2, Bool>, +h: {Nat.is_le(Nat.add(SC.length(Bool, xs), SC.length(Bool, Con{b, t})), Nat.mul(SC.pow2(c), 32n)) == True{} : Bool}) -> {Nat.is_le(Nat.add(SC.length(Bool, SC.snoc(Bool, xs, b)), SC.length(Bool, t)), Nat.mul(SC.pow2(c), 32n)) == True{} : Bool}:
  %Equal.sym(Nat, SC.length(Bool, SC.snoc(Bool, xs, b)), 1n+SC.length(Bool, xs), LL.length_snoc(Bool, xs, b)) : {Nat.is_le(Nat.add(_, SC.length(Bool, t)), Nat.mul(SC.pow2(c), 32n)) == True{} : Bool}
  L.subst(Nat, z => {Nat.is_le(z, Nat.mul(SC.pow2(c), 32n)) == True{} : Bool}, Nat.add(SC.length(Bool, xs), 1n+SC.length(Bool, t)), 1n+Nat.add(SC.length(Bool, xs), SC.length(Bool, t)), N.add_succ(SC.length(Bool, xs), SC.length(Bool, t)), h)

def push_all_spells(+bs: List<&2, Bool>, +c: Nat, +xs: List<&2, Bool>, +h: {Nat.is_le(Nat.add(SC.length(Bool, xs), SC.length(Bool, bs)), Nat.mul(SC.pow2(c), 32n)) == True{} : Bool}) -> {S.push_all(bs, S.M{None{}, c, xs}) == S.M{None{}, c, SC.append(Bool, xs, bs)} : S.Model}:
  match bs:
    case Nil{}:
      Equal.sym(S.Model, S.M{None{}, c, SC.append(Bool, xs, Nil{})}, S.M{None{}, c, xs}, Equal.cong(List<&2, Bool>, S.Model, z => S.M{None{}, c, z}, SC.append(Bool, xs, Nil{}), xs, LL.append_nil(Bool, xs)))
    case Con{+b, +t}:
      %Equal.sym(S.Model & E.Obs, S.step(S.M{None{}, c, xs}, E.Push{b}), (S.M{None{}, c, SC.snoc(Bool, xs, b)}, E.OUnit{Done{Unit{}}}), push_step(None{}, c, xs, b, room_of(c, xs, b, t, h))) : {S.push_all(t, Pair.fst(S.Model, E.Obs, _)) == S.M{None{}, c, SC.append(Bool, xs, Con{b, t})} : S.Model}
      %Equal.sym(List<&2, Bool>, SC.append(Bool, xs, Con{b, t}), SC.append(Bool, SC.snoc(Bool, xs, b), t), Equal.sym(List<&2, Bool>, SC.append(Bool, SC.snoc(Bool, xs, b), t), SC.append(Bool, xs, Con{b, t}), LL.snoc_append_cons(Bool, xs, b, t))) : {S.push_all(t, S.M{None{}, c, SC.snoc(Bool, xs, b)}) == S.M{None{}, c, _} : S.Model}
      push_all_spells(t, c, SC.snoc(Bool, xs, b), fits_tail(c, xs, b, t, h))
