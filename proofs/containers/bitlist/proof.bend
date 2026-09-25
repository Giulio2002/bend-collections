import Base
import ../../../spec/lib/common.bend as SC
import ../../../src/containers/bitlist.bend as BLI
import ../../../src/containers/types/bitlist.bend as E
import ../../../spec/containers/bitlist.bend as S
import ./state.bend as SS
import ./steps.bend as BS
import ./trace.bend as TR
import ../../lib/list.bend as LL
import ../bitset/lists.bend as BL
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../../spec/lib/sequence.bend as V
import ../../lib/sequence.bend as VL

# ==== the contract of bitlist (stated in spec/containers/bitlist.bend) ====================

# ---- assign: the written bit reads back, every other bit is unchanged ----
def assign_in(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}, +y: Maybe<&2, Bool>, +hy: {SC.nth(Bool, xs, i) == y : Maybe<&2, Bool>}) -> {S.assign_at(y, l, c, xs, i, v) == (S.M{l, c, SC.update(Bool, xs, i, v)}, E.OUnit{Done{Unit{}}}) : S.Model & E.Obs}:
  match y:
    case None{}:
      Empty.absurd({S.assign_at(None{}, l, c, xs, i, v) == (S.M{l, c, SC.update(Bool, xs, i, v)}, E.OUnit{Done{Unit{}}}) : S.Model & E.Obs}, LL.sc_nth_some(Bool, xs, i, h, hy))
    case Some{b}:
      {==}

def assign_step(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> {S.step(S.M{l, c, xs}, E.Assign{i, v}) == (S.M{l, c, SC.update(Bool, xs, i, v)}, E.OUnit{Done{Unit{}}}) : S.Model & E.Obs}:
  assign_in(l, c, xs, i, v, h, SC.nth(Bool, xs, i), {==})

def get_assign_same(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> S.Replace_Element.get_assign_same(l, c, xs, i, v, h):
  %Equal.sym(S.Model & E.Obs, S.step(S.M{l, c, xs}, E.Assign{i, v}), (S.M{l, c, SC.update(Bool, xs, i, v)}, E.OUnit{Done{Unit{}}}), assign_step(l, c, xs, i, v, h)) : {Pair.snd(S.Model, E.Obs, S.step(Pair.fst(S.Model, E.Obs, _), E.Get{i})) == E.OBit{Done{v}} : E.Obs}
  %Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, SC.update(Bool, xs, i, v), i), Some{v}, LL.nth_update_same(Bool, xs, i, v, h)) : {E.OBit{S.bit(_)} == E.OBit{Done{v}} : E.Obs}
  {==}

def get_assign_other(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +j: Nat, +v: Bool, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}, +ne: {Nat.is_eq(i, j) == False{} : Bool}) -> S.Replace_Element.get_assign_other(l, c, xs, i, j, v, h, ne):
  %Equal.sym(S.Model & E.Obs, S.step(S.M{l, c, xs}, E.Assign{i, v}), (S.M{l, c, SC.update(Bool, xs, i, v)}, E.OUnit{Done{Unit{}}}), assign_step(l, c, xs, i, v, h)) : {Pair.snd(S.Model, E.Obs, S.step(Pair.fst(S.Model, E.Obs, _), E.Get{j})) == E.OBit{S.bit(SC.nth(Bool, xs, j))} : E.Obs}
  %Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, SC.update(Bool, xs, i, v), j), SC.nth(Bool, xs, j), LL.nth_update_other(Bool, xs, i, j, v, ne)) : {E.OBit{S.bit(_)} == E.OBit{S.bit(SC.nth(Bool, xs, j))} : E.Obs}
  {==}

def length_assign(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> S.Replace_Element.length_assign(l, c, xs, i, v, h):
  %Equal.sym(S.Model & E.Obs, S.step(S.M{l, c, xs}, E.Assign{i, v}), (S.M{l, c, SC.update(Bool, xs, i, v)}, E.OUnit{Done{Unit{}}}), assign_step(l, c, xs, i, v, h)) : {SC.length(Bool, S.bits(Pair.fst(S.Model, E.Obs, _))) == SC.length(Bool, xs) : Nat}
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

def length_push(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {S.room(l, c, SC.length(Bool, xs)) == True{} : Bool}) -> S.Append.length_push(l, c, xs, v, h):
  %Equal.sym(S.Model & E.Obs, S.step(S.M{l, c, xs}, E.Push{v}), (S.M{l, c, SC.snoc(Bool, xs, v)}, E.OUnit{Done{Unit{}}}), push_step(l, c, xs, v, h)) : {SC.length(Bool, S.bits(Pair.fst(S.Model, E.Obs, _))) == 1n+SC.length(Bool, xs) : Nat}
  LL.length_snoc(Bool, xs, v)

def get_push_last(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {S.room(l, c, SC.length(Bool, xs)) == True{} : Bool}) -> S.Append.get_push_last(l, c, xs, v, h):
  %Equal.sym(S.Model & E.Obs, S.step(S.M{l, c, xs}, E.Push{v}), (S.M{l, c, SC.snoc(Bool, xs, v)}, E.OUnit{Done{Unit{}}}), push_step(l, c, xs, v, h)) : {Pair.snd(S.Model, E.Obs, S.step(Pair.fst(S.Model, E.Obs, _), E.Get{SC.length(Bool, xs)})) == E.OBit{Done{v}} : E.Obs}
  %Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, SC.snoc(Bool, xs, v), SC.length(Bool, xs)), Some{v}, nth_snoc_end(xs, v)) : {E.OBit{S.bit(_)} == E.OBit{Done{v}} : E.Obs}
  {==}

def pop_push(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {S.room(l, c, SC.length(Bool, xs)) == True{} : Bool}) -> S.Delete_Last.pop_push(l, c, xs, v, h):
  %Equal.sym(S.Model & E.Obs, S.step(S.M{l, c, xs}, E.Push{v}), (S.M{l, c, SC.snoc(Bool, xs, v)}, E.OUnit{Done{Unit{}}}), push_step(l, c, xs, v, h)) : {S.step(Pair.fst(S.Model, E.Obs, _), E.Pop{}) == (S.M{l, c, xs}, E.OBit{Done{v}}) : S.Model & E.Obs}
  pop_snoc(l, c, xs, v)

def count_push(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {S.room(l, c, SC.length(Bool, xs)) == True{} : Bool}) -> S.Append.count_push(l, c, xs, v, h):
  %Equal.sym(S.Model & E.Obs, S.step(S.M{l, c, xs}, E.Push{v}), (S.M{l, c, SC.snoc(Bool, xs, v)}, E.OUnit{Done{Unit{}}}), push_step(l, c, xs, v, h)) : {S.count(S.bits(Pair.fst(S.Model, E.Obs, _))) == Nat.add(S.count(xs), S.count(Con{v, Nil{}})) : Nat}
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


# Packed bit list (SSZ Bitlist[N]): public proof entry point.
#   specification  S.*   (a list of Booleans, an optional maximum length and
#                  the storage capacity exponent;
#                  spec/containers/bitlist.bend)
#   abstraction    SS.model(BSh{limit, len, w}) = the first len stored bits
#   invariant      SS.good: the word array is a good dynamic array, it holds
#                  at least len bits, and every stored bit from len on is
#                  zero (the masked tail)
#   word array     used only through the proved dynamic-array contract
#                  (proofs/containers/dynamic_array), see da.bend
#   operations     BS.step_ok: every operation (errors included) refines
#                  S.step and keeps the invariant
#   traces         trace_new / trace_with_limit: arbitrary finite op lists
#   from_bools     builds the unbounded list whose bits are its input
#   contracts      *: assign reads back and frames the other bits; push
#                  grows the length by one, reads back at the end, and pop
#                  undoes it; count adds the pushed bit
#
# Specification shape after: ConsenSys eth2.0-dafny SSZ Bitlist
# (src/dafny/ssz/BitListSeDes.dfy), Lean 4 List Bool / BitVec lemmas
# (Init.Data.BitVec.Lemmas, List.getElem_set), SPARK Ada Formal_Vectors
# postconditions.

def new_real() -> {BLI.new() == SS.real(TR.initial(None{})) : BLI.Bitlist}:
  TR.new_real()

def new_model() -> {SS.model(TR.initial(None{})) == S.new() : S.Model}:
  TR.new_model()

def with_limit_real(+n: Nat) -> {BLI.with_limit(n) == SS.real(TR.initial(Some{n})) : BLI.Bitlist}:
  TR.with_limit_real(n)

def with_limit_model(+n: Nat) -> {SS.model(TR.initial(Some{n})) == S.with_limit(n) : S.Model}:
  TR.with_limit_model(n)

def initial_good(+l: Maybe<&2, Nat>) -> {SS.good(TR.initial(l)) == True{} : Bool}:
  TR.initial_good(l)

def step_ok(+sh: SS.Sh, +op: E.Op, +g: {SS.good(sh) == True{} : Bool}) -> BS.StepOK(sh, op):
  BS.step_ok(sh, op, g)

def trace_new(+ops: List<&2, E.Op>) -> TR.TraceOK(ops, TR.initial(None{})):
  TR.trace_from(ops, TR.initial(None{}), TR.initial_good(None{}))

def trace_with_limit(+n: Nat, +ops: List<&2, E.Op>) -> TR.TraceOK(ops, TR.initial(Some{n})):
  TR.trace_from(ops, TR.initial(Some{n}), TR.initial_good(Some{n}))

def from_bools(+bs: List<&2, Bool>) -> TR.FromOK(bs, TR.initial(None{})):
  TR.from_bools_ok(bs)

# with room for every bit, the spec's from_bools is exactly the input
def from_bools_spells(+bs: List<&2, Bool>, +c: Nat, +hc: {c == 31n : Nat}, +h: {Nat.is_le(SC.length(Bool, bs), Nat.mul(SC.pow2(c), 32n)) == True{} : Bool}) -> {S.push_all(bs, S.M{None{}, c, Nil{}}) == S.M{None{}, c, bs} : S.Model}:
  push_all_spells(bs, c, Nil{}, h)

# ==== the contract of bitlist (stated in spec/containers/bitlist.bend) ====================

# ---- the implementation ----
def Impl(sh: SS.Sh, op: E.Op, Post: (S.Model & E.Obs) -> Type) -> Type:
  Sigma<&1, &1, SS.Sh, sh2 => Sigma<&1, &1, E.Obs, o => {BLI.step(SS.real(sh), op) == (SS.real(sh2), o) : BLI.Bitlist & E.Obs} & ({SS.good(sh2) == True{} : Bool} & Post((SS.model(sh2), o)))>>

def impl_of(-sh: SS.Sh, -op: E.Op, -Post: (S.Model & E.Obs) -> Type, k: BS.StepOK(sh, op), pf: Post(S.step(SS.model(sh), op))) -> Impl(sh, op, Post):
  match k:
    case Tuple{sh2, Tuple{o, Tuple{e1, Tuple{g2, e2}}}}:
      (sh2, (o, (e1, (g2, L.subst(S.Model & E.Obs, Post, S.step(SS.model(sh), op), (SS.model(sh2), o), Equal.sym(S.Model & E.Obs, (SS.model(sh2), o), S.step(SS.model(sh), op), e2), pf)))))

def impl(+sh: SS.Sh, +op: E.Op, +g: {SS.good(sh) == True{} : Bool}, -Post: (S.Model & E.Obs) -> Type, pf: Post(S.step(SS.model(sh), op))) -> Impl(sh, op, Post):
  impl_of(sh, op, Post, step_ok(sh, op, g), pf)

# ---- Length, Capacity (the S.limit), Count, iteration: the value, and nothing changes ----
def length_result(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>) -> S.Length.length_result(l, c, xs):
  {==}

def length_frame(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>) -> S.Length.length_frame(l, c, xs):
  {==}

def limit_result(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>) -> S.Capacity.limit_result(l, c, xs):
  {==}

def limit_frame(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>) -> S.Capacity.limit_frame(l, c, xs):
  {==}

def count_result(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>) -> S.Implementation.count_result(l, c, xs):
  {==}

def to_list_model(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>) -> S.Iteration.to_list_model(l, c, xs):
  {==}

def to_list_frame(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>) -> S.Iteration.to_list_frame(l, c, xs):
  {==}

# ---- Empty_Vector, To_Vector ----
def new_empty() -> S.Empty_Vector.new_empty():
  {==}

def with_limit_empty(+n: Nat) -> S.Empty_Vector.with_limit_empty(n):
  {==}

def new_impl() -> {BLI.new() == SS.real(TR.initial(None{})) : BLI.Bitlist}:
  new_real()

def from_bools_model(+bs: List<&2, Bool>, +c: Nat, +hc: {c == 31n : Nat}, +h: {Nat.is_le(SC.length(Bool, bs), Nat.mul(SC.pow2(c), 32n)) == True{} : Bool}) -> S.To_Vector.from_bools_model(bs, c, hc, h):
  from_bools_spells(bs, c, hc, h)

# ---- Clear: Length 0 (the S.limit is kept) ----
def clear_length(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>) -> S.Clear.clear_length(l, c, xs):
  {==}

def clear_limit(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>) -> S.Clear.clear_limit(l, c, xs):
  {==}

# ---- Element ----
def get_element(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {SC.nth(Bool, xs, i) == Some{v} : Maybe<&2, Bool>}) -> S.Element.get_element(l, c, xs, i, v, h):
  %Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, xs, i), Some{v}, h) : {E.OBit{S.bit(_)} == E.OBit{Done{v}} : E.Obs}
  {==}

def get_frame(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat) -> S.Element.get_frame(l, c, xs, i):
  {==}

def get_outside(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_le(SC.length(Bool, xs), i) == True{} : Bool}) -> S.Element.get_outside(l, c, xs, i, h):
  %Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, xs, i), None{}, LL.nth_none(Bool, xs, i, h)) : {E.OBit{S.bit(_)} == E.OBit{Fail{E.IndexOutOfRange{}}} : E.Obs}
  {==}

# ---- Replace_Element: Length kept, Element (Index) = New_Item, Equal_Except elsewhere ----
def assign_bits(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> {S.bits(S.nx(S.M{l, c, xs}, E.Assign{i, v})) == SC.update(Bool, xs, i, v) : List<&2, Bool>}:
  %Equal.sym(S.Model & E.Obs, S.step(S.M{l, c, xs}, E.Assign{i, v}), (S.M{l, c, SC.update(Bool, xs, i, v)}, E.OUnit{Done{Unit{}}}), assign_step(l, c, xs, i, v, h)) : {S.bits(Pair.fst(S.Model, E.Obs, _)) == SC.update(Bool, xs, i, v) : List<&2, Bool>}
  {==}

def assign_length(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> S.Replace_Element.assign_length(l, c, xs, i, v, h):
  length_assign(l, c, xs, i, v, h)

def assign_element(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> S.Replace_Element.assign_element(l, c, xs, i, v, h):
  %Equal.sym(List<&2, Bool>, S.bits(S.nx(S.M{l, c, xs}, E.Assign{i, v})), SC.update(Bool, xs, i, v), assign_bits(l, c, xs, i, v, h)) : {SC.nth(Bool, _, i) == Some{v} : Maybe<&2, Bool>}
  VL.update_at(Bool, xs, i, v, h)

def assign_except(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> S.Replace_Element.assign_except(l, c, xs, i, v, h):
  L.subst(List<&2, Bool>, z => V.EqualExcept(Bool, xs, z, i), SC.update(Bool, xs, i, v), S.bits(S.nx(S.M{l, c, xs}, E.Assign{i, v})), Equal.sym(List<&2, Bool>, S.bits(S.nx(S.M{l, c, xs}, E.Assign{i, v})), SC.update(Bool, xs, i, v), assign_bits(l, c, xs, i, v, h)), VL.update_except(Bool, xs, i, v))

def assign_outside(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_le(SC.length(Bool, xs), i) == True{} : Bool}) -> S.Replace_Element.assign_outside(l, c, xs, i, v, h):
  %Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, xs, i), None{}, LL.nth_none(Bool, xs, i, h)) : {S.assign_at(_, l, c, xs, i, v) == (S.M{l, c, xs}, E.OUnit{Fail{E.IndexOutOfRange{}}}) : S.Model & E.Obs}
  {==}

# ---- Append: Length + 1, Equal_Prefix (Model'Old, Model), Element (Last'Old + 1) = New_Item ----
def push_bits(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {S.room(l, c, SC.length(Bool, xs)) == True{} : Bool}) -> {S.bits(S.nx(S.M{l, c, xs}, E.Push{v})) == SC.snoc(Bool, xs, v) : List<&2, Bool>}:
  %Equal.sym(S.Model & E.Obs, S.step(S.M{l, c, xs}, E.Push{v}), (S.M{l, c, SC.snoc(Bool, xs, v)}, E.OUnit{Done{Unit{}}}), push_step(l, c, xs, v, h)) : {S.bits(Pair.fst(S.Model, E.Obs, _)) == SC.snoc(Bool, xs, v) : List<&2, Bool>}
  {==}

def push_length(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {S.room(l, c, SC.length(Bool, xs)) == True{} : Bool}) -> S.Append.push_length(l, c, xs, v, h):
  length_push(l, c, xs, v, h)

def push_prefix(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {S.room(l, c, SC.length(Bool, xs)) == True{} : Bool}) -> S.Append.push_prefix(l, c, xs, v, h):
  L.subst(List<&2, Bool>, z => V.EqualPrefix(Bool, xs, z), SC.snoc(Bool, xs, v), S.bits(S.nx(S.M{l, c, xs}, E.Push{v})), Equal.sym(List<&2, Bool>, S.bits(S.nx(S.M{l, c, xs}, E.Push{v})), SC.snoc(Bool, xs, v), push_bits(l, c, xs, v, h)), VL.snoc_prefix(Bool, xs, v))

def push_element(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {S.room(l, c, SC.length(Bool, xs)) == True{} : Bool}) -> S.Append.push_element(l, c, xs, v, h):
  %Equal.sym(List<&2, Bool>, S.bits(S.nx(S.M{l, c, xs}, E.Push{v})), SC.snoc(Bool, xs, v), push_bits(l, c, xs, v, h)) : {SC.nth(Bool, _, SC.length(Bool, xs)) == Some{v} : Maybe<&2, Bool>}
  VL.snoc_last(Bool, xs, v)

def push_full(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {S.room(l, c, SC.length(Bool, xs)) == False{} : Bool}) -> S.Append.push_full(l, c, xs, v, h):
  %Equal.sym(Bool, S.room(l, c, SC.length(Bool, xs)), False{}, h) : {S.push_if(_, l, c, xs, v) == (S.M{l, c, xs}, E.OUnit{Fail{E.Full{}}}) : S.Model & E.Obs}
  {==}

# ---- Delete_Last: Length - 1, Equal_Prefix (Model, Model'Old); pop returns Last_Element'Old ----
def pop_length(+l: Maybe<&2, Nat>, +c: Nat, +h: Bool, +t: List<&2, Bool>) -> S.Delete_Last.pop_length(l, c, h, t):
  VL.init_length(Bool, t, h)

def pop_prefix(+l: Maybe<&2, Nat>, +c: Nat, +h: Bool, +t: List<&2, Bool>) -> S.Delete_Last.pop_prefix(l, c, h, t):
  VL.init_prefix(Bool, t, h)

def pop_result(+l: Maybe<&2, Nat>, +c: Nat, +h: Bool, +t: List<&2, Bool>) -> S.Delete_Last.pop_result(l, c, h, t):
  %Equal.sym(Maybe<&2, Bool>, SC.last(Bool, Con{h, t}), V.last_elem(Bool, Con{h, t}), VL.last_is_elem(Bool, t, h)) : {E.OBit{S.last_bit(_)} == E.OBit{S.last_bit(V.last_elem(Bool, Con{h, t}))} : E.Obs}
  {==}

def pop_empty(+l: Maybe<&2, Nat>, +c: Nat) -> S.Delete_Last.pop_empty(l, c):
  {==}
