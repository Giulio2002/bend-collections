import Base
import ../../lib/spec_common.bend as SC
import ../../../src/containers/bitlist.bend as BLI
import ../../../src/containers/types/bitlist.bend as E
import ./spec.bend as S
import ./state.bend as SS
import ./steps.bend as BS
import ./trace.bend as TR
import ./contracts.bend as CT

# Packed bit list (SSZ Bitlist[N]): public proof entry point.
#   specification  S.*   (a list of Booleans, an optional maximum length and
#                  the storage capacity exponent; proofs/containers/bitlist/
#                  spec.bend)
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
#   contracts      CT.*: assign reads back and frames the other bits; push
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
  CT.push_all_spells(bs, c, Nil{}, h)

def get_assign_same(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}) -> {Pair.snd(S.Model, E.Obs, S.step(Pair.fst(S.Model, E.Obs, S.step(S.M{l, c, xs}, E.Assign{i, v})), E.Get{i})) == E.OBit{Done{v}} : E.Obs}:
  CT.get_assign_same(l, c, xs, i, v, h)

def get_assign_other(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +j: Nat, +v: Bool, +h: {Nat.is_lt(i, SC.length(Bool, xs)) == True{} : Bool}, +ne: {Nat.is_eq(i, j) == False{} : Bool}) -> {Pair.snd(S.Model, E.Obs, S.step(Pair.fst(S.Model, E.Obs, S.step(S.M{l, c, xs}, E.Assign{i, v})), E.Get{j})) == Pair.snd(S.Model, E.Obs, S.step(S.M{l, c, xs}, E.Get{j})) : E.Obs}:
  CT.get_assign_other(l, c, xs, i, j, v, h, ne)

def pop_push(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {S.room(l, c, SC.length(Bool, xs)) == True{} : Bool}) -> {S.step(Pair.fst(S.Model, E.Obs, S.step(S.M{l, c, xs}, E.Push{v})), E.Pop{}) == (S.M{l, c, xs}, E.OBit{Done{v}}) : S.Model & E.Obs}:
  CT.pop_push(l, c, xs, v, h)
