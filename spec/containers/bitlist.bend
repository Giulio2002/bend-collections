import Base
import ../lib/common.bend as C
import ./bitset.bend as BS
import ../../src/containers/types/bitlist.bend as E
import ../lib/sequence.bend as V

# Independent model of a bit list: a sequence of Booleans (bit 0 first), an
# optional maximum length and the capacity exponent of the storage (a bit
# list holds at most 32 * 2^cexp bits). Nothing here refers to words,
# shifts, masks or arrays.
#
# Shape of the specification, following verified bit-sequence developments:
#   * SSZ Bitlist[N] as in the ConsenSys eth2.0-dafny SSZ proofs
#     (src/dafny/ssz/BitListSeDes.dfy, wiki/ssz-notes.md): a bitlist is a
#     sequence of booleans whose length is bounded by N; appending past N
#     is not allowed.
#   * Lean 4 core `List Bool` / `BitVec` lemmas (Init.Data.BitVec.Lemmas,
#     getLsbD_concat / getLsbD_cons, List.getElem_set): reading bit i after
#     writing bit j is the written bit when i = j and the old bit otherwise;
#     appending one bit extends the sequence by exactly that bit.
#   * SPARK Ada formal vectors (Formal_Vectors: Length / Element /
#     Replace_Element / Append postconditions): every operation is stated by
#     its effect on the whole model plus frame conditions (proofs/containers
#     /bitlist/proof.bend).

type Model is Data:
  M{limit: Maybe<&2, Nat>, cexp: Nat, bits: List<&2, Bool>}

def new() -> Model:
  M{None{}, 31n, Nil{}}

def with_limit(+n: Nat) -> Model:
  M{Some{n}, 31n, Nil{}}

# One more bit fits under the limit and in the storage.
def below(lim: Maybe<&2, Nat>, +n: Nat) -> Bool:
  match lim:
    case None{}:
      True{}
    case Some{k}:
      Nat.is_lt(n, k)

def room(lim: Maybe<&2, Nat>, +c: Nat, +n: Nat) -> Bool:
  Bool.and(below(lim, n), Nat.is_lt(n, Nat.mul(C.pow2(c), 32n)))

# Number of True bits (the popcount of the bitset specification).
def count(xs: List<&2, Bool>) -> Nat:
  BS.count(xs)

def bit(x: Maybe<&2, Bool>) -> Result<&2, &2, E.Error, Bool>:
  match x:
    case None{}:
      Fail{E.IndexOutOfRange{}}
    case Some{b}:
      Done{b}

def last_bit(x: Maybe<&2, Bool>) -> Result<&2, &2, E.Error, Bool>:
  match x:
    case None{}:
      Fail{E.Empty{}}
    case Some{b}:
      Done{b}

# Assign bit i; out of range leaves the list unchanged and fails.
def assign_at(x: Maybe<&2, Bool>, +l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, i: Nat, v: Bool) -> Model & E.Obs:
  match x:
    case None{}:
      (M{l, c, xs}, E.OUnit{Fail{E.IndexOutOfRange{}}})
    case Some{b}:
      (M{l, c, C.update(Bool, xs, i, v)}, E.OUnit{Done{Unit{}}})

def push_if(ok: Bool, +l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, v: Bool) -> Model & E.Obs:
  match ok:
    case True{}:
      (M{l, c, C.snoc(Bool, xs, v)}, E.OUnit{Done{Unit{}}})
    case False{}:
      (M{l, c, xs}, E.OUnit{Fail{E.Full{}}})

def pop(+l: Maybe<&2, Nat>, +c: Nat, xs: List<&2, Bool>) -> Model & E.Obs:
  match xs:
    case Nil{}:
      (M{l, c, Nil{}}, E.OBit{Fail{E.Empty{}}})
    case Con{+h, +t}:
      (M{l, c, C.init(Bool, Con{h, t})}, E.OBit{last_bit(C.last(Bool, Con{h, t}))})

def step_parts(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, op: E.Op) -> Model & E.Obs:
  match op:
    case E.Length{}:
      (M{l, c, xs}, E.ONat{C.length(Bool, xs)})
    case E.Limit{}:
      (M{l, c, xs}, E.OLimit{l})
    case E.Get{+i}:
      (M{l, c, xs}, E.OBit{bit(C.nth(Bool, xs, i))})
    case E.Assign{+i, +v}:
      assign_at(C.nth(Bool, xs, i), l, c, xs, i, v)
    case E.Push{+v}:
      push_if(room(l, c, C.length(Bool, xs)), l, c, xs, v)
    case E.Pop{}:
      pop(l, c, xs)
    case E.Clear{}:
      (M{l, c, Nil{}}, E.OUnit{Done{Unit{}}})
    case E.Count{}:
      (M{l, c, xs}, E.ONat{count(xs)})
    case E.ToList{}:
      (M{l, c, xs}, E.OBits{xs})

# Every operation: the next model and the observation.
def step(m: Model, op: E.Op) -> Model & E.Obs:
  M{+l, +c, +xs} = m
  step_parts(l, c, xs, op)

def cons_obs(o: E.Obs, r: Model & List<&2, E.Obs>) -> Model & List<&2, E.Obs>:
  (m, os) = r
  (m, Con{o, os})

def run(ops: List<&2, E.Op>, +m: Model) -> Model & List<&2, E.Obs>:
  match ops:
    case Nil{}:
      (m, Nil{})
    case Con{+op, rest}:
      cons_obs(Pair.snd(Model, E.Obs, step(m, op)), run(rest, Pair.fst(Model, E.Obs, step(m, op))))

# from_bools: the bits pushed one by one onto the unbounded list.
def push_all(bs: List<&2, Bool>, +m: Model) -> Model:
  match bs:
    case Nil{}:
      m
    case Con{+b, t}:
      push_all(t, Pair.fst(Model, E.Obs, step(m, E.Push{b})))

def from_bools(+bs: List<&2, Bool>) -> Model:
  push_all(bs, new())

# ---- contract (SPARK formal containers) ----
# Each `<Subprogram>.<clause>` definition below states one Post clause of
# that SPARK subprogram, as a proposition on this model; the table names the
# clauses. proofs/containers/bitlist/ proves every clause under its clause name,
# and its `impl` lemma carries them to the implementation.
#
# Contracts of the specification, in the style of the SPARK formal vector
# postconditions (Replace_Element: Element(Container, I) = New_Item and every
# other element unchanged; Append: Length + 1 and Last_Element = New_Item)
# and of the Lean 4 List lemmas (List.getElem_set_self / getElem_set_ne,
# List.length_concat, List.dropLast_concat): each law is about the model
# step, and proofs/containers/bitlist/steps.bend makes the implementation
# step equal to step on every good bitlist, so each law holds for the
# implementation.
#
#   SPARK subprogram (.ads line)   ours    clauses
#   Replace_Element (384)          assign  get_assign_same, get_assign_other, length_assign
#   Append (706)                   push    length_push, get_push_last, count_push
#   Delete_Last (866)              pop     pop_push

def bits(m: Model) -> List<&2, Bool>:
  match m:
    case M{l, c, xs}:
      xs

# Replace_Element (384)
def Replace_Element.get_assign_same(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, C.length(Bool, xs)) == True{} : Bool}) -> Type:
  {Pair.snd(Model, E.Obs, step(Pair.fst(Model, E.Obs, step(M{l, c, xs}, E.Assign{i, v})), E.Get{i})) == E.OBit{Done{v}} : E.Obs}

# Replace_Element (384)
def Replace_Element.get_assign_other(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +j: Nat, +v: Bool, +h: {Nat.is_lt(i, C.length(Bool, xs)) == True{} : Bool}, +ne: {Nat.is_eq(i, j) == False{} : Bool}) -> Type:
  {Pair.snd(Model, E.Obs, step(Pair.fst(Model, E.Obs, step(M{l, c, xs}, E.Assign{i, v})), E.Get{j})) == Pair.snd(Model, E.Obs, step(M{l, c, xs}, E.Get{j})) : E.Obs}

# Replace_Element (384)
def Replace_Element.length_assign(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, C.length(Bool, xs)) == True{} : Bool}) -> Type:
  {C.length(Bool, bits(Pair.fst(Model, E.Obs, step(M{l, c, xs}, E.Assign{i, v})))) == C.length(Bool, xs) : Nat}

# Append (706)
def Append.length_push(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {room(l, c, C.length(Bool, xs)) == True{} : Bool}) -> Type:
  {C.length(Bool, bits(Pair.fst(Model, E.Obs, step(M{l, c, xs}, E.Push{v})))) == 1n+C.length(Bool, xs) : Nat}

# Append (706)
def Append.get_push_last(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {room(l, c, C.length(Bool, xs)) == True{} : Bool}) -> Type:
  {Pair.snd(Model, E.Obs, step(Pair.fst(Model, E.Obs, step(M{l, c, xs}, E.Push{v})), E.Get{C.length(Bool, xs)})) == E.OBit{Done{v}} : E.Obs}

# Delete_Last (866)
def Delete_Last.pop_push(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {room(l, c, C.length(Bool, xs)) == True{} : Bool}) -> Type:
  {step(Pair.fst(Model, E.Obs, step(M{l, c, xs}, E.Push{v})), E.Pop{}) == (M{l, c, xs}, E.OBit{Done{v}}) : Model & E.Obs}

# Append (706)
def Append.count_push(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {room(l, c, C.length(Bool, xs)) == True{} : Bool}) -> Type:
  {count(bits(Pair.fst(Model, E.Obs, step(M{l, c, xs}, E.Push{v})))) == Nat.add(count(xs), count(Con{v, Nil{}})) : Nat}

# ---- contract (SPARK formal containers) ----
# Each `<Subprogram>.<clause>` definition below states one Post clause of
# that SPARK subprogram, as a proposition on this model; the table names the
# clauses. proofs/containers/bitlist/ proves every clause under its clause name,
# and its `impl` lemma carries them to the implementation.
#
# The bit list against the complete SPARK formal-vector contract set
# (SPARKlib src/spark-containers-formal-vectors.ads, AdaCore/SPARKlib
# 46ec319; model predicates in spec/lib/sequence.bend), on top of the
# read-back laws above. Each lemma is one Post clause of
# step; `impl` (via P.step_ok) carries every clause to the
# implementation: BLI.step on the bit list of a good shadow lands on the
# bit list of a good shadow whose model satisfies it.
#
#   SPARK subprogram (.ads line)   ours              clauses
#   Length (284)                   length            length_result, length_frame
#   Capacity (322)                 limit             limit_result, limit_frame
#   Empty_Vector (292)             new, with_limit   new_empty, with_limit_empty, new_impl
#   Clear (341)                    clear             clear_length, clear_limit
#   Element (373)                  get               get_element, get_frame, get_outside
#   Replace_Element (384)          assign/set/unset  assign_length, assign_element,
#                                                    assign_except, assign_outside
#   Append (706)                   push              push_length, push_prefix,
#                                                    push_element, push_full
#   Delete_Last (866)              pop               pop_length, pop_prefix, pop_result, pop_empty
#   Last_Element (923)             pop's result      pop_result
#   iteration (Iter_Model, 1193)   to_list           to_list_model, to_list_frame
#   To_Vector (308)                from_bools        from_bools_model (the model spells the input)
#   implementation                 BLI.step          impl
# count has no SPARK counterpart (count_result: the number of set bits).
# Not in this API: Is_Empty, "=", Assign/Copy/Move, Reserve_Capacity,
# Reference, Insert*, Prepend*, Append_Vector/Count, Delete (at an index),
# Delete_First, Delete_Last with Count, First_Element, Reverse_Elements,
# Swap, Find_Index, Reverse_Find_Index, Contains, Has_Element.

def nx(+m: Model, +op: E.Op) -> Model:
  Pair.fst(Model, E.Obs, step(m, op))

def ob(+m: Model, +op: E.Op) -> E.Obs:
  Pair.snd(Model, E.Obs, step(m, op))

def limit(m: Model) -> Maybe<&2, Nat>:
  match m:
    case M{l, c, xs}:
      l

# Length (284)
def Length.length_result(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>) -> Type:
  {ob(M{l, c, xs}, E.Length{}) == E.ONat{C.length(Bool, xs)} : E.Obs}

# Length (284)
def Length.length_frame(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>) -> Type:
  {nx(M{l, c, xs}, E.Length{}) == M{l, c, xs} : Model}

# Capacity (322)
def Capacity.limit_result(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>) -> Type:
  {ob(M{l, c, xs}, E.Limit{}) == E.OLimit{l} : E.Obs}

# Capacity (322)
def Capacity.limit_frame(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>) -> Type:
  {nx(M{l, c, xs}, E.Limit{}) == M{l, c, xs} : Model}

# implementation
def Implementation.count_result(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>) -> Type:
  {ob(M{l, c, xs}, E.Count{}) == E.ONat{count(xs)} : E.Obs}

# iteration (Iter_Model, 1193)
def Iteration.to_list_model(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>) -> Type:
  {ob(M{l, c, xs}, E.ToList{}) == E.OBits{xs} : E.Obs}

# iteration (Iter_Model, 1193)
def Iteration.to_list_frame(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>) -> Type:
  {nx(M{l, c, xs}, E.ToList{}) == M{l, c, xs} : Model}

# Empty_Vector (292)
def Empty_Vector.new_empty() -> Type:
  {C.length(Bool, bits(new())) == 0n : Nat}

# Empty_Vector (292)
def Empty_Vector.with_limit_empty(+n: Nat) -> Type:
  {C.length(Bool, bits(with_limit(n))) == 0n : Nat}

# To_Vector (308)
def To_Vector.from_bools_model(+bs: List<&2, Bool>, +c: Nat, +hc: {c == 31n : Nat}, +h: {Nat.is_le(C.length(Bool, bs), Nat.mul(C.pow2(c), 32n)) == True{} : Bool}) -> Type:
  {push_all(bs, M{None{}, c, Nil{}}) == M{None{}, c, bs} : Model}

# Clear (341)
def Clear.clear_length(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>) -> Type:
  {C.length(Bool, bits(nx(M{l, c, xs}, E.Clear{}))) == 0n : Nat}

# Clear (341)
def Clear.clear_limit(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>) -> Type:
  {limit(nx(M{l, c, xs}, E.Clear{})) == l : Maybe<&2, Nat>}

# Element (373)
def Element.get_element(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {C.nth(Bool, xs, i) == Some{v} : Maybe<&2, Bool>}) -> Type:
  {ob(M{l, c, xs}, E.Get{i}) == E.OBit{Done{v}} : E.Obs}

# Element (373)
def Element.get_frame(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat) -> Type:
  {nx(M{l, c, xs}, E.Get{i}) == M{l, c, xs} : Model}

# Element (373)
def Element.get_outside(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_le(C.length(Bool, xs), i) == True{} : Bool}) -> Type:
  {ob(M{l, c, xs}, E.Get{i}) == E.OBit{Fail{E.IndexOutOfRange{}}} : E.Obs}

# Replace_Element (384)
def Replace_Element.assign_length(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, C.length(Bool, xs)) == True{} : Bool}) -> Type:
  {C.length(Bool, bits(nx(M{l, c, xs}, E.Assign{i, v}))) == C.length(Bool, xs) : Nat}

# Replace_Element (384)
def Replace_Element.assign_element(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, C.length(Bool, xs)) == True{} : Bool}) -> Type:
  {C.nth(Bool, bits(nx(M{l, c, xs}, E.Assign{i, v})), i) == Some{v} : Maybe<&2, Bool>}

# Replace_Element (384)
def Replace_Element.assign_except(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, C.length(Bool, xs)) == True{} : Bool}) -> Type:
  V.EqualExcept(Bool, xs, bits(nx(M{l, c, xs}, E.Assign{i, v})), i)

# Replace_Element (384)
def Replace_Element.assign_outside(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_le(C.length(Bool, xs), i) == True{} : Bool}) -> Type:
  {step(M{l, c, xs}, E.Assign{i, v}) == (M{l, c, xs}, E.OUnit{Fail{E.IndexOutOfRange{}}}) : Model & E.Obs}

# Append (706)
def Append.push_length(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {room(l, c, C.length(Bool, xs)) == True{} : Bool}) -> Type:
  {C.length(Bool, bits(nx(M{l, c, xs}, E.Push{v}))) == 1n+C.length(Bool, xs) : Nat}

# Append (706)
def Append.push_prefix(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {room(l, c, C.length(Bool, xs)) == True{} : Bool}) -> Type:
  V.EqualPrefix(Bool, xs, bits(nx(M{l, c, xs}, E.Push{v})))

# Append (706)
def Append.push_element(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {room(l, c, C.length(Bool, xs)) == True{} : Bool}) -> Type:
  {C.nth(Bool, bits(nx(M{l, c, xs}, E.Push{v})), C.length(Bool, xs)) == Some{v} : Maybe<&2, Bool>}

# Append (706)
def Append.push_full(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {room(l, c, C.length(Bool, xs)) == False{} : Bool}) -> Type:
  {step(M{l, c, xs}, E.Push{v}) == (M{l, c, xs}, E.OUnit{Fail{E.Full{}}}) : Model & E.Obs}

# Delete_Last (866)
def Delete_Last.pop_length(+l: Maybe<&2, Nat>, +c: Nat, +h: Bool, +t: List<&2, Bool>) -> Type:
  {C.length(Bool, bits(nx(M{l, c, Con{h, t}}, E.Pop{}))) == C.length(Bool, t) : Nat}

# Delete_Last (866)
def Delete_Last.pop_prefix(+l: Maybe<&2, Nat>, +c: Nat, +h: Bool, +t: List<&2, Bool>) -> Type:
  V.EqualPrefix(Bool, bits(nx(M{l, c, Con{h, t}}, E.Pop{})), Con{h, t})

# Delete_Last (866)
def Delete_Last.pop_result(+l: Maybe<&2, Nat>, +c: Nat, +h: Bool, +t: List<&2, Bool>) -> Type:
  {ob(M{l, c, Con{h, t}}, E.Pop{}) == E.OBit{last_bit(V.last_elem(Bool, Con{h, t}))} : E.Obs}

# Delete_Last (866)
def Delete_Last.pop_empty(+l: Maybe<&2, Nat>, +c: Nat) -> Type:
  {step(M{l, c, Nil{}}, E.Pop{}) == (M{l, c, Nil{}}, E.OBit{Fail{E.Empty{}}}) : Model & E.Obs}
