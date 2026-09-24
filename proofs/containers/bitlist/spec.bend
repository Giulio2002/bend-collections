import Base
import ../../lib/spec_common.bend as C
import ../bitset/spec.bend as BS
import ../../../src/containers/types/bitlist.bend as E

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
#     /bitlist/contracts.bend).

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
