import Base
import ../lib/common.bend as C
import ../../src/math/u64.bend as W
import ../../src/math/w64.bend as X
import ../../src/math/f64.bend as F
import ../../src/math/random/rand.bend as R
import ../../src/math/random/chacha8.bend as C8
import ../../src/math/random/chacha8/block.bend as B
import ../../src/math/random/pcg.bend as P
import ./w64.bend as SW
import ./f64.bend as SF
import ./random/source.bend as SRC
import ./random/chacha8rand.bend as SC
import ./random/pcg.bend as SP
import ./random/rand.bend as SR

# The contract of src/math/random.bend (Go's math/rand/v2): one
# <Function>.<clause> proposition per guarantee, each proved for every
# input in proofs/math/random/proof.bend under its name. The executable
# specifications are spec/math/random/{chacha8rand,pcg,rand,source}.bend;
# docs/MATH_CONTRACTS.md has the table.
#
#   ChaCha8 (C2SP chacha8rand)
#     ChaCha8.stream        the outputs of the generator keyed by k are
#                           C2SP's stream keyed by k's eight words
#     ChaCha8.seeded        new(seed) is None unless the seed is 32 bytes
#                           below 256, and otherwise outputs the stream keyed
#                           by the seed's little-endian words
#   PCG (Go's PCG-DXSM)
#     PCG.step              one step is s * mul + inc mod 2^128, for every
#                           multiplier and increment
#     PCG.output            the output is DXSM of the new state, for every
#                           DXSM multiplier: dxsm3 of the first half's
#                           value dxsm1
#     PCG.constants         next uses Go's constants
#   Bounded integers (Lemire, as Go's uint64n)
#     Uint64n.value         uint64n(n) is the first accepted draw of the
#                           specification's draw among at most 128 draws
#     Uint64n.lt            uint64n(n) < n for n > 0, for every source
#     Lemire.unbiased       for every width w, bound 0 < n < 2^w and k < n,
#                           exactly floor(2^w / n) of the 2^w source outputs
#                           draw k: a uniform source gives a uniform result
#   Permutations (Fisher-Yates, as Go's Shuffle and Perm)
#     Shuffle.permutation   shuffle(xs) has as many elements related to v as
#                           xs, for every relation and v (with an equality:
#                           the same multiset)
#     Perm.permutation      perm(n) holds every i < n exactly once and
#                           nothing else
#   Words and bounded wrappers
#     Uint32.value, Int64.value, Int32.value   the top 32, low 63 and top
#                           31 bits of the source output (Go's Uint32, Int64,
#                           Int32)
#     Uint32n.lt            uint32n(n) < n for n > 0
#     Intn.lt               intn(n) < n for 0 < n < 2^64 (a run-time Nat is
#                           below 2^48)
#     IntRange.bounds       lo <= int_range(lo, hi) < hi for lo < hi
#   Floats
#     Float64.value         float64 is the double m * 2^-53, m the low 53
#                           bits of the source output (exact, as Go)
#     Float64.lt_one        float64 < 1.0

def map_outputs(+n: Nat, m: Maybe<&2, C8.ChaCha8>) -> Maybe<&2, List<&2, W.U64>>:
  match m:
    case None{}:
      None{}
    case Some{g}:
      Some{SRC.outputs(~C8.ChaCha8, ~C8.next, n, g)}

def map_stream(+n: Nat, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, W.U64>>:
  match m:
    case None{}:
      None{}
    case Some{kl}:
      Some{SC.stream(n, kl)}

def ChaCha8.stream(+n: Nat, +k: B.Key) -> Type:
  {SRC.outputs(~C8.ChaCha8, ~C8.next, n, C8.of_key(k)) == SC.stream(n, SC.key_list(k)) : List<&2, W.U64>}

def ChaCha8.seeded(+n: Nat, +seed: List<&2, U32>) -> Type:
  {map_outputs(n, C8.new(seed)) == map_stream(n, SC.key_of_seed(seed)) : Maybe<&2, List<&2, W.U64>>}

def value128(p: P.PCG) -> Nat:
  match p:
    case P.P{hi, lo}:
      Nat.add(SW.value(lo), C.shift(64n, SW.value(hi)))

def PCG.step(+mh: W.U64, +ml: W.U64, +ih: W.U64, +il: W.U64, +p: P.PCG) -> Type:
  {value128(P.step_with(mh, ml, ih, il, p)) == SP.lcg(value128(P.P{mh, ml}), value128(P.P{ih, il}), value128(p)) : Nat}

# stated through the intermediate value t of the first half (so the
# checker never compares two copies of the nested 64-bit recursion);
# t = dxsm1(cm, hi) gives output == dxsm(cm, hi, lo)
def PCG.output(+cm: W.U64, +hi: W.U64, +lo: W.U64, +t: Nat, +ht: {t == SP.dxsm1(SW.value(cm), SW.value(hi)) : Nat}) -> Type:
  {SW.value(P.dxsm_with(cm, hi, lo)) == SP.dxsm3(t, SW.value(lo)) : Nat}

def PCG.constants(+p: P.PCG) -> Type:
  {P.next(p) == P.out(P.step_with(P.mul_hi(), P.mul_lo(), P.inc_hi(), P.inc_lo(), p)) : W.U64 & P.PCG}

def val_pair(-S: Data, r: W.U64 & S) -> Nat & S:
  (x, s) = r
  (SW.value(x), s)

def Uint64n.value(~S: Data, ~next: S -> W.U64 & S, +s: S, +n: W.U64) -> Type:
  {val_pair(S, R.uint64n(~S, ~next, s, n)) == SR.below(~S, ~next, 127n, SW.value(n), s) : Nat & S}

def Uint64n.lt(~S: Data, ~next: S -> W.U64 & S, +s: S, +n: W.U64, +hn: {X.is_zero(n) == False{} : Bool}) -> Type:
  {Nat.is_lt(SW.value(R.fst(W.U64, S, R.uint64n(~S, ~next, s, n))), SW.value(n)) == True{} : Bool}

def Lemire.unbiased(+w: Nat, +n: Nat, +k: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +hw: {C.fits(w, n) == True{} : Bool}, +hk: {Nat.is_lt(k, n) == True{} : Bool}) -> Type:
  {SR.count(w, n, k, C.shift(w, 1n)) == Nat.div(C.shift(w, 1n), n) : Nat}

def Shuffle.permutation(~A: Data, ~V: Data, ~rel: A -> V -> Bool, ~S: Data, ~next: S -> W.U64 & S, +s: S, +xs: List<&2, A>, +v: V) -> Type:
  {SR.occurrences(~A, ~V, ~rel, v, R.fst(List<&2, A>, S, R.shuffle(~A, ~S, ~next, s, xs))) == SR.occurrences(~A, ~V, ~rel, v, xs) : Nat}

def Perm.permutation(~S: Data, ~next: S -> W.U64 & S, +s: S, +n: Nat, +i: Nat) -> Type:
  {SR.occurrences(~Nat, ~Nat, ~Nat.is_eq, i, R.fst(List<&2, Nat>, S, R.perm(~S, ~next, s, n))) == SR.b2n(Nat.is_lt(i, n)) : Nat}

# the exact double m * 2^-53 (the exponent zb - 53 as a variable xv, so no
# closed 3000-step natural is compared)
def Float64.value(+x: W.U64, +xv: Nat, +hx: {Nat.sub(SF.zb(), 53n) == xv : Nat}) -> Type:
  {R.to_float(x) == SF.round(False{}, C.low(53n, SW.value(x)), xv) : F.F64}

def Float64.lt_one(+x: W.U64) -> Type:
  {F.lt(R.to_float(x), F.one()) == True{} : Bool}

# ---- the word slices and the bounded wrappers (Go's Uint32, Int64, Int32,
# Uint32N, IntN and lo + IntN(hi - lo)) ----

def x0(~S: Data, ~next: S -> W.U64 & S, +s: S) -> Nat:
  SW.value(SRC.fst64(S, next(s)))

def Uint32.value(~S: Data, ~next: S -> W.U64 & S, +s: S) -> Type:
  {U32.to_nat(R.fst(U32, S, R.uint32(~S, ~next, s))) == C.high(32n, x0(~S, ~next, s)) : Nat}

def Int64.value(~S: Data, ~next: S -> W.U64 & S, +s: S) -> Type:
  {SW.value(R.fst(W.U64, S, R.int64(~S, ~next, s))) == C.low(63n, x0(~S, ~next, s)) : Nat}

def Int32.value(~S: Data, ~next: S -> W.U64 & S, +s: S) -> Type:
  {U32.to_nat(R.fst(U32, S, R.int32(~S, ~next, s))) == C.high(33n, x0(~S, ~next, s)) : Nat}

def Uint32n.lt(~S: Data, ~next: S -> W.U64 & S, +s: S, +n: U32, +hn: {U32.is_zero(n) == False{} : Bool}) -> Type:
  {Nat.is_lt(U32.to_nat(R.fst(U32, S, R.uint32n(~S, ~next, s, n))), U32.to_nat(n)) == True{} : Bool}

def Intn.lt(~S: Data, ~next: S -> W.U64 & S, +s: S, +n: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +hw: {C.fits(64n, n) == True{} : Bool}) -> Type:
  {Nat.is_lt(R.fst(Nat, S, R.intn(~S, ~next, s, n)), n) == True{} : Bool}

def IntRange.bounds(~S: Data, ~next: S -> W.U64 & S, +s: S, +lo: Nat, +hi: Nat, +h: {Nat.is_lt(lo, hi) == True{} : Bool}, +hw: {C.fits(64n, Nat.sub(hi, lo)) == True{} : Bool}) -> Type:
  {Bool.and(Nat.is_le(lo, R.fst(Nat, S, R.int_range(~S, ~next, s, lo, hi))), Nat.is_lt(R.fst(Nat, S, R.int_range(~S, ~next, s, lo, hi)), hi)) == True{} : Bool}
