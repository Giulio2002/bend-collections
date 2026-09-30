import Base
import ../../../spec/lib/common.bend as C
import ../../../src/math/u64.bend as W
import ../../../src/math/w64.bend as X
import ../../../spec/math/random.bend as SRM
import ./uint64n.bend as UN
import ./bounded.bend as BD
import ./wrappers.bend as WR

# Entry point: `bend proofs/math/random/proof_draws.bend` checks the bounded and
# fixed-width draw clauses (Uint64n, Uint32, Int64, Int32, Uint32n, Intn,
# IntRange) of spec/math/random.bend, under the clause's name, for every input
# (and every source, relation and element type where the clause is a
# template). No holes, no axioms. The other clauses are checked by
# proofs/math/random/proof.bend, proofs/math/random/proof_pcg.bend,
# proofs/math/random/proof_float.bend, so each root only re-checks the lemma
# files it needs.

def Uint64n.value(~S: Data, ~next: S -> W.U64 & S, +s: S, +n: W.U64) -> SRM.Uint64n.value(~S, ~next, s, n):
  UN.uint64n_value(~S, ~next, s, n)

def Uint64n.lt(~S: Data, ~next: S -> W.U64 & S, +s: S, +n: W.U64, +hn: {X.is_zero(n) == False{} : Bool}) -> SRM.Uint64n.lt(~S, ~next, s, n, hn):
  BD.uint64n_lt(~S, ~next, s, n, hn)

def Uint32.value(~S: Data, ~next: S -> W.U64 & S, +s: S) -> SRM.Uint32.value(~S, ~next, s):
  WR.uint32_value(~S, ~next, s)

def Int64.value(~S: Data, ~next: S -> W.U64 & S, +s: S) -> SRM.Int64.value(~S, ~next, s):
  WR.int64_value(~S, ~next, s)

def Int32.value(~S: Data, ~next: S -> W.U64 & S, +s: S) -> SRM.Int32.value(~S, ~next, s):
  WR.int32_value(~S, ~next, s)

def Uint32n.lt(~S: Data, ~next: S -> W.U64 & S, +s: S, +n: U32, +hn: {U32.is_zero(n) == False{} : Bool}) -> SRM.Uint32n.lt(~S, ~next, s, n, hn):
  WR.uint32n_lt(~S, ~next, s, n, hn)

def Intn.lt(~S: Data, ~next: S -> W.U64 & S, +s: S, +n: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +hw: {C.fits(64n, n) == True{} : Bool}) -> SRM.Intn.lt(~S, ~next, s, n, hn, hw):
  WR.intn_lt(~S, ~next, s, n, hn, hw)

def IntRange.bounds(~S: Data, ~next: S -> W.U64 & S, +s: S, +lo: Nat, +hi: Nat, +h: {Nat.is_lt(lo, hi) == True{} : Bool}, +hw: {C.fits(64n, Nat.sub(hi, lo)) == True{} : Bool}) -> SRM.IntRange.bounds(~S, ~next, s, lo, hi, h, hw):
  WR.int_range_bounds(~S, ~next, s, lo, hi, h, hw)
