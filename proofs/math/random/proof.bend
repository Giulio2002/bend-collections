import Base
import ../../../spec/lib/common.bend as C
import ../../../src/math/u64.bend as W
import ../../../src/math/w64.bend as X
import ../../../src/math/random/rand.bend as R
import ../../../src/math/random/chacha8/block.bend as B
import ../../../spec/math/w64.bend as SW
import ../../../spec/math/random.bend as SRM
import ../../../spec/math/random/rand.bend as SR
import ../../lib/logic.bend as L
import ../typed/w64add.bend as WA
import ./chacha8/stream.bend as CS
import ./chacha8/seed.bend as SEED
import ./lemire.bend as LE
import ./uint64n.bend as UN
import ./below.bend as BL
import ./shuffle.bend as SH
import ./bounded.bend as BD
import ./wrappers.bend as WR
import ./float.bend as FL
import ./pcg.bend as PC
import ../../../spec/math/random/pcg.bend as SP
import ../../../spec/math/f64.bend as SF
import ../../../src/math/random/pcg.bend as P

# Entry point: `bend proofs/math/random/proof.bend` checks every clause of
# spec/math/random.bend, under the clause's name, for every input (and every
# source, relation and element type where the clause is a template). No
# holes, no axioms.

def ChaCha8.stream(+n: Nat, +k: B.Key) -> SRM.ChaCha8.stream(n, k):
  CS.stream(n, k)

def ChaCha8.seeded(+n: Nat, +seed: List<&2, U32>) -> SRM.ChaCha8.seeded(n, seed):
  SEED.seeded(n, seed)

def Uint64n.value(~S: Data, ~next: S -> W.U64 & S, +s: S, +n: W.U64) -> SRM.Uint64n.value(~S, ~next, s, n):
  UN.uint64n_value(~S, ~next, s, n)

def Uint64n.lt(~S: Data, ~next: S -> W.U64 & S, +s: S, +n: W.U64, +hn: {X.is_zero(n) == False{} : Bool}) -> SRM.Uint64n.lt(~S, ~next, s, n, hn):
  BD.uint64n_lt(~S, ~next, s, n, hn)

def Lemire.unbiased(+w: Nat, +n: Nat, +k: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +hw: {C.fits(w, n) == True{} : Bool}, +hk: {Nat.is_lt(k, n) == True{} : Bool}) -> SRM.Lemire.unbiased(w, n, k, hn, hw, hk):
  LE.unbiased(w, n, k, hn, hw, hk)

def Shuffle.permutation(~A: Data, ~V: Data, ~rel: A -> V -> Bool, ~S: Data, ~next: S -> W.U64 & S, +s: S, +xs: List<&2, A>, +v: V) -> SRM.Shuffle.permutation(~A, ~V, ~rel, ~S, ~next, s, xs, v):
  SH.shuffle_perm(~A, ~V, ~rel, ~S, ~next, s, xs, v)

def Perm.permutation(~S: Data, ~next: S -> W.U64 & S, +s: S, +n: Nat, +i: Nat) -> SRM.Perm.permutation(~S, ~next, s, n, i):
  SH.perm_perm(~S, ~next, s, n, i)

def PCG.step(+mh: W.U64, +ml: W.U64, +ih: W.U64, +il: W.U64, +p: P.PCG) -> SRM.PCG.step(mh, ml, ih, il, p):
  PC.step(mh, ml, ih, il, p)

def PCG.output(+cm: W.U64, +hi: W.U64, +lo: W.U64, +t: Nat, +ht: {t == SP.dxsm1(SW.value(cm), SW.value(hi)) : Nat}) -> SRM.PCG.output(cm, hi, lo, t, ht):
  PC.output(cm, hi, lo, t, ht)

def PCG.constants(+p: P.PCG) -> SRM.PCG.constants(p):
  PC.constants(p)

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

def Float64.value(+x: W.U64, +xv: Nat, +hx: {Nat.sub(SF.zb(), 53n) == xv : Nat}) -> SRM.Float64.value(x, xv, hx):
  FL.value(x, xv, hx)

def Float64.lt_one(+x: W.U64) -> SRM.Float64.lt_one(x):
  FL.lt_one(x)
