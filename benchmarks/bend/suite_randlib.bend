import Base
import ./suite.bend as S
import ../../src/math/u64.bend as W
import ../../src/math/f64.bend as F
import ../../src/math/random.bend as R
import ../../src/math/random/chacha8.bend as C8
import ../../src/math/random/chacha8/block.bend as B

# Shared code of the random-group drivers (suite_chacha8_u64, suite_pcg_u64,
# suite_uint_below, suite_float64, suite_shuffle, suite_crandom). A timed
# loop threads (outputs so far, generator) as one pair and prepends every
# output; the checksum after the timed region folds the outputs in list
# order, i.e. LAST draw first, each 64-bit value as its 8 little-endian bytes
# (low word first), with suite.bend's c = c * 31 + byte.

# the fixed ChaCha8 seed: bytes (7 * i + 1) mod 256
def seeded(m: Maybe<&2, C8.ChaCha8>) -> C8.ChaCha8:
  match m:
    case None{}:
      C8.of_key(B.K{0, 0, 0, 0, 0, 0, 0, 0})
    case Some{g}:
      g

def chacha8() -> C8.ChaCha8:
  seeded(R.chacha8(S.pattern(32n, 7, 1)))

# ---- 64-bit draws
def push(-S: Data, acc: List<&2, W.U64>, r: W.U64 & S) -> List<&2, W.U64> & S:
  (x, s) = r
  (Con{x, acc}, s)

def draw(~S: Data, ~next: S -> W.U64 & S, st: List<&2, W.U64> & S) -> List<&2, W.U64> & S:
  (acc, s) = st
  push(S, acc, R.uint64(~S, ~next, s))

def draws(~S: Data, ~next: S -> W.U64 & S, n: Nat, st: List<&2, W.U64> & S) -> List<&2, W.U64> & S:
  match n:
    case 0n:
      st
    case 1n+p:
      draws(~S, ~next, p, draw(~S, ~next, st))

def below(~S: Data, ~next: S -> W.U64 & S, +bound: W.U64, st: List<&2, W.U64> & S) -> List<&2, W.U64> & S:
  (acc, s) = st
  push(S, acc, R.uint_below(~S, ~next, s, bound))

def belows(~S: Data, ~next: S -> W.U64 & S, n: Nat, +bound: W.U64, st: List<&2, W.U64> & S) -> List<&2, W.U64> & S:
  match n:
    case 0n:
      st
    case 1n+p:
      belows(~S, ~next, p, bound, below(~S, ~next, bound, st))

# ---- float64 draws
def fpush(-S: Data, acc: List<&2, F.F64>, r: F.F64 & S) -> List<&2, F.F64> & S:
  (x, s) = r
  (Con{x, acc}, s)

def fdraw(~S: Data, ~next: S -> W.U64 & S, st: List<&2, F.F64> & S) -> List<&2, F.F64> & S:
  (acc, s) = st
  fpush(S, acc, R.float64(~S, ~next, s))

def fdraws(~S: Data, ~next: S -> W.U64 & S, n: Nat, st: List<&2, F.F64> & S) -> List<&2, F.F64> & S:
  match n:
    case 0n:
      st
    case 1n+p:
      fdraws(~S, ~next, p, fdraw(~S, ~next, st))

# ---- the checksum
def fold32(+w: U32, c: U32) -> U32:
  S.fold([U32.and(w, 255), U32.and(U32.shrn(w, 8n), 255), U32.and(U32.shrn(w, 16n), 255), U32.shrn(w, 24n)], c)

def fold_u64(x: W.U64, c: U32) -> U32:
  match x:
    case W.U64{+lo, +hi}:
      fold32(hi, fold32(lo, c))

def fold_u64s(xs: List<&2, W.U64>, c: U32) -> U32:
  match xs:
    case Nil{}:
      c
    case Con{x, t}:
      fold_u64s(t, fold_u64(x, c))

def fold_f64(x: F.F64, c: U32) -> U32:
  match x:
    case F.Bits{+lo, +hi}:
      fold32(hi, fold32(lo, c))

def fold_f64s(xs: List<&2, F.F64>, c: U32) -> U32:
  match xs:
    case Nil{}:
      c
    case Con{x, t}:
      fold_f64s(t, fold_f64(x, c))

def fold_u32s(xs: List<&2, U32>, c: U32) -> U32:
  match xs:
    case Nil{}:
      c
    case Con{+x, t}:
      fold_u32s(t, fold32(x, c))

def u64s_of(-S: Data, st: List<&2, W.U64> & S) -> List<&2, W.U64>:
  (xs, s) = st
  xs

def f64s_of(-S: Data, st: List<&2, F.F64> & S) -> List<&2, F.F64>:
  (xs, s) = st
  xs

def report_sum(start: Nat, stop: Nat, sum: U32) -> IO(Unit):
  do IO<Unit>:
    IO.print("BENCH_MS=" ++ Nat.show(Nat.sub(stop, start)))
    IO.print("SUM=" ++ U32.show(sum))
