import Base
import ./suite.bend as S
import ./suite_randlib.bend as L
import ../../src/math/random.bend as R
import ../../src/math/random/chacha8.bend as C8

# BENCH_COUNT successive shuffles (Go's r.Shuffle, Fisher-Yates) of a list of
# BENCH_SIZE U32s, starting from 0, 1, ..., n - 1 (built before the timed
# region), each shuffle applied to the previous result on the continuing
# ChaCha8 source of suite_chacha8_u64. Checksum: the final permutation's
# elements as 4 LE bytes each, first element first, after the timed region.

def range(n: Nat, +i: U32) -> List<&2, U32>:
  match n:
    case 0n:
      []
    case 1n+p:
      Con{i, range(p, U32.add(i, 1))}

def once(st: List<&2, U32> & C8.ChaCha8) -> List<&2, U32> & C8.ChaCha8:
  (xs, g) = st
  R.shuffle(~U32, ~C8.ChaCha8, ~R.chacha8_next, g, xs)

def times(k: Nat, st: List<&2, U32> & C8.ChaCha8) -> List<&2, U32> & C8.ChaCha8:
  match k:
    case 0n:
      st
    case 1n+p:
      times(p, once(st))

def perm(st: List<&2, U32> & C8.ChaCha8) -> List<&2, U32>:
  (xs, g) = st
  xs

def main() -> IO(Unit):
  do IO<Unit>:
    n : Nat <- S.env_nat("BENCH_SIZE")
    k : Nat <- S.env_nat("BENCH_COUNT")
    xs : List<&2, U32> = range(n, 0)
    g : C8.ChaCha8 = L.chacha8()
    start : Nat <- IO.now()
    st : List<&2, U32> & C8.ChaCha8 = times(k, (xs, g))
    stop : Nat <- IO.now()
    L.report_sum(start, stop, L.fold_u32s(perm(st), 0))
