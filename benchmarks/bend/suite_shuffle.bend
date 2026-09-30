import Base
import ./suite.bend as S
import ./suite_randlib.bend as L
import ../../src/math/random.bend as R
import ../../src/math/random/rand.bend as RR
import ../../src/math/random/chacha8.bend as C8

# BENCH_COUNT successive shuffles (Go's r.Shuffle, Fisher-Yates) of an
# Array<U32> holding 0, 1, ..., n - 1 in its first n = BENCH_SIZE slots (built
# before the timed region, like the C array), each shuffle applied in place
# to the previous result on the continuing ChaCha8 source of
# suite_chacha8_u64. Checksum: the final permutation's elements as 4 LE
# bytes each, first element first, after the timed region.

def fill(n: Nat, +i: U32, a: Array<U32>) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+p:
      fill(p, U32.add(i, 1), Array.set(U32, a, i, i))

def once(+n: Nat, st: Array<U32> & C8.ChaCha8) -> Array<U32> & C8.ChaCha8:
  (a, g) = st
  R.shuffle_array(~U32, ~C8.ChaCha8, ~R.chacha8_next, g, a, n)

def times(k: Nat, +n: Nat, st: Array<U32> & C8.ChaCha8) -> Array<U32> & C8.ChaCha8:
  match k:
    case 0n:
      st
    case 1n+p:
      times(p, n, once(n, st))

# slots k - 1, ..., 0 before acc
def read(k: Nat, acc: List<&2, U32>, r: Array<U32> & U32) -> List<&2, U32>:
  match k r:
    case 0n Tuple{a, x}:
      Con{x, acc}
    case 1n+ +p Tuple{a, x}:
      read(p, Con{x, acc}, Array.get(U32, a, U32.from_nat(p)))

def perm(+n: Nat, st: Array<U32> & C8.ChaCha8) -> List<&2, U32>:
  (a, g) = st
  read(Nat.sub(n, 1n), [], Array.get(U32, a, U32.from_nat(Nat.sub(n, 1n))))

def main() -> IO(Unit):
  do IO<Unit>:
    +n : Nat <- S.env_nat("BENCH_SIZE")
    k : Nat <- S.env_nat("BENCH_COUNT")
    a : Array<U32> = fill(n, 0, Array.new(U32, RR.depth(n), 0))
    g : C8.ChaCha8 = L.chacha8()
    start : Nat <- IO.now()
    st : Array<U32> & C8.ChaCha8 = times(k, n, (a, g))
    stop : Nat <- IO.now()
    L.report_sum(start, stop, L.fold_u32s(perm(n, st), 0))
