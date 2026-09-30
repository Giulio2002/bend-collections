import Base
import ./suite.bend as S
import ./suite_randlib.bend as L
import ../../src/crypto/random.bend as CR

# BENCH_COUNT successive reads of BENCH_SIZE bytes from crypto/random's
# generator (Go's ChaCha8.Read) made by new(seed), seed bytes
# (7 * i + 1) mod 256. Checksum: suite.bend's (every byte, last read first),
# after the timed region.

def gen(m: Maybe<&2, CR.Gen>) -> CR.Gen:
  match m:
    case None{}:
      CR.of_words(0, 0, 0, 0, 0, 0, 0, 0)
    case Some{g}:
      g

def push(acc: List<&2, List<&2, U32>>, r: List<&2, U32> & CR.Gen) -> List<&2, List<&2, U32>> & CR.Gen:
  (bs, g) = r
  (Con{bs, acc}, g)

def read(+n: Nat, st: List<&2, List<&2, U32>> & CR.Gen) -> List<&2, List<&2, U32>> & CR.Gen:
  (acc, g) = st
  push(acc, CR.bytes(g, n))

def reads(k: Nat, +n: Nat, st: List<&2, List<&2, U32>> & CR.Gen) -> List<&2, List<&2, U32>> & CR.Gen:
  match k:
    case 0n:
      st
    case 1n+p:
      reads(p, n, read(n, st))

def outs(st: List<&2, List<&2, U32>> & CR.Gen) -> List<&2, List<&2, U32>>:
  (xs, g) = st
  xs

def main() -> IO(Unit):
  do IO<Unit>:
    +n : Nat <- S.env_nat("BENCH_SIZE")
    k : Nat <- S.env_nat("BENCH_COUNT")
    g : CR.Gen = gen(CR.new(S.pattern(32n, 7, 1)))
    start : Nat <- IO.now()
    st : List<&2, List<&2, U32>> & CR.Gen = reads(k, n, ([], g))
    stop : Nat <- IO.now()
    S.report(start, stop, outs(st))
