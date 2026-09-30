import Base
import ./suite.bend as S
import ../../src/crypto/random.bend as CR
import ../../src/math/random/rand.bend as RR

# BENCH_COUNT successive reads of BENCH_SIZE bytes (a multiple of 8) from the
# generator of suite_crandom.bend, as crypto.random.read_words into one
# Array<U32> allocated before the timed region (C: go_chacha8_read into one
# buffer). The checksum after the timed region reads the bytes back (4 LE
# bytes per word) and folds them exactly as suite_crandom.bend: last read
# first.

def gen(m: Maybe<&2, CR.Gen>) -> CR.Gen:
  match m:
    case None{}:
      CR.of_words(0, 0, 0, 0, 0, 0, 0, 0)
    case Some{g}:
      g

def reads(k: Nat, +i: Nat, +w: Nat, st: Array<U32> & CR.Gen) -> Array<U32> & CR.Gen:
  match k st:
    case 0n Tuple{a, g}:
      (a, g)
    case 1n+p Tuple{a, g}:
      reads(p, Nat.add(i, w), w, CR.read_words(g, a, i, Nat.div(w, 2n)))

def b4(+x: U32, acc: List<&2, U32>) -> List<&2, U32>:
  Con{U32.and(x, 255), Con{U32.and(U32.shrn(x, 8n), 255), Con{U32.and(U32.shrn(x, 16n), 255), Con{U32.shrn(x, 24n), acc}}}}

# r holds word j + m; the bytes of words j .. j + m, before acc
def bytes_of(m: Nat, +j: Nat, acc: List<&2, U32>, r: Array<U32> & U32) -> Array<U32> & List<&2, U32>:
  match m r:
    case 0n Tuple{a, +x}:
      (a, b4(x, acc))
    case 1n+ +p Tuple{a, +x}:
      bytes_of(p, j, b4(x, acc), Array.get(U32, a, U32.from_nat(Nat.add(j, p))))

def one_read(+j: Nat, +w: Nat, a: Array<U32>) -> Array<U32> & List<&2, U32>:
  bytes_of(Nat.sub(w, 1n), j, [], Array.get(U32, a, U32.from_nat(Nat.add(j, Nat.sub(w, 1n)))))

def push(outs: List<&2, List<&2, U32>>, r: Array<U32> & List<&2, U32>) -> Array<U32> & List<&2, List<&2, U32>>:
  match r:
    case Tuple{a, bs}:
      (a, Con{bs, outs})

def collect(k: Nat, +i: Nat, +w: Nat, st: Array<U32> & List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match k st:
    case 0n Tuple{a, outs}:
      outs
    case 1n+p Tuple{a, outs}:
      collect(p, Nat.add(i, w), w, push(outs, one_read(i, w, a)))

def arr(st: Array<U32> & CR.Gen) -> Array<U32>:
  match st:
    case Tuple{a, g}:
      a

def main() -> IO(Unit):
  do IO<Unit>:
    +n : Nat <- S.env_nat("BENCH_SIZE")
    +k : Nat <- S.env_nat("BENCH_COUNT")
    +w : Nat = Nat.div(n, 4n)
    g : CR.Gen = gen(CR.new(S.pattern(32n, 7, 1)))
    a : Array<U32> = Array.new(U32, RR.depth(Nat.mul(k, w)), 0)
    start : Nat <- IO.now()
    st : Array<U32> & CR.Gen = reads(k, 0n, w, (a, g))
    stop : Nat <- IO.now()
    S.report(start, stop, collect(k, 0n, w, (arr(st), [])))
