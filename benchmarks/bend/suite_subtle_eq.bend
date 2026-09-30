import Base
import ./suite.bend as S
import ../../src/crypto/subtle.bend as Sub

# subtle.eq of every message against an equal copy (the input file read
# twice): the full-length, worst-case comparison. C: a constant-time
# accumulate-the-XOR loop. BENCH_PARAM 1 compares the same bytes packed four
# to a 32-bit word (the word lists are built before the timed region; eq
# takes any U32 list).

def run(xs: List<&2, List<&2, U32>>, ys: List<&2, List<&2, U32>>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs ys:
    case h <> t g <> u:
      run(t, u, S.bit(Sub.eq(h, g)) <> acc)
    case _ _:
      acc

# four little-endian bytes per word (a short tail stays as it is)
def pack(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case a <> b <> c <> d <> rest:
      U32.or(U32.or(a, U32.shln(b, 8n)), U32.or(U32.shln(c, 16n), U32.shln(d, 24n))) <> pack(rest)
    case _:
      xs

def packs(xss: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xss:
    case Nil{}:
      Nil{}
    case h <> t:
      pack(h) <> packs(t)

def pick(p: Nat, xss: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match p:
    case 0n:
      xss
    case 1n+q:
      packs(xss)

def main() -> IO(Unit):
  do IO<Unit>:
    +param : Nat <- S.env_nat("BENCH_PARAM")
    inputs : List<&2, List<&2, U32>> <- S.messages()
    others : List<&2, List<&2, U32>> <- S.messages()
    +xs : List<&2, List<&2, U32>> = pick(param, inputs)
    +ys : List<&2, List<&2, U32>> = pick(param, others)
    start : Nat <- IO.now()
    outs : List<&2, List<&2, U32>> = run(xs, ys, Nil{})
    stop : Nat <- IO.now()
    S.report(start, stop, outs)
