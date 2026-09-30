import Base
import ./suite.bend as S
import ../../src/crypto/subtle.bend as Sub

# subtle.eq of every message against an equal copy (the input file read
# twice): the full-length, worst-case comparison. C: a constant-time
# accumulate-the-XOR loop.

def run(xs: List<&2, List<&2, U32>>, ys: List<&2, List<&2, U32>>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs ys:
    case h <> t g <> u:
      run(t, u, S.bit(Sub.eq(h, g)) <> acc)
    case _ _:
      acc

def main() -> IO(Unit):
  do IO<Unit>:
    inputs : List<&2, List<&2, U32>> <- S.messages()
    others : List<&2, List<&2, U32>> <- S.messages()
    start : Nat <- IO.now()
    outs : List<&2, List<&2, U32>> = run(inputs, others, Nil{})
    stop : Nat <- IO.now()
    S.report(start, stop, outs)
