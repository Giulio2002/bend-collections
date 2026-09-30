import Base
import ../../../src/math/u64.bend as W

# What a source (the Source interface of src/math/random/rand.bend: a state
# type S and a step ~next: S -> W.U64 & S) is observed to do: the sequence of
# its outputs. Two sources with the same outputs are the same generator for
# every function of rand.bend.

def fst64(-S: Data, p: W.U64 & S) -> W.U64:
  (x, s) = p
  x

def snd64(-S: Data, p: W.U64 & S) -> S:
  (x, s) = p
  s

# the first n outputs of the source from state s
def outputs(~S: Data, ~next: S -> W.U64 & S, n: Nat, +s: S) -> List<&2, W.U64>:
  match n:
    case 0n:
      []
    case 1n+p:
      Con{fst64(S, next(s)), outputs(~S, ~next, p, snd64(S, next(s)))}
