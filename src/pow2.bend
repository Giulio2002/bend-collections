import Base

# 2^d by a TAIL recursion (an accumulator), so every def that calls it can
# compile to a flat native loop. The structures' own `pow2` (the structural
# `double(pow2(p))`, which the proofs unfold) is a non-tail recursion; the
# native backend compiles a def that calls a non-tail recursion as a
# segmented continuation instead of a flat loop, which made count, to_list,
# the bitwise combinators and reserve several times slower than they need to
# be. proofs/lib/pow2t.bend proves pow2t(d) == 2^d.

def go(d: Nat, acc: Nat) -> Nat:
  match d:
    case 0n:
      acc
    case 1n+p:
      go(p, Nat.double(acc))

def pow2t(+d: Nat) -> Nat:
  go(d, 1n)
