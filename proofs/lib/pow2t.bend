import Base
import ./logic.bend as L
import ../spec/common.bend as SC
import ../../src/math/pow2.bend as P

# The tail-recursive 2^d (src/pow2.bend) is the structural spec pow2.

def go_double(+d: Nat, +acc: Nat) -> {P.go(d, Nat.double(acc)) == Nat.double(P.go(d, acc)) : Nat}:
  match d:
    case 0n:
      {==}
    case 1n+ +p:
      go_double(p, Nat.double(acc))

def same(+d: Nat) -> {P.pow2t(d) == SC.pow2(d) : Nat}:
  match d:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.trans(Nat, P.go(p, 2n), Nat.double(P.go(p, 1n)), SC.pow2(1n+p), go_double(p, 1n), Equal.cong(Nat, Nat, Nat.double, P.go(p, 1n), SC.pow2(p), same(p)))
