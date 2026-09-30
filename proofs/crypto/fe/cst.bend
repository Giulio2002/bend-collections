import Base
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../lib/word.bend as WD

# The radix of the callers of src/crypto/curve25519/fe.bend: FE.radix(one)
# is 2^17 in the symbolic one, and the run-time one X.one_of(xs) (a match
# on an input list, which keeps the checker from evaluating a closed 2^17)
# is 1.

def rad(+n: Nat, +x: Nat) -> {FE.pow2(n, x) == WD.sc(n, x) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      Equal.cong(Nat, Nat, t => Nat.double(t), FE.pow2(m, x), WD.sc(m, x), rad(m, x))

def rad17(+one: Nat) -> {FE.radix(one) == WD.sc(17n, one) : Nat}:
  rad(17n, one)

def one_of_eq(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>) -> {X.one_of(xs) == one : Nat}:
  match xs:
    case Nil{}:
      Equal.sym(Nat, one, 1n, h1)
    case Con{h, t}:
      Equal.sym(Nat, one, 1n, h1)

def radix_of_eq(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>) -> {X.radix_of(xs) == WD.sc(17n, one) : Nat}:
  Equal.trans(Nat, FE.radix(X.one_of(xs)), FE.radix(one), WD.sc(17n, one), Equal.cong(Nat, Nat, t => FE.radix(t), X.one_of(xs), one, one_of_eq(one, h1, xs)), rad17(one))
