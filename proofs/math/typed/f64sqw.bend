import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ./width.bend as WW
import ./natcmp.bend as NC
import ./w64add.bend as WA
import ./w64dm.bend as DM
import ./f64cmp.bend as FC
import ./f64mul.bend as MU
import ./f64sqa.bend as AQ

# Small Bool and Nat facts for the F64 square root proofs.

def ltz(+l: Nat) -> {Nat.is_lt(0n, l) == Bool.not(Nat.is_eq(l, 0n)) : Bool}:
  match l:
    case 0n:
      {==}
    case 1n+ +lp:
      {==}

def eq_comm(+a: Nat, +b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  Equal.trans(Bool, Nat.is_eq(a, b), Cmp.is_eq(SF.flip(Nat.cmp(a, b))), Nat.is_eq(b, a), FC.eqflip(Nat.cmp(a, b)), Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), SF.flip(Nat.cmp(a, b)), Nat.cmp(b, a), NC.cmp_flip(a, b)))

def and_comm(+a: Bool, +b: Bool) -> {Bool.and(a, b) == Bool.and(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}
