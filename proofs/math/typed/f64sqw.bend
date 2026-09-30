import Base
import ../../../spec/math/f64.bend as SF
import ./natcmp.bend as NC
import ./f64cmp.bend as FC

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
