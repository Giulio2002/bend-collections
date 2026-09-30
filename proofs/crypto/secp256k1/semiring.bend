import Base
import ../../../spec/lib/common.bend as C
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/typed/width.bend as WW

# The few semiring facts the rewrite generator (tools/generators/rw.py,
# %norm) uses besides nat_algebra and width.

def zero_add(+x: Nat) -> {Nat.add(0n, x) == x : Nat}:
  {==}

def zero_mul(+x: Nat) -> {Nat.mul(0n, x) == 0n : Nat}:
  {==}

def one_mul(+x: Nat) -> {Nat.mul(1n, x) == x : Nat}:
  NA.add_zero(x)

def shift0(+x: Nat) -> {C.shift(0n, x) == x : Nat}:
  {==}

def mul_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(a, Nat.mul(b, c)) == Nat.mul(b, Nat.mul(a, c)) : Nat}:
  %NA.mul_assoc(a, b, c) : {_ == Nat.mul(b, Nat.mul(a, c)) : Nat}
  %NA.mul_assoc(b, a, c) : {Nat.mul(Nat.mul(a, b), c) == _ : Nat}
  %NA.mul_comm(a, b) : {Nat.mul(Nat.mul(a, b), c) == Nat.mul(_, c) : Nat}
  {==}

def shift_shift(+j: Nat, +k: Nat, +x: Nat) -> {C.shift(j, C.shift(k, x)) == C.shift(Nat.add(j, k), x) : Nat}:
  Equal.sym(Nat, C.shift(Nat.add(j, k), x), C.shift(j, C.shift(k, x)), WW.shift_comp(j, k, x))

def succ_add(+k: Nat, +x: Nat) -> {Nat.add(k, x) == Nat.add(x, k) : Nat}:
  NA.add_comm(k, x)
