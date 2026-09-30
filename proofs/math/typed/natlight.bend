import Base
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../natural/arith.bend as NR
import ./natfuel.bend as NF

# Small Nat lemmas shared by the F64 and the integer (Montgomery, gcd)
# proofs. They live here, away from the F64 files, so that importing them
# does not re-check the F64 proofs (a Bend import re-checks its file).

def dmq(+x: Nat, +D: Nat, +hD: {Nat.is_lt(0n, D) == True{} : Bool}) -> {Nat.add(Nat.mul(Nat.div(x, D), D), Nat.mod(x, D)) == x : Nat}:
  match D:
    case 0n:
      Empty.absurd({Nat.add(Nat.mul(Nat.div(x, 0n), 0n), Nat.mod(x, 0n)) == x : Nat}, N.lt_zero_absurd(0n, hD))
    case 1n+ +dp:
      Equal.sym(Nat, x, Nat.add(Nat.mul(Nat.div(x, 1n+dp), 1n+dp), Nat.mod(x, 1n+dp)), NR.dm_eq(dp, x))

def dml(+x: Nat, +D: Nat, +hD: {Nat.is_lt(0n, D) == True{} : Bool}) -> {Nat.is_lt(Nat.mod(x, D), D) == True{} : Bool}:
  match D:
    case 0n:
      Empty.absurd({Nat.is_lt(Nat.mod(x, 0n), 0n) == True{} : Bool}, N.lt_zero_absurd(0n, hD))
    case 1n+ +dp:
      NR.dm_lt(dp, x)

def mle2(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +hab: {Nat.is_le(a, b) == True{} : Bool}, +hcd: {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_le(Nat.mul(a, c), Nat.mul(b, d)) == True{} : Bool}:
  +l1 = NF.mul_le_r(a, c, d, hcd)
  +l2 = L.subst(Nat, z => {Nat.is_le(z, Nat.mul(d, b)) == True{} : Bool}, Nat.mul(d, a), Nat.mul(a, d), NA.mul_comm(d, a), NF.mul_le_r(d, a, b, hab))
  N.le_trans(Nat.mul(a, c), Nat.mul(a, d), Nat.mul(b, d), l1, L.subst(Nat, z => {Nat.is_le(Nat.mul(a, d), z) == True{} : Bool}, Nat.mul(d, b), Nat.mul(b, d), NA.mul_comm(d, b), l2))

def mul1(+y: Nat) -> {Nat.mul(1n, y) == y : Nat}:
  Equal.trans(Nat, Nat.mul(1n, y), Nat.mul(y, 1n), y, NA.mul_comm(1n, y), NA.mul_one(y))

def two_mul(+S: Nat) -> {Nat.mul(S, 2n) == Nat.add(S, S) : Nat}:
  Equal.trans(Nat, Nat.mul(S, 2n), Nat.mul(2n, S), Nat.add(S, S), NA.mul_comm(S, 2n), Equal.cong(Nat, Nat, z => Nat.add(S, z), Nat.mul(1n, S), S, mul1(S)))
