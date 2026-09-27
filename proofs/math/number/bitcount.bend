import Base
import ../../../spec/lib/common.bend as C
import ../../lib/nat.bend as N
import ../../lib/lemmas/proofs/nat_algebra.bend as A
import ../../../src/math/number.bend as NB
import ../../../spec/math/number.bend as SN
import ../typed/width.bend as WW

# bit_count counts the 1 bits (Python int.bit_count; Lean 4 Mathlib
# Nat.bits and List.count true): each step adds n mod 2 == bit(n) and
# continues with n div 2 == half(n), the definition of ones.

def half_div2(+n: Nat) -> {C.half(n) == Nat.div(n, 2n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+ +q:
      Equal.trans(Nat, 1n+C.half(q), 1n+Nat.div(q, 2n), Nat.div(2n+q, 2n), Equal.cong(Nat, Nat, t => 1n+t, C.half(q), Nat.div(q, 2n), half_div2(q)), Equal.sym(Nat, Nat.div(2n+q, 2n), 1n+Nat.div(q, 2n), N.div2_step(q)))

def ones_zero(+k: Nat) -> {SN.ones(k, 0n) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      ones_zero(p)

# the loop adds the ones of its fuel's worth of bits
def go(+f: Nat, +n: Nat, +acc: Nat) -> {NB.bit_count_go(f, n, acc) == Nat.add(acc, SN.ones(f, n)) : Nat}:
  match f n:
    case 0n _:
      Equal.sym(Nat, Nat.add(acc, 0n), acc, A.add_zero(acc))
    case 1n+ +g 0n:
      %Equal.sym(Nat, SN.ones(g, 0n), 0n, ones_zero(g)) : {acc == Nat.add(acc, _) : Nat}
      Equal.sym(Nat, Nat.add(acc, 0n), acc, A.add_zero(acc))
    case 1n+ +g 1n+ +np:
      %Equal.sym(Nat, C.bit(1n+np), Nat.mod(1n+np, 2n), WW.bit_mod(1n+np)) : {NB.bit_count_go(g, Nat.div(1n+np, 2n), Nat.add(acc, Nat.mod(1n+np, 2n))) == Nat.add(acc, Nat.add(_, SN.ones(g, C.half(1n+np)))) : Nat}
      %Equal.sym(Nat, C.half(1n+np), Nat.div(1n+np, 2n), half_div2(1n+np)) : {NB.bit_count_go(g, Nat.div(1n+np, 2n), Nat.add(acc, Nat.mod(1n+np, 2n))) == Nat.add(acc, Nat.add(Nat.mod(1n+np, 2n), SN.ones(g, _))) : Nat}
      %A.add_assoc(acc, Nat.mod(1n+np, 2n), SN.ones(g, Nat.div(1n+np, 2n))) : {NB.bit_count_go(g, Nat.div(1n+np, 2n), Nat.add(acc, Nat.mod(1n+np, 2n))) == _ : Nat}
      go(g, Nat.div(1n+np, 2n), Nat.add(acc, Nat.mod(1n+np, 2n)))

def bit_count_value(+n: Nat) -> SN.BitCount.value(n):
  go(n, n, 0n)
