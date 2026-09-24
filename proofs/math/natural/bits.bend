import Base
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/spec_common.bend as SC
import ../../lib/lemmas/proofs/nat_algebra.bend as A
import ../../../src/math/natural.bend as M
import ./arith.bend as R

# bit_length(n) is the number of binary digits of n: n < 2^bit_length(n),
# and 2^(bit_length(n) - 1) <= n for n > 0, stated as 2^L <= 2 n
# (Lean 4 Mathlib Mathlib/Data/Nat/Size: Nat.lt_size_self and
# Nat.size_le; Python's int.bit_length). bit_length(0) == 0.

# ---- halving ----

# n == 2 (n / 2) + n mod 2
def half_eq(+n: Nat) -> {n == Nat.add(Nat.double(Nat.div(n, 2n)), Nat.mod(n, 2n)) : Nat}:
  %Equal.sym(Nat, Nat.double(Nat.div(n, 2n)), Nat.mul(Nat.div(n, 2n), 2n), Equal.trans(Nat, Nat.double(Nat.div(n, 2n)), Nat.mul(2n, Nat.div(n, 2n)), Nat.mul(Nat.div(n, 2n), 2n), A.double_mul(Nat.div(n, 2n)), A.mul_comm(2n, Nat.div(n, 2n)))) : {n == Nat.add(_, Nat.mod(n, 2n)) : Nat}
  R.dm_eq(1n, n)

# a + (1 + b) <= a is false
def add_succ_nle(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.add(a, 1n+b), a) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+ +ap:
      add_succ_nle(ap, b)

# n / 2 < n for n > 0
def half_lt(+np: Nat) -> {Nat.is_lt(Nat.div(1n+np, 2n), 1n+np) == True{} : Bool}:
  +n = {1n+np : Nat}
  +e = Equal.trans(Bool, Nat.is_le(n, Nat.div(n, 2n)), Nat.is_le(Nat.mul(n, 2n), n), False{}, R.le_div(1n, n, n),
    Equal.trans(Bool, Nat.is_le(Nat.mul(n, 2n), n), Nat.is_le(Nat.add(n, Nat.add(n, 0n)), n), False{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, n), Nat.mul(n, 2n), Nat.add(n, Nat.add(n, 0n)), A.mul_comm(n, 2n)),
      Equal.trans(Bool, Nat.is_le(Nat.add(n, Nat.add(n, 0n)), n), Nat.is_le(Nat.add(n, n), n), False{}, Equal.cong(Nat, Bool, z => Nat.is_le(Nat.add(n, z), n), Nat.add(n, 0n), n, A.add_zero(n)), add_succ_nle(n, np))))
  N.not_le_lt(n, Nat.div(n, 2n), e)

# n mod 2 <= 1
def half_rem(+n: Nat) -> {Nat.is_lt(Nat.mod(n, 2n), 2n) == True{} : Bool}:
  R.dm_lt(1n, n)

# ---- bit_length ----

def go_acc(fuel: Nat, +n: Nat, +k: Nat) -> {M.bit_length_go(fuel, n, 1n+k) == 1n+M.bit_length_go(fuel, n, k) : Nat}:
  match fuel n:
    case 0n n0:
      {==}
    case 1n+f 0n:
      {==}
    case 1n+ +f 1n+ +np:
      go_acc(f, Nat.div(1n+np, 2n), 1n+k)

def go_zero(+fuel: Nat, +k: Nat) -> {M.bit_length_go(fuel, 0n, k) == k : Nat}:
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      {==}

# the halved argument stays within the fuel
def half_fuel(+np: Nat, +f: Nat, +hf: {Nat.is_le(np, f) == True{} : Bool}) -> {Nat.is_le(Nat.div(1n+np, 2n), f) == True{} : Bool}:
  N.le_trans(Nat.div(1n+np, 2n), np, f, N.lt_succ_le(Nat.div(1n+np, 2n), np, half_lt(np)), hf)

# 2 h + r < 2 (1 + h) for r < 2
def half_bound(+np: Nat) -> {Nat.is_lt(1n+np, Nat.double(1n+Nat.div(1n+np, 2n))) == True{} : Bool}:
  +h = Nat.div(1n+np, 2n)
  %Equal.sym(Nat, 1n+np, Nat.add(Nat.double(h), Nat.mod(1n+np, 2n)), half_eq(1n+np)) : {Nat.is_lt(_, Nat.double(1n+h)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(2n, Nat.double(h)), Nat.add(Nat.double(h), 2n), A.add_comm(2n, Nat.double(h))) : {Nat.is_lt(Nat.add(Nat.double(h), Nat.mod(1n+np, 2n)), _) == True{} : Bool}
  N.lt_add_left(Nat.mod(1n+np, 2n), 2n, Nat.double(h), half_rem(1n+np))

def lt_go(fuel: Nat, +n: Nat, +hf: {Nat.is_le(n, fuel) == True{} : Bool}) -> {Nat.is_lt(n, SC.pow2(M.bit_length_go(fuel, n, 0n))) == True{} : Bool}:
  match fuel n:
    case 0n 0n:
      {==}
    case 0n 1n+np:
      Empty.absurd({Nat.is_lt(1n+np, SC.pow2(M.bit_length_go(0n, 1n+np, 0n))) == True{} : Bool}, L.false_true(hf))
    case 1n+f 0n:
      {==}
    case 1n+ +f 1n+ +np:
      +h = Nat.div(1n+np, 2n)
      +x = M.bit_length_go(f, h, 0n)
      +ih = lt_go(f, h, half_fuel(np, f, hf))
      %Equal.sym(Nat, M.bit_length_go(f, h, 1n), 1n+x, go_acc(f, h, 0n)) : {Nat.is_lt(1n+np, SC.pow2(_)) == True{} : Bool}
      N.lt_le_trans(1n+np, Nat.double(1n+h), Nat.double(SC.pow2(x)), half_bound(np), N.double_le(1n+h, SC.pow2(x), N.lt_succ_le_succ(h, SC.pow2(x), ih)))

# n < 2^bit_length(n)   (Mathlib Nat.lt_size_self)
def bit_length_lt(+n: Nat) -> {Nat.is_lt(n, SC.pow2(M.bit_length(n))) == True{} : Bool}:
  lt_go(n, n, N.le_refl(n))

# the lower bound, as 2^L <= max(1, 2 n)
def le_step(+np: Nat, +h: Nat, +x: Nat, +e: {1n+np == Nat.add(Nat.double(h), Nat.mod(1n+np, 2n)) : Nat}, +ih: {Nat.is_le(SC.pow2(x), Nat.max(1n, Nat.double(h))) == True{} : Bool}) -> {Nat.is_le(SC.pow2(x), 1n+np) == True{} : Bool}:
  match h:
    case 0n:
      N.le_trans(SC.pow2(x), 1n, 1n+np, ih, N.lt_succ_le_succ(0n, 1n+np, {==}))
    case 1n+ +hp:
      N.le_trans(SC.pow2(x), Nat.double(1n+hp), 1n+np, ih, N.le_trans(Nat.double(1n+hp), Nat.add(Nat.double(1n+hp), Nat.mod(1n+np, 2n)), 1n+np, N.le_add_right(Nat.double(1n+hp), Nat.mod(1n+np, 2n)), N.eq_le(Nat.add(Nat.double(1n+hp), Nat.mod(1n+np, 2n)), 1n+np, Equal.sym(Nat, 1n+np, Nat.add(Nat.double(1n+hp), Nat.mod(1n+np, 2n)), e))))

def le_go(fuel: Nat, +n: Nat, +hf: {Nat.is_le(n, fuel) == True{} : Bool}) -> {Nat.is_le(SC.pow2(M.bit_length_go(fuel, n, 0n)), Nat.max(1n, Nat.double(n))) == True{} : Bool}:
  match fuel n:
    case 0n 0n:
      {==}
    case 0n 1n+np:
      Empty.absurd({Nat.is_le(SC.pow2(M.bit_length_go(0n, 1n+np, 0n)), Nat.max(1n, Nat.double(1n+np))) == True{} : Bool}, L.false_true(hf))
    case 1n+f 0n:
      {==}
    case 1n+ +f 1n+ +np:
      +h = Nat.div(1n+np, 2n)
      +x = M.bit_length_go(f, h, 0n)
      +ih = le_go(f, h, half_fuel(np, f, hf))
      %Equal.sym(Nat, M.bit_length_go(f, h, 1n), 1n+x, go_acc(f, h, 0n)) : {Nat.is_le(SC.pow2(_), Nat.max(1n, Nat.double(1n+np))) == True{} : Bool}
      N.double_le(SC.pow2(x), 1n+np, le_step(np, h, x, half_eq(1n+np), ih))

# 2^bit_length(n) <= 2 n for n > 0, i.e. 2^(bit_length(n) - 1) <= n   (Mathlib Nat.size_le)
def bit_length_le(+np: Nat) -> {Nat.is_le(SC.pow2(M.bit_length(1n+np)), Nat.double(1n+np)) == True{} : Bool}:
  le_go(1n+np, 1n+np, N.le_refl(1n+np))

def bit_length_zero() -> {M.bit_length(0n) == 0n : Nat}:
  {==}
