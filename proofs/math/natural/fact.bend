import Base
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as A
import ../../../src/math/natural.bend as M
import ./arith.bend as R
import ./lcm.bend as LC
import ./spec.bend as S

# factorial, perm and comb against the structural definitions of
# spec.bend, following Lean 4 Mathlib (Mathlib/Data/Nat/Factorial/Basic,
# Mathlib/Data/Nat/Choose/Basic): Nat.factorial_pos,
# Nat.succ_descFactorial_succ, Nat.descFactorial_self,
# Nat.factorial_mul_descFactorial, Nat.add_one_mul_choose_eq,
# Nat.choose_succ_right_eq, Nat.descFactorial_eq_factorial_mul_choose,
# Nat.choose_mul_factorial_mul_factorial, Nat.choose_symm,
# Nat.choose_eq_zero_of_lt.

# (x a) f == a (x f)
def mul_left_comm(+x: Nat, +a: Nat, +f: Nat) -> {Nat.mul(Nat.mul(x, a), f) == Nat.mul(a, Nat.mul(x, f)) : Nat}:
  Equal.trans(Nat, Nat.mul(Nat.mul(x, a), f), Nat.mul(Nat.mul(a, x), f), Nat.mul(a, Nat.mul(x, f)), Equal.cong(Nat, Nat, z => Nat.mul(z, f), Nat.mul(x, a), Nat.mul(a, x), A.mul_comm(x, a)), A.mul_assoc(a, x, f))

# ---- factorial ----

def factorial_go(+n: Nat, +acc: Nat) -> {M.factorial_go(n, acc) == Nat.mul(acc, S.factorial(n)) : Nat}:
  match n:
    case 0n:
      Equal.sym(Nat, Nat.mul(acc, 1n), acc, A.mul_one(acc))
    case 1n+ +p:
      Equal.trans(Nat, M.factorial_go(p, Nat.mul(1n+p, acc)), Nat.mul(Nat.mul(1n+p, acc), S.factorial(p)), Nat.mul(acc, Nat.mul(1n+p, S.factorial(p))), factorial_go(p, Nat.mul(1n+p, acc)), mul_left_comm(1n+p, acc, S.factorial(p)))

# factorial(n) == n!
def factorial_ok(+n: Nat) -> {M.factorial(n) == S.factorial(n) : Nat}:
  Equal.trans(Nat, M.factorial(n), Nat.mul(1n, S.factorial(n)), S.factorial(n), factorial_go(n, 1n), LC.one_mul(S.factorial(n)))

def pos_mul(+p: Nat, +f: Nat, +h: {Nat.is_lt(0n, f) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.mul(1n+p, f)) == True{} : Bool}:
  match f:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, Nat.mul(1n+p, 0n)) == True{} : Bool}, L.false_true(h))
    case 1n+fp:
      {==}

# 0 < n!   (Mathlib Nat.factorial_pos)
def factorial_pos(+n: Nat) -> {Nat.is_lt(0n, S.factorial(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      pos_mul(p, S.factorial(p), factorial_pos(p))

# ---- descending factorial: perm ----

# (1+m).desc(1+j) == (1+m) * m.desc(j)   (Mathlib Nat.succ_descFactorial_succ)
def desc_succ(+m: Nat, +j: Nat) -> {S.desc(1n+m, 1n+j) == Nat.mul(1n+m, S.desc(m, j)) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+ +i:
      %Equal.sym(Nat, S.desc(1n+m, 1n+i), Nat.mul(1n+m, S.desc(m, i)), desc_succ(m, i)) : {Nat.mul(Nat.sub(m, i), _) == Nat.mul(1n+m, Nat.mul(Nat.sub(m, i), S.desc(m, i))) : Nat}
      LC.swap_cw(Nat.sub(m, i), 1n+m, S.desc(m, i))

# m * (m - 1).desc(j) == m.desc(1+j), the order perm multiplies in
def desc_front(+m: Nat, +j: Nat) -> {Nat.mul(m, S.desc(Nat.sub(m, 1n), j)) == S.desc(m, 1n+j) : Nat}:
  match m:
    case 0n:
      Equal.sym(Nat, Nat.mul(Nat.sub(0n, j), S.desc(0n, j)), 0n, Equal.cong(Nat, Nat, z => Nat.mul(z, S.desc(0n, j)), Nat.sub(0n, j), 0n, R.zsub(j)))
    case 1n+ +mp:
      %Equal.sym(Nat, Nat.sub(1n+mp, 1n), mp, N.sub_zero(mp)) : {Nat.mul(1n+mp, S.desc(_, j)) == S.desc(1n+mp, 1n+j) : Nat}
      Equal.sym(Nat, S.desc(1n+mp, 1n+j), Nat.mul(1n+mp, S.desc(mp, j)), desc_succ(mp, j))

def perm_go(+k: Nat, +m: Nat, +acc: Nat) -> {M.perm_go(k, m, acc) == Nat.mul(acc, S.desc(m, k)) : Nat}:
  match k:
    case 0n:
      Equal.sym(Nat, Nat.mul(acc, 1n), acc, A.mul_one(acc))
    case 1n+ +j:
      Equal.trans(Nat, M.perm_go(j, Nat.sub(m, 1n), Nat.mul(acc, m)), Nat.mul(Nat.mul(acc, m), S.desc(Nat.sub(m, 1n), j)), Nat.mul(acc, S.desc(m, 1n+j)), perm_go(j, Nat.sub(m, 1n), Nat.mul(acc, m)),
        Equal.trans(Nat, Nat.mul(Nat.mul(acc, m), S.desc(Nat.sub(m, 1n), j)), Nat.mul(acc, Nat.mul(m, S.desc(Nat.sub(m, 1n), j))), Nat.mul(acc, S.desc(m, 1n+j)), A.mul_assoc(acc, m, S.desc(Nat.sub(m, 1n), j)),
          Equal.cong(Nat, Nat, z => Nat.mul(acc, z), Nat.mul(m, S.desc(Nat.sub(m, 1n), j)), S.desc(m, 1n+j), desc_front(m, j))))

# perm(n, k) == n.descFactorial(k)
def perm_ok(+n: Nat, +k: Nat) -> {M.perm(n, k) == S.desc(n, k) : Nat}:
  Equal.trans(Nat, M.perm(n, k), Nat.mul(1n, S.desc(n, k)), S.desc(n, k), perm_go(k, n, 1n), LC.one_mul(S.desc(n, k)))

# n.desc(n) == n!   (Mathlib Nat.descFactorial_self)
def desc_self(+n: Nat) -> {S.desc(n, n) == S.factorial(n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.trans(Nat, S.desc(1n+p, 1n+p), Nat.mul(1n+p, S.desc(p, p)), S.factorial(1n+p), desc_succ(p, p), Equal.cong(Nat, Nat, z => Nat.mul(1n+p, z), S.desc(p, p), S.factorial(p), desc_self(p)))

# j < n gives n - j == 1 + (n - (1 + j))
def sub_lt_succ(+n: Nat, +j: Nat, +h: {Nat.is_lt(j, n) == True{} : Bool}) -> {Nat.sub(n, j) == 1n+Nat.sub(n, 1n+j) : Nat}:
  match n j:
    case 0n j0:
      Empty.absurd({Nat.sub(0n, j0) == 1n+Nat.sub(0n, 1n+j0) : Nat}, N.lt_zero_absurd(j0, h))
    case 1n+ +np 0n:
      Equal.sym(Nat, 1n+Nat.sub(np, 0n), 1n+np, N.succ_cong(Nat.sub(np, 0n), np, N.sub_zero(np)))
    case 1n+ +np 1n+ +jp:
      sub_lt_succ(np, jp, h)

# (n - k)! * n.desc(k) == n!   (Mathlib Nat.factorial_mul_descFactorial)
def factorial_mul_desc(+n: Nat, +k: Nat, +h: {Nat.is_le(k, n) == True{} : Bool}) -> {Nat.mul(S.factorial(Nat.sub(n, k)), S.desc(n, k)) == S.factorial(n) : Nat}:
  match k:
    case 0n:
      %Equal.sym(Nat, Nat.sub(n, 0n), n, N.sub_zero(n)) : {Nat.mul(S.factorial(_), 1n) == S.factorial(n) : Nat}
      A.mul_one(S.factorial(n))
    case 1n+ +j:
      +t = Nat.sub(n, 1n+j)
      +hj = N.succ_le_lt(j, n, h)
      +ih = factorial_mul_desc(n, j, N.lt_le(j, n, hj))
      +es = sub_lt_succ(n, j, hj)
      # t! * ((n - j) * n.desc(j)) == ((n - j) * t!) * n.desc(j) == (n - j)! * n.desc(j)
      %Equal.sym(Nat, Nat.mul(S.factorial(t), Nat.mul(Nat.sub(n, j), S.desc(n, j))), Nat.mul(Nat.mul(Nat.sub(n, j), S.factorial(t)), S.desc(n, j)), Equal.sym(Nat, Nat.mul(Nat.mul(Nat.sub(n, j), S.factorial(t)), S.desc(n, j)), Nat.mul(S.factorial(t), Nat.mul(Nat.sub(n, j), S.desc(n, j))), mul_left_comm(Nat.sub(n, j), S.factorial(t), S.desc(n, j)))) : {_ == S.factorial(n) : Nat}
      %Equal.sym(Nat, Nat.sub(n, j), 1n+t, es) : {Nat.mul(Nat.mul(_, S.factorial(t)), S.desc(n, j)) == S.factorial(n) : Nat}
      %Equal.sym(Nat, Nat.mul(1n+t, S.factorial(t)), S.factorial(Nat.sub(n, j)), Equal.trans(Nat, Nat.mul(1n+t, S.factorial(t)), S.factorial(1n+t), S.factorial(Nat.sub(n, j)), {==}, Equal.cong(Nat, Nat, z => S.factorial(z), 1n+t, Nat.sub(n, j), Equal.sym(Nat, Nat.sub(n, j), 1n+t, es)))) : {Nat.mul(_, S.desc(n, j)) == S.factorial(n) : Nat}
      ih

# ---- binomial coefficients ----

def choose_zero_right(+n: Nat) -> {S.choose(n, 0n) == 1n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

# C(n, 1) == n
def choose_one_right(+n: Nat) -> {S.choose(n, 1n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      %Equal.sym(Nat, S.choose(m, 0n), 1n, choose_zero_right(m)) : {Nat.add(_, S.choose(m, 1n)) == 1n+m : Nat}
      N.succ_cong(S.choose(m, 1n), m, choose_one_right(m))

# (n + 1) C(n, k) == C(n + 1, k + 1) (k + 1)   (Mathlib Nat.add_one_mul_choose_eq)
def succ_mul_choose(+n: Nat, +k: Nat) -> {Nat.mul(1n+n, S.choose(n, k)) == Nat.mul(S.choose(1n+n, 1n+k), 1n+k) : Nat}:
  match n k:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      {==}
    case 1n+ +m 0n:
      %Equal.sym(Nat, S.choose(1n+m, 0n), 1n, choose_zero_right(1n+m)) : {Nat.mul(2n+m, _) == Nat.mul(Nat.add(S.choose(1n+m, 0n), S.choose(1n+m, 1n)), 1n) : Nat}
      %Equal.sym(Nat, S.choose(1n+m, 0n), 1n, choose_zero_right(1n+m)) : {Nat.mul(2n+m, 1n) == Nat.mul(Nat.add(_, S.choose(1n+m, 1n)), 1n) : Nat}
      %Equal.sym(Nat, S.choose(1n+m, 1n), 1n+m, choose_one_right(1n+m)) : {Nat.mul(2n+m, 1n) == Nat.mul(Nat.add(1n, _), 1n) : Nat}
      {==}
    case 1n+ +m 1n+ +j:
      +x = S.choose(1n+m, 1n+j)
      +y = S.choose(1n+m, 2n+j)
      +c0 = S.choose(m, j)
      +c1 = S.choose(m, 1n+j)
      # (x + y)(2 + j) == x + x(1 + j) + y(2 + j) == x + (1+m) c0 + (1+m) c1 == x + (1+m) x
      %Equal.sym(Nat, Nat.mul(Nat.add(x, y), 2n+j), Nat.add(Nat.mul(x, 2n+j), Nat.mul(y, 2n+j)), A.mul_add_right(x, y, 2n+j)) : {Nat.mul(2n+m, x) == _ : Nat}
      %Equal.sym(Nat, Nat.mul(x, 2n+j), Nat.add(x, Nat.mul(x, 1n+j)), A.mul_succ(x, 1n+j)) : {Nat.mul(2n+m, x) == Nat.add(_, Nat.mul(y, 2n+j)) : Nat}
      %Equal.sym(Nat, Nat.mul(x, 1n+j), Nat.mul(1n+m, c0), Equal.sym(Nat, Nat.mul(1n+m, c0), Nat.mul(x, 1n+j), succ_mul_choose(m, j))) : {Nat.mul(2n+m, x) == Nat.add(Nat.add(x, _), Nat.mul(y, 2n+j)) : Nat}
      %Equal.sym(Nat, Nat.mul(y, 2n+j), Nat.mul(1n+m, c1), Equal.sym(Nat, Nat.mul(1n+m, c1), Nat.mul(y, 2n+j), succ_mul_choose(m, 1n+j))) : {Nat.mul(2n+m, x) == Nat.add(Nat.add(x, Nat.mul(1n+m, c0)), _) : Nat}
      %Equal.sym(Nat, Nat.add(Nat.add(x, Nat.mul(1n+m, c0)), Nat.mul(1n+m, c1)), Nat.add(x, Nat.add(Nat.mul(1n+m, c0), Nat.mul(1n+m, c1))), A.add_assoc(x, Nat.mul(1n+m, c0), Nat.mul(1n+m, c1))) : {Nat.mul(2n+m, x) == _ : Nat}
      %Equal.sym(Nat, Nat.add(Nat.mul(1n+m, c0), Nat.mul(1n+m, c1)), Nat.mul(1n+m, Nat.add(c0, c1)), Equal.sym(Nat, Nat.mul(1n+m, Nat.add(c0, c1)), Nat.add(Nat.mul(1n+m, c0), Nat.mul(1n+m, c1)), A.mul_add_left(1n+m, c0, c1))) : {Nat.mul(2n+m, x) == Nat.add(x, _) : Nat}
      {==}

# a (x - y) == a x - a y
def mul_sub_left(+a: Nat, +x: Nat, +y: Nat) -> {Nat.mul(a, Nat.sub(x, y)) == Nat.sub(Nat.mul(a, x), Nat.mul(a, y)) : Nat}:
  %Equal.sym(Nat, Nat.mul(a, Nat.sub(x, y)), Nat.mul(Nat.sub(x, y), a), A.mul_comm(a, Nat.sub(x, y))) : {_ == Nat.sub(Nat.mul(a, x), Nat.mul(a, y)) : Nat}
  %Equal.sym(Nat, Nat.mul(a, x), Nat.mul(x, a), A.mul_comm(a, x)) : {Nat.mul(Nat.sub(x, y), a) == Nat.sub(_, Nat.mul(a, y)) : Nat}
  %Equal.sym(Nat, Nat.mul(a, y), Nat.mul(y, a), A.mul_comm(a, y)) : {Nat.mul(Nat.sub(x, y), a) == Nat.sub(Nat.mul(x, a), _) : Nat}
  R.mul_sub(x, y, a)

# C(n, k + 1) (k + 1) == C(n, k) (n - k)   (Mathlib Nat.choose_succ_right_eq)
def choose_succ_right(+n: Nat, +k: Nat) -> {Nat.mul(S.choose(n, 1n+k), 1n+k) == Nat.mul(S.choose(n, k), Nat.sub(n, k)) : Nat}:
  +c = S.choose(n, k)
  +d = S.choose(n, 1n+k)
  # (1 + n) c == c (1 + k) + d (1 + k)
  +e = Equal.trans(Nat, Nat.mul(1n+n, c), Nat.mul(Nat.add(c, d), 1n+k), Nat.add(Nat.mul(c, 1n+k), Nat.mul(d, 1n+k)), succ_mul_choose(n, k), A.mul_add_right(c, d, 1n+k))
  %Equal.sym(Nat, Nat.mul(c, Nat.sub(n, k)), Nat.sub(Nat.mul(c, 1n+n), Nat.mul(c, 1n+k)), mul_sub_left(c, 1n+n, 1n+k)) : {Nat.mul(d, 1n+k) == _ : Nat}
  %Equal.sym(Nat, Nat.mul(c, 1n+n), Nat.mul(1n+n, c), A.mul_comm(c, 1n+n)) : {Nat.mul(d, 1n+k) == Nat.sub(_, Nat.mul(c, 1n+k)) : Nat}
  %Equal.sym(Nat, Nat.mul(1n+n, c), Nat.add(Nat.mul(c, 1n+k), Nat.mul(d, 1n+k)), e) : {Nat.mul(d, 1n+k) == Nat.sub(_, Nat.mul(c, 1n+k)) : Nat}
  Equal.sym(Nat, Nat.sub(Nat.add(Nat.mul(c, 1n+k), Nat.mul(d, 1n+k)), Nat.mul(c, 1n+k)), Nat.mul(d, 1n+k), N.add_sub_cancel(Nat.mul(c, 1n+k), Nat.mul(d, 1n+k)))

# C(n, k) k! == n.desc(k)   (Mathlib Nat.descFactorial_eq_factorial_mul_choose)
def choose_mul_factorial(+n: Nat, +k: Nat) -> {Nat.mul(S.choose(n, k), S.factorial(k)) == S.desc(n, k) : Nat}:
  match k:
    case 0n:
      %Equal.sym(Nat, S.choose(n, 0n), 1n, choose_zero_right(n)) : {Nat.mul(_, 1n) == 1n : Nat}
      {==}
    case 1n+ +j:
      # C(n, 1+j) ((1+j) j!) == (C(n, 1+j) (1+j)) j! == (C(n, j) (n - j)) j! == (n - j) (C(n, j) j!)
      %Equal.sym(Nat, Nat.mul(S.choose(n, 1n+j), Nat.mul(1n+j, S.factorial(j))), Nat.mul(Nat.mul(S.choose(n, 1n+j), 1n+j), S.factorial(j)), Equal.sym(Nat, Nat.mul(Nat.mul(S.choose(n, 1n+j), 1n+j), S.factorial(j)), Nat.mul(S.choose(n, 1n+j), Nat.mul(1n+j, S.factorial(j))), A.mul_assoc(S.choose(n, 1n+j), 1n+j, S.factorial(j)))) : {_ == S.desc(n, 1n+j) : Nat}
      %Equal.sym(Nat, Nat.mul(S.choose(n, 1n+j), 1n+j), Nat.mul(S.choose(n, j), Nat.sub(n, j)), choose_succ_right(n, j)) : {Nat.mul(_, S.factorial(j)) == S.desc(n, 1n+j) : Nat}
      %Equal.sym(Nat, Nat.mul(Nat.mul(S.choose(n, j), Nat.sub(n, j)), S.factorial(j)), Nat.mul(Nat.sub(n, j), Nat.mul(S.choose(n, j), S.factorial(j))), Equal.trans(Nat, Nat.mul(Nat.mul(S.choose(n, j), Nat.sub(n, j)), S.factorial(j)), Nat.mul(Nat.mul(Nat.sub(n, j), S.choose(n, j)), S.factorial(j)), Nat.mul(Nat.sub(n, j), Nat.mul(S.choose(n, j), S.factorial(j))), Equal.cong(Nat, Nat, z => Nat.mul(z, S.factorial(j)), Nat.mul(S.choose(n, j), Nat.sub(n, j)), Nat.mul(Nat.sub(n, j), S.choose(n, j)), A.mul_comm(S.choose(n, j), Nat.sub(n, j))), A.mul_assoc(Nat.sub(n, j), S.choose(n, j), S.factorial(j)))) : {_ == S.desc(n, 1n+j) : Nat}
      Equal.cong(Nat, Nat, z => Nat.mul(Nat.sub(n, j), z), Nat.mul(S.choose(n, j), S.factorial(j)), S.desc(n, j), choose_mul_factorial(n, j))

# n < k gives C(n, k) == 0   (Mathlib Nat.choose_eq_zero_of_lt)
def choose_eq_zero(+n: Nat, +k: Nat, +h: {Nat.is_lt(n, k) == True{} : Bool}) -> {S.choose(n, k) == 0n : Nat}:
  match n k:
    case n0 0n:
      Empty.absurd({S.choose(n0, 0n) == 0n : Nat}, N.lt_zero_absurd(n0, h))
    case 0n 1n+j:
      {==}
    case 1n+ +m 1n+ +j:
      %Equal.sym(Nat, S.choose(m, j), 0n, choose_eq_zero(m, j, h)) : {Nat.add(_, S.choose(m, 1n+j)) == 0n : Nat}
      choose_eq_zero(m, 1n+j, N.lt_trans(m, j, 1n+j, h, N.lt_succ(j)))

def pos_pos(+a: Nat, +b: Nat, +ha: {Nat.is_lt(0n, a) == True{} : Bool}, +hb: {Nat.is_lt(0n, b) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.mul(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, Nat.mul(0n, b)) == True{} : Bool}, L.false_true(ha))
    case 1n+ +ap:
      pos_mul(ap, b, hb)

# C(n, k) (k! (n - k)!) == n!   (Mathlib Nat.choose_mul_factorial_mul_factorial)
def choose_mul_facts(+n: Nat, +k: Nat, +h: {Nat.is_le(k, n) == True{} : Bool}) -> {Nat.mul(S.choose(n, k), Nat.mul(S.factorial(k), S.factorial(Nat.sub(n, k)))) == S.factorial(n) : Nat}:
  %Equal.sym(Nat, Nat.mul(S.choose(n, k), Nat.mul(S.factorial(k), S.factorial(Nat.sub(n, k)))), Nat.mul(Nat.mul(S.choose(n, k), S.factorial(k)), S.factorial(Nat.sub(n, k))), Equal.sym(Nat, Nat.mul(Nat.mul(S.choose(n, k), S.factorial(k)), S.factorial(Nat.sub(n, k))), Nat.mul(S.choose(n, k), Nat.mul(S.factorial(k), S.factorial(Nat.sub(n, k)))), A.mul_assoc(S.choose(n, k), S.factorial(k), S.factorial(Nat.sub(n, k))))) : {_ == S.factorial(n) : Nat}
  %Equal.sym(Nat, Nat.mul(S.choose(n, k), S.factorial(k)), S.desc(n, k), choose_mul_factorial(n, k)) : {Nat.mul(_, S.factorial(Nat.sub(n, k))) == S.factorial(n) : Nat}
  %Equal.sym(Nat, Nat.mul(S.desc(n, k), S.factorial(Nat.sub(n, k))), Nat.mul(S.factorial(Nat.sub(n, k)), S.desc(n, k)), A.mul_comm(S.desc(n, k), S.factorial(Nat.sub(n, k)))) : {_ == S.factorial(n) : Nat}
  factorial_mul_desc(n, k, h)

# n - (n - k) == k for k <= n
def sub_sub_self(+n: Nat, +k: Nat, +h: {Nat.is_le(k, n) == True{} : Bool}) -> {Nat.sub(n, Nat.sub(n, k)) == k : Nat}:
  +e = N.sub_add(n, k, h)
  %Equal.sym(Nat, n, Nat.add(k, Nat.sub(n, k)), Equal.sym(Nat, Nat.add(k, Nat.sub(n, k)), n, e)) : {Nat.sub(_, Nat.sub(n, k)) == k : Nat}
  %Equal.sym(Nat, Nat.add(k, Nat.sub(n, k)), Nat.add(Nat.sub(n, k), k), A.add_comm(k, Nat.sub(n, k))) : {Nat.sub(_, Nat.sub(n, k)) == k : Nat}
  N.add_sub_cancel(Nat.sub(n, k), k)

def sub_le_self(+n: Nat, +k: Nat) -> {Nat.is_le(Nat.sub(n, k), n) == True{} : Bool}:
  match n k:
    case 0n k0:
      %Equal.sym(Nat, Nat.sub(0n, k0), 0n, R.zsub(k0)) : {Nat.is_le(_, 0n) == True{} : Bool}
      {==}
    case 1n+ +np 0n:
      N.le_refl(1n+np)
    case 1n+ +np 1n+ +kp:
      N.le_trans(Nat.sub(np, kp), np, 1n+np, sub_le_self(np, kp), N.le_succ(np))

# C(n, n - k) == C(n, k)   (Mathlib Nat.choose_symm)
def choose_symm(+n: Nat, +k: Nat, +h: {Nat.is_le(k, n) == True{} : Bool}) -> {S.choose(n, Nat.sub(n, k)) == S.choose(n, k) : Nat}:
  +kk = Nat.sub(n, k)
  +fk = S.factorial(k)
  +fkk = S.factorial(kk)
  +e1 = choose_mul_facts(n, kk, sub_le_self(n, k))
  +e1b = Equal.trans(Nat, Nat.mul(S.choose(n, kk), Nat.mul(fkk, fk)), Nat.mul(S.choose(n, kk), Nat.mul(fkk, S.factorial(Nat.sub(n, kk)))), S.factorial(n),
    Equal.cong(Nat, Nat, z => Nat.mul(S.choose(n, kk), Nat.mul(fkk, S.factorial(z))), k, Nat.sub(n, kk), Equal.sym(Nat, Nat.sub(n, kk), k, sub_sub_self(n, k, h))), e1)
  +e2 = Equal.trans(Nat, Nat.mul(S.choose(n, k), Nat.mul(fkk, fk)), Nat.mul(S.choose(n, k), Nat.mul(fk, fkk)), S.factorial(n),
    Equal.cong(Nat, Nat, z => Nat.mul(S.choose(n, k), z), Nat.mul(fkk, fk), Nat.mul(fk, fkk), A.mul_comm(fkk, fk)), choose_mul_facts(n, k, h))
  LC.cancel_pos(S.choose(n, kk), S.choose(n, k), Nat.mul(fkk, fk), pos_pos(fkk, fk, factorial_pos(kk), factorial_pos(k)), Equal.trans(Nat, Nat.mul(S.choose(n, kk), Nat.mul(fkk, fk)), S.factorial(n), Nat.mul(S.choose(n, k), Nat.mul(fkk, fk)), e1b, Equal.sym(Nat, Nat.mul(S.choose(n, k), Nat.mul(fkk, fk)), S.factorial(n), e2)))

# ---- comb ----

# every r_i is C(n, i), so each division is exact
def comb_go(+j: Nat, +n: Nat, +i: Nat) -> {M.comb_go(j, n, i, S.choose(n, i)) == S.choose(n, Nat.add(i, j)) : Nat}:
  match j:
    case 0n:
      Equal.cong(Nat, Nat, z => S.choose(n, z), i, Nat.add(i, 0n), Equal.sym(Nat, Nat.add(i, 0n), i, A.add_zero(i)))
    case 1n+ +jp:
      %Equal.sym(Nat, Nat.mul(S.choose(n, i), Nat.sub(n, i)), Nat.add(Nat.mul(S.choose(n, 1n+i), 1n+i), 0n), Equal.trans(Nat, Nat.mul(S.choose(n, i), Nat.sub(n, i)), Nat.mul(S.choose(n, 1n+i), 1n+i), Nat.add(Nat.mul(S.choose(n, 1n+i), 1n+i), 0n), Equal.sym(Nat, Nat.mul(S.choose(n, 1n+i), 1n+i), Nat.mul(S.choose(n, i), Nat.sub(n, i)), choose_succ_right(n, i)), Equal.sym(Nat, Nat.add(Nat.mul(S.choose(n, 1n+i), 1n+i), 0n), Nat.mul(S.choose(n, 1n+i), 1n+i), A.add_zero(Nat.mul(S.choose(n, 1n+i), 1n+i))))) : {M.comb_go(jp, n, 1n+i, Nat.div(_, 1n+i)) == S.choose(n, Nat.add(i, 1n+jp)) : Nat}
      %Equal.sym(Nat, Nat.div(Nat.add(Nat.mul(S.choose(n, 1n+i), 1n+i), 0n), 1n+i), S.choose(n, 1n+i), R.div_of(S.choose(n, 1n+i), i, 0n, {==})) : {M.comb_go(jp, n, 1n+i, _) == S.choose(n, Nat.add(i, 1n+jp)) : Nat}
      %Equal.sym(Nat, Nat.add(i, 1n+jp), 1n+Nat.add(i, jp), A.add_succ(i, jp)) : {M.comb_go(jp, n, 1n+i, S.choose(n, 1n+i)) == S.choose(n, _) : Nat}
      comb_go(jp, n, 1n+i)

def comb_min(+n: Nat, +k: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}, +b: Bool, +hb: {Nat.is_lt(k, Nat.sub(n, k)) == b : Bool}) -> {S.choose(n, Nat.min(k, Nat.sub(n, k))) == S.choose(n, k) : Nat}:
  match b:
    case True{}:
      Equal.cong(Nat, Nat, z => S.choose(n, z), Nat.min(k, Nat.sub(n, k)), k, N.min_left(k, Nat.sub(n, k), hb))
    case False{}:
      Equal.trans(Nat, S.choose(n, Nat.min(k, Nat.sub(n, k))), S.choose(n, Nat.sub(n, k)), S.choose(n, k), Equal.cong(Nat, Nat, z => S.choose(n, z), Nat.min(k, Nat.sub(n, k)), Nat.sub(n, k), N.min_right(k, Nat.sub(n, k), hb)), choose_symm(n, k, hk))

def comb_small(+n: Nat, +k: Nat, +b: Bool, +hb: {Nat.is_lt(n, k) == b : Bool}) -> {M.comb_small(n, k, b) == S.choose(n, k) : Nat}:
  match b:
    case True{}:
      Equal.sym(Nat, S.choose(n, k), 0n, choose_eq_zero(n, k, hb))
    case False{}:
      +m = Nat.min(k, Nat.sub(n, k))
      %Equal.sym(Nat, 1n, S.choose(n, 0n), Equal.sym(Nat, S.choose(n, 0n), 1n, choose_zero_right(n))) : {M.comb_go(m, n, 0n, _) == S.choose(n, k) : Nat}
      Equal.trans(Nat, M.comb_go(m, n, 0n, S.choose(n, 0n)), S.choose(n, m), S.choose(n, k), comb_go(m, n, 0n), comb_min(n, k, N.not_lt_le(n, k, hb), Nat.is_lt(k, Nat.sub(n, k)), {==}))

# comb(n, k) == C(n, k)
def comb_ok(+n: Nat, +k: Nat) -> {M.comb(n, k) == S.choose(n, k) : Nat}:
  comb_small(n, k, Nat.is_lt(n, k), {==})
