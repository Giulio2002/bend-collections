import Base
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../../math/natural/modpow.bend as MP

# Congruence mod p = 1 + pp: ceq(pp, a, b) is a mod p == b mod p.

def ceq(+pp: Nat, +a: Nat, +b: Nat) -> Data:
  {Nat.mod(a, 1n+pp) == Nat.mod(b, 1n+pp) : Nat}

def c_refl(+pp: Nat, +a: Nat) -> ceq(pp, a, a):
  {==}

def c_sym(+pp: Nat, +a: Nat, +b: Nat, +h: ceq(pp, a, b)) -> ceq(pp, b, a):
  Equal.sym(Nat, Nat.mod(a, 1n+pp), Nat.mod(b, 1n+pp), h)

def c_trans(+pp: Nat, +a: Nat, +b: Nat, +c: Nat, +h1: ceq(pp, a, b), +h2: ceq(pp, b, c)) -> ceq(pp, a, c):
  Equal.trans(Nat, Nat.mod(a, 1n+pp), Nat.mod(b, 1n+pp), Nat.mod(c, 1n+pp), h1, h2)

def c_eq(+pp: Nat, +a: Nat, +b: Nat, +e: {a == b : Nat}) -> ceq(pp, a, b):
  Equal.cong(Nat, Nat, t => Nat.mod(t, 1n+pp), a, b, e)

# the reduced value is congruent to the value
def c_mod(+pp: Nat, +a: Nat) -> ceq(pp, Nat.mod(a, 1n+pp), a):
  NR.mod_mod(pp, a)

def c_add(+pp: Nat, +a: Nat, +a2: Nat, +b: Nat, +b2: Nat, +ha: ceq(pp, a, a2), +hb: ceq(pp, b, b2)) -> ceq(pp, Nat.add(a, b), Nat.add(a2, b2)):
  +n = {1n+pp : Nat}
  +e1 = Equal.sym(Nat, Nat.mod(Nat.add(Nat.mod(a, n), b), n), Nat.mod(Nat.add(a, b), n), NR.mod_add_l(pp, a, b))
  +e2 = Equal.cong(Nat, Nat, t => Nat.mod(Nat.add(t, b), n), Nat.mod(a, n), Nat.mod(a2, n), ha)
  +e3 = NR.mod_add_l(pp, a2, b)
  +e4 = Equal.sym(Nat, Nat.mod(Nat.add(a2, Nat.mod(b, n)), n), Nat.mod(Nat.add(a2, b), n), NR.mod_add_r(pp, a2, b))
  +e5 = Equal.cong(Nat, Nat, t => Nat.mod(Nat.add(a2, t), n), Nat.mod(b, n), Nat.mod(b2, n), hb)
  +e6 = NR.mod_add_r(pp, a2, b2)
  Equal.trans(Nat, Nat.mod(Nat.add(a, b), n), Nat.mod(Nat.add(Nat.mod(a, n), b), n), Nat.mod(Nat.add(a2, b2), n), e1,
    Equal.trans(Nat, Nat.mod(Nat.add(Nat.mod(a, n), b), n), Nat.mod(Nat.add(Nat.mod(a2, n), b), n), Nat.mod(Nat.add(a2, b2), n), e2,
      Equal.trans(Nat, Nat.mod(Nat.add(Nat.mod(a2, n), b), n), Nat.mod(Nat.add(a2, b), n), Nat.mod(Nat.add(a2, b2), n), e3,
        Equal.trans(Nat, Nat.mod(Nat.add(a2, b), n), Nat.mod(Nat.add(a2, Nat.mod(b, n)), n), Nat.mod(Nat.add(a2, b2), n), e4,
          Equal.trans(Nat, Nat.mod(Nat.add(a2, Nat.mod(b, n)), n), Nat.mod(Nat.add(a2, Nat.mod(b2, n)), n), Nat.mod(Nat.add(a2, b2), n), e5, e6)))))

def c_mul(+pp: Nat, +a: Nat, +a2: Nat, +b: Nat, +b2: Nat, +ha: ceq(pp, a, a2), +hb: ceq(pp, b, b2)) -> ceq(pp, Nat.mul(a, b), Nat.mul(a2, b2)):
  +n = {1n+pp : Nat}
  +e1 = Equal.sym(Nat, Nat.mod(Nat.mul(Nat.mod(a, n), b), n), Nat.mod(Nat.mul(a, b), n), NR.mod_mul_l(pp, a, b))
  +e2 = Equal.cong(Nat, Nat, t => Nat.mod(Nat.mul(t, b), n), Nat.mod(a, n), Nat.mod(a2, n), ha)
  +e3 = NR.mod_mul_l(pp, a2, b)
  +e4 = Equal.sym(Nat, Nat.mod(Nat.mul(a2, Nat.mod(b, n)), n), Nat.mod(Nat.mul(a2, b), n), NR.mod_mul_r(pp, a2, b))
  +e5 = Equal.cong(Nat, Nat, t => Nat.mod(Nat.mul(a2, t), n), Nat.mod(b, n), Nat.mod(b2, n), hb)
  +e6 = NR.mod_mul_r(pp, a2, b2)
  Equal.trans(Nat, Nat.mod(Nat.mul(a, b), n), Nat.mod(Nat.mul(Nat.mod(a, n), b), n), Nat.mod(Nat.mul(a2, b2), n), e1,
    Equal.trans(Nat, Nat.mod(Nat.mul(Nat.mod(a, n), b), n), Nat.mod(Nat.mul(Nat.mod(a2, n), b), n), Nat.mod(Nat.mul(a2, b2), n), e2,
      Equal.trans(Nat, Nat.mod(Nat.mul(Nat.mod(a2, n), b), n), Nat.mod(Nat.mul(a2, b), n), Nat.mod(Nat.mul(a2, b2), n), e3,
        Equal.trans(Nat, Nat.mod(Nat.mul(a2, b), n), Nat.mod(Nat.mul(a2, Nat.mod(b, n)), n), Nat.mod(Nat.mul(a2, b2), n), e4,
          Equal.trans(Nat, Nat.mod(Nat.mul(a2, Nat.mod(b, n)), n), Nat.mod(Nat.mul(a2, Nat.mod(b2, n)), n), Nat.mod(Nat.mul(a2, b2), n), e5, e6)))))

def c_pow(+pp: Nat, +a: Nat, +a2: Nat, +k: Nat, +ha: ceq(pp, a, a2)) -> ceq(pp, Nat.pow(a, k), Nat.pow(a2, k)):
  +n = {1n+pp : Nat}
  +e1 = Equal.sym(Nat, Nat.mod(Nat.pow(Nat.mod(a, n), k), n), Nat.mod(Nat.pow(a, k), n), MP.mod_pow(pp, a, k))
  +e2 = Equal.cong(Nat, Nat, t => Nat.mod(Nat.pow(t, k), n), Nat.mod(a, n), Nat.mod(a2, n), ha)
  Equal.trans(Nat, Nat.mod(Nat.pow(a, k), n), Nat.mod(Nat.pow(Nat.mod(a, n), k), n), Nat.mod(Nat.pow(a2, k), n), e1, Equal.trans(Nat, Nat.mod(Nat.pow(Nat.mod(a, n), k), n), Nat.mod(Nat.pow(Nat.mod(a2, n), k), n), Nat.mod(Nat.pow(a2, k), n), e2, MP.mod_pow(pp, a2, k)))

# ---- power algebra ----

def pow_one_base(+k: Nat) -> {Nat.pow(1n, k) == 1n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +q:
      +e = pow_one_base(q)
      %Equal.sym(Nat, Nat.pow(1n, q), 1n, e) : {Nat.mul(1n, _) == 1n : Nat}
      {==}

def pow_pow(+x: Nat, +a: Nat, +b: Nat) -> {Nat.pow(Nat.pow(x, a), b) == Nat.pow(x, Nat.mul(a, b)) : Nat}:
  match b:
    case 0n:
      %Equal.sym(Nat, Nat.mul(a, 0n), 0n, NA.mul_zero(a)) : {1n == Nat.pow(x, _) : Nat}
      {==}
    case 1n+ +q:
      +ih = pow_pow(x, a, q)
      +e1 = Equal.cong(Nat, Nat, t => Nat.mul(Nat.pow(x, a), t), Nat.pow(Nat.pow(x, a), q), Nat.pow(x, Nat.mul(a, q)), ih)
      +e2 = Equal.sym(Nat, Nat.pow(x, Nat.add(a, Nat.mul(a, q))), Nat.mul(Nat.pow(x, a), Nat.pow(x, Nat.mul(a, q))), NR.pow_add(x, a, Nat.mul(a, q)))
      +e3 = Equal.cong(Nat, Nat, t => Nat.pow(x, t), Nat.add(a, Nat.mul(a, q)), Nat.mul(a, 1n+q), Equal.sym(Nat, Nat.mul(a, 1n+q), Nat.add(a, Nat.mul(a, q)), NA.mul_succ(a, q)))
      Equal.trans(Nat, Nat.mul(Nat.pow(x, a), Nat.pow(Nat.pow(x, a), q)), Nat.mul(Nat.pow(x, a), Nat.pow(x, Nat.mul(a, q))), Nat.pow(x, Nat.mul(a, 1n+q)), e1, Equal.trans(Nat, Nat.mul(Nat.pow(x, a), Nat.pow(x, Nat.mul(a, q))), Nat.pow(x, Nat.add(a, Nat.mul(a, q))), Nat.pow(x, Nat.mul(a, 1n+q)), e2, e3))

def cancel_r(+a: Nat, +b: Nat, +c: Nat, +e: {Nat.add(a, c) == Nat.add(b, c) : Nat}) -> {a == b : Nat}:
  NR.add_cancel(c, a, b, Equal.trans(Nat, Nat.add(c, a), Nat.add(a, c), Nat.add(c, b), NA.add_comm(c, a), Equal.trans(Nat, Nat.add(a, c), Nat.add(b, c), Nat.add(c, b), e, NA.add_comm(b, c))))
