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

# (z + m) + t == k + z when m + t == k
def shift3(+z: Nat, +m: Nat, +t: Nat, +k: Nat, +e: {Nat.add(m, t) == k : Nat}) -> {Nat.add(Nat.add(z, m), t) == Nat.add(k, z) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(z, m), t), Nat.add(z, Nat.add(m, t)), Nat.add(k, z), NA.add_assoc(z, m, t), Equal.trans(Nat, Nat.add(z, Nat.add(m, t)), Nat.add(z, k), Nat.add(k, z), Equal.cong(Nat, Nat, w => Nat.add(z, w), Nat.add(m, t), k, e), NA.add_comm(z, k)))

# X + m == Y + m (mod p) -> X == Y (mod p): add p - (m mod p) to both
def c_cancel(+pp: Nat, +X: Nat, +Y: Nat, +m: Nat, +h: ceq(pp, Nat.add(X, m), Nat.add(Y, m))) -> ceq(pp, X, Y):
  +P = {1n+pp : Nat}
  +q = Nat.div(m, P)
  +r = Nat.mod(m, P)
  +t = Nat.sub(P, r)
  +hm = NR.dm_eq(pp, m)
  +hrt = N.sub_add(P, r, N.lt_le(r, P, NR.dm_lt(pp, m)))
  +k = Nat.add(Nat.mul(q, P), P)
  +hk = Equal.trans(Nat, Nat.add(m, t), Nat.add(Nat.add(Nat.mul(q, P), r), t), k, Equal.cong(Nat, Nat, z => Nat.add(z, t), m, Nat.add(Nat.mul(q, P), r), hm), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(q, P), r), t), Nat.add(Nat.mul(q, P), Nat.add(r, t)), k, NA.add_assoc(Nat.mul(q, P), r, t), Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(q, P), z), Nat.add(r, t), P, hrt)))
  +hk2 = Equal.trans(Nat, Nat.add(m, t), k, Nat.mul(1n+q, P), hk, NA.add_comm(Nat.mul(q, P), P))
  +ex = c_trans(pp, X, Nat.add(Nat.mul(1n+q, P), X), Nat.add(Nat.add(X, m), t), c_sym(pp, Nat.add(Nat.mul(1n+q, P), X), X, NR.absorb(pp, 1n+q, X)), c_eq(pp, Nat.add(Nat.mul(1n+q, P), X), Nat.add(Nat.add(X, m), t), Equal.sym(Nat, Nat.add(Nat.add(X, m), t), Nat.add(Nat.mul(1n+q, P), X), shift3(X, m, t, Nat.mul(1n+q, P), hk2))))
  +ey = c_trans(pp, Nat.add(Nat.add(Y, m), t), Nat.add(Nat.mul(1n+q, P), Y), Y, c_eq(pp, Nat.add(Nat.add(Y, m), t), Nat.add(Nat.mul(1n+q, P), Y), shift3(Y, m, t, Nat.mul(1n+q, P), hk2)), NR.absorb(pp, 1n+q, Y))
  c_trans(pp, X, Nat.add(Nat.add(X, m), t), Y, ex, c_trans(pp, Nat.add(Nat.add(X, m), t), Nat.add(Nat.add(Y, m), t), Y, c_add(pp, Nat.add(X, m), Nat.add(Y, m), t, t, h, c_refl(pp, t)), ey))

def le_add_l(+a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(b, z) == True{} : Bool}, Nat.add(b, a), Nat.add(a, b), NA.add_comm(b, a), N.le_add_right(b, a))

# (X + p) - m == (Y + p) - m (mod p) for X == Y (mod p) and m <= p
def c_subm(+pp: Nat, +X: Nat, +Y: Nat, +m: Nat, +h: ceq(pp, X, Y), +hm: {Nat.is_le(m, 1n+pp) == True{} : Bool}) -> ceq(pp, Nat.sub(Nat.add(X, 1n+pp), m), Nat.sub(Nat.add(Y, 1n+pp), m)):
  +P = {1n+pp : Nat}
  +X2 = Nat.sub(Nat.add(X, P), m)
  +Y2 = Nat.sub(Nat.add(Y, P), m)
  +mx = N.le_trans(m, P, Nat.add(X, P), hm, le_add_l(X, P))
  +my = N.le_trans(m, P, Nat.add(Y, P), hm, le_add_l(Y, P))
  +ex = Equal.trans(Nat, Nat.add(X2, m), Nat.add(m, X2), Nat.add(X, P), NA.add_comm(X2, m), N.sub_add(Nat.add(X, P), m, mx))
  +ey = Equal.trans(Nat, Nat.add(Y2, m), Nat.add(m, Y2), Nat.add(Y, P), NA.add_comm(Y2, m), N.sub_add(Nat.add(Y, P), m, my))
  +e = c_trans(pp, Nat.add(X2, m), Nat.add(X, P), Nat.add(Y2, m), c_eq(pp, Nat.add(X2, m), Nat.add(X, P), ex), c_trans(pp, Nat.add(X, P), Nat.add(Y, P), Nat.add(Y2, m), c_add(pp, X, Y, P, P, h, c_refl(pp, P)), c_eq(pp, Nat.add(Y, P), Nat.add(Y2, m), Equal.sym(Nat, Nat.add(Y2, m), Nat.add(Y, P), ey))))
  c_cancel(pp, X2, Y2, m, e)
