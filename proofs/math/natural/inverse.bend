import Base
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as A
import ../../../src/math/natural.bend as M
import ./arith.bend as R
import ./gcd.bend as G
import ./lcm.bend as LC

# mod_inverse(a, m) (Python pow(a, -1, m)): a Done{x} result is an inverse,
# a * x == 1 (mod m) with x < m, and a NotInvertible result comes with a
# common divisor g >= 2 of a and m. The invariant is the extended-Euclid
# Bezout relation a s_i == r_i (mod m) (Lean 4 Mathlib
# Mathlib/Data/Int/GCD: Nat.gcdA / Nat.gcd_eq_gcd_ab; ZMod.inv_coe_unit and
# Nat.Coprime), kept here with the coefficient reduced mod m so everything
# stays in the naturals; the remainders are Euclid's, so the final one
# divides a and m (Nat.gcd_dvd_left/right, as in gcd.bend).

def bg(bz: M.Bezout) -> Nat:
  match bz:
    case M.BZ{g, s}:
      g

def bc(bz: M.Bezout) -> Nat:
  match bz:
    case M.BZ{g, s}:
      s

# ---- congruence steps mod m = 1+mp ----

def cong_add_r(+mp: Nat, +x: Nat, +y: Nat, +y2: Nat, +e: {Nat.mod(y, 1n+mp) == Nat.mod(y2, 1n+mp) : Nat}) -> {Nat.mod(Nat.add(x, y), 1n+mp) == Nat.mod(Nat.add(x, y2), 1n+mp) : Nat}:
  Equal.trans(Nat, Nat.mod(Nat.add(x, y), 1n+mp), Nat.mod(Nat.add(x, Nat.mod(y, 1n+mp)), 1n+mp), Nat.mod(Nat.add(x, y2), 1n+mp), Equal.sym(Nat, Nat.mod(Nat.add(x, Nat.mod(y, 1n+mp)), 1n+mp), Nat.mod(Nat.add(x, y), 1n+mp), R.mod_add_r(mp, x, y)),
    Equal.trans(Nat, Nat.mod(Nat.add(x, Nat.mod(y, 1n+mp)), 1n+mp), Nat.mod(Nat.add(x, Nat.mod(y2, 1n+mp)), 1n+mp), Nat.mod(Nat.add(x, y2), 1n+mp), Equal.cong(Nat, Nat, z => Nat.mod(Nat.add(x, z), 1n+mp), Nat.mod(y, 1n+mp), Nat.mod(y2, 1n+mp), e), R.mod_add_r(mp, x, y2)))

def cong_mul_r(+mp: Nat, +x: Nat, +y: Nat, +y2: Nat, +e: {Nat.mod(y, 1n+mp) == Nat.mod(y2, 1n+mp) : Nat}) -> {Nat.mod(Nat.mul(x, y), 1n+mp) == Nat.mod(Nat.mul(x, y2), 1n+mp) : Nat}:
  Equal.trans(Nat, Nat.mod(Nat.mul(x, y), 1n+mp), Nat.mod(Nat.mul(x, Nat.mod(y, 1n+mp)), 1n+mp), Nat.mod(Nat.mul(x, y2), 1n+mp), Equal.sym(Nat, Nat.mod(Nat.mul(x, Nat.mod(y, 1n+mp)), 1n+mp), Nat.mod(Nat.mul(x, y), 1n+mp), R.mod_mul_r(mp, x, y)),
    Equal.trans(Nat, Nat.mod(Nat.mul(x, Nat.mod(y, 1n+mp)), 1n+mp), Nat.mod(Nat.mul(x, Nat.mod(y2, 1n+mp)), 1n+mp), Nat.mod(Nat.mul(x, y2), 1n+mp), Equal.cong(Nat, Nat, z => Nat.mod(Nat.mul(x, z), 1n+mp), Nat.mod(y, 1n+mp), Nat.mod(y2, 1n+mp), e), R.mod_mul_r(mp, x, y2)))

# (z + c) + k == M + z when c + k == M
def shift(+z: Nat, +c: Nat, +k: Nat, +mm: Nat, +e: {Nat.add(c, k) == mm : Nat}) -> {Nat.add(Nat.add(z, c), k) == Nat.add(mm, z) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(z, c), k), Nat.add(z, Nat.add(c, k)), Nat.add(mm, z), A.add_assoc(z, c, k), Equal.trans(Nat, Nat.add(z, Nat.add(c, k)), Nat.add(z, mm), Nat.add(mm, z), Equal.cong(Nat, Nat, w => Nat.add(z, w), Nat.add(c, k), mm, e), A.add_comm(z, mm)))

# x + c == y + c (mod m) gives x == y (mod m): add m - (c mod m) to both
def add_cancel_mod(+mp: Nat, +x: Nat, +y: Nat, +c: Nat, +e: {Nat.mod(Nat.add(x, c), 1n+mp) == Nat.mod(Nat.add(y, c), 1n+mp) : Nat}) -> {Nat.mod(x, 1n+mp) == Nat.mod(y, 1n+mp) : Nat}:
  +m = {1n+mp : Nat}
  +qc = Nat.div(c, m)
  +rc = Nat.mod(c, m)
  +k = Nat.sub(m, rc)
  # c + k == (qc + 1) m
  +eck = Equal.trans(Nat, Nat.add(c, k), Nat.add(Nat.add(Nat.mul(qc, m), rc), k), Nat.mul(1n+qc, m),
    Equal.cong(Nat, Nat, z => Nat.add(z, k), c, Nat.add(Nat.mul(qc, m), rc), R.dm_eq(mp, c)),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(qc, m), rc), k), Nat.add(Nat.mul(qc, m), Nat.add(rc, k)), Nat.mul(1n+qc, m), A.add_assoc(Nat.mul(qc, m), rc, k),
      Equal.trans(Nat, Nat.add(Nat.mul(qc, m), Nat.add(rc, k)), Nat.add(Nat.mul(qc, m), m), Nat.mul(1n+qc, m), Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(qc, m), z), Nat.add(rc, k), m, N.sub_add(m, rc, N.lt_le(rc, m, R.dm_lt(mp, c)))),
        Equal.sym(Nat, Nat.mul(1n+qc, m), Nat.add(Nat.mul(qc, m), m), A.add_comm(m, Nat.mul(qc, m))))))
  # z + c + k == (qc + 1) m + z, so its residue is z's
  +ex = Equal.trans(Nat, Nat.mod(Nat.add(Nat.add(x, c), k), m), Nat.mod(Nat.add(Nat.mul(1n+qc, m), x), m), Nat.mod(x, m), Equal.cong(Nat, Nat, z => Nat.mod(z, m), Nat.add(Nat.add(x, c), k), Nat.add(Nat.mul(1n+qc, m), x), shift(x, c, k, Nat.mul(1n+qc, m), eck)), R.absorb(mp, 1n+qc, x))
  +ey = Equal.trans(Nat, Nat.mod(Nat.add(Nat.add(y, c), k), m), Nat.mod(Nat.add(Nat.mul(1n+qc, m), y), m), Nat.mod(y, m), Equal.cong(Nat, Nat, z => Nat.mod(z, m), Nat.add(Nat.add(y, c), k), Nat.add(Nat.mul(1n+qc, m), y), shift(y, c, k, Nat.mul(1n+qc, m), eck)), R.absorb(mp, 1n+qc, y))
  +exy = Equal.trans(Nat, Nat.mod(Nat.add(Nat.add(x, c), k), m), Nat.mod(Nat.add(Nat.add(y, c), k), m), Nat.mod(y, m),
    Equal.trans(Nat, Nat.mod(Nat.add(Nat.add(x, c), k), m), Nat.mod(Nat.add(Nat.mod(Nat.add(x, c), m), k), m), Nat.mod(Nat.add(Nat.add(y, c), k), m), Equal.sym(Nat, Nat.mod(Nat.add(Nat.mod(Nat.add(x, c), m), k), m), Nat.mod(Nat.add(Nat.add(x, c), k), m), R.mod_add_l(mp, Nat.add(x, c), k)),
      Equal.trans(Nat, Nat.mod(Nat.add(Nat.mod(Nat.add(x, c), m), k), m), Nat.mod(Nat.add(Nat.mod(Nat.add(y, c), m), k), m), Nat.mod(Nat.add(Nat.add(y, c), k), m), Equal.cong(Nat, Nat, z => Nat.mod(Nat.add(z, k), m), Nat.mod(Nat.add(x, c), m), Nat.mod(Nat.add(y, c), m), e), R.mod_add_l(mp, Nat.add(y, c), k))), ey)
  Equal.trans(Nat, Nat.mod(x, m), Nat.mod(Nat.add(Nat.add(x, c), k), m), Nat.mod(y, m), Equal.sym(Nat, Nat.mod(Nat.add(Nat.add(x, c), k), m), Nat.mod(x, m), ex), exy)

# ---- the Bezout invariant a s_i == r_i (mod m) ----

# u + t == m for t < m, u = m - t
def sub_plus(+m: Nat, +t: Nat, +h: {Nat.is_lt(t, m) == True{} : Bool}) -> {Nat.add(Nat.sub(m, t), t) == m : Nat}:
  Equal.trans(Nat, Nat.add(Nat.sub(m, t), t), Nat.add(t, Nat.sub(m, t)), m, A.add_comm(Nat.sub(m, t), t), N.sub_add(m, t, N.lt_le(t, m, h)))

# one extended-Euclid step keeps the invariant
def inv_step_ok(+mp: Nat, +a: Nat, +r0: Nat, +s0: Nat, +rp: Nat, +s1: Nat, +h0: {Nat.mod(Nat.mul(a, s0), 1n+mp) == Nat.mod(r0, 1n+mp) : Nat}, +h1: {Nat.mod(Nat.mul(a, s1), 1n+mp) == Nat.mod(1n+rp, 1n+mp) : Nat}) -> {Nat.mod(Nat.mul(a, M.inv_step(1n+mp, Nat.div(r0, 1n+rp), s0, s1)), 1n+mp) == Nat.mod(Nat.mod(r0, 1n+rp), 1n+mp) : Nat}:
  +m = {1n+mp : Nat}
  +r1 = {1n+rp : Nat}
  +q = Nat.div(r0, r1)
  +r = Nat.mod(r0, r1)
  +t = Nat.mod(Nat.mul(q, s1), m)
  +u = Nat.sub(m, t)
  +x = Nat.mul(a, Nat.add(s0, u))
  +c = Nat.mul(q, r1)
  +e1 = R.mod_mul_r(mp, a, Nat.add(s0, u))
  # c == a t (mod m)
  +ec = Equal.trans(Nat, Nat.mod(c, m), Nat.mod(Nat.mul(q, Nat.mul(a, s1)), m), Nat.mod(Nat.mul(a, t), m), cong_mul_r(mp, q, r1, Nat.mul(a, s1), Equal.sym(Nat, Nat.mod(Nat.mul(a, s1), m), Nat.mod(r1, m), h1)),
    Equal.trans(Nat, Nat.mod(Nat.mul(q, Nat.mul(a, s1)), m), Nat.mod(Nat.mul(a, Nat.mul(q, s1)), m), Nat.mod(Nat.mul(a, t), m), Equal.cong(Nat, Nat, z => Nat.mod(z, m), Nat.mul(q, Nat.mul(a, s1)), Nat.mul(a, Nat.mul(q, s1)), LC.swap_cw(q, a, s1)), Equal.sym(Nat, Nat.mod(Nat.mul(a, t), m), Nat.mod(Nat.mul(a, Nat.mul(q, s1)), m), R.mod_mul_r(mp, a, Nat.mul(q, s1)))))
  # x + a t == a s0 + a m
  +ex = Equal.trans(Nat, Nat.add(x, Nat.mul(a, t)), Nat.add(Nat.add(Nat.mul(a, s0), Nat.mul(a, u)), Nat.mul(a, t)), Nat.add(Nat.mul(a, m), Nat.mul(a, s0)),
    Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(a, t)), x, Nat.add(Nat.mul(a, s0), Nat.mul(a, u)), A.mul_add_left(a, s0, u)),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(a, s0), Nat.mul(a, u)), Nat.mul(a, t)), Nat.add(Nat.mul(a, s0), Nat.add(Nat.mul(a, u), Nat.mul(a, t))), Nat.add(Nat.mul(a, m), Nat.mul(a, s0)), A.add_assoc(Nat.mul(a, s0), Nat.mul(a, u), Nat.mul(a, t)),
      Equal.trans(Nat, Nat.add(Nat.mul(a, s0), Nat.add(Nat.mul(a, u), Nat.mul(a, t))), Nat.add(Nat.mul(a, s0), Nat.mul(a, m)), Nat.add(Nat.mul(a, m), Nat.mul(a, s0)),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(a, s0), z), Nat.add(Nat.mul(a, u), Nat.mul(a, t)), Nat.mul(a, m), Equal.trans(Nat, Nat.add(Nat.mul(a, u), Nat.mul(a, t)), Nat.mul(a, Nat.add(u, t)), Nat.mul(a, m), Equal.sym(Nat, Nat.mul(a, Nat.add(u, t)), Nat.add(Nat.mul(a, u), Nat.mul(a, t)), A.mul_add_left(a, u, t)), Equal.cong(Nat, Nat, z => Nat.mul(a, z), Nat.add(u, t), m, sub_plus(m, t, R.dm_lt(mp, Nat.mul(q, s1)))))),
        A.add_comm(Nat.mul(a, s0), Nat.mul(a, m)))))
  # x + c == r + c (mod m), both == r0
  +exc = Equal.trans(Nat, Nat.mod(Nat.add(x, c), m), Nat.mod(Nat.add(x, Nat.mul(a, t)), m), Nat.mod(r0, m), cong_add_r(mp, x, c, Nat.mul(a, t), ec),
    Equal.trans(Nat, Nat.mod(Nat.add(x, Nat.mul(a, t)), m), Nat.mod(Nat.add(Nat.mul(a, m), Nat.mul(a, s0)), m), Nat.mod(r0, m), Equal.cong(Nat, Nat, z => Nat.mod(z, m), Nat.add(x, Nat.mul(a, t)), Nat.add(Nat.mul(a, m), Nat.mul(a, s0)), ex),
      Equal.trans(Nat, Nat.mod(Nat.add(Nat.mul(a, m), Nat.mul(a, s0)), m), Nat.mod(Nat.mul(a, s0), m), Nat.mod(r0, m), R.absorb(mp, a, Nat.mul(a, s0)), h0)))
  +erc = Equal.cong(Nat, Nat, z => Nat.mod(z, m), Nat.add(r, c), r0, Equal.trans(Nat, Nat.add(r, c), Nat.add(c, r), r0, A.add_comm(r, c), Equal.sym(Nat, r0, Nat.add(c, r), R.dm_eq(rp, r0))))
  Equal.trans(Nat, Nat.mod(Nat.mul(a, M.inv_step(m, q, s0, s1)), m), Nat.mod(x, m), Nat.mod(r, m), e1, add_cancel_mod(mp, x, r, c, Equal.trans(Nat, Nat.mod(Nat.add(x, c), m), Nat.mod(r0, m), Nat.mod(Nat.add(r, c), m), exc, Equal.sym(Nat, Nat.mod(Nat.add(r, c), m), Nat.mod(r0, m), erc))))

def inv_inv(fuel: Nat, +mp: Nat, +a: Nat, +r0: Nat, +s0: Nat, +r1: Nat, +s1: Nat, +h0: {Nat.mod(Nat.mul(a, s0), 1n+mp) == Nat.mod(r0, 1n+mp) : Nat}, +h1: {Nat.mod(Nat.mul(a, s1), 1n+mp) == Nat.mod(r1, 1n+mp) : Nat}) -> {Nat.mod(Nat.mul(a, bc(M.inv_go(fuel, 1n+mp, r0, s0, r1, s1))), 1n+mp) == Nat.mod(bg(M.inv_go(fuel, 1n+mp, r0, s0, r1, s1)), 1n+mp) : Nat}:
  match fuel r1:
    case 0n 0n:
      h0
    case 0n 1n+rp:
      h0
    case 1n+f 0n:
      h0
    case 1n+ +f 1n+ +rp:
      inv_inv(f, mp, a, 1n+rp, s1, Nat.mod(r0, 1n+rp), M.inv_step(1n+mp, Nat.div(r0, 1n+rp), s0, s1), h1, inv_step_ok(mp, a, r0, s0, rp, s1, h0, h1))

# the remainders are Euclid's
def inv_r(fuel: Nat, +m: Nat, +r0: Nat, +s0: Nat, +r1: Nat, +s1: Nat) -> {bg(M.inv_go(fuel, m, r0, s0, r1, s1)) == M.gcd_go(fuel, r0, r1) : Nat}:
  match fuel r1:
    case 0n 0n:
      {==}
    case 0n 1n+rp:
      {==}
    case 1n+f 0n:
      {==}
    case 1n+ +f 1n+ +rp:
      inv_r(f, m, 1n+rp, s1, Nat.mod(r0, 1n+rp), M.inv_step(m, Nat.div(r0, 1n+rp), s0, s1))

# ---- the theorems ----

def unwrap(r: Result<&2, &2, M.MathError, Nat>) -> Nat:
  match r:
    case Done{v}:
      v
    case Fail{e}:
      0n

def is_done(r: Result<&2, &2, M.MathError, Nat>) -> Bool:
  match r:
    case Done{v}:
      True{}
    case Fail{e}:
      False{}

def mod_self(+mp: Nat) -> {Nat.mod(1n+mp, 1n+mp) == 0n : Nat}:
  %Equal.sym(Nat, 1n+mp, Nat.add(Nat.mul(1n, 1n+mp), 0n), Equal.trans(Nat, 1n+mp, Nat.mul(1n, 1n+mp), Nat.add(Nat.mul(1n, 1n+mp), 0n), Equal.sym(Nat, Nat.mul(1n, 1n+mp), 1n+mp, LC.one_mul(1n+mp)), Equal.sym(Nat, Nat.add(Nat.mul(1n, 1n+mp), 0n), Nat.mul(1n, 1n+mp), A.add_zero(Nat.mul(1n, 1n+mp))))) : {Nat.mod(_, 1n+mp) == 0n : Nat}
  R.mod_of(1n, mp, 0n, {==})

# the extended-Euclid state mod_inverse(a, m) ends in
def inv_bz(+a: Nat, +mp: Nat) -> M.Bezout:
  M.inv_go(1n+mp, 1n+mp, 1n+mp, 0n, Nat.mod(a, 1n+mp), 1n)

def inv_bezout(+a: Nat, +mp: Nat) -> {Nat.mod(Nat.mul(a, bc(inv_bz(a, mp))), 1n+mp) == Nat.mod(bg(inv_bz(a, mp)), 1n+mp) : Nat}:
  +m = {1n+mp : Nat}
  +h0 = Equal.trans(Nat, Nat.mod(Nat.mul(a, 0n), m), 0n, Nat.mod(m, m), Equal.cong(Nat, Nat, z => Nat.mod(z, m), Nat.mul(a, 0n), 0n, A.mul_zero(a)), Equal.sym(Nat, Nat.mod(m, m), 0n, mod_self(mp)))
  +h1 = Equal.trans(Nat, Nat.mod(Nat.mul(a, 1n), m), Nat.mod(a, m), Nat.mod(Nat.mod(a, m), m), Equal.cong(Nat, Nat, z => Nat.mod(z, m), Nat.mul(a, 1n), a, A.mul_one(a)), Equal.sym(Nat, Nat.mod(Nat.mod(a, m), m), Nat.mod(a, m), R.mod_mod(mp, a)))
  inv_inv(m, mp, a, m, 0n, Nat.mod(a, m), 1n, h0, h1)

# the final remainder divides m and a
def inv_km(+a: Nat, +mp: Nat) -> Nat:
  G.wl(G.ws(1n+mp, 1n+mp, Nat.mod(a, 1n+mp)))

def inv_ka(+a: Nat, +mp: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.div(a, 1n+mp), inv_km(a, mp)), G.wr(G.ws(1n+mp, 1n+mp, Nat.mod(a, 1n+mp))))

def inv_dvd_m(+a: Nat, +mp: Nat) -> {1n+mp == Nat.mul(inv_km(a, mp), bg(inv_bz(a, mp))) : Nat}:
  +m = {1n+mp : Nat}
  +g = M.gcd_go(m, m, Nat.mod(a, m))
  %Equal.sym(Nat, bg(inv_bz(a, mp)), g, inv_r(m, m, m, 0n, Nat.mod(a, m), 1n)) : {m == Nat.mul(inv_km(a, mp), _) : Nat}
  G.both_l(m, Nat.mod(a, m), g, G.ws(m, m, Nat.mod(a, m)), G.gcd_both(m, m, Nat.mod(a, m), N.lt_le(Nat.mod(a, m), m, R.dm_lt(mp, a))))

def inv_dvd_a2(+a: Nat, +mp: Nat, +g: Nat, +w: G.Wit, p: G.divides_both(1n+mp, Nat.mod(a, 1n+mp), g, w)) -> {a == Nat.mul(Nat.add(Nat.mul(Nat.div(a, 1n+mp), G.wl(w)), G.wr(w)), g) : Nat}:
  (en, er) = p
  G.dvd_of_mod(mp, a, g, G.wl(w), G.wr(w), en, er)

def inv_dvd_a(+a: Nat, +mp: Nat) -> {a == Nat.mul(inv_ka(a, mp), bg(inv_bz(a, mp))) : Nat}:
  +m = {1n+mp : Nat}
  +g = M.gcd_go(m, m, Nat.mod(a, m))
  +w = G.ws(m, m, Nat.mod(a, m))
  %Equal.sym(Nat, bg(inv_bz(a, mp)), g, inv_r(m, m, m, 0n, Nat.mod(a, m), 1n)) : {a == Nat.mul(inv_ka(a, mp), _) : Nat}
  inv_dvd_a2(a, mp, g, w, G.gcd_both(m, m, Nat.mod(a, m), N.lt_le(Nat.mod(a, m), m, R.dm_lt(mp, a))))

def done_bz(+mp: Nat, +a: Nat, +bz: M.Bezout, +hinv: {Nat.mod(Nat.mul(a, bc(bz)), 1n+mp) == Nat.mod(bg(bz), 1n+mp) : Nat}, +x: Nat, +h: {M.inv_fin(1n+mp, bz) == Done{x} : Result<&2, &2, M.MathError, Nat>}) -> {Nat.mod(Nat.mul(a, x), 1n+mp) == Nat.mod(1n, 1n+mp) : Nat} & {Nat.is_lt(x, 1n+mp) == True{} : Bool}:
  match bz:
    case M.BZ{0n, +s}:
      Empty.absurd({Nat.mod(Nat.mul(a, x), 1n+mp) == Nat.mod(1n, 1n+mp) : Nat} & {Nat.is_lt(x, 1n+mp) == True{} : Bool}, L.false_true(Equal.cong(Result<&2, &2, M.MathError, Nat>, Bool, is_done, Fail{M.NotInvertible{}}, Done{x}, h)))
    case M.BZ{1n, +s}:
      +ex = Equal.cong(Result<&2, &2, M.MathError, Nat>, Nat, unwrap, Done{Nat.mod(s, 1n+mp)}, Done{x}, h)
      %Equal.sym(Nat, x, Nat.mod(s, 1n+mp), Equal.sym(Nat, Nat.mod(s, 1n+mp), x, ex)) : {Nat.mod(Nat.mul(a, _), 1n+mp) == Nat.mod(1n, 1n+mp) : Nat} & {Nat.is_lt(_, 1n+mp) == True{} : Bool}
      (Equal.trans(Nat, Nat.mod(Nat.mul(a, Nat.mod(s, 1n+mp)), 1n+mp), Nat.mod(Nat.mul(a, s), 1n+mp), Nat.mod(1n, 1n+mp), R.mod_mul_r(mp, a, s), hinv), R.dm_lt(mp, s))
    case M.BZ{2n+gg, +s}:
      Empty.absurd({Nat.mod(Nat.mul(a, x), 1n+mp) == Nat.mod(1n, 1n+mp) : Nat} & {Nat.is_lt(x, 1n+mp) == True{} : Bool}, L.false_true(Equal.cong(Result<&2, &2, M.MathError, Nat>, Bool, is_done, Fail{M.NotInvertible{}}, Done{x}, h)))

# mod_inverse(a, m) == Done{x}: a x == 1 (mod m) and x < m   (Mathlib ZMod.mul_inv_of_unit)
def inverse_done(+a: Nat, +mp: Nat, +x: Nat, +h: {M.mod_inverse(a, 1n+mp) == Done{x} : Result<&2, &2, M.MathError, Nat>}) -> {Nat.mod(Nat.mul(a, x), 1n+mp) == Nat.mod(1n, 1n+mp) : Nat} & {Nat.is_lt(x, 1n+mp) == True{} : Bool}:
  done_bz(mp, a, inv_bz(a, mp), inv_bezout(a, mp), x, h)

def fail_bz(+mp: Nat, +bz: M.Bezout, +km: Nat, +em: {1n+mp == Nat.mul(km, bg(bz)) : Nat}, +h: {M.inv_fin(1n+mp, bz) == Fail{M.NotInvertible{}} : Result<&2, &2, M.MathError, Nat>}) -> {Nat.is_le(2n, bg(bz)) == True{} : Bool}:
  match bz:
    case M.BZ{0n, s}:
      Empty.absurd({Nat.is_le(2n, 0n) == True{} : Bool}, L.false_true(LC.gcd_pos(mp, km, 0n, em)))
    case M.BZ{1n, s}:
      Empty.absurd({Nat.is_le(2n, 1n) == True{} : Bool}, L.false_true(Equal.sym(Bool, True{}, False{}, Equal.cong(Result<&2, &2, M.MathError, Nat>, Bool, is_done, Done{Nat.mod(s, 1n+mp)}, Fail{M.NotInvertible{}}, h))))
    case M.BZ{2n+ +gg, s}:
      N.le_add_right(2n, gg)

# mod_inverse(a, m) == Fail{NotInvertible}: g >= 2 divides a and m, so a
# and m are not coprime   (Mathlib Nat.Coprime, ZMod.unitOfCoprime)
def inverse_fail(+a: Nat, +mp: Nat, +h: {M.mod_inverse(a, 1n+mp) == Fail{M.NotInvertible{}} : Result<&2, &2, M.MathError, Nat>}) -> {Nat.is_le(2n, bg(inv_bz(a, mp))) == True{} : Bool} & ({a == Nat.mul(inv_ka(a, mp), bg(inv_bz(a, mp))) : Nat} & {1n+mp == Nat.mul(inv_km(a, mp), bg(inv_bz(a, mp))) : Nat}):
  (fail_bz(mp, inv_bz(a, mp), inv_km(a, mp), inv_dvd_m(a, mp), h), (inv_dvd_a(a, mp), inv_dvd_m(a, mp)))

def inverse_zero(+a: Nat) -> {M.mod_inverse(a, 0n) == Fail{M.ZeroDivision{}} : Result<&2, &2, M.MathError, Nat>}:
  {==}
