import Base
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/x25519.bend as SX
import ../../../spec/crypto/curve25519/edwards.bend as G
import ../../../spec/crypto/ed25519.bend as SE
import ../../../spec/crypto/ed25519_group.bend as EG
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../../math/number/nt_prime.bend as PM
import ../curve25519/cong.bend as CG
import ../fe/eqarith.bend as EA
import ../secp256k1/semiring.bend as SR
import ./group/idm.bend as IM
import ./group/fq.bend as FQ
import ./group/glaw.bend as GL
import ./group/ext.bend as GX

# Every point the specification's decoding returns (RFC 8032 5.1.3) is a
# valid point of the curve, and so is the base point (the decoding of
# y = 4/5): v x^2 == u with u = y^2 - 1, v = d y^2 + 1 is the curve equation
# y^2 - x^2 == 1 + d x^2 y^2, the other root x sqrt(-1) when v x^2 == -u,
# and the sign choice -x keeps x^2.

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

# ---- congruences ----

def mod_self(+mp: Nat) -> {Nat.mod(1n+mp, 1n+mp) == 0n : Nat}:
  L.subst(Nat, z => {Nat.mod(z, 1n+mp) == 0n : Nat}, Nat.add(Nat.mul(1n, 1n+mp), 0n), 1n+mp, IM.s1(1n+mp), NR.mod_of(1n, mp, 0n, {==}))

# a + p == a
def add_p(+mp: Nat, +a: Nat) -> CG.ceq(mp, Nat.add(a, 1n+mp), a):
  +P = {1n+mp : Nat}
  tr(Nat.mod(Nat.add(a, P), P), Nat.mod(Nat.add(a, Nat.mod(P, P)), P), Nat.mod(a, P), sy(Nat.mod(Nat.add(a, Nat.mod(P, P)), P), Nat.mod(Nat.add(a, P), P), NR.mod_add_r(mp, a, P)), tr(Nat.mod(Nat.add(a, Nat.mod(P, P)), P), Nat.mod(Nat.add(a, 0n), P), Nat.mod(a, P), Equal.cong(Nat, Nat, z => Nat.mod(Nat.add(a, z), P), Nat.mod(P, P), 0n, mod_self(mp)), Equal.cong(Nat, Nat, z => Nat.mod(z, P), Nat.add(a, 0n), a, N.add_zero(a))))

# (a - b) + b == a
def sub_add(+mp: Nat, +a: Nat, +b: Nat) -> CG.ceq(mp, Nat.add(FS.fsub(1n+mp, a, b), b), a):
  +P = {1n+mp : Nat}
  +m = Nat.mod(b, P)
  +S = EA.pw(mp, a, m)
  CG.c_trans(mp, Nat.add(Nat.mod(S, P), b), Nat.add(S, m), a, CG.c_add(mp, Nat.mod(S, P), S, b, m, CG.c_mod(mp, S), CG.c_sym(mp, m, b, CG.c_mod(mp, b))), CG.c_trans(mp, Nat.add(S, m), Nat.add(a, P), a, CG.c_eq(mp, Nat.add(S, m), Nat.add(a, P), EA.w_eq(mp, a, m, NR.dm_lt(mp, b))), add_p(mp, a)))

def cm(+mp: Nat, +a: Nat, +b: Nat) -> CG.ceq(mp, FS.fmul(1n+mp, a, b), Nat.mul(a, b)):
  CG.c_mod(mp, Nat.mul(a, b))

def ca(+mp: Nat, +a: Nat, +b: Nat) -> CG.ceq(mp, FS.fadd(1n+mp, a, b), Nat.add(a, b)):
  CG.c_mod(mp, Nat.add(a, b))

# ---- the curve equation from the decoder's test ----

# (d yy + 1) xx == yy - 1, for xx = x^2 and yy = y^2
def DH(+mp: Nat, +d: Nat, +xx: Nat, +yy: Nat) -> Data:
  {FS.fmul(1n+mp, FS.fadd(1n+mp, FS.fmul(1n+mp, d, yy), 1n), xx) == FS.fsub(1n+mp, yy, 1n) : Nat}

# yy - xx == 1 + d xx yy
def curve_sq(+mp: Nat, +d: Nat, +xx: Nat, +yy: Nat, +h: DH(mp, d, xx, yy)) -> {FS.fsub(1n+mp, yy, xx) == FS.fadd(1n+mp, 1n, FS.fmul(1n+mp, d, FS.fmul(1n+mp, xx, yy))) : Nat}:
  +P = {1n+mp : Nat}
  +T = FS.fmul(P, d, FS.fmul(P, xx, yy))
  +A = Nat.mul(d, Nat.mul(xx, yy))
  +V = FS.fadd(P, FS.fmul(P, d, yy), 1n)
  +W = Nat.add(Nat.mul(d, yy), 1n)
  +U = FS.fsub(P, yy, 1n)
  +cT = CG.c_trans(mp, T, Nat.mul(d, FS.fmul(P, xx, yy)), A, cm(mp, d, FS.fmul(P, xx, yy)), CG.c_mul(mp, d, d, FS.fmul(P, xx, yy), Nat.mul(xx, yy), CG.c_refl(mp, d), cm(mp, xx, yy)))
  +r1 = CG.c_add(mp, FS.fadd(P, 1n, T), Nat.add(1n, A), xx, xx, CG.c_trans(mp, FS.fadd(P, 1n, T), Nat.add(1n, T), Nat.add(1n, A), ca(mp, 1n, T), CG.c_add(mp, 1n, 1n, T, A, CG.c_refl(mp, 1n), cT)), CG.c_refl(mp, xx))
  +eW = tr(Nat.mul(W, xx), Nat.add(Nat.mul(Nat.mul(d, yy), xx), Nat.mul(1n, xx)), Nat.add(A, xx), NA.mul_add_right(Nat.mul(d, yy), 1n, xx), Equal.trans(Nat, Nat.add(Nat.mul(Nat.mul(d, yy), xx), Nat.mul(1n, xx)), Nat.add(A, Nat.mul(1n, xx)), Nat.add(A, xx), Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(1n, xx)), Nat.mul(Nat.mul(d, yy), xx), A, tr(Nat.mul(Nat.mul(d, yy), xx), Nat.mul(d, Nat.mul(yy, xx)), A, NA.mul_assoc(d, yy, xx), Equal.cong(Nat, Nat, z => Nat.mul(d, z), Nat.mul(yy, xx), Nat.mul(xx, yy), NA.mul_comm(yy, xx)))), Equal.cong(Nat, Nat, z => Nat.add(A, z), Nat.mul(1n, xx), xx, SR.one_mul(xx))))
  +e2 = sy(Nat.add(Nat.mul(W, xx), 1n), Nat.add(Nat.add(1n, A), xx), tr(Nat.add(Nat.mul(W, xx), 1n), Nat.add(Nat.add(A, xx), 1n), Nat.add(Nat.add(1n, A), xx), Equal.cong(Nat, Nat, z => Nat.add(z, 1n), Nat.mul(W, xx), Nat.add(A, xx), eW), NA.add_comm(Nat.add(A, xx), 1n)))
  +cV = CG.c_trans(mp, V, Nat.add(FS.fmul(P, d, yy), 1n), W, ca(mp, FS.fmul(P, d, yy), 1n), CG.c_add(mp, FS.fmul(P, d, yy), Nat.mul(d, yy), 1n, 1n, cm(mp, d, yy), CG.c_refl(mp, 1n)))
  +cVx = CG.c_trans(mp, FS.fmul(P, V, xx), Nat.mul(V, xx), Nat.mul(W, xx), cm(mp, V, xx), CG.c_mul(mp, V, W, xx, xx, cV, CG.c_refl(mp, xx)))
  +r3 = CG.c_add(mp, Nat.mul(W, xx), FS.fmul(P, V, xx), 1n, 1n, CG.c_sym(mp, FS.fmul(P, V, xx), Nat.mul(W, xx), cVx), CG.c_refl(mp, 1n))
  +r4 = CG.c_eq(mp, Nat.add(FS.fmul(P, V, xx), 1n), Nat.add(U, 1n), Equal.cong(Nat, Nat, z => Nat.add(z, 1n), FS.fmul(P, V, xx), U, h))
  +r5 = sub_add(mp, yy, 1n)
  +R0 = Nat.add(FS.fadd(P, 1n, T), xx)
  +R1 = Nat.add(Nat.add(1n, A), xx)
  +R2 = Nat.add(Nat.mul(W, xx), 1n)
  +R3 = Nat.add(FS.fmul(P, V, xx), 1n)
  +R4 = Nat.add(U, 1n)
  +right = CG.c_trans(mp, R0, R1, yy, r1, CG.c_trans(mp, R1, R2, yy, CG.c_eq(mp, R1, R2, e2), CG.c_trans(mp, R2, R3, yy, r3, CG.c_trans(mp, R3, R4, yy, r4, r5))))
  +L0 = Nat.add(FS.fsub(P, yy, xx), xx)
  FQ.red_eq(mp, FS.fsub(P, yy, xx), FS.fadd(P, 1n, T), FQ.fsub_red(mp, yy, xx), FQ.fadd_red(mp, 1n, T), CG.c_cancel(mp, FS.fsub(P, yy, xx), FS.fadd(P, 1n, T), xx, CG.c_trans(mp, L0, yy, R0, sub_add(mp, yy, xx), CG.c_sym(mp, R0, yy, right))))

# (-x)^2 == x^2
def neg_sq(+mp: Nat, +x: Nat) -> {FS.fmul(1n+mp, FS.fsub(1n+mp, 0n, x), FS.fsub(1n+mp, 0n, x)) == FS.fmul(1n+mp, x, x) : Nat}:
  +P = {1n+mp : Nat}
  +n = FS.fsub(P, 0n, x)
  +z1 = sub_add(mp, 0n, x)
  +z2 = CG.c_trans(mp, Nat.add(x, n), Nat.add(n, x), 0n, CG.c_eq(mp, Nat.add(x, n), Nat.add(n, x), NA.add_comm(x, n)), z1)
  +A1 = CG.c_trans(mp, Nat.add(Nat.mul(n, n), Nat.mul(n, x)), Nat.mul(n, Nat.add(n, x)), 0n, CG.c_eq(mp, Nat.add(Nat.mul(n, n), Nat.mul(n, x)), Nat.mul(n, Nat.add(n, x)), sy(Nat.mul(n, Nat.add(n, x)), Nat.add(Nat.mul(n, n), Nat.mul(n, x)), NA.mul_add_left(n, n, x))), CG.c_trans(mp, Nat.mul(n, Nat.add(n, x)), Nat.mul(n, 0n), 0n, CG.c_mul(mp, n, n, Nat.add(n, x), 0n, CG.c_refl(mp, n), z1), CG.c_eq(mp, Nat.mul(n, 0n), 0n, NA.mul_zero(n))))
  +A2 = CG.c_trans(mp, Nat.add(Nat.mul(x, x), Nat.mul(n, x)), Nat.mul(Nat.add(x, n), x), 0n, CG.c_eq(mp, Nat.add(Nat.mul(x, x), Nat.mul(n, x)), Nat.mul(Nat.add(x, n), x), sy(Nat.mul(Nat.add(x, n), x), Nat.add(Nat.mul(x, x), Nat.mul(n, x)), NA.mul_add_right(x, n, x))), CG.c_mul(mp, Nat.add(x, n), 0n, x, x, z2, CG.c_refl(mp, x)))
  CG.c_cancel(mp, Nat.mul(n, n), Nat.mul(x, x), Nat.mul(n, x), CG.c_trans(mp, Nat.add(Nat.mul(n, n), Nat.mul(n, x)), 0n, Nat.add(Nat.mul(x, x), Nat.mul(n, x)), A1, CG.c_sym(mp, Nat.add(Nat.mul(x, x), Nat.mul(n, x)), 0n, A2)))

# the other root: v x^2 == -u gives v (x i)^2 == u, for i^2 == -1
def sq_i(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +x: Nat, +yy: Nat, +hn: {FS.fmul(1n+mp, FS.fadd(1n+mp, FS.fmul(1n+mp, d, yy), 1n), FS.fmul(1n+mp, x, x)) == FS.fsub(1n+mp, 0n, FS.fsub(1n+mp, yy, 1n)) : Nat}) -> DH(mp, d, FS.fmul(1n+mp, FS.fmul(1n+mp, x, G.sqm1(1n+mp)), FS.fmul(1n+mp, x, G.sqm1(1n+mp))), yy):
  +P = {1n+mp : Nat}
  +s = G.sqm1(P)
  +V = FS.fadd(P, FS.fmul(P, d, yy), 1n)
  +U = FS.fsub(P, yy, 1n)
  +xx = FS.fmul(P, x, x)
  +ss = FS.fmul(P, s, s)
  +x1 = FS.fmul(P, x, s)
  +xx1 = FS.fmul(P, x1, x1)
  +w = FS.fmul(P, V, xx)
  +k1 = CG.c_trans(mp, xx1, Nat.mul(x1, x1), Nat.mul(xx, ss), cm(mp, x1, x1), CG.c_trans(mp, Nat.mul(x1, x1), Nat.mul(Nat.mul(x, s), Nat.mul(x, s)), Nat.mul(xx, ss), CG.c_mul(mp, x1, Nat.mul(x, s), x1, Nat.mul(x, s), cm(mp, x, s), cm(mp, x, s)), CG.c_trans(mp, Nat.mul(Nat.mul(x, s), Nat.mul(x, s)), Nat.mul(Nat.mul(x, x), Nat.mul(s, s)), Nat.mul(xx, ss), CG.c_eq(mp, Nat.mul(Nat.mul(x, s), Nat.mul(x, s)), Nat.mul(Nat.mul(x, x), Nat.mul(s, s)), NR.mul_swap4(x, s, x, s)), CG.c_mul(mp, Nat.mul(x, x), xx, Nat.mul(s, s), ss, CG.c_sym(mp, xx, Nat.mul(x, x), cm(mp, x, x)), CG.c_sym(mp, ss, Nat.mul(s, s), cm(mp, s, s))))))
  +k2 = CG.c_trans(mp, FS.fmul(P, V, xx1), Nat.mul(V, xx1), Nat.mul(w, ss), cm(mp, V, xx1), CG.c_trans(mp, Nat.mul(V, xx1), Nat.mul(V, Nat.mul(xx, ss)), Nat.mul(w, ss), CG.c_mul(mp, V, V, xx1, Nat.mul(xx, ss), CG.c_refl(mp, V), k1), CG.c_trans(mp, Nat.mul(V, Nat.mul(xx, ss)), Nat.mul(Nat.mul(V, xx), ss), Nat.mul(w, ss), CG.c_eq(mp, Nat.mul(V, Nat.mul(xx, ss)), Nat.mul(Nat.mul(V, xx), ss), sy(Nat.mul(Nat.mul(V, xx), ss), Nat.mul(V, Nat.mul(xx, ss)), NA.mul_assoc(V, xx, ss))), CG.c_mul(mp, Nat.mul(V, xx), w, ss, ss, CG.c_sym(mp, w, Nat.mul(V, xx), cm(mp, V, xx)), CG.c_refl(mp, ss)))))
  +e3 = tr(Nat.add(Nat.mul(w, ss), w), Nat.add(Nat.mul(w, ss), Nat.mul(w, 1n)), Nat.mul(w, Nat.add(ss, 1n)), Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(w, ss), z), w, Nat.mul(w, 1n), sy(Nat.mul(w, 1n), w, NA.mul_one(w))), sy(Nat.mul(w, Nat.add(ss, 1n)), Nat.add(Nat.mul(w, ss), Nat.mul(w, 1n)), NA.mul_add_left(w, ss, 1n)))
  +k3 = CG.c_trans(mp, Nat.add(Nat.mul(w, ss), w), Nat.mul(w, Nat.add(ss, 1n)), 0n, CG.c_eq(mp, Nat.add(Nat.mul(w, ss), w), Nat.mul(w, Nat.add(ss, 1n)), e3), CG.c_trans(mp, Nat.mul(w, Nat.add(ss, 1n)), Nat.mul(w, FS.fadd(P, ss, 1n)), 0n, CG.c_mul(mp, w, w, Nat.add(ss, 1n), FS.fadd(P, ss, 1n), CG.c_refl(mp, w), CG.c_sym(mp, FS.fadd(P, ss, 1n), Nat.add(ss, 1n), ca(mp, ss, 1n))), CG.c_eq(mp, Nat.mul(w, FS.fadd(P, ss, 1n)), 0n, tr(Nat.mul(w, FS.fadd(P, ss, 1n)), Nat.mul(w, 0n), 0n, Equal.cong(Nat, Nat, z => Nat.mul(w, z), FS.fadd(P, ss, 1n), 0n, FQ.cv_i(mp, d, hc)), NA.mul_zero(w)))))
  +nu = FS.fsub(P, 0n, U)
  +k4 = CG.c_trans(mp, Nat.add(U, w), Nat.add(nu, U), 0n, CG.c_eq(mp, Nat.add(U, w), Nat.add(nu, U), tr(Nat.add(U, w), Nat.add(U, nu), Nat.add(nu, U), Equal.cong(Nat, Nat, z => Nat.add(U, z), w, nu, hn), NA.add_comm(U, nu))), sub_add(mp, 0n, U))
  +k5 = CG.c_cancel(mp, Nat.mul(w, ss), U, w, CG.c_trans(mp, Nat.add(Nat.mul(w, ss), w), 0n, Nat.add(U, w), k3, CG.c_sym(mp, Nat.add(U, w), 0n, k4)))
  FQ.red_eq(mp, FS.fmul(P, V, xx1), U, FQ.fmul_red(mp, V, xx1), FQ.fsub_red(mp, yy, 1n), CG.c_trans(mp, FS.fmul(P, V, xx1), Nat.mul(w, ss), U, k2, k5))

# ---- the decoded point is valid ----

# a / 1 == a mod p
def qd1(+mp: Nat, +hp: PM.Prime(1n+mp), +a: Nat) -> {GX.qd(mp, a, 1n) == Nat.mod(a, 1n+mp) : Nat}:
  +P = {1n+mp : Nat}
  +m = Nat.mod(a, P)
  +e = tr(FS.fmul(P, m, 1n), Nat.mod(m, P), m, Equal.cong(Nat, Nat, z => Nat.mod(z, P), Nat.mul(m, 1n), m, NA.mul_one(m)), NR.mod_mod(mp, a))
  FQ.frac_val(mp, hp, a, 1n, m, GX.nz_one(mp, hp), NR.dm_lt(mp, a), sy(Nat.mod(FS.fmul(P, m, 1n), P), m, tr(Nat.mod(FS.fmul(P, m, 1n), P), Nat.mod(m, P), m, Equal.cong(Nat, Nat, z => Nat.mod(z, P), FS.fmul(P, m, 1n), m, e), NR.mod_mod(mp, a))))

# (x mod p)^2 == x^2
def sq_mod(+mp: Nat, +x: Nat) -> {FS.fmul(1n+mp, Nat.mod(x, 1n+mp), Nat.mod(x, 1n+mp)) == FS.fmul(1n+mp, x, x) : Nat}:
  +P = {1n+mp : Nat}
  +m = Nat.mod(x, P)
  tr(Nat.mod(Nat.mul(m, m), P), Nat.mod(Nat.mul(x, m), P), Nat.mod(Nat.mul(x, x), P), NR.mod_mul_l(mp, x, m), NR.mod_mul_r(mp, x, x))

# (x : y : 1 : x y) with the decoder's test on x^2 and y^2
def valid_xy(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +x: Nat, +y: Nat, +h: DH(mp, d, FS.fmul(1n+mp, x, x), FS.fmul(1n+mp, y, y))) -> EG.Valid(1n+mp, d, SE.EPt{x, y, 1n, FS.fmul(1n+mp, x, y)}):
  +P = {1n+mp : Nat}
  +hp = FQ.cv_prime(mp, d, hc)
  +mx = Nat.mod(x, P)
  +my = Nat.mod(y, P)
  +xx = FS.fmul(P, x, x)
  +yy = FS.fmul(P, y, y)
  +e0 = curve_sq(mp, d, xx, yy, h)
  +e1 = L.subst(Nat, z => {FS.fsub(P, z, xx) == FS.fadd(P, 1n, FS.fmul(P, d, FS.fmul(P, xx, z))) : Nat}, yy, FS.fmul(P, my, my), sy(FS.fmul(P, my, my), yy, sq_mod(mp, y)), e0)
  +e2 = L.subst(Nat, z => {FS.fsub(P, FS.fmul(P, my, my), z) == FS.fadd(P, 1n, FS.fmul(P, d, FS.fmul(P, z, FS.fmul(P, my, my)))) : Nat}, xx, FS.fmul(P, mx, mx), sy(FS.fmul(P, mx, mx), xx, sq_mod(mp, x)), e1)
  +e3 = L.subst(Nat, z => GL.Eq(mp, d, mx, z), my, GX.qd(mp, y, 1n), sy(GX.qd(mp, y, 1n), my, qd1(mp, hp, y)), e2)
  +he = L.subst(Nat, z => GL.Eq(mp, d, z, GX.qd(mp, y, 1n)), mx, GX.qd(mp, x, 1n), sy(GX.qd(mp, x, 1n), mx, qd1(mp, hp, x)), e3)
  +w = FS.fmul(P, x, y)
  +ht = tr(FS.fmul(P, w, 1n), Nat.mod(w, P), w, Equal.cong(Nat, Nat, z => Nat.mod(z, P), Nat.mul(w, 1n), w, NA.mul_one(w)), FQ.fmul_red(mp, x, y))
  GX.v_in(mp, d, x, y, 1n, w, GX.nz_one(mp, hp), he, ht)

# the sign choice: x or -x
def sel_valid(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +s: Nat, +x: Nat, +y: Nat, +h: DH(mp, d, FS.fmul(1n+mp, x, x), FS.fmul(1n+mp, y, y))) -> EG.Valid(1n+mp, d, SE.EPt{SX.cs_fst(s, x, FS.fsub(1n+mp, 0n, x)), y, 1n, FS.fmul(1n+mp, SX.cs_fst(s, x, FS.fsub(1n+mp, 0n, x)), y)}):
  match s:
    case 0n:
      valid_xy(mp, d, hc, x, y, h)
    case 1n+q:
      +P = {1n+mp : Nat}
      +n = FS.fsub(P, 0n, x)
      valid_xy(mp, d, hc, n, y, L.subst(Nat, z => DH(mp, d, z, FS.fmul(P, y, y)), FS.fmul(P, x, x), FS.fmul(P, n, n), sy(FS.fmul(P, n, n), FS.fmul(P, x, x), neg_sq(mp, x)), h))

def fin_valid(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +x: Nat, +y: Nat, +x0: Nat, +fail: Bool, +h: DH(mp, d, FS.fmul(1n+mp, x, x), FS.fmul(1n+mp, y, y))) -> EG.Valid(1n+mp, d, SE.base_of(SE.dec_fin(1n+mp, x, y, x0, fail))):
  match fail:
    case True{}:
      GX.id_valid(mp, d, hc)
    case False{}:
      sel_valid(mp, d, hc, SX.bxor(Nat.mod(x, 2n), x0), x, y, h)

def root_valid(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +x: Nat, +y: Nat, +x0: Nat, +b1: Bool, +b2: Bool, hu: @+e: {b1 == True{} : Bool} -> DH(mp, d, FS.fmul(1n+mp, x, x), FS.fmul(1n+mp, y, y)), hn: @+e: {b2 == True{} : Bool} -> {FS.fmul(1n+mp, FS.fadd(1n+mp, FS.fmul(1n+mp, d, FS.fmul(1n+mp, y, y)), 1n), FS.fmul(1n+mp, x, x)) == FS.fsub(1n+mp, 0n, FS.fsub(1n+mp, FS.fmul(1n+mp, y, y), 1n)) : Nat}) -> EG.Valid(1n+mp, d, SE.base_of(SE.dec_root(1n+mp, x, y, x0, b1, b2))):
  match b1:
    case True{}:
      fin_valid(mp, d, hc, x, y, x0, Bool.and(Nat.is_eq(x, 0n), Nat.is_eq(x0, 1n)), hu({==}))
    case False{}:
      match b2:
        case True{}:
          +x1 = FS.fmul(1n+mp, x, SE.sqm1(1n+mp))
          fin_valid(mp, d, hc, x1, y, x0, Bool.and(Nat.is_eq(x1, 0n), Nat.is_eq(x0, 1n)), sq_i(mp, d, hc, x, FS.fmul(1n+mp, y, y), hn({==})))
        case False{}:
          GX.id_valid(mp, d, hc)

def y_valid(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +y: Nat, +x0: Nat, +bad: Bool) -> EG.Valid(1n+mp, d, SE.base_of(SE.dec_y(1n+mp, d, y, x0, bad))):
  match bad:
    case True{}:
      GX.id_valid(mp, d, hc)
    case False{}:
      +P = {1n+mp : Nat}
      +yy = FS.fmul(P, y, y)
      +u = FS.fsub(P, yy, 1n)
      +v = FS.fadd(P, FS.fmul(P, d, yy), 1n)
      +v3 = FS.fmul(P, FS.fmul(P, v, v), v)
      +v7 = FS.fmul(P, FS.fmul(P, v3, v3), v)
      +x = FS.fmul(P, FS.fmul(P, u, v3), FS.fpow(P, FS.fmul(P, u, v7), Nat.div(Nat.sub(P, 5n), 8n)))
      +vxx = FS.fmul(P, v, FS.fmul(P, x, x))
      root_valid(mp, d, hc, x, y, x0, Nat.is_eq(vxx, u), Nat.is_eq(vxx, FS.fsub(P, 0n, u)), e => N.eq_from_is_eq(vxx, u, e), e => N.eq_from_is_eq(vxx, FS.fsub(P, 0n, u), e))

# whatever the bytes: the decoded point, or the identity when there is none
def decode_valid(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +bs: List<&2, U32>) -> EG.Valid(1n+mp, d, SE.base_of(SE.decode(1n+mp, d, bs))):
  y_valid(mp, d, hc, FS.value(SX.mask_last(bs)), SX.kbit(FS.value(bs), 255n), Bool.not(Nat.is_lt(FS.value(SX.mask_last(bs)), 1n+mp)))

# the base point
def base_valid(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d)) -> EG.Valid(1n+mp, d, SE.base(1n+mp, d)):
  decode_valid(mp, d, hc, SX.le_bytes(32n, FS.fmul(1n+mp, 4n, FS.finv(1n+mp, 5n))))
