import Base
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as A
import ../../../src/math/natural.bend as M
import ./arith.bend as R
import ./gcd.bend as G

# lcm is the least common multiple (Lean 4 Mathlib, Mathlib/Data/Nat/GCD:
# Nat.dvd_lcm_left, Nat.dvd_lcm_right, Nat.gcd_mul_lcm, Nat.lcm_dvd; the
# leastness goes through Nat.gcd_mul_left and dvd antisymmetry,
# Nat.dvd_antisymm). Divisibility again carries its witness.

# ---- divisibility is antisymmetric ----

def add_succ_zero(+b: Nat, +x: Nat, +e: {Nat.add(b, 1n+x) == 0n : Nat}) -> Empty:
  N.succ_zero(Nat.add(b, x), Equal.trans(Nat, 1n+Nat.add(b, x), Nat.add(b, 1n+x), 0n, Equal.sym(Nat, Nat.add(b, 1n+x), 1n+Nat.add(b, x), A.add_succ(b, x)), e))

def one_s(+ap: Nat, +bq: Nat, +e: {Nat.add(bq, Nat.mul(ap, 1n+bq)) == 0n : Nat}) -> {1n+ap == 1n : Nat}:
  match ap:
    case 0n:
      {==}
    case 1n+ +app:
      Empty.absurd({2n+app == 1n : Nat}, add_succ_zero(bq, Nat.add(bq, Nat.mul(app, 1n+bq)), e))

# a b == 1 gives a == 1   (Mathlib Nat.eq_one_of_mul_eq_one_right)
def mul_eq_one(+a: Nat, +b: Nat, +e: {Nat.mul(a, b) == 1n : Nat}) -> {a == 1n : Nat}:
  match a b:
    case 0n b0:
      Empty.absurd({0n == 1n : Nat}, N.zero_succ(0n, e))
    case 1n+ +ap 0n:
      Empty.absurd({1n+ap == 1n : Nat}, N.zero_succ(0n, Equal.trans(Nat, 0n, Nat.mul(1n+ap, 0n), 1n, Equal.sym(Nat, Nat.mul(1n+ap, 0n), 0n, A.mul_zero(1n+ap)), e)))
    case 1n+ +ap 1n+ +bq:
      one_s(ap, bq, N.succ_inj(Nat.add(bq, Nat.mul(ap, 1n+bq)), 0n, e))

def one_mul(+d: Nat) -> {Nat.mul(1n, d) == d : Nat}:
  A.add_zero(d)

# x == kx y and y == ky x give x == y   (Mathlib Nat.dvd_antisymm)
def dvd_antisymm(+x: Nat, +y: Nat, +kx: Nat, +ky: Nat, +ex: {x == Nat.mul(kx, y) : Nat}, +ey: {y == Nat.mul(ky, x) : Nat}) -> {x == y : Nat}:
  match x:
    case 0n:
      Equal.sym(Nat, y, 0n, Equal.trans(Nat, y, Nat.mul(ky, 0n), 0n, ey, A.mul_zero(ky)))
    case 1n+ +xp:
      +e1 = Equal.trans(Nat, Nat.mul(Nat.mul(kx, ky), 1n+xp), Nat.mul(kx, Nat.mul(ky, 1n+xp)), Nat.mul(1n, 1n+xp),
        A.mul_assoc(kx, ky, 1n+xp),
        Equal.trans(Nat, Nat.mul(kx, Nat.mul(ky, 1n+xp)), Nat.mul(kx, y), Nat.mul(1n, 1n+xp),
          Equal.cong(Nat, Nat, z => Nat.mul(kx, z), Nat.mul(ky, 1n+xp), y, Equal.sym(Nat, y, Nat.mul(ky, 1n+xp), ey)),
          Equal.trans(Nat, Nat.mul(kx, y), 1n+xp, Nat.mul(1n, 1n+xp), Equal.sym(Nat, 1n+xp, Nat.mul(kx, y), ex), Equal.sym(Nat, Nat.mul(1n, 1n+xp), 1n+xp, one_mul(1n+xp)))))
      +k1 = mul_eq_one(kx, ky, R.mul_cancel(Nat.mul(kx, ky), 1n, xp, e1))
      Equal.trans(Nat, 1n+xp, Nat.mul(kx, y), y, ex, Equal.trans(Nat, Nat.mul(kx, y), Nat.mul(1n, y), y, Equal.cong(Nat, Nat, z => Nat.mul(z, y), kx, 1n, k1), one_mul(y)))

# c (w g) == w (c g)
def swap_cw(+c: Nat, +w: Nat, +g: Nat) -> {Nat.mul(c, Nat.mul(w, g)) == Nat.mul(w, Nat.mul(c, g)) : Nat}:
  Equal.trans(Nat, Nat.mul(c, Nat.mul(w, g)), Nat.mul(Nat.mul(c, w), g), Nat.mul(w, Nat.mul(c, g)),
    Equal.sym(Nat, Nat.mul(Nat.mul(c, w), g), Nat.mul(c, Nat.mul(w, g)), A.mul_assoc(c, w, g)),
    Equal.trans(Nat, Nat.mul(Nat.mul(c, w), g), Nat.mul(Nat.mul(w, c), g), Nat.mul(w, Nat.mul(c, g)),
      Equal.cong(Nat, Nat, z => Nat.mul(z, g), Nat.mul(c, w), Nat.mul(w, c), A.mul_comm(c, w)),
      A.mul_assoc(w, c, g)))

# x == w g gives c x == w (c g)
def scale_dvd(+c: Nat, +x: Nat, +w: Nat, +g: Nat, +e: {x == Nat.mul(w, g) : Nat}) -> {Nat.mul(c, x) == Nat.mul(w, Nat.mul(c, g)) : Nat}:
  Equal.trans(Nat, Nat.mul(c, x), Nat.mul(c, Nat.mul(w, g)), Nat.mul(w, Nat.mul(c, g)), Equal.cong(Nat, Nat, z => Nat.mul(c, z), x, Nat.mul(w, g), e), swap_cw(c, w, g))

# c x == w (h c) gives x == w h (c > 0)
def unscale(+cp: Nat, +x: Nat, +w: Nat, +h: Nat, +e: {Nat.mul(1n+cp, x) == Nat.mul(w, Nat.mul(h, 1n+cp)) : Nat}) -> {x == Nat.mul(w, h) : Nat}:
  R.mul_cancel(x, Nat.mul(w, h), cp, Equal.trans(Nat, Nat.mul(x, 1n+cp), Nat.mul(1n+cp, x), Nat.mul(Nat.mul(w, h), 1n+cp), A.mul_comm(x, 1n+cp), Equal.trans(Nat, Nat.mul(1n+cp, x), Nat.mul(w, Nat.mul(h, 1n+cp)), Nat.mul(Nat.mul(w, h), 1n+cp), e, Equal.sym(Nat, Nat.mul(Nat.mul(w, h), 1n+cp), Nat.mul(w, Nat.mul(h, 1n+cp)), A.mul_assoc(w, h, 1n+cp)))))

def gcd_mul_pos(+cp: Nat, +a: Nat, +b: Nat) -> {M.gcd(Nat.mul(1n+cp, a), Nat.mul(1n+cp, b)) == Nat.mul(1n+cp, M.gcd(a, b)) : Nat}:
  +c = {1n+cp : Nat}
  +ca = Nat.mul(c, a)
  +cb = Nat.mul(c, b)
  +g = M.gcd(a, b)
  +gc = M.gcd(ca, cb)
  +la = G.wl(G.ws(b, a, b))
  +lb = G.wr(G.ws(b, a, b))
  # c g divides gc
  +eu = G.dvd_gcd(ca, cb, Nat.mul(c, g), la, lb, scale_dvd(c, a, la, g, G.gcd_dvd_left(a, b)), scale_dvd(c, b, lb, g, G.gcd_dvd_right(a, b)))
  # c divides gc: gc == h c
  +eh = G.dvd_gcd(ca, cb, c, a, b, A.mul_comm(c, a), A.mul_comm(c, b))
  +h = G.dw(cb, ca, cb, a, b)
  # gc == h c divides c a and c b, so h divides a and b
  +ma = G.wl(G.ws(cb, ca, cb))
  +mb = G.wr(G.ws(cb, ca, cb))
  +ea2 = unscale(cp, a, ma, h, Equal.trans(Nat, ca, Nat.mul(ma, gc), Nat.mul(ma, Nat.mul(h, c)), G.gcd_dvd_left(ca, cb), Equal.cong(Nat, Nat, z => Nat.mul(ma, z), gc, Nat.mul(h, c), eh)))
  +eb2 = unscale(cp, b, mb, h, Equal.trans(Nat, cb, Nat.mul(mb, gc), Nat.mul(mb, Nat.mul(h, c)), G.gcd_dvd_right(ca, cb), Equal.cong(Nat, Nat, z => Nat.mul(mb, z), gc, Nat.mul(h, c), eh)))
  # so h divides g: g == v h, and c g == v (h c) == v gc
  +ev = G.dvd_gcd(a, b, h, ma, mb, ea2, eb2)
  +v = G.dw(b, a, b, ma, mb)
  +ecg = Equal.trans(Nat, Nat.mul(c, g), Nat.mul(v, Nat.mul(c, h)), Nat.mul(v, gc), scale_dvd(c, g, v, h, ev),
    Equal.cong(Nat, Nat, z => Nat.mul(v, z), Nat.mul(c, h), gc, Equal.trans(Nat, Nat.mul(c, h), Nat.mul(h, c), gc, A.mul_comm(c, h), Equal.sym(Nat, gc, Nat.mul(h, c), eh))))
  dvd_antisymm(gc, Nat.mul(c, g), G.dw(cb, ca, cb, la, lb), v, eu, ecg)

# gcd(c a, c b) == c gcd(a, b)   (Mathlib Nat.gcd_mul_left)
def gcd_mul_left(+c: Nat, +a: Nat, +b: Nat) -> {M.gcd(Nat.mul(c, a), Nat.mul(c, b)) == Nat.mul(c, M.gcd(a, b)) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+ +cp:
      gcd_mul_pos(cp, a, b)

# ---- lcm of positive a, b is (a / g) b ----

# a == la g with a > 0 makes g positive
def gcd_pos(+ap: Nat, +l: Nat, +g: Nat, +e: {1n+ap == Nat.mul(l, g) : Nat}) -> {Nat.is_lt(0n, g) == True{} : Bool}:
  match g:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, N.succ_zero(ap, Equal.trans(Nat, 1n+ap, Nat.mul(l, 0n), 0n, e, A.mul_zero(l))))
    case 1n+gp:
      {==}

def div_exact(+x: Nat, +l: Nat, +g: Nat, +hg: {Nat.is_lt(0n, g) == True{} : Bool}, +e: {x == Nat.mul(l, g) : Nat}) -> {Nat.div(x, g) == l : Nat}:
  match g:
    case 0n:
      Empty.absurd({Nat.div(x, 0n) == l : Nat}, L.false_true(hg))
    case 1n+ +gp:
      %Equal.sym(Nat, x, Nat.add(Nat.mul(l, 1n+gp), 0n), Equal.trans(Nat, x, Nat.mul(l, 1n+gp), Nat.add(Nat.mul(l, 1n+gp), 0n), e, Equal.sym(Nat, Nat.add(Nat.mul(l, 1n+gp), 0n), Nat.mul(l, 1n+gp), A.add_zero(Nat.mul(l, 1n+gp))))) : {Nat.div(_, 1n+gp) == l : Nat}
      R.div_of(l, gp, 0n, {==})

def lcm_pos(+ap: Nat, +bp: Nat) -> {M.lcm(1n+ap, 1n+bp) == Nat.mul(G.wl(G.ws(1n+bp, 1n+ap, 1n+bp)), 1n+bp) : Nat}:
  +g = M.gcd(1n+ap, 1n+bp)
  +la = G.wl(G.ws(1n+bp, 1n+ap, 1n+bp))
  +ea = G.gcd_dvd_left(1n+ap, 1n+bp)
  Equal.cong(Nat, Nat, z => Nat.mul(z, 1n+bp), Nat.div(1n+ap, g), la, div_exact(1n+ap, la, g, gcd_pos(ap, la, g, ea), ea))

# lcm(a, b) == kl a and lcm(a, b) == kr b   (Mathlib Nat.dvd_lcm_left/right)
def lcm_wl(+a: Nat, +b: Nat) -> Nat:
  match a b:
    case 0n _:
      0n
    case 1n+ap 0n:
      0n
    case 1n+ +ap 1n+ +bp:
      G.wr(G.ws(1n+bp, 1n+ap, 1n+bp))

def lcm_wr(+a: Nat, +b: Nat) -> Nat:
  match a b:
    case 0n _:
      0n
    case 1n+ap 0n:
      0n
    case 1n+ +ap 1n+ +bp:
      G.wl(G.ws(1n+bp, 1n+ap, 1n+bp))

def dvd_lcm_left(+a: Nat, +b: Nat) -> {M.lcm(a, b) == Nat.mul(lcm_wl(a, b), a) : Nat}:
  match a b:
    case 0n b0:
      {==}
    case 1n+ ap 0n:
      {==}
    case 1n+ +ap 1n+ +bp:
      +g = M.gcd(1n+ap, 1n+bp)
      +la = G.wl(G.ws(1n+bp, 1n+ap, 1n+bp))
      +lb = G.wr(G.ws(1n+bp, 1n+ap, 1n+bp))
      %Equal.sym(Nat, M.lcm(1n+ap, 1n+bp), Nat.mul(la, 1n+bp), lcm_pos(ap, bp)) : {_ == Nat.mul(lb, 1n+ap) : Nat}
      %Equal.sym(Nat, 1n+bp, Nat.mul(lb, g), G.gcd_dvd_right(1n+ap, 1n+bp)) : {Nat.mul(la, _) == Nat.mul(lb, 1n+ap) : Nat}
      %Equal.sym(Nat, 1n+ap, Nat.mul(la, g), G.gcd_dvd_left(1n+ap, 1n+bp)) : {Nat.mul(la, Nat.mul(lb, g)) == Nat.mul(lb, _) : Nat}
      swap_cw(la, lb, g)

def dvd_lcm_right(+a: Nat, +b: Nat) -> {M.lcm(a, b) == Nat.mul(lcm_wr(a, b), b) : Nat}:
  match a b:
    case 0n b0:
      Equal.sym(Nat, Nat.mul(0n, b0), 0n, {==})
    case 1n+ ap 0n:
      Equal.sym(Nat, Nat.mul(0n, 0n), 0n, {==})
    case 1n+ +ap 1n+ +bp:
      lcm_pos(ap, bp)

# gcd(a, b) lcm(a, b) == a b   (Mathlib Nat.gcd_mul_lcm)
def gcd_mul_lcm(+a: Nat, +b: Nat) -> {Nat.mul(M.gcd(a, b), M.lcm(a, b)) == Nat.mul(a, b) : Nat}:
  match a b:
    case 0n b0:
      A.mul_zero(M.gcd(0n, b0))
    case 1n+ +ap 0n:
      Equal.trans(Nat, Nat.mul(M.gcd(1n+ap, 0n), 0n), 0n, Nat.mul(1n+ap, 0n), A.mul_zero(M.gcd(1n+ap, 0n)), Equal.sym(Nat, Nat.mul(1n+ap, 0n), 0n, A.mul_zero(1n+ap)))
    case 1n+ +ap 1n+ +bp:
      +g = M.gcd(1n+ap, 1n+bp)
      +la = G.wl(G.ws(1n+bp, 1n+ap, 1n+bp))
      %Equal.sym(Nat, M.lcm(1n+ap, 1n+bp), Nat.mul(la, 1n+bp), lcm_pos(ap, bp)) : {Nat.mul(g, _) == Nat.mul(1n+ap, 1n+bp) : Nat}
      %Equal.sym(Nat, Nat.mul(g, Nat.mul(la, 1n+bp)), Nat.mul(Nat.mul(g, la), 1n+bp), Equal.sym(Nat, Nat.mul(Nat.mul(g, la), 1n+bp), Nat.mul(g, Nat.mul(la, 1n+bp)), A.mul_assoc(g, la, 1n+bp))) : {_ == Nat.mul(1n+ap, 1n+bp) : Nat}
      %Equal.sym(Nat, Nat.mul(g, la), Nat.mul(la, g), A.mul_comm(g, la)) : {Nat.mul(_, 1n+bp) == Nat.mul(1n+ap, 1n+bp) : Nat}
      Equal.cong(Nat, Nat, z => Nat.mul(z, 1n+bp), Nat.mul(la, g), 1n+ap, Equal.sym(Nat, 1n+ap, Nat.mul(la, g), G.gcd_dvd_left(1n+ap, 1n+bp)))

def cancel_pos(+x: Nat, +y: Nat, +g: Nat, +hg: {Nat.is_lt(0n, g) == True{} : Bool}, +e: {Nat.mul(x, g) == Nat.mul(y, g) : Nat}) -> {x == y : Nat}:
  match g:
    case 0n:
      Empty.absurd({x == y : Nat}, L.false_true(hg))
    case 1n+ +gp:
      R.mul_cancel(x, y, gp, e)

# the quotient m / lcm(a, b) for a common multiple m == x a == y b
def lcm_dw(+a: Nat, +b: Nat, +m: Nat, +x: Nat, +y: Nat) -> Nat:
  match a b:
    case 0n _:
      0n
    case 1n+ap 0n:
      0n
    case 1n+ +ap 1n+ +bp:
      G.dw(Nat.mul(m, 1n+bp), Nat.mul(m, 1n+ap), Nat.mul(m, 1n+bp), y, x)

def lcm_dvd_pos(+ap: Nat, +bp: Nat, +m: Nat, +x: Nat, +y: Nat, +ex: {m == Nat.mul(x, 1n+ap) : Nat}, +ey: {m == Nat.mul(y, 1n+bp) : Nat}) -> {m == Nat.mul(lcm_dw(1n+ap, 1n+bp, m, x, y), M.lcm(1n+ap, 1n+bp)) : Nat}:
  +a = {1n+ap : Nat}
  +b = {1n+bp : Nat}
  +g = M.gcd(a, b)
  +l = M.lcm(a, b)
  +ab = Nat.mul(a, b)
  +t = lcm_dw(a, b, m, x, y)
  +la = G.wl(G.ws(b, a, b))
  +ea = Equal.trans(Nat, Nat.mul(m, a), Nat.mul(Nat.mul(y, b), a), Nat.mul(y, ab), Equal.cong(Nat, Nat, z => Nat.mul(z, a), m, Nat.mul(y, b), ey),
    Equal.trans(Nat, Nat.mul(Nat.mul(y, b), a), Nat.mul(y, Nat.mul(b, a)), Nat.mul(y, ab), A.mul_assoc(y, b, a), Equal.cong(Nat, Nat, z => Nat.mul(y, z), Nat.mul(b, a), ab, A.mul_comm(b, a))))
  +eb = Equal.trans(Nat, Nat.mul(m, b), Nat.mul(Nat.mul(x, a), b), Nat.mul(x, ab), Equal.cong(Nat, Nat, z => Nat.mul(z, b), m, Nat.mul(x, a), ex), A.mul_assoc(x, a, b))
  +e2 = G.dvd_gcd(Nat.mul(m, a), Nat.mul(m, b), ab, y, x, ea, eb)
  +e1 = gcd_mul_left(m, a, b)
  +e3 = Equal.sym(Nat, Nat.mul(g, l), ab, gcd_mul_lcm(a, b))
  +emg = Equal.trans(Nat, Nat.mul(m, g), M.gcd(Nat.mul(m, a), Nat.mul(m, b)), Nat.mul(t, Nat.mul(g, l)), Equal.sym(Nat, M.gcd(Nat.mul(m, a), Nat.mul(m, b)), Nat.mul(m, g), e1),
    Equal.trans(Nat, M.gcd(Nat.mul(m, a), Nat.mul(m, b)), Nat.mul(t, ab), Nat.mul(t, Nat.mul(g, l)), e2, Equal.cong(Nat, Nat, z => Nat.mul(t, z), ab, Nat.mul(g, l), e3)))
  +emg2 = Equal.trans(Nat, Nat.mul(m, g), Nat.mul(t, Nat.mul(g, l)), Nat.mul(Nat.mul(t, l), g), emg,
    Equal.trans(Nat, Nat.mul(t, Nat.mul(g, l)), Nat.mul(t, Nat.mul(l, g)), Nat.mul(Nat.mul(t, l), g), Equal.cong(Nat, Nat, z => Nat.mul(t, z), Nat.mul(g, l), Nat.mul(l, g), A.mul_comm(g, l)), Equal.sym(Nat, Nat.mul(Nat.mul(t, l), g), Nat.mul(t, Nat.mul(l, g)), A.mul_assoc(t, l, g))))
  cancel_pos(m, Nat.mul(t, l), g, gcd_pos(ap, la, g, G.gcd_dvd_left(a, b)), emg2)

# every common multiple of a and b is a multiple of lcm(a, b)   (Mathlib Nat.lcm_dvd)
def lcm_dvd(+a: Nat, +b: Nat, +m: Nat, +x: Nat, +y: Nat, +ex: {m == Nat.mul(x, a) : Nat}, +ey: {m == Nat.mul(y, b) : Nat}) -> {m == Nat.mul(lcm_dw(a, b, m, x, y), M.lcm(a, b)) : Nat}:
  match a b:
    case 0n b0:
      Equal.trans(Nat, m, Nat.mul(x, 0n), 0n, ex, A.mul_zero(x))
    case 1n+ ap 0n:
      Equal.trans(Nat, m, Nat.mul(y, 0n), 0n, ey, A.mul_zero(y))
    case 1n+ +ap 1n+ +bp:
      lcm_dvd_pos(ap, bp, m, x, y, ex, ey)
