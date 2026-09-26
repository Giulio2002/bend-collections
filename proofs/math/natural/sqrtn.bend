import Base
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as A
import ../../../src/math/natural.bend as M
import ../../../src/math/pow2.bend as P2
import ./arith.bend as R
import ./bits.bend as B
import ./roots.bend as RT
import ./logs.bend as LG

# isqrt(n) by Heron's iteration is the integer square root: r^2 <= n <
# (r + 1)^2. The proof follows Lean 4 Mathlib's Nat.sqrt (Mathlib/Data/Nat/
# Defs: Nat.sqrt.iter_sq_le, Nat.sqrt.lt_iter_succ_sq): at a fixed point g
# <= n / g, so g^2 <= n; and every step keeps n < (g + 1)^2. For the step,
# Mathlib goes through AM-GM, 4 g n <= (g^2 + n)^2; here the same bound is
# the product lemma u + v <= 2 w => u v <= w^2 (joint induction), applied to
# u = g, v = n / g + 1, w = next + 1.

# ---- products ----

# (1 + u)(1 + v) == 1 + ((u + v) + u v)
def succ_mul_succ(+u: Nat, +v: Nat) -> {Nat.mul(1n+u, 1n+v) == 1n+Nat.add(Nat.add(u, v), Nat.mul(u, v)) : Nat}:
  %Equal.sym(Nat, Nat.mul(u, 1n+v), Nat.add(u, Nat.mul(u, v)), A.mul_succ(u, v)) : {Nat.add(1n+v, _) == 1n+Nat.add(Nat.add(u, v), Nat.mul(u, v)) : Nat}
  N.succ_cong(Nat.add(v, Nat.add(u, Nat.mul(u, v))), Nat.add(Nat.add(u, v), Nat.mul(u, v)), Equal.trans(Nat, Nat.add(v, Nat.add(u, Nat.mul(u, v))), Nat.add(u, Nat.add(v, Nat.mul(u, v))), Nat.add(Nat.add(u, v), Nat.mul(u, v)), A.add_swap(v, u, Nat.mul(u, v)), Equal.sym(Nat, Nat.add(Nat.add(u, v), Nat.mul(u, v)), Nat.add(u, Nat.add(v, Nat.mul(u, v))), A.add_assoc(u, v, Nat.mul(u, v)))))

# a <= b and c <= d give a + c <= b + d
def le_add2(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +h1: {Nat.is_le(a, b) == True{} : Bool}, +h2: {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  N.le_trans(Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), LG.le_add_r(a, b, c, h1), N.le_add_left(c, d, b, h2))

# (1 + x) + (1 + y) == 2 + (x + y)
def add_two(+x: Nat, +y: Nat) -> {Nat.add(1n+x, 1n+y) == 2n+Nat.add(x, y) : Nat}:
  N.succ_cong(Nat.add(x, 1n+y), 1n+Nat.add(x, y), A.add_succ(x, y))

# u + v <= 2 w gives u v <= w w
def prod_le(+u: Nat, +v: Nat, +w: Nat, +h: {Nat.is_le(Nat.add(u, v), Nat.add(w, w)) == True{} : Bool}) -> {Nat.is_le(Nat.mul(u, v), Nat.mul(w, w)) == True{} : Bool}:
  match u v w:
    case 0n v0 w0:
      N.zero_le(Nat.mul(w0, w0))
    case 1n+ +up 0n w0:
      %Equal.sym(Nat, Nat.mul(1n+up, 0n), 0n, A.mul_zero(1n+up)) : {Nat.is_le(_, Nat.mul(w0, w0)) == True{} : Bool}
      N.zero_le(Nat.mul(w0, w0))
    case 1n+ +up 1n+ +vp 0n:
      Empty.absurd({Nat.is_le(Nat.mul(1n+up, 1n+vp), 0n) == True{} : Bool}, L.false_true(Equal.trans(Bool, False{}, Nat.is_le(Nat.add(1n+up, 1n+vp), 0n), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, 0n), 2n+Nat.add(up, vp), Nat.add(1n+up, 1n+vp), Equal.sym(Nat, Nat.add(1n+up, 1n+vp), 2n+Nat.add(up, vp), add_two(up, vp))), h)))
    case 1n+ +up 1n+ +vp 1n+ +wp:
      +h2 = Equal.trans(Bool, Nat.is_le(Nat.add(up, vp), Nat.add(wp, wp)), Nat.is_le(Nat.add(1n+up, 1n+vp), Nat.add(1n+wp, 1n+wp)), True{},
        Equal.trans(Bool, Nat.is_le(Nat.add(up, vp), Nat.add(wp, wp)), Nat.is_le(2n+Nat.add(up, vp), 2n+Nat.add(wp, wp)), Nat.is_le(Nat.add(1n+up, 1n+vp), Nat.add(1n+wp, 1n+wp)), {==},
          Equal.trans(Bool, Nat.is_le(2n+Nat.add(up, vp), 2n+Nat.add(wp, wp)), Nat.is_le(Nat.add(1n+up, 1n+vp), 2n+Nat.add(wp, wp)), Nat.is_le(Nat.add(1n+up, 1n+vp), Nat.add(1n+wp, 1n+wp)), Equal.cong(Nat, Bool, z => Nat.is_le(z, 2n+Nat.add(wp, wp)), 2n+Nat.add(up, vp), Nat.add(1n+up, 1n+vp), Equal.sym(Nat, Nat.add(1n+up, 1n+vp), 2n+Nat.add(up, vp), add_two(up, vp))), Equal.cong(Nat, Bool, z => Nat.is_le(Nat.add(1n+up, 1n+vp), z), 2n+Nat.add(wp, wp), Nat.add(1n+wp, 1n+wp), Equal.sym(Nat, Nat.add(1n+wp, 1n+wp), 2n+Nat.add(wp, wp), add_two(wp, wp))))), h)
      %Equal.sym(Nat, Nat.mul(1n+up, 1n+vp), 1n+Nat.add(Nat.add(up, vp), Nat.mul(up, vp)), succ_mul_succ(up, vp)) : {Nat.is_le(_, Nat.mul(1n+wp, 1n+wp)) == True{} : Bool}
      %Equal.sym(Nat, Nat.mul(1n+wp, 1n+wp), 1n+Nat.add(Nat.add(wp, wp), Nat.mul(wp, wp)), succ_mul_succ(wp, wp)) : {Nat.is_le(1n+Nat.add(Nat.add(up, vp), Nat.mul(up, vp)), _) == True{} : Bool}
      le_add2(Nat.add(up, vp), Nat.add(wp, wp), Nat.mul(up, vp), Nat.mul(wp, wp), h2, prod_le(up, vp, wp, h2))

# ---- the fixed point: next >= g gives g^2 <= n   (Mathlib Nat.sqrt.iter_sq_le) ----

def stop_sq(+n: Nat, +g: Nat, +h: {Nat.is_lt(M.sqrt_next(n, g), g) == False{} : Bool}) -> {Nat.is_le(Nat.mul(g, g), n) == True{} : Bool}:
  match g:
    case 0n:
      N.zero_le(n)
    case 1n+ +gp:
      +q = Nat.div(n, 1n+gp)
      +hge = N.not_lt_le(M.sqrt_next(n, 1n+gp), 1n+gp, h)
      +h2 = Equal.trans(Bool, Nat.is_le(1n+gp, q), Nat.is_le(Nat.add(1n+gp, 1n+gp), Nat.add(1n+gp, q)), True{}, Equal.sym(Bool, Nat.is_le(Nat.add(1n+gp, 1n+gp), Nat.add(1n+gp, q)), Nat.is_le(1n+gp, q), R.le_add_cancel(1n+gp, 1n+gp, q)),
        Equal.trans(Bool, Nat.is_le(Nat.add(1n+gp, 1n+gp), Nat.add(1n+gp, q)), Nat.is_le(Nat.mul(1n+gp, 2n), Nat.add(1n+gp, q)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, Nat.add(1n+gp, q)), Nat.add(1n+gp, 1n+gp), Nat.mul(1n+gp, 2n), Equal.sym(Nat, Nat.mul(1n+gp, 2n), Nat.add(1n+gp, 1n+gp), RT.two_mul(1n+gp))),
          Equal.trans(Bool, Nat.is_le(Nat.mul(1n+gp, 2n), Nat.add(1n+gp, q)), Nat.is_le(1n+gp, M.sqrt_next(n, 1n+gp)), True{}, Equal.sym(Bool, Nat.is_le(1n+gp, Nat.div(Nat.add(1n+gp, q), 2n)), Nat.is_le(Nat.mul(1n+gp, 2n), Nat.add(1n+gp, q)), R.le_div(1n, 1n+gp, Nat.add(1n+gp, q))), hge)))
      Equal.trans(Bool, Nat.is_le(Nat.mul(1n+gp, 1n+gp), n), Nat.is_le(1n+gp, q), True{}, Equal.sym(Bool, Nat.is_le(1n+gp, Nat.div(n, 1n+gp)), Nat.is_le(Nat.mul(1n+gp, 1n+gp), n), R.le_div(gp, 1n+gp, n)), h2)

def le_zero(+g: Nat, +h: {Nat.is_le(g, 0n) == True{} : Bool}) -> {g == 0n : Nat}:
  match g:
    case 0n:
      {==}
    case 1n+gp:
      Empty.absurd({1n+gp == 0n : Nat}, L.false_true(h))

def iter_sq(fuel: Nat, +n: Nat, +g: Nat, +m: Nat, +down: Bool, +hm: {m == M.sqrt_next(n, g) : Nat}, +hd: {down == Nat.is_lt(m, g) : Bool}, +hf: {Nat.is_le(g, fuel) == True{} : Bool}) -> {Nat.is_le(Nat.mul(M.sqrt_iter(fuel, n, g, m, down), M.sqrt_iter(fuel, n, g, m, down)), n) == True{} : Bool}:
  match fuel down:
    case 0n False{}:
      %Equal.sym(Nat, g, 0n, le_zero(g, hf)) : {Nat.is_le(Nat.mul(_, _), n) == True{} : Bool}
      N.zero_le(n)
    case 0n True{}:
      %Equal.sym(Nat, g, 0n, le_zero(g, hf)) : {Nat.is_le(Nat.mul(_, _), n) == True{} : Bool}
      N.zero_le(n)
    case 1n+f False{}:
      stop_sq(n, g, Equal.trans(Bool, Nat.is_lt(M.sqrt_next(n, g), g), Nat.is_lt(m, g), False{}, Equal.cong(Nat, Bool, z => Nat.is_lt(z, g), M.sqrt_next(n, g), m, Equal.sym(Nat, m, M.sqrt_next(n, g), hm)), Equal.sym(Bool, False{}, Nat.is_lt(m, g), hd)))
    case 1n+ +f True{}:
      iter_sq(f, n, m, M.sqrt_next(n, m), Nat.is_lt(M.sqrt_next(n, m), m), {==}, {==}, RT.shrink(m, g, f, Equal.sym(Bool, True{}, Nat.is_lt(m, g), hd), hf))

# ---- a step keeps n < (g + 1)^2   (Mathlib Nat.sqrt.lt_iter_succ_sq) ----

def step_lt(+n: Nat, +gp: Nat, +m: Nat, +hm: {m == M.sqrt_next(n, 1n+gp) : Nat}) -> {Nat.is_lt(n, Nat.mul(1n+m, 1n+m)) == True{} : Bool}:
  +g = {1n+gp : Nat}
  +q = Nat.div(n, g)
  +r = Nat.mod(n, g)
  +s = Nat.add(g, q)
  # n < g (q + 1)
  +ha = Equal.trans(Bool, Nat.is_lt(n, Nat.mul(g, 1n+q)), Nat.is_lt(Nat.add(Nat.mul(q, g), r), Nat.add(Nat.mul(q, g), g)), True{},
    Equal.trans(Bool, Nat.is_lt(n, Nat.mul(g, 1n+q)), Nat.is_lt(Nat.add(Nat.mul(q, g), r), Nat.mul(g, 1n+q)), Nat.is_lt(Nat.add(Nat.mul(q, g), r), Nat.add(Nat.mul(q, g), g)),
      Equal.cong(Nat, Bool, z => Nat.is_lt(z, Nat.mul(g, 1n+q)), n, Nat.add(Nat.mul(q, g), r), R.dm_eq(gp, n)),
      Equal.cong(Nat, Bool, z => Nat.is_lt(Nat.add(Nat.mul(q, g), r), z), Nat.mul(g, 1n+q), Nat.add(Nat.mul(q, g), g), Equal.trans(Nat, Nat.mul(g, 1n+q), Nat.mul(1n+q, g), Nat.add(Nat.mul(q, g), g), A.mul_comm(g, 1n+q), A.add_comm(g, Nat.mul(q, g))))),
    N.lt_add_left(r, g, Nat.mul(q, g), R.dm_lt(gp, n)))
  # g + (q + 1) <= 2 (m + 1): s == 2 m + (s mod 2)
  +es = Equal.trans(Nat, s, Nat.add(Nat.double(m), Nat.mod(s, 2n)), Nat.add(Nat.add(m, m), Nat.mod(s, 2n)),
    Equal.trans(Nat, s, Nat.add(Nat.double(Nat.div(s, 2n)), Nat.mod(s, 2n)), Nat.add(Nat.double(m), Nat.mod(s, 2n)), B.half_eq(s), Equal.cong(Nat, Nat, z => Nat.add(Nat.double(z), Nat.mod(s, 2n)), Nat.div(s, 2n), m, Equal.sym(Nat, m, Nat.div(s, 2n), hm))),
    Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mod(s, 2n)), Nat.double(m), Nat.add(m, m), A.double_self(m)))
  +hs = Equal.trans(Bool, Nat.is_le(s, 1n+Nat.add(m, m)), Nat.is_le(Nat.add(Nat.add(m, m), Nat.mod(s, 2n)), Nat.add(Nat.add(m, m), 1n)), True{},
    Equal.trans(Bool, Nat.is_le(s, 1n+Nat.add(m, m)), Nat.is_le(Nat.add(Nat.add(m, m), Nat.mod(s, 2n)), 1n+Nat.add(m, m)), Nat.is_le(Nat.add(Nat.add(m, m), Nat.mod(s, 2n)), Nat.add(Nat.add(m, m), 1n)),
      Equal.cong(Nat, Bool, z => Nat.is_le(z, 1n+Nat.add(m, m)), s, Nat.add(Nat.add(m, m), Nat.mod(s, 2n)), es),
      Equal.cong(Nat, Bool, z => Nat.is_le(Nat.add(Nat.add(m, m), Nat.mod(s, 2n)), z), 1n+Nat.add(m, m), Nat.add(Nat.add(m, m), 1n), A.add_comm(1n, Nat.add(m, m)))),
    N.le_add_left(Nat.mod(s, 2n), 1n, Nat.add(m, m), N.lt_succ_le(Nat.mod(s, 2n), 1n, B.half_rem(s))))
  +hb = Equal.trans(Bool, Nat.is_le(Nat.add(g, 1n+q), Nat.add(1n+m, 1n+m)), Nat.is_le(1n+s, 2n+Nat.add(m, m)), True{},
    Equal.trans(Bool, Nat.is_le(Nat.add(g, 1n+q), Nat.add(1n+m, 1n+m)), Nat.is_le(1n+s, Nat.add(1n+m, 1n+m)), Nat.is_le(1n+s, 2n+Nat.add(m, m)),
      Equal.cong(Nat, Bool, z => Nat.is_le(z, Nat.add(1n+m, 1n+m)), Nat.add(g, 1n+q), 1n+s, A.add_succ(g, q)),
      Equal.cong(Nat, Bool, z => Nat.is_le(1n+s, z), Nat.add(1n+m, 1n+m), 2n+Nat.add(m, m), add_two(m, m))),
    hs)
  N.lt_le_trans(n, Nat.mul(g, 1n+q), Nat.mul(1n+m, 1n+m), ha, prod_le(g, 1n+q, 1n+m, hb))

def step_any(+n: Nat, +g: Nat, +m: Nat, +hm: {m == M.sqrt_next(n, g) : Nat}, +hlt: {Nat.is_lt(m, g) == True{} : Bool}) -> {Nat.is_lt(n, Nat.mul(1n+m, 1n+m)) == True{} : Bool}:
  match g:
    case 0n:
      Empty.absurd({Nat.is_lt(n, Nat.mul(1n+m, 1n+m)) == True{} : Bool}, N.lt_zero_absurd(m, hlt))
    case 1n+ +gp:
      step_lt(n, gp, m, hm)

def iter_lt(fuel: Nat, +n: Nat, +g: Nat, +m: Nat, +down: Bool, +hm: {m == M.sqrt_next(n, g) : Nat}, +hd: {down == Nat.is_lt(m, g) : Bool}, +hn: {Nat.is_lt(n, Nat.mul(1n+g, 1n+g)) == True{} : Bool}) -> {Nat.is_lt(n, Nat.mul(1n+M.sqrt_iter(fuel, n, g, m, down), 1n+M.sqrt_iter(fuel, n, g, m, down))) == True{} : Bool}:
  match fuel down:
    case 0n False{}:
      hn
    case 0n True{}:
      hn
    case 1n+f False{}:
      hn
    case 1n+ +f True{}:
      iter_lt(f, n, m, M.sqrt_next(n, m), Nat.is_lt(M.sqrt_next(n, m), m), {==}, {==}, step_any(n, g, m, hm, Equal.sym(Bool, True{}, Nat.is_lt(m, g), hd)))

# ---- the theorems ----

def g0_bound(+n: Nat) -> {Nat.is_lt(n, Nat.mul(1n+P2.pow2t(1n+Nat.div(M.bit_length(n), 2n)), 1n+P2.pow2t(1n+Nat.div(M.bit_length(n), 2n)))) == True{} : Bool}:
  +g = P2.pow2t(1n+Nat.div(M.bit_length(n), 2n))
  +lt = N.not_le_lt(Nat.pow(g, 2n), n, Equal.trans(Bool, Nat.is_le(Nat.pow(g, 2n), n), M.root_le(n, 2n, g), False{}, Equal.sym(Bool, M.root_le(n, 2n, g), Nat.is_le(Nat.pow(g, 2n), n), RT.root_le_ok(n, 2n, g)), RT.hi_bound(n, 1n)))
  +lt2 = Equal.trans(Bool, Nat.is_lt(n, Nat.mul(g, g)), Nat.is_lt(n, Nat.pow(g, 2n)), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(n, Nat.mul(g, z)), g, Nat.mul(g, 1n), Equal.sym(Nat, Nat.mul(g, 1n), g, A.mul_one(g))), lt)
  N.lt_le_trans(n, Nat.mul(g, g), Nat.mul(1n+g, 1n+g), lt2, prod_le(g, g, 1n+g, le_add2(g, 1n+g, g, 1n+g, N.le_succ(g), N.le_succ(g))))

# isqrt(n)^2 <= n   (Mathlib Nat.sqrt_le')
def isqrt_le(+n: Nat) -> {Nat.is_le(Nat.pow(M.isqrt(n), 2n), n) == True{} : Bool}:
  +g = P2.pow2t(1n+Nat.div(M.bit_length(n), 2n))
  %Equal.sym(Nat, Nat.pow(M.isqrt(n), 2n), Nat.mul(M.isqrt(n), M.isqrt(n)), Equal.cong(Nat, Nat, z => Nat.mul(M.isqrt(n), z), Nat.mul(M.isqrt(n), 1n), M.isqrt(n), A.mul_one(M.isqrt(n)))) : {Nat.is_le(_, n) == True{} : Bool}
  iter_sq(g, n, g, M.sqrt_next(n, g), Nat.is_lt(M.sqrt_next(n, g), g), {==}, {==}, N.le_refl(g))

# n < (isqrt(n) + 1)^2   (Mathlib Nat.lt_succ_sqrt')
def lt_succ_isqrt(+n: Nat) -> {Nat.is_lt(n, Nat.pow(1n+M.isqrt(n), 2n)) == True{} : Bool}:
  +g = P2.pow2t(1n+Nat.div(M.bit_length(n), 2n))
  %Equal.sym(Nat, Nat.pow(1n+M.isqrt(n), 2n), Nat.mul(1n+M.isqrt(n), 1n+M.isqrt(n)), Equal.cong(Nat, Nat, z => Nat.mul(1n+M.isqrt(n), z), Nat.mul(1n+M.isqrt(n), 1n), 1n+M.isqrt(n), A.mul_one(1n+M.isqrt(n)))) : {Nat.is_lt(n, _) == True{} : Bool}
  iter_lt(g, n, g, M.sqrt_next(n, g), Nat.is_lt(M.sqrt_next(n, g), g), {==}, {==}, g0_bound(n))
