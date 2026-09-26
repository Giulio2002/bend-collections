import Base
import ../../lib/nat.bend as N
import ../../lib/lemmas/proofs/nat_algebra.bend as A
import ../../lib/lemmas/proofs/word_value.bend as WV
import ../../lib/lemmas/proofs/natural_division.bend as ND

# Natural-number arithmetic the math proofs share: the division theorem,
# cancellation, and the order/division exchange. Statement shapes follow
# Lean 4 Mathlib (Nat.div_add_mod, Nat.mod_lt, Nat.le_div_iff_mul_le,
# Nat.eq_of_mul_eq_mul_right, Nat.mul_sub_right_distrib); the divisor is
# written 1+d so that it is positive.

# ---- the division theorem ----

def dm_e2(+bp: Nat, +v: Nat, g: WV.go_equation(bp, v, bp, 0n, 0n)) -> {v == Nat.add(Nat.mul(Nat.div(v, 1n+bp), 1n+bp), Nat.mod(v, 1n+bp)) : Nat}:
  (e, l) = g
  e

def dm_l2(+bp: Nat, +v: Nat, g: WV.go_equation(bp, v, bp, 0n, 0n)) -> {Nat.is_lt(Nat.mod(v, 1n+bp), 1n+bp) == True{} : Bool}:
  (e, l) = g
  N.le_lt_succ(Nat.mod(v, 1n+bp), bp, l)

# v == (v / n) n + v mod n   (Mathlib Nat.div_add_mod)
def dm_eq(+bp: Nat, +v: Nat) -> {v == Nat.add(Nat.mul(Nat.div(v, 1n+bp), 1n+bp), Nat.mod(v, 1n+bp)) : Nat}:
  dm_e2(bp, v, WV.go(bp, v, bp, 0n, 0n, N.add_zero(bp)))

# v mod n < n   (Mathlib Nat.mod_lt)
def dm_lt(+bp: Nat, +v: Nat) -> {Nat.is_lt(Nat.mod(v, 1n+bp), 1n+bp) == True{} : Bool}:
  dm_l2(bp, v, WV.go(bp, v, bp, 0n, 0n, N.add_zero(bp)))

# the quotient and remainder are unique
def div_of(+q: Nat, +bp: Nat, +r: Nat, +h: {Nat.is_lt(r, 1n+bp) == True{} : Bool}) -> {Nat.div(Nat.add(Nat.mul(q, 1n+bp), r), 1n+bp) == q : Nat}:
  ND.quotient(q, bp, r, N.lt_succ_le(r, bp, h))

def mod_of(+q: Nat, +bp: Nat, +r: Nat, +h: {Nat.is_lt(r, 1n+bp) == True{} : Bool}) -> {Nat.mod(Nat.add(Nat.mul(q, 1n+bp), r), 1n+bp) == r : Nat}:
  ND.remainder(q, bp, r, N.lt_succ_le(r, bp, h))

# ---- cancellation ----

# c + a == c + b gives a == b   (Mathlib Nat.add_left_cancel)
def add_cancel(+c: Nat, +a: Nat, +b: Nat, +e: {Nat.add(c, a) == Nat.add(c, b) : Nat}) -> {a == b : Nat}:
  match c:
    case 0n:
      e
    case 1n+ +cp:
      add_cancel(cp, a, b, N.succ_inj(Nat.add(cp, a), Nat.add(cp, b), e))

# x c == y c with c > 0 gives x == y   (Mathlib Nat.eq_of_mul_eq_mul_right)
def mul_cancel(+x: Nat, +y: Nat, +bp: Nat, +e: {Nat.mul(x, 1n+bp) == Nat.mul(y, 1n+bp) : Nat}) -> {x == y : Nat}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+yp:
      Empty.absurd({0n == 1n+yp : Nat}, N.zero_succ(Nat.add(bp, Nat.mul(yp, 1n+bp)), e))
    case 1n+xp 0n:
      Empty.absurd({1n+xp == 0n : Nat}, N.succ_zero(Nat.add(bp, Nat.mul(xp, 1n+bp)), e))
    case 1n+ +xp 1n+ +yp:
      N.succ_cong(xp, yp, mul_cancel(xp, yp, bp, add_cancel(1n+bp, Nat.mul(xp, 1n+bp), Nat.mul(yp, 1n+bp), e)))

# ---- order and division ----

# d + x <= d + y is x <= y
def le_add_cancel(+d: Nat, +x: Nat, +y: Nat) -> {Nat.is_le(Nat.add(d, x), Nat.add(d, y)) == Nat.is_le(x, y) : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+ +dp:
      le_add_cancel(dp, x, y)

def le_div_g(+x: Nat, +q: Nat, +bp: Nat, +r: Nat, +hr: {Nat.is_lt(r, 1n+bp) == True{} : Bool}) -> {Nat.is_le(x, q) == Nat.is_le(Nat.mul(x, 1n+bp), Nat.add(Nat.mul(q, 1n+bp), r)) : Bool}:
  match x q:
    case 0n q0:
      %Equal.sym(Bool, Nat.is_le(0n, q0), True{}, N.zero_le(q0)) : {_ == Nat.is_le(0n, Nat.add(Nat.mul(q0, 1n+bp), r)) : Bool}
      Equal.sym(Bool, Nat.is_le(0n, Nat.add(Nat.mul(q0, 1n+bp), r)), True{}, N.zero_le(Nat.add(Nat.mul(q0, 1n+bp), r)))
    case 1n+ +xp 0n:
      Equal.sym(Bool, Nat.is_le(Nat.add(1n+bp, Nat.mul(xp, 1n+bp)), r), False{}, N.lt_not_le(r, Nat.add(1n+bp, Nat.mul(xp, 1n+bp)), N.lt_le_trans(r, 1n+bp, Nat.add(1n+bp, Nat.mul(xp, 1n+bp)), hr, N.le_add_right(1n+bp, Nat.mul(xp, 1n+bp)))))
    case 1n+ +xp 1n+ +qp:
      %Equal.sym(Nat, Nat.add(Nat.add(1n+bp, Nat.mul(qp, 1n+bp)), r), Nat.add(1n+bp, Nat.add(Nat.mul(qp, 1n+bp), r)), A.add_assoc(1n+bp, Nat.mul(qp, 1n+bp), r)) : {Nat.is_le(xp, qp) == Nat.is_le(Nat.add(1n+bp, Nat.mul(xp, 1n+bp)), _) : Bool}
      %Equal.sym(Bool, Nat.is_le(Nat.add(1n+bp, Nat.mul(xp, 1n+bp)), Nat.add(1n+bp, Nat.add(Nat.mul(qp, 1n+bp), r))), Nat.is_le(Nat.mul(xp, 1n+bp), Nat.add(Nat.mul(qp, 1n+bp), r)), le_add_cancel(1n+bp, Nat.mul(xp, 1n+bp), Nat.add(Nat.mul(qp, 1n+bp), r))) : {Nat.is_le(xp, qp) == _ : Bool}
      le_div_g(xp, qp, bp, r, hr)

# x <= n / d is x d <= n   (Mathlib Nat.le_div_iff_mul_le)
def le_div(+bp: Nat, +x: Nat, +n: Nat) -> {Nat.is_le(x, Nat.div(n, 1n+bp)) == Nat.is_le(Nat.mul(x, 1n+bp), n) : Bool}:
  +e = dm_eq(bp, n)
  %Equal.sym(Nat, n, Nat.add(Nat.mul(Nat.div(n, 1n+bp), 1n+bp), Nat.mod(n, 1n+bp)), e) : {Nat.is_le(x, Nat.div(n, 1n+bp)) == Nat.is_le(Nat.mul(x, 1n+bp), _) : Bool}
  le_div_g(x, Nat.div(n, 1n+bp), bp, Nat.mod(n, 1n+bp), dm_lt(bp, n))

# ---- subtraction ----

def zsub(+b: Nat) -> {Nat.sub(0n, b) == 0n : Nat}:
  match b:
    case 0n:
      {==}
    case 1n+p:
      {==}

def sub_cancel_l(+c: Nat, +a: Nat, +b: Nat) -> {Nat.sub(Nat.add(c, a), Nat.add(c, b)) == Nat.sub(a, b) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+ +cp:
      sub_cancel_l(cp, a, b)

# (x - y) c == x c - y c   (Mathlib Nat.mul_sub_right_distrib)
def mul_sub(+x: Nat, +y: Nat, +c: Nat) -> {Nat.mul(Nat.sub(x, y), c) == Nat.sub(Nat.mul(x, c), Nat.mul(y, c)) : Nat}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+ +yp:
      Equal.sym(Nat, Nat.sub(0n, Nat.add(c, Nat.mul(yp, c))), 0n, zsub(Nat.add(c, Nat.mul(yp, c))))
    case 1n+ +xp 0n:
      Equal.sym(Nat, Nat.sub(Nat.add(c, Nat.mul(xp, c)), 0n), Nat.add(c, Nat.mul(xp, c)), N.sub_zero(Nat.add(c, Nat.mul(xp, c))))
    case 1n+ +xp 1n+ +yp:
      %Equal.sym(Nat, Nat.sub(Nat.add(c, Nat.mul(xp, c)), Nat.add(c, Nat.mul(yp, c))), Nat.sub(Nat.mul(xp, c), Nat.mul(yp, c)), sub_cancel_l(c, Nat.mul(xp, c), Nat.mul(yp, c))) : {Nat.mul(Nat.sub(xp, yp), c) == _ : Nat}
      mul_sub(xp, yp, c)

# ---- congruences mod n = 1+bp ----

# (q n + r) mod n == r mod n   (Mathlib Nat.mul_add_mod)
def absorb(+bp: Nat, +q: Nat, +r: Nat) -> {Nat.mod(Nat.add(Nat.mul(q, 1n+bp), r), 1n+bp) == Nat.mod(r, 1n+bp) : Nat}:
  +n = {1n+bp : Nat}
  +qr = Nat.div(r, n)
  +m = Nat.mod(r, n)
  +e = Equal.trans(Nat, Nat.add(Nat.mul(q, n), r), Nat.add(Nat.mul(q, n), Nat.add(Nat.mul(qr, n), m)), Nat.add(Nat.mul(Nat.add(q, qr), n), m),
    Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(q, n), z), r, Nat.add(Nat.mul(qr, n), m), dm_eq(bp, r)),
    Equal.trans(Nat, Nat.add(Nat.mul(q, n), Nat.add(Nat.mul(qr, n), m)), Nat.add(Nat.add(Nat.mul(q, n), Nat.mul(qr, n)), m), Nat.add(Nat.mul(Nat.add(q, qr), n), m),
      Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(q, n), Nat.mul(qr, n)), m), Nat.add(Nat.mul(q, n), Nat.add(Nat.mul(qr, n), m)), A.add_assoc(Nat.mul(q, n), Nat.mul(qr, n), m)),
      Equal.cong(Nat, Nat, z => Nat.add(z, m), Nat.add(Nat.mul(q, n), Nat.mul(qr, n)), Nat.mul(Nat.add(q, qr), n), Equal.sym(Nat, Nat.mul(Nat.add(q, qr), n), Nat.add(Nat.mul(q, n), Nat.mul(qr, n)), A.mul_add_right(q, qr, n)))))
  Equal.trans(Nat, Nat.mod(Nat.add(Nat.mul(q, n), r), n), Nat.mod(Nat.add(Nat.mul(Nat.add(q, qr), n), m), n), m, Equal.cong(Nat, Nat, z => Nat.mod(z, n), Nat.add(Nat.mul(q, n), r), Nat.add(Nat.mul(Nat.add(q, qr), n), m), e), mod_of(Nat.add(q, qr), bp, m, dm_lt(bp, r)))

# (x mod n) mod n == x mod n   (Mathlib Nat.mod_mod)
def mod_mod(+bp: Nat, +x: Nat) -> {Nat.mod(Nat.mod(x, 1n+bp), 1n+bp) == Nat.mod(x, 1n+bp) : Nat}:
  mod_of(0n, bp, Nat.mod(x, 1n+bp), dm_lt(bp, x))

# (x + y mod n) mod n == (x + y) mod n   (Mathlib Nat.add_mod)
def mod_add_r(+bp: Nat, +x: Nat, +y: Nat) -> {Nat.mod(Nat.add(x, Nat.mod(y, 1n+bp)), 1n+bp) == Nat.mod(Nat.add(x, y), 1n+bp) : Nat}:
  +n = {1n+bp : Nat}
  +qy = Nat.div(y, n)
  +my = Nat.mod(y, n)
  +e = Equal.trans(Nat, Nat.add(x, y), Nat.add(x, Nat.add(Nat.mul(qy, n), my)), Nat.add(Nat.mul(qy, n), Nat.add(x, my)),
    Equal.cong(Nat, Nat, z => Nat.add(x, z), y, Nat.add(Nat.mul(qy, n), my), dm_eq(bp, y)),
    A.add_swap(x, Nat.mul(qy, n), my))
  Equal.sym(Nat, Nat.mod(Nat.add(x, y), n), Nat.mod(Nat.add(x, my), n), Equal.trans(Nat, Nat.mod(Nat.add(x, y), n), Nat.mod(Nat.add(Nat.mul(qy, n), Nat.add(x, my)), n), Nat.mod(Nat.add(x, my), n), Equal.cong(Nat, Nat, z => Nat.mod(z, n), Nat.add(x, y), Nat.add(Nat.mul(qy, n), Nat.add(x, my)), e), absorb(bp, qy, Nat.add(x, my))))

def mod_add_l(+bp: Nat, +x: Nat, +y: Nat) -> {Nat.mod(Nat.add(Nat.mod(x, 1n+bp), y), 1n+bp) == Nat.mod(Nat.add(x, y), 1n+bp) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.mod(x, 1n+bp), y), Nat.add(y, Nat.mod(x, 1n+bp)), A.add_comm(Nat.mod(x, 1n+bp), y)) : {Nat.mod(_, 1n+bp) == Nat.mod(Nat.add(x, y), 1n+bp) : Nat}
  %Equal.sym(Nat, Nat.add(x, y), Nat.add(y, x), A.add_comm(x, y)) : {Nat.mod(Nat.add(y, Nat.mod(x, 1n+bp)), 1n+bp) == Nat.mod(_, 1n+bp) : Nat}
  mod_add_r(bp, y, x)

# (x (y mod n)) mod n == (x y) mod n   (Mathlib Nat.mul_mod)
def mod_mul_r(+bp: Nat, +x: Nat, +y: Nat) -> {Nat.mod(Nat.mul(x, Nat.mod(y, 1n+bp)), 1n+bp) == Nat.mod(Nat.mul(x, y), 1n+bp) : Nat}:
  +n = {1n+bp : Nat}
  +qy = Nat.div(y, n)
  +my = Nat.mod(y, n)
  +e = Equal.trans(Nat, Nat.mul(x, y), Nat.mul(x, Nat.add(Nat.mul(qy, n), my)), Nat.add(Nat.mul(Nat.mul(x, qy), n), Nat.mul(x, my)),
    Equal.cong(Nat, Nat, z => Nat.mul(x, z), y, Nat.add(Nat.mul(qy, n), my), dm_eq(bp, y)),
    Equal.trans(Nat, Nat.mul(x, Nat.add(Nat.mul(qy, n), my)), Nat.add(Nat.mul(x, Nat.mul(qy, n)), Nat.mul(x, my)), Nat.add(Nat.mul(Nat.mul(x, qy), n), Nat.mul(x, my)),
      A.mul_add_left(x, Nat.mul(qy, n), my),
      Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(x, my)), Nat.mul(x, Nat.mul(qy, n)), Nat.mul(Nat.mul(x, qy), n), Equal.sym(Nat, Nat.mul(Nat.mul(x, qy), n), Nat.mul(x, Nat.mul(qy, n)), A.mul_assoc(x, qy, n)))))
  Equal.sym(Nat, Nat.mod(Nat.mul(x, y), n), Nat.mod(Nat.mul(x, my), n), Equal.trans(Nat, Nat.mod(Nat.mul(x, y), n), Nat.mod(Nat.add(Nat.mul(Nat.mul(x, qy), n), Nat.mul(x, my)), n), Nat.mod(Nat.mul(x, my), n), Equal.cong(Nat, Nat, z => Nat.mod(z, n), Nat.mul(x, y), Nat.add(Nat.mul(Nat.mul(x, qy), n), Nat.mul(x, my)), e), absorb(bp, Nat.mul(x, qy), Nat.mul(x, my))))

def mod_mul_l(+bp: Nat, +x: Nat, +y: Nat) -> {Nat.mod(Nat.mul(Nat.mod(x, 1n+bp), y), 1n+bp) == Nat.mod(Nat.mul(x, y), 1n+bp) : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.mod(x, 1n+bp), y), Nat.mul(y, Nat.mod(x, 1n+bp)), A.mul_comm(Nat.mod(x, 1n+bp), y)) : {Nat.mod(_, 1n+bp) == Nat.mod(Nat.mul(x, y), 1n+bp) : Nat}
  %Equal.sym(Nat, Nat.mul(x, y), Nat.mul(y, x), A.mul_comm(x, y)) : {Nat.mod(Nat.mul(y, Nat.mod(x, 1n+bp)), 1n+bp) == Nat.mod(_, 1n+bp) : Nat}
  mod_mul_r(bp, y, x)

# ---- powers ----

# a^(x + y) == a^x a^y   (Mathlib pow_add)
def pow_add(+a: Nat, +x: Nat, +y: Nat) -> {Nat.pow(a, Nat.add(x, y)) == Nat.mul(Nat.pow(a, x), Nat.pow(a, y)) : Nat}:
  match x:
    case 0n:
      Equal.sym(Nat, Nat.add(Nat.pow(a, y), 0n), Nat.pow(a, y), A.add_zero(Nat.pow(a, y)))
    case 1n+ +xp:
      %Equal.sym(Nat, Nat.pow(a, Nat.add(xp, y)), Nat.mul(Nat.pow(a, xp), Nat.pow(a, y)), pow_add(a, xp, y)) : {Nat.mul(a, _) == Nat.mul(Nat.mul(a, Nat.pow(a, xp)), Nat.pow(a, y)) : Nat}
      Equal.sym(Nat, Nat.mul(Nat.mul(a, Nat.pow(a, xp)), Nat.pow(a, y)), Nat.mul(a, Nat.mul(Nat.pow(a, xp), Nat.pow(a, y))), A.mul_assoc(a, Nat.pow(a, xp), Nat.pow(a, y)))

# (a b)(c d) == (a c)(b d)
def mul_swap4(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.mul(Nat.mul(a, b), Nat.mul(c, d)) == Nat.mul(Nat.mul(a, c), Nat.mul(b, d)) : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.mul(a, b), Nat.mul(c, d)), Nat.mul(a, Nat.mul(b, Nat.mul(c, d))), A.mul_assoc(a, b, Nat.mul(c, d))) : {_ == Nat.mul(Nat.mul(a, c), Nat.mul(b, d)) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(a, c), Nat.mul(b, d)), Nat.mul(a, Nat.mul(c, Nat.mul(b, d))), A.mul_assoc(a, c, Nat.mul(b, d))) : {Nat.mul(a, Nat.mul(b, Nat.mul(c, d))) == _ : Nat}
  %Equal.sym(Nat, Nat.mul(b, Nat.mul(c, d)), Nat.mul(Nat.mul(b, c), d), Equal.sym(Nat, Nat.mul(Nat.mul(b, c), d), Nat.mul(b, Nat.mul(c, d)), A.mul_assoc(b, c, d))) : {Nat.mul(a, _) == Nat.mul(a, Nat.mul(c, Nat.mul(b, d))) : Nat}
  %Equal.sym(Nat, Nat.mul(c, Nat.mul(b, d)), Nat.mul(Nat.mul(c, b), d), Equal.sym(Nat, Nat.mul(Nat.mul(c, b), d), Nat.mul(c, Nat.mul(b, d)), A.mul_assoc(c, b, d))) : {Nat.mul(a, Nat.mul(Nat.mul(b, c), d)) == Nat.mul(a, _) : Nat}
  %Equal.sym(Nat, Nat.mul(b, c), Nat.mul(c, b), A.mul_comm(b, c)) : {Nat.mul(a, Nat.mul(_, d)) == Nat.mul(a, Nat.mul(Nat.mul(c, b), d)) : Nat}
  {==}

# (x y)^k == x^k y^k   (Mathlib mul_pow)
def mul_pow(+x: Nat, +y: Nat, +k: Nat) -> {Nat.pow(Nat.mul(x, y), k) == Nat.mul(Nat.pow(x, k), Nat.pow(y, k)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +kp:
      %Equal.sym(Nat, Nat.pow(Nat.mul(x, y), kp), Nat.mul(Nat.pow(x, kp), Nat.pow(y, kp)), mul_pow(x, y, kp)) : {Nat.mul(Nat.mul(x, y), _) == Nat.mul(Nat.mul(x, Nat.pow(x, kp)), Nat.mul(y, Nat.pow(y, kp))) : Nat}
      mul_swap4(x, y, Nat.pow(x, kp), Nat.pow(y, kp))
