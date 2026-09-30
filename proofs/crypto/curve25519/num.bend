import Base
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/lemmas/proofs/nat_algebra.bend as NA

# Order and power-of-two helpers for the curve25519 proofs. Powers of two
# are WD.sc(k, one) with a symbolic one (spec/crypto/curve25519/field.bend).

# ---- equalities ----

def cong_l(+x: Nat, +y: Nat, +z: Nat, +e: {x == y : Nat}) -> {Nat.add(x, z) == Nat.add(y, z) : Nat}:
  Equal.cong(Nat, Nat, t => Nat.add(t, z), x, y, e)

def cong_r(+z: Nat, +x: Nat, +y: Nat, +e: {x == y : Nat}) -> {Nat.add(z, x) == Nat.add(z, y) : Nat}:
  Equal.cong(Nat, Nat, t => Nat.add(z, t), x, y, e)

def cong_add(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e1: {a == b : Nat}, +e2: {c == d : Nat}) -> {Nat.add(a, c) == Nat.add(b, d) : Nat}:
  Equal.trans(Nat, Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), cong_l(a, b, c, e1), cong_r(b, c, d, e2))

def cong_mul(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e1: {a == b : Nat}, +e2: {c == d : Nat}) -> {Nat.mul(a, c) == Nat.mul(b, d) : Nat}:
  Equal.trans(Nat, Nat.mul(a, c), Nat.mul(b, c), Nat.mul(b, d), Equal.cong(Nat, Nat, t => Nat.mul(t, c), a, b, e1), Equal.cong(Nat, Nat, t => Nat.mul(b, t), c, d, e2))

def cong_sc(+k: Nat, +x: Nat, +y: Nat, +e: {x == y : Nat}) -> {WD.sc(k, x) == WD.sc(k, y) : Nat}:
  Equal.cong(Nat, Nat, t => WD.sc(k, t), x, y, e)

def cong_mod(+m: Nat, +x: Nat, +y: Nat, +e: {x == y : Nat}) -> {Nat.mod(x, m) == Nat.mod(y, m) : Nat}:
  Equal.cong(Nat, Nat, t => Nat.mod(t, m), x, y, e)

# (a + b) + (c + d) == (a + c) + (b + d)
def add4(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)), NA.add_assoc(a, b, Nat.add(c, d)),
    Equal.trans(Nat, Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(a, Nat.add(c, Nat.add(b, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)), cong_r(a, Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), NA.add_swap(b, c, d)),
      Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))), NA.add_assoc(a, c, Nat.add(b, d)))))

# 2^k x + 2^k y == 2^k (x + y)
def sc_add(+k: Nat, +x: Nat, +y: Nat) -> {Nat.add(WD.sc(k, x), WD.sc(k, y)) == WD.sc(k, Nat.add(x, y)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      +e = sc_add(q, x, y)
      +d = Equal.sym(Nat, Nat.double(Nat.add(WD.sc(q, x), WD.sc(q, y))), Nat.add(Nat.double(WD.sc(q, x)), Nat.double(WD.sc(q, y))), NA.double_add(WD.sc(q, x), WD.sc(q, y)))
      Equal.trans(Nat, Nat.add(Nat.double(WD.sc(q, x)), Nat.double(WD.sc(q, y))), Nat.double(Nat.add(WD.sc(q, x), WD.sc(q, y))), Nat.double(WD.sc(q, Nat.add(x, y))), d, Equal.cong(Nat, Nat, t => Nat.double(t), Nat.add(WD.sc(q, x), WD.sc(q, y)), WD.sc(q, Nat.add(x, y)), e))

# 2^k x + 2^k x == 2^(k+1) x
def sc_dbl(+k: Nat, +x: Nat) -> {Nat.add(WD.sc(k, x), WD.sc(k, x)) == WD.sc(1n+k, x) : Nat}:
  Equal.sym(Nat, Nat.double(WD.sc(k, x)), Nat.add(WD.sc(k, x), WD.sc(k, x)), NA.double_self(WD.sc(k, x)))

# 2^j (2^k x) == 2^(j+k) x
def sc_sc(+j: Nat, +k: Nat, +x: Nat) -> {WD.sc(j, WD.sc(k, x)) == WD.sc(Nat.add(j, k), x) : Nat}:
  Equal.sym(Nat, WD.sc(Nat.add(j, k), x), WD.sc(j, WD.sc(k, x)), AR.sc_idx(j, k, x))

# x 2^k == 2^k x
def mul_sc_r(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: Nat) -> {Nat.mul(x, WD.sc(k, one)) == WD.sc(k, x) : Nat}:
  AR.mul_sc1(k, one, h1, x)

# (2^j x)(2^k y) == 2^(j+k) (x y)
def mul_sc2(+j: Nat, +k: Nat, +x: Nat, +y: Nat) -> {Nat.mul(WD.sc(j, x), WD.sc(k, y)) == WD.sc(Nat.add(j, k), Nat.mul(x, y)) : Nat}:
  +a = Equal.sym(Nat, WD.sc(j, Nat.mul(x, WD.sc(k, y))), Nat.mul(WD.sc(j, x), WD.sc(k, y)), AR.sc_mul(j, x, WD.sc(k, y)))
  +b0 = Equal.trans(Nat, Nat.mul(x, WD.sc(k, y)), Nat.mul(WD.sc(k, y), x), WD.sc(k, Nat.mul(y, x)), NA.mul_comm(x, WD.sc(k, y)), Equal.sym(Nat, WD.sc(k, Nat.mul(y, x)), Nat.mul(WD.sc(k, y), x), AR.sc_mul(k, y, x)))
  +b = Equal.trans(Nat, Nat.mul(x, WD.sc(k, y)), WD.sc(k, Nat.mul(y, x)), WD.sc(k, Nat.mul(x, y)), b0, cong_sc(k, Nat.mul(y, x), Nat.mul(x, y), NA.mul_comm(y, x)))
  Equal.trans(Nat, Nat.mul(WD.sc(j, x), WD.sc(k, y)), WD.sc(j, Nat.mul(x, WD.sc(k, y))), WD.sc(Nat.add(j, k), Nat.mul(x, y)), a,
    Equal.trans(Nat, WD.sc(j, Nat.mul(x, WD.sc(k, y))), WD.sc(j, WD.sc(k, Nat.mul(x, y))), WD.sc(Nat.add(j, k), Nat.mul(x, y)), cong_sc(j, Nat.mul(x, WD.sc(k, y)), WD.sc(k, Nat.mul(x, y)), b), sc_sc(j, k, Nat.mul(x, y))))

# ---- order ----

def le_refl(+x: Nat) -> {Nat.is_le(x, x) == True{} : Bool}:
  N.le_refl(x)

# x <= a -> x + y <= a + y
def le_add_r(+x: Nat, +a: Nat, +y: Nat, +h: {Nat.is_le(x, a) == True{} : Bool}) -> {Nat.is_le(Nat.add(x, y), Nat.add(a, y)) == True{} : Bool}:
  +e1 = N.le_add_left(x, a, y, h)
  %NA.add_comm(y, x) : {Nat.is_le(_, Nat.add(a, y)) == True{} : Bool}
  %NA.add_comm(y, a) : {Nat.is_le(Nat.add(y, x), _) == True{} : Bool}
  e1

def le_add2(+x: Nat, +y: Nat, +a: Nat, +b: Nat, +hx: {Nat.is_le(x, a) == True{} : Bool}, +hy: {Nat.is_le(y, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(x, y), Nat.add(a, b)) == True{} : Bool}:
  N.le_trans(Nat.add(x, y), Nat.add(a, y), Nat.add(a, b), le_add_r(x, a, y, hx), N.le_add_left(y, b, a, hy))

# x <= a, y <= b -> x y <= a b
def le_mul2(+x: Nat, +y: Nat, +a: Nat, +b: Nat, +hx: {Nat.is_le(x, a) == True{} : Bool}, +hy: {Nat.is_le(y, b) == True{} : Bool}) -> {Nat.is_le(Nat.mul(x, y), Nat.mul(a, b)) == True{} : Bool}:
  +e1 = AR.mul_le(x, a, y, hx)
  +e2 = AR.mul_le(y, b, a, hy)
  +e2c = L.subst(Nat, z => {Nat.is_le(z, Nat.mul(b, a)) == True{} : Bool}, Nat.mul(y, a), Nat.mul(a, y), NA.mul_comm(y, a), e2)
  +e2d = L.subst(Nat, z => {Nat.is_le(Nat.mul(a, y), z) == True{} : Bool}, Nat.mul(b, a), Nat.mul(a, b), NA.mul_comm(b, a), e2c)
  N.le_trans(Nat.mul(x, y), Nat.mul(a, y), Nat.mul(a, b), e1, e2d)

def le_sc(+k: Nat, +x: Nat, +a: Nat, +h: {Nat.is_le(x, a) == True{} : Bool}) -> {Nat.is_le(WD.sc(k, x), WD.sc(k, a)) == True{} : Bool}:
  AR.sc_le(k, x, a, h)

# 2^a <= 2^b for a <= b, with b = d + a
def sc_mono(+d: Nat, +a: Nat, +x: Nat) -> {Nat.is_le(WD.sc(a, x), WD.sc(Nat.add(d, a), x)) == True{} : Bool}:
  %sc_sc(d, a, x) : {Nat.is_le(WD.sc(a, x), _) == True{} : Bool}
  AR.le_sc(d, WD.sc(a, x))
