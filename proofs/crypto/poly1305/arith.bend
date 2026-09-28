import Base
import ../../../spec/lib/common.bend as C
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/arith.bend as AR
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/typed/width.bend as WW
import ../../math/typed/w64mul.bend as WM
import ../../math/typed/w64sh.bend as SH

# Small Nat facts for the Poly1305 proofs: equality plumbing, monotonicity of
# + and *, and fits (k-bit bounds, spec/lib/common.bend) for sums and
# products. No closed power of two is ever formed.

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

# a + b == a' + b'
def cadd(+a: Nat, +a2: Nat, +b: Nat, +b2: Nat, +ea: {a == a2 : Nat}, +eb: {b == b2 : Nat}) -> {Nat.add(a, b) == Nat.add(a2, b2) : Nat}:
  tr(Nat.add(a, b), Nat.add(a2, b), Nat.add(a2, b2), WM.cong_l(a, a2, b, ea), WM.cong_r(a2, b, b2, eb))

def cmul(+a: Nat, +a2: Nat, +b: Nat, +b2: Nat, +ea: {a == a2 : Nat}, +eb: {b == b2 : Nat}) -> {Nat.mul(a, b) == Nat.mul(a2, b2) : Nat}:
  tr(Nat.mul(a, b), Nat.mul(a2, b), Nat.mul(a2, b2), Equal.cong(Nat, Nat, t => Nat.mul(t, b), a, a2, ea), Equal.cong(Nat, Nat, t => Nat.mul(a2, t), b, b2, eb))

def csh(+k: Nat, +a: Nat, +b: Nat, +e: {a == b : Nat}) -> {C.shift(k, a) == C.shift(k, b) : Nat}:
  Equal.cong(Nat, Nat, t => C.shift(k, t), a, b, e)

# Bool rewriting of a proposition {x == True}
def btrue(+x: Bool, +y: Bool, +e: {x == y : Bool}, +h: {y == True{} : Bool}) -> {x == True{} : Bool}:
  Equal.trans(Bool, x, y, True{}, e, h)

def le_subst(+a: Nat, +b: Nat, +c: Nat, +e: {b == c : Nat}, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(a, z) == True{} : Bool}, b, c, e, h)

def le_substl(+a: Nat, +b: Nat, +c: Nat, +e: {a == b : Nat}, +h: {Nat.is_le(a, c) == True{} : Bool}) -> {Nat.is_le(b, c) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(z, c) == True{} : Bool}, a, b, e, h)

def lt_subst(+a: Nat, +b: Nat, +c: Nat, +e: {b == c : Nat}, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(a, z) == True{} : Bool}, b, c, e, h)

def lt_substl(+a: Nat, +b: Nat, +c: Nat, +e: {a == b : Nat}, +h: {Nat.is_lt(a, c) == True{} : Bool}) -> {Nat.is_lt(b, c) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(z, c) == True{} : Bool}, a, b, e, h)

def fits_subst(+k: Nat, +a: Nat, +b: Nat, +e: {a == b : Nat}, +h: {C.fits(k, a) == True{} : Bool}) -> {C.fits(k, b) == True{} : Bool}:
  L.subst(Nat, z => {C.fits(k, z) == True{} : Bool}, a, b, e, h)

# b <= a + b
def le_add_l(+a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  le_subst(b, Nat.add(b, a), Nat.add(a, b), N.add_comm(b, a), N.le_add_right(b, a))

# a <= c, b <= d: a + b <= c + d
def le_add2(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +h1: {Nat.is_le(a, c) == True{} : Bool}, +h2: {Nat.is_le(b, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, b), Nat.add(c, d)) == True{} : Bool}:
  N.le_trans(Nat.add(a, b), Nat.add(c, b), Nat.add(c, d), WW.le_add_r(a, c, b, h1), N.le_add_left(b, d, c, h2))

# a <= c, b <= d: a b <= c d
def le_mul2(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +h1: {Nat.is_le(a, c) == True{} : Bool}, +h2: {Nat.is_le(b, d) == True{} : Bool}) -> {Nat.is_le(Nat.mul(a, b), Nat.mul(c, d)) == True{} : Bool}:
  N.le_trans(Nat.mul(a, b), Nat.mul(c, b), Nat.mul(c, d), AR.mul_le(a, c, b, h1), WM.le_mul_r(c, b, d, h2))

# x <= y and y fits k bits: x fits k bits
def fits_le(+k: Nat, +x: Nat, +y: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}, +hy: {C.fits(k, y) == True{} : Bool}) -> {C.fits(k, x) == True{} : Bool}:
  SH.fits_lek(k, x, y, h, hy)

# x <= y + z and fits(k, y + z)
def fits_add_l(+k: Nat, +y: Nat, +z: Nat, +h: {C.fits(k, Nat.add(y, z)) == True{} : Bool}) -> {C.fits(k, y) == True{} : Bool}:
  fits_le(k, y, Nat.add(y, z), N.le_add_right(y, z), h)

def fits_add_r(+k: Nat, +y: Nat, +z: Nat, +h: {C.fits(k, Nat.add(y, z)) == True{} : Bool}) -> {C.fits(k, z) == True{} : Bool}:
  fits_le(k, z, Nat.add(y, z), le_add_l(y, z), h)

# a < c, b < d: a + b < c + d
def lt_add2(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +h1: {Nat.is_lt(a, c) == True{} : Bool}, +h2: {Nat.is_lt(b, d) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a, b), Nat.add(c, d)) == True{} : Bool}:
  N.lt_le_trans(Nat.add(a, b), Nat.add(c, b), Nat.add(c, d), N.lt_add_r2(a, c, b, h1), N.le_add_left(b, d, c, N.lt_le(b, d, h2)))

# a < c, b <= d: a + b < c + d
def lt_le_add(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +h1: {Nat.is_lt(a, c) == True{} : Bool}, +h2: {Nat.is_le(b, d) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a, b), Nat.add(c, d)) == True{} : Bool}:
  N.lt_le_trans(Nat.add(a, b), Nat.add(c, b), Nat.add(c, d), N.lt_add_r2(a, c, b, h1), N.le_add_left(b, d, c, h2))

# a and b fit k bits: a + b fits k + 1 bits
def fits_add(+k: Nat, +a: Nat, +b: Nat, +ha: {C.fits(k, a) == True{} : Bool}, +hb: {C.fits(k, b) == True{} : Bool}) -> {C.fits(1n+k, Nat.add(a, b)) == True{} : Bool}:
  +p = C.pow2(k)
  +s = lt_add2(a, b, p, p, WW.lt_of_fits(k, a, ha), WW.lt_of_fits(k, b, hb))
  WW.fits_of_lt(1n+k, Nat.add(a, b), lt_subst(Nat.add(a, b), Nat.add(p, p), Nat.double(p), sy(Nat.double(p), Nat.add(p, p), NA.double_self(p)), s))

# x < A, y < B: x y < A B
def lt_mul(+x: Nat, +y: Nat, +a: Nat, +b: Nat, +hx: {Nat.is_lt(x, a) == True{} : Bool}, +hy: {Nat.is_lt(y, b) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(x, y), Nat.mul(a, b)) == True{} : Bool}:
  match x:
    case 0n:
      match a b:
        case 0n _: Empty.absurd({Nat.is_lt(0n, Nat.mul(0n, b)) == True{} : Bool}, N.lt_zero_absurd(0n, hx))
        case 1n+ap 0n: Empty.absurd({Nat.is_lt(0n, Nat.mul(1n+ap, 0n)) == True{} : Bool}, N.lt_zero_absurd(y, hy))
        case 1n+ap 1n+bp: {==}
    case 1n+xp:
      +s1 = lt_le_add(y, Nat.mul(xp, y), b, Nat.mul(xp, b), hy, WM.le_mul_r(xp, y, b, N.lt_le(y, b, hy)))
      N.lt_le_trans(Nat.mul(1n+xp, y), Nat.mul(1n+xp, b), Nat.mul(a, b), s1, AR.mul_le(1n+xp, a, b, N.lt_le(1n+xp, a, hx)))

def pow2_add(+a: Nat, +b: Nat) -> {Nat.mul(C.pow2(a), C.pow2(b)) == C.pow2(Nat.add(a, b)) : Nat}:
  +pa = C.pow2(a)
  +pb = C.pow2(b)
  tr(Nat.mul(pa, pb), Nat.mul(pb, pa), C.pow2(Nat.add(a, b)), NA.mul_comm(pa, pb),
    tr(Nat.mul(pb, pa), Nat.mul(pb, C.shift(a, 1n)), C.pow2(Nat.add(a, b)), Equal.cong(Nat, Nat, t => Nat.mul(pb, t), pa, C.shift(a, 1n), sy(C.shift(a, 1n), pa, WW.shift_one(a))),
      tr(Nat.mul(pb, C.shift(a, 1n)), C.shift(a, pb), C.pow2(Nat.add(a, b)), sy(C.shift(a, pb), Nat.mul(pb, C.shift(a, 1n)), WW.shift_mul(a, pb)), WW.shift_pow2(a, b))))

# x fits a bits, y fits b bits: x y fits a + b bits
def fits_mul(+a: Nat, +b: Nat, +x: Nat, +y: Nat, +hx: {C.fits(a, x) == True{} : Bool}, +hy: {C.fits(b, y) == True{} : Bool}) -> {C.fits(Nat.add(a, b), Nat.mul(x, y)) == True{} : Bool}:
  WW.fits_of_lt(Nat.add(a, b), Nat.mul(x, y), lt_subst(Nat.mul(x, y), Nat.mul(C.pow2(a), C.pow2(b)), C.pow2(Nat.add(a, b)), pow2_add(a, b), lt_mul(x, y, C.pow2(a), C.pow2(b), WW.lt_of_fits(a, x, hx), WW.lt_of_fits(b, y, hy))))

# x fits k bits: x <= 2^k (with 2^k written C.shift(k, one), one = 1)
def le_one(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +h: {C.fits(k, x) == True{} : Bool}) -> {Nat.is_le(x, C.shift(k, one)) == True{} : Bool}:
  N.lt_le(x, C.shift(k, one), WW.lt_one(k, one, h1, x, h))

# 1 <= 2^k
def one_le_shift(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_le(1n, C.shift(k, one)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(z, C.shift(k, one)) == True{} : Bool}, one, 1n, h1, WW.shift_ge(k, one))

# x <= 2^k: x fits k + 1 bits
def fits_le_one(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +h: {Nat.is_le(x, C.shift(k, one)) == True{} : Bool}) -> {C.fits(1n+k, x) == True{} : Bool}:
  +s = C.shift(k, one)
  +h2 = N.le_lt_trans(x, s, Nat.double(s), h, lt_subst(s, Nat.add(s, s), Nat.double(s), sy(Nat.double(s), Nat.add(s, s), NA.double_self(s)), lt_le_add(0n, s, s, s, N.lt_le_trans(0n, 1n, s, {==}, one_le_shift(k, one, h1)), N.le_refl(s))))
  WW.fits_one(1n+k, one, h1, x, h2)

# 2^a 2^b = 2^(a+b)
def shmul(+a: Nat, +b: Nat, +one: Nat, +h1: {one == 1n : Nat}) -> {Nat.mul(C.shift(a, one), C.shift(b, one)) == C.shift(Nat.add(a, b), one) : Nat}:
  +sb = C.shift(b, one)
  tr(Nat.mul(C.shift(a, one), sb), C.shift(a, Nat.mul(one, sb)), C.shift(Nat.add(a, b), one), WW.shift_mul_l(a, one, sb),
    tr(C.shift(a, Nat.mul(one, sb)), C.shift(a, sb), C.shift(Nat.add(a, b), one),
      csh(a, Nat.mul(one, sb), sb, L.subst(Nat, z => {Nat.mul(z, sb) == sb : Nat}, 1n, one, sy(one, 1n, h1), AR.one_mul(sb))),
      sy(C.shift(Nat.add(a, b), one), C.shift(a, sb), WW.shift_comp(a, b, one))))

# 2^k c = c * 2^k
def mul_pow(+c: Nat, +k: Nat, +x: Nat) -> {Nat.mul(x, C.pow2(k)) == C.shift(k, x) : Nat}:
  tr(Nat.mul(x, C.pow2(k)), Nat.mul(x, C.shift(k, 1n)), C.shift(k, x), Equal.cong(Nat, Nat, t => Nat.mul(x, t), C.pow2(k), C.shift(k, 1n), sy(C.shift(k, 1n), C.pow2(k), WW.shift_one(k))), sy(C.shift(k, x), Nat.mul(x, C.shift(k, 1n)), WW.shift_mul(k, x)))
