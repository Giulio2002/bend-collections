import Base
import ../../../../spec/lib/common.bend as C
import ../../../../spec/math/w64.bend as SW
import ../../../../spec/math/random/pcg.bend as SP
import ../../../../src/math/u64.bend as WU
import ../../../../src/math/w64.bend as X
import ../../../../src/math/random/pcg.bend as P
import ../../../lib/lemmas/spec/numeric.bend as S
import ../../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../../lib/u32alg.bend as A
import ../../typed/width.bend as WW
import ../../typed/w64add.bend as WA
import ../../typed/w64m128.bend as M128
import ../../typed/w64mul.bend as W64M
import ../../typed/w64sh.bend as SH

# One PCG step (src/math/random/pcg.bend step_with) is the 128-bit LCG
# s * mul + inc mod 2^128 of spec/math/random/pcg.bend, for every state,
# multiplier and increment: the limb algebra of Go's (*PCG).next (a 64x64
# product, the cross products mod 2^64, and a carried 128-bit sum), closed by
# arithmetic mod 2^64 and 2^128 on the values (C.low), never forming a
# closed power of two.

# ---- arithmetic mod 2^k ----

def low_l(+k: Nat, +a: Nat, +b: Nat) -> {C.low(k, Nat.add(C.low(k, a), b)) == C.low(k, Nat.add(a, b)) : Nat}:
  +la = C.low(k, a)
  +h = C.high(k, a)
  +e1 = Equal.trans(Nat, Nat.add(a, b), Nat.add(Nat.add(la, C.shift(k, h)), b), Nat.add(Nat.add(la, b), C.shift(k, h)),
    Equal.cong(Nat, Nat, z => Nat.add(z, b), a, Nat.add(la, C.shift(k, h)), WW.low_high(k, a)),
    A.add_rot(la, C.shift(k, h), b))
  Equal.sym(Nat, C.low(k, Nat.add(a, b)), C.low(k, Nat.add(la, b)),
    Equal.trans(Nat, C.low(k, Nat.add(a, b)), C.low(k, Nat.add(Nat.add(la, b), C.shift(k, h))), C.low(k, Nat.add(la, b)),
      Equal.cong(Nat, Nat, z => C.low(k, z), Nat.add(a, b), Nat.add(Nat.add(la, b), C.shift(k, h)), e1),
      WW.low_add_shift(k, Nat.add(la, b), h)))

def low_r(+k: Nat, +a: Nat, +b: Nat) -> {C.low(k, Nat.add(a, C.low(k, b))) == C.low(k, Nat.add(a, b)) : Nat}:
  Equal.trans(Nat, C.low(k, Nat.add(a, C.low(k, b))), C.low(k, Nat.add(C.low(k, b), a)), C.low(k, Nat.add(a, b)),
    Equal.cong(Nat, Nat, z => C.low(k, z), Nat.add(a, C.low(k, b)), Nat.add(C.low(k, b), a), NA.add_comm(a, C.low(k, b))),
    Equal.trans(Nat, C.low(k, Nat.add(C.low(k, b), a)), C.low(k, Nat.add(b, a)), C.low(k, Nat.add(a, b)),
      low_l(k, b, a),
      Equal.cong(Nat, Nat, z => C.low(k, z), Nat.add(b, a), Nat.add(a, b), NA.add_comm(b, a))))

# congruence mod 2^k is kept by sums
def low_add(+k: Nat, +x: Nat, +x2: Nat, +y: Nat, +y2: Nat, +hx: {C.low(k, x) == C.low(k, x2) : Nat}, +hy: {C.low(k, y) == C.low(k, y2) : Nat}) -> {C.low(k, Nat.add(x, y)) == C.low(k, Nat.add(x2, y2)) : Nat}:
  +e1 = Equal.trans(Nat, C.low(k, Nat.add(x, y)), C.low(k, Nat.add(C.low(k, x), y)), C.low(k, Nat.add(C.low(k, x2), y)),
    Equal.sym(Nat, C.low(k, Nat.add(C.low(k, x), y)), C.low(k, Nat.add(x, y)), low_l(k, x, y)),
    Equal.cong(Nat, Nat, z => C.low(k, Nat.add(z, y)), C.low(k, x), C.low(k, x2), hx))
  +e2 = Equal.trans(Nat, C.low(k, Nat.add(C.low(k, x2), y)), C.low(k, Nat.add(x2, y)), C.low(k, Nat.add(x2, C.low(k, y))),
    low_l(k, x2, y),
    Equal.sym(Nat, C.low(k, Nat.add(x2, C.low(k, y))), C.low(k, Nat.add(x2, y)), low_r(k, x2, y)))
  +e3 = Equal.trans(Nat, C.low(k, Nat.add(x2, C.low(k, y))), C.low(k, Nat.add(x2, C.low(k, y2))), C.low(k, Nat.add(x2, y2)),
    Equal.cong(Nat, Nat, z => C.low(k, Nat.add(x2, z)), C.low(k, y), C.low(k, y2), hy),
    low_r(k, x2, y2))
  Equal.trans(Nat, C.low(k, Nat.add(x, y)), C.low(k, Nat.add(C.low(k, x2), y)), C.low(k, Nat.add(x2, y2)), e1,
    Equal.trans(Nat, C.low(k, Nat.add(C.low(k, x2), y)), C.low(k, Nat.add(x2, C.low(k, y))), C.low(k, Nat.add(x2, y2)), e2, e3))

def low_low(+k: Nat, +x: Nat) -> {C.low(k, C.low(k, x)) == C.low(k, x) : Nat}:
  WW.low_fit(k, C.low(k, x), WW.low_fits(k, x))

# mod 2^128, a + 2^64 b depends on b mod 2^64 only
def low_hi(+a: Nat, +b: Nat) -> {C.low(128n, Nat.add(a, C.shift(64n, b))) == C.low(128n, Nat.add(a, C.shift(64n, C.low(64n, b)))) : Nat}:
  +lb = C.low(64n, b)
  +hb = C.high(64n, b)
  +e1 = Equal.trans(Nat, C.shift(64n, b), C.shift(64n, Nat.add(lb, C.shift(64n, hb))), Nat.add(C.shift(64n, lb), C.shift(64n, C.shift(64n, hb))),
    Equal.cong(Nat, Nat, z => C.shift(64n, z), b, Nat.add(lb, C.shift(64n, hb)), WW.low_high(64n, b)),
    WW.shift_add(64n, lb, C.shift(64n, hb)))
  +e2 = Equal.sym(Nat, C.shift(128n, hb), C.shift(64n, C.shift(64n, hb)), WW.shift_comp(64n, 64n, hb))
  +e3 = Equal.trans(Nat, Nat.add(a, C.shift(64n, b)), Nat.add(a, Nat.add(C.shift(64n, lb), C.shift(128n, hb))), Nat.add(Nat.add(a, C.shift(64n, lb)), C.shift(128n, hb)),
    Equal.cong(Nat, Nat, z => Nat.add(a, z), C.shift(64n, b), Nat.add(C.shift(64n, lb), C.shift(128n, hb)),
      Equal.trans(Nat, C.shift(64n, b), Nat.add(C.shift(64n, lb), C.shift(64n, C.shift(64n, hb))), Nat.add(C.shift(64n, lb), C.shift(128n, hb)), e1,
        Equal.cong(Nat, Nat, z => Nat.add(C.shift(64n, lb), z), C.shift(64n, C.shift(64n, hb)), C.shift(128n, hb), e2))),
    Equal.sym(Nat, Nat.add(Nat.add(a, C.shift(64n, lb)), C.shift(128n, hb)), Nat.add(a, Nat.add(C.shift(64n, lb), C.shift(128n, hb))), NA.add_assoc(a, C.shift(64n, lb), C.shift(128n, hb))))
  Equal.trans(Nat, C.low(128n, Nat.add(a, C.shift(64n, b))), C.low(128n, Nat.add(Nat.add(a, C.shift(64n, lb)), C.shift(128n, hb))), C.low(128n, Nat.add(a, C.shift(64n, lb))),
    Equal.cong(Nat, Nat, z => C.low(128n, z), Nat.add(a, C.shift(64n, b)), Nat.add(Nat.add(a, C.shift(64n, lb)), C.shift(128n, hb)), e3),
    WW.low_add_shift(128n, Nat.add(a, C.shift(64n, lb)), hb))

# ---- rearrangements ----

# (((a + c) + d) + (e + g)) + (b + f) == (a + b) + (((c + (e + d)) + f) + g)
def perm7(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat, +f: Nat, +g: Nat) -> {Nat.add(Nat.add(Nat.add(Nat.add(a, c), d), Nat.add(e, g)), Nat.add(b, f)) == Nat.add(Nat.add(a, b), Nat.add(Nat.add(Nat.add(c, Nat.add(e, d)), f), g)) : Nat}:
  +R2 = Nat.add(e, Nat.add(f, g))
  +T = Nat.add(Nat.add(e, g), Nat.add(b, f))
  +CAN = Nat.add(a, Nat.add(b, Nat.add(c, Nat.add(d, R2))))
  +eT1 = Equal.trans(Nat, T, Nat.add(e, Nat.add(g, Nat.add(b, f))), Nat.add(e, Nat.add(b, Nat.add(g, f))),
    NA.add_assoc(e, g, Nat.add(b, f)),
    Equal.cong(Nat, Nat, z => Nat.add(e, z), Nat.add(g, Nat.add(b, f)), Nat.add(b, Nat.add(g, f)), NA.add_swap(g, b, f)))
  +eT2 = Equal.trans(Nat, Nat.add(e, Nat.add(b, Nat.add(g, f))), Nat.add(e, Nat.add(b, Nat.add(f, g))), Nat.add(b, R2),
    Equal.cong(Nat, Nat, z => Nat.add(e, Nat.add(b, z)), Nat.add(g, f), Nat.add(f, g), NA.add_comm(g, f)),
    NA.add_swap(e, b, Nat.add(f, g)))
  +eT = Equal.trans(Nat, T, Nat.add(e, Nat.add(b, Nat.add(g, f))), Nat.add(b, R2), eT1, eT2)
  +eU = Equal.trans(Nat, Nat.add(Nat.add(c, d), Nat.add(b, R2)), Nat.add(c, Nat.add(d, Nat.add(b, R2))), Nat.add(b, Nat.add(c, Nat.add(d, R2))),
    NA.add_assoc(c, d, Nat.add(b, R2)),
    Equal.trans(Nat, Nat.add(c, Nat.add(d, Nat.add(b, R2))), Nat.add(c, Nat.add(b, Nat.add(d, R2))), Nat.add(b, Nat.add(c, Nat.add(d, R2))),
      Equal.cong(Nat, Nat, z => Nat.add(c, z), Nat.add(d, Nat.add(b, R2)), Nat.add(b, Nat.add(d, R2)), NA.add_swap(d, b, R2)),
      NA.add_swap(c, b, Nat.add(d, R2))))
  +eL1 = Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.add(a, c), d), Nat.add(e, g)), Nat.add(b, f)), Nat.add(Nat.add(Nat.add(a, c), d), T), Nat.add(Nat.add(a, Nat.add(c, d)), T),
    NA.add_assoc(Nat.add(Nat.add(a, c), d), Nat.add(e, g), Nat.add(b, f)),
    Equal.cong(Nat, Nat, z => Nat.add(z, T), Nat.add(Nat.add(a, c), d), Nat.add(a, Nat.add(c, d)), NA.add_assoc(a, c, d)))
  +eL2 = Equal.trans(Nat, Nat.add(Nat.add(a, Nat.add(c, d)), T), Nat.add(a, Nat.add(Nat.add(c, d), T)), CAN,
    NA.add_assoc(a, Nat.add(c, d), T),
    Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(Nat.add(c, d), T), Nat.add(b, Nat.add(c, Nat.add(d, R2))),
      Equal.trans(Nat, Nat.add(Nat.add(c, d), T), Nat.add(Nat.add(c, d), Nat.add(b, R2)), Nat.add(b, Nat.add(c, Nat.add(d, R2))),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.add(c, d), z), T, Nat.add(b, R2), eT), eU)))
  +eL = Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.add(a, c), d), Nat.add(e, g)), Nat.add(b, f)), Nat.add(Nat.add(a, Nat.add(c, d)), T), CAN, eL1, eL2)
  +Rr = Nat.add(Nat.add(Nat.add(c, Nat.add(e, d)), f), g)
  +eR1 = Equal.trans(Nat, Rr, Nat.add(Nat.add(c, Nat.add(e, d)), Nat.add(f, g)), Nat.add(c, Nat.add(Nat.add(e, d), Nat.add(f, g))),
    NA.add_assoc(Nat.add(c, Nat.add(e, d)), f, g),
    NA.add_assoc(c, Nat.add(e, d), Nat.add(f, g)))
  +eR2 = Equal.trans(Nat, Nat.add(Nat.add(e, d), Nat.add(f, g)), Nat.add(e, Nat.add(d, Nat.add(f, g))), Nat.add(d, R2),
    NA.add_assoc(e, d, Nat.add(f, g)),
    NA.add_swap(e, d, Nat.add(f, g)))
  +eR = Equal.trans(Nat, Nat.add(Nat.add(a, b), Rr), Nat.add(a, Nat.add(b, Rr)), CAN,
    NA.add_assoc(a, b, Rr),
    Equal.cong(Nat, Nat, z => Nat.add(a, Nat.add(b, z)), Rr, Nat.add(c, Nat.add(d, R2)),
      Equal.trans(Nat, Rr, Nat.add(c, Nat.add(Nat.add(e, d), Nat.add(f, g))), Nat.add(c, Nat.add(d, R2)), eR1,
        Equal.cong(Nat, Nat, z => Nat.add(c, z), Nat.add(Nat.add(e, d), Nat.add(f, g)), Nat.add(d, R2), eR2))))
  Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.add(a, c), d), Nat.add(e, g)), Nat.add(b, f)), CAN, Nat.add(Nat.add(a, b), Rr), eL, Equal.sym(Nat, Nat.add(Nat.add(a, b), Rr), CAN, eR))

# (L + x) + (y + z) == L + ((y + x) + z)
def swap3(+L: Nat, +x: Nat, +y: Nat, +z: Nat) -> {Nat.add(Nat.add(L, x), Nat.add(y, z)) == Nat.add(L, Nat.add(Nat.add(y, x), z)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(L, x), Nat.add(y, z)), Nat.add(L, Nat.add(x, Nat.add(y, z))), Nat.add(L, Nat.add(Nat.add(y, x), z)),
    NA.add_assoc(L, x, Nat.add(y, z)),
    Equal.cong(Nat, Nat, t => Nat.add(L, t), Nat.add(x, Nat.add(y, z)), Nat.add(Nat.add(y, x), z),
      Equal.trans(Nat, Nat.add(x, Nat.add(y, z)), Nat.add(Nat.add(x, y), z), Nat.add(Nat.add(y, x), z),
        Equal.sym(Nat, Nat.add(Nat.add(x, y), z), Nat.add(x, Nat.add(y, z)), NA.add_assoc(x, y, z)),
        Equal.cong(Nat, Nat, t => Nat.add(t, z), Nat.add(x, y), Nat.add(y, x), NA.add_comm(x, y)))))

# 2^64 ((((h + (p2 + p1)) + i) + c) + 2^64 p3), distributed
def shx(+h: Nat, +p2: Nat, +p1: Nat, +i: Nat, +c: Nat, +p3: Nat) -> {C.shift(64n, Nat.add(Nat.add(Nat.add(Nat.add(h, Nat.add(p2, p1)), i), c), C.shift(64n, p3))) == Nat.add(Nat.add(Nat.add(Nat.add(C.shift(64n, h), Nat.add(C.shift(64n, p2), C.shift(64n, p1))), C.shift(64n, i)), C.shift(64n, c)), C.shift(64n, C.shift(64n, p3))) : Nat}:
  +w1 = Nat.add(Nat.add(h, Nat.add(p2, p1)), i)
  +ew1 = Equal.trans(Nat, C.shift(64n, w1), Nat.add(C.shift(64n, Nat.add(h, Nat.add(p2, p1))), C.shift(64n, i)), Nat.add(Nat.add(C.shift(64n, h), Nat.add(C.shift(64n, p2), C.shift(64n, p1))), C.shift(64n, i)),
    WW.shift_add(64n, Nat.add(h, Nat.add(p2, p1)), i),
    Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(64n, i)), C.shift(64n, Nat.add(h, Nat.add(p2, p1))), Nat.add(C.shift(64n, h), Nat.add(C.shift(64n, p2), C.shift(64n, p1))),
      Equal.trans(Nat, C.shift(64n, Nat.add(h, Nat.add(p2, p1))), Nat.add(C.shift(64n, h), C.shift(64n, Nat.add(p2, p1))), Nat.add(C.shift(64n, h), Nat.add(C.shift(64n, p2), C.shift(64n, p1))),
        WW.shift_add(64n, h, Nat.add(p2, p1)),
        Equal.cong(Nat, Nat, z => Nat.add(C.shift(64n, h), z), C.shift(64n, Nat.add(p2, p1)), Nat.add(C.shift(64n, p2), C.shift(64n, p1)), WW.shift_add(64n, p2, p1)))))
  Equal.trans(Nat, C.shift(64n, Nat.add(Nat.add(w1, c), C.shift(64n, p3))), Nat.add(C.shift(64n, Nat.add(w1, c)), C.shift(64n, C.shift(64n, p3))), Nat.add(Nat.add(Nat.add(Nat.add(C.shift(64n, h), Nat.add(C.shift(64n, p2), C.shift(64n, p1))), C.shift(64n, i)), C.shift(64n, c)), C.shift(64n, C.shift(64n, p3))),
    WW.shift_add(64n, Nat.add(w1, c), C.shift(64n, p3)),
    Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(64n, C.shift(64n, p3))), C.shift(64n, Nat.add(w1, c)), Nat.add(Nat.add(Nat.add(C.shift(64n, h), Nat.add(C.shift(64n, p2), C.shift(64n, p1))), C.shift(64n, i)), C.shift(64n, c)),
      Equal.trans(Nat, C.shift(64n, Nat.add(w1, c)), Nat.add(C.shift(64n, w1), C.shift(64n, c)), Nat.add(Nat.add(Nat.add(C.shift(64n, h), Nat.add(C.shift(64n, p2), C.shift(64n, p1))), C.shift(64n, i)), C.shift(64n, c)),
        WW.shift_add(64n, w1, c),
        Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(64n, c)), C.shift(64n, w1), Nat.add(Nat.add(C.shift(64n, h), Nat.add(C.shift(64n, p2), C.shift(64n, p1))), C.shift(64n, i)), ew1))))

# ---- the step on values ----

# s * M + I == L + 2^64 Z for Z = ((((h + (P2 + P1)) + i) + c) + 2^64 P3)
def expand(+vlo: Nat, +vhi: Nat, +vml: Nat, +vmh: Nat, +vil: Nat, +vih: Nat, +vl: Nat, +vh: Nat, +L: Nat, +c: Nat, +h1: {Nat.add(vl, C.shift(64n, vh)) == Nat.mul(vlo, vml) : Nat}, +h3: {Nat.add(vl, vil) == Nat.add(L, C.shift(64n, c)) : Nat}) -> {Nat.add(Nat.mul(Nat.add(vlo, C.shift(64n, vhi)), Nat.add(vml, C.shift(64n, vmh))), Nat.add(vil, C.shift(64n, vih))) == Nat.add(L, C.shift(64n, Nat.add(Nat.add(Nat.add(Nat.add(vh, Nat.add(Nat.mul(vhi, vml), Nat.mul(vlo, vmh))), vih), c), C.shift(64n, Nat.mul(vhi, vmh))))) : Nat}:
  +P1 = Nat.mul(vlo, vmh)
  +P2 = Nat.mul(vhi, vml)
  +P3 = Nat.mul(vhi, vmh)
  +a = vl
  +b = vil
  +cc = C.shift(64n, vh)
  +d = C.shift(64n, P1)
  +e = C.shift(64n, P2)
  +f = C.shift(64n, vih)
  +g = C.shift(64n, C.shift(64n, P3))
  +W0 = Nat.add(Nat.add(cc, Nat.add(e, d)), f)
  +s1 = Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(vlo, C.shift(64n, vhi)), Nat.add(vml, C.shift(64n, vmh))), Nat.add(b, f)), Nat.add(Nat.add(Nat.add(Nat.mul(vlo, vml), d), Nat.add(e, g)), Nat.add(b, f)), Nat.add(Nat.add(Nat.add(Nat.add(a, cc), d), Nat.add(e, g)), Nat.add(b, f)),
    Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(b, f)), Nat.mul(Nat.add(vlo, C.shift(64n, vhi)), Nat.add(vml, C.shift(64n, vmh))), Nat.add(Nat.add(Nat.mul(vlo, vml), d), Nat.add(e, g)), WW.expand_k(64n, vlo, vhi, vml, vmh)),
    Equal.cong(Nat, Nat, z => Nat.add(Nat.add(Nat.add(z, d), Nat.add(e, g)), Nat.add(b, f)), Nat.mul(vlo, vml), Nat.add(a, cc), Equal.sym(Nat, Nat.add(a, cc), Nat.mul(vlo, vml), h1)))
  +s2 = Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.add(a, cc), d), Nat.add(e, g)), Nat.add(b, f)), Nat.add(Nat.add(a, b), Nat.add(W0, g)), Nat.add(Nat.add(L, C.shift(64n, c)), Nat.add(W0, g)),
    perm7(a, b, cc, d, e, f, g),
    Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(W0, g)), Nat.add(a, b), Nat.add(L, C.shift(64n, c)), h3))
  +s3 = Equal.trans(Nat, Nat.add(Nat.add(L, C.shift(64n, c)), Nat.add(W0, g)), Nat.add(L, Nat.add(Nat.add(W0, C.shift(64n, c)), g)), Nat.add(L, C.shift(64n, Nat.add(Nat.add(Nat.add(Nat.add(vh, Nat.add(P2, P1)), vih), c), C.shift(64n, P3)))),
    swap3(L, C.shift(64n, c), W0, g),
    Equal.cong(Nat, Nat, z => Nat.add(L, z), Nat.add(Nat.add(W0, C.shift(64n, c)), g), C.shift(64n, Nat.add(Nat.add(Nat.add(Nat.add(vh, Nat.add(P2, P1)), vih), c), C.shift(64n, P3))),
      Equal.sym(Nat, C.shift(64n, Nat.add(Nat.add(Nat.add(Nat.add(vh, Nat.add(P2, P1)), vih), c), C.shift(64n, P3))), Nat.add(Nat.add(W0, C.shift(64n, c)), g), shx(vh, P2, P1, vih, c, P3))))
  Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(vlo, C.shift(64n, vhi)), Nat.add(vml, C.shift(64n, vmh))), Nat.add(b, f)), Nat.add(Nat.add(Nat.add(Nat.add(a, cc), d), Nat.add(e, g)), Nat.add(b, f)), Nat.add(L, C.shift(64n, Nat.add(Nat.add(Nat.add(Nat.add(vh, Nat.add(P2, P1)), vih), c), C.shift(64n, P3)))), s1,
    Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.add(a, cc), d), Nat.add(e, g)), Nat.add(b, f)), Nat.add(Nat.add(L, C.shift(64n, c)), Nat.add(W0, g)), Nat.add(L, C.shift(64n, Nat.add(Nat.add(Nat.add(Nat.add(vh, Nat.add(P2, P1)), vih), c), C.shift(64n, P3)))), s2, s3))

# the new high word is Z mod 2^64
def high_word(+vlo: Nat, +vhi: Nat, +vml: Nat, +vmh: Nat, +vih: Nat, +vh: Nat, +vH: Nat, +c: Nat, +vH2: Nat, +h2: {vH == C.low(64n, Nat.add(vh, C.low(64n, Nat.add(C.low(64n, Nat.mul(vhi, vml)), C.low(64n, Nat.mul(vlo, vmh)))))) : Nat}, +h4: {vH2 == C.low(64n, Nat.add(C.low(64n, Nat.add(vH, vih)), c)) : Nat}) -> {C.low(64n, Nat.add(Nat.add(Nat.add(Nat.add(vh, Nat.add(Nat.mul(vhi, vml), Nat.mul(vlo, vmh))), vih), c), C.shift(64n, Nat.mul(vhi, vmh)))) == vH2 : Nat}:
  +P1 = Nat.mul(vlo, vmh)
  +P2 = Nat.mul(vhi, vml)
  +W1 = Nat.add(Nat.add(vh, Nat.add(P2, P1)), vih)
  +eP = Equal.trans(Nat, C.low(64n, C.low(64n, Nat.add(C.low(64n, P2), C.low(64n, P1)))), C.low(64n, Nat.add(C.low(64n, P2), C.low(64n, P1))), C.low(64n, Nat.add(P2, P1)),
    low_low(64n, Nat.add(C.low(64n, P2), C.low(64n, P1))),
    low_add(64n, C.low(64n, P2), P2, C.low(64n, P1), P1, low_low(64n, P2), low_low(64n, P1)))
  +X0 = Nat.add(vh, C.low(64n, Nat.add(C.low(64n, P2), C.low(64n, P1))))
  +eH = Equal.trans(Nat, C.low(64n, vH), C.low(64n, C.low(64n, X0)), C.low(64n, Nat.add(vh, Nat.add(P2, P1))),
    Equal.cong(Nat, Nat, z => C.low(64n, z), vH, C.low(64n, X0), h2),
    Equal.trans(Nat, C.low(64n, C.low(64n, X0)), C.low(64n, X0), C.low(64n, Nat.add(vh, Nat.add(P2, P1))),
      low_low(64n, X0),
      low_add(64n, vh, vh, C.low(64n, Nat.add(C.low(64n, P2), C.low(64n, P1))), Nat.add(P2, P1), {==}, eP)))
  +eI = Equal.trans(Nat, C.low(64n, C.low(64n, Nat.add(vH, vih))), C.low(64n, Nat.add(vH, vih)), C.low(64n, W1),
    low_low(64n, Nat.add(vH, vih)),
    low_add(64n, vH, Nat.add(vh, Nat.add(P2, P1)), vih, vih, eH, {==}))
  +eZ = Equal.trans(Nat, C.low(64n, Nat.add(Nat.add(W1, c), C.shift(64n, Nat.mul(vhi, vmh)))), C.low(64n, Nat.add(W1, c)), C.low(64n, Nat.add(C.low(64n, Nat.add(vH, vih)), c)),
    WW.low_add_shift(64n, Nat.add(W1, c), Nat.mul(vhi, vmh)),
    Equal.sym(Nat, C.low(64n, Nat.add(C.low(64n, Nat.add(vH, vih)), c)), C.low(64n, Nat.add(W1, c)), low_add(64n, C.low(64n, Nat.add(vH, vih)), W1, c, c, eI, {==})))
  Equal.trans(Nat, C.low(64n, Nat.add(Nat.add(W1, c), C.shift(64n, Nat.mul(vhi, vmh)))), C.low(64n, Nat.add(C.low(64n, Nat.add(vH, vih)), c)), vH2, eZ, Equal.sym(Nat, vH2, C.low(64n, Nat.add(C.low(64n, Nat.add(vH, vih)), c)), h4))

# THEOREM on values: the limb results are the LCG step mod 2^128
def main(+vlo: Nat, +vhi: Nat, +vml: Nat, +vmh: Nat, +vil: Nat, +vih: Nat, +vl: Nat, +vh: Nat, +vH: Nat, +L: Nat, +c: Nat, +vH2: Nat, +h1: {Nat.add(vl, C.shift(64n, vh)) == Nat.mul(vlo, vml) : Nat}, +h2: {vH == C.low(64n, Nat.add(vh, C.low(64n, Nat.add(C.low(64n, Nat.mul(vhi, vml)), C.low(64n, Nat.mul(vlo, vmh)))))) : Nat}, +h3: {Nat.add(vl, vil) == Nat.add(L, C.shift(64n, c)) : Nat}, +h4: {vH2 == C.low(64n, Nat.add(C.low(64n, Nat.add(vH, vih)), c)) : Nat}, +hL: {C.fits(64n, L) == True{} : Bool}, +hH: {C.fits(64n, vH2) == True{} : Bool}) -> {Nat.add(L, C.shift(64n, vH2)) == SP.lcg(Nat.add(vml, C.shift(64n, vmh)), Nat.add(vil, C.shift(64n, vih)), Nat.add(vlo, C.shift(64n, vhi))) : Nat}:
  +Z = Nat.add(Nat.add(Nat.add(Nat.add(vh, Nat.add(Nat.mul(vhi, vml), Nat.mul(vlo, vmh))), vih), c), C.shift(64n, Nat.mul(vhi, vmh)))
  +SMI = Nat.add(Nat.mul(Nat.add(vlo, C.shift(64n, vhi)), Nat.add(vml, C.shift(64n, vmh))), Nat.add(vil, C.shift(64n, vih)))
  +e1 = Equal.trans(Nat, C.low(128n, SMI), C.low(128n, Nat.add(L, C.shift(64n, Z))), C.low(128n, Nat.add(L, C.shift(64n, C.low(64n, Z)))),
    Equal.cong(Nat, Nat, z => C.low(128n, z), SMI, Nat.add(L, C.shift(64n, Z)), expand(vlo, vhi, vml, vmh, vil, vih, vl, vh, L, c, h1, h3)),
    low_hi(L, Z))
  +e2 = Equal.trans(Nat, C.low(128n, Nat.add(L, C.shift(64n, C.low(64n, Z)))), C.low(128n, Nat.add(L, C.shift(64n, vH2))), Nat.add(L, C.shift(64n, vH2)),
    Equal.cong(Nat, Nat, z => C.low(128n, Nat.add(L, C.shift(64n, z))), C.low(64n, Z), vH2, high_word(vlo, vhi, vml, vmh, vih, vh, vH, c, vH2, h2, h4)),
    WW.low_fit(128n, Nat.add(L, C.shift(64n, vH2)), WW.limbs_fit(64n, 64n, L, vH2, hL, hH)))
  Equal.sym(Nat, C.low(128n, SMI), Nat.add(L, C.shift(64n, vH2)), Equal.trans(Nat, C.low(128n, SMI), C.low(128n, Nat.add(L, C.shift(64n, C.low(64n, Z)))), Nat.add(L, C.shift(64n, vH2)), e1, e2))

# ---- the implementation's words ----

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def carry_value(+c: Bool) -> {SW.value(WU.U64{X.b32(c), 0}) == S.bit_value(c) : Nat}:
  Equal.trans(Nat, SW.value(WU.U64{X.b32(c), 0}), v(X.b32(c)), S.bit_value(c), SH.val0(X.b32(c)), W64M.b32_v(c))

# step_mul for any product pair (l, h) with l + 2^64 h == lo * ml
def step_pair(+mh: WU.U64, +ml: WU.U64, +ih: WU.U64, +il: WU.U64, +hi: WU.U64, +lo: WU.U64, +pr: WU.U64 & WU.U64, +h1: {Nat.add(SW.value(X.pfst(pr)), C.shift(64n, SW.value(X.psnd(pr)))) == Nat.mul(SW.value(lo), SW.value(ml)) : Nat}) -> {Nat.add(SW.value(X.add(X.pfst(pr), il)), C.shift(64n, SW.value(X.add(X.add(X.add(X.psnd(pr), X.add(X.mul(hi, ml), X.mul(lo, mh))), ih), WU.U64{X.b32(X.add_over(X.pfst(pr), il)), 0})))) == SP.lcg(Nat.add(SW.value(ml), C.shift(64n, SW.value(mh))), Nat.add(SW.value(il), C.shift(64n, SW.value(ih))), Nat.add(SW.value(lo), C.shift(64n, SW.value(hi)))) : Nat}:
  match pr:
    case Tuple{+l, +h}:
      +m1 = X.mul(hi, ml)
      +m2 = X.mul(lo, mh)
      +t = X.add(m1, m2)
      +H = X.add(h, t)
      +H1 = X.add(H, ih)
      +cb = X.add_over(l, il)
      +H2 = X.add(H1, WU.U64{X.b32(cb), 0})
      +et = Equal.trans(Nat, SW.value(t), C.low(64n, Nat.add(SW.value(m1), SW.value(m2))), C.low(64n, Nat.add(C.low(64n, Nat.mul(SW.value(hi), SW.value(ml))), C.low(64n, Nat.mul(SW.value(lo), SW.value(mh))))),
        WA.add_value(m1, m2),
        Equal.trans(Nat, C.low(64n, Nat.add(SW.value(m1), SW.value(m2))), C.low(64n, Nat.add(C.low(64n, Nat.mul(SW.value(hi), SW.value(ml))), SW.value(m2))), C.low(64n, Nat.add(C.low(64n, Nat.mul(SW.value(hi), SW.value(ml))), C.low(64n, Nat.mul(SW.value(lo), SW.value(mh))))),
          Equal.cong(Nat, Nat, z => C.low(64n, Nat.add(z, SW.value(m2))), SW.value(m1), C.low(64n, Nat.mul(SW.value(hi), SW.value(ml))), WA.mul_value(hi, ml)),
          Equal.cong(Nat, Nat, z => C.low(64n, Nat.add(C.low(64n, Nat.mul(SW.value(hi), SW.value(ml))), z)), SW.value(m2), C.low(64n, Nat.mul(SW.value(lo), SW.value(mh))), WA.mul_value(lo, mh))))
      +h2 = Equal.trans(Nat, SW.value(H), C.low(64n, Nat.add(SW.value(h), SW.value(t))), C.low(64n, Nat.add(SW.value(h), C.low(64n, Nat.add(C.low(64n, Nat.mul(SW.value(hi), SW.value(ml))), C.low(64n, Nat.mul(SW.value(lo), SW.value(mh))))))),
        WA.add_value(h, t),
        Equal.cong(Nat, Nat, z => C.low(64n, Nat.add(SW.value(h), z)), SW.value(t), C.low(64n, Nat.add(C.low(64n, Nat.mul(SW.value(hi), SW.value(ml))), C.low(64n, Nat.mul(SW.value(lo), SW.value(mh))))), et))
      +h3 = M128.add_split(l, il)
      +h4 = Equal.trans(Nat, SW.value(H2), C.low(64n, Nat.add(SW.value(H1), SW.value(WU.U64{X.b32(cb), 0}))), C.low(64n, Nat.add(C.low(64n, Nat.add(SW.value(H), SW.value(ih))), S.bit_value(cb))),
        WA.add_value(H1, WU.U64{X.b32(cb), 0}),
        Equal.trans(Nat, C.low(64n, Nat.add(SW.value(H1), SW.value(WU.U64{X.b32(cb), 0}))), C.low(64n, Nat.add(C.low(64n, Nat.add(SW.value(H), SW.value(ih))), SW.value(WU.U64{X.b32(cb), 0}))), C.low(64n, Nat.add(C.low(64n, Nat.add(SW.value(H), SW.value(ih))), S.bit_value(cb))),
          Equal.cong(Nat, Nat, z => C.low(64n, Nat.add(z, SW.value(WU.U64{X.b32(cb), 0}))), SW.value(H1), C.low(64n, Nat.add(SW.value(H), SW.value(ih))), WA.add_value(H, ih)),
          Equal.cong(Nat, Nat, z => C.low(64n, Nat.add(C.low(64n, Nat.add(SW.value(H), SW.value(ih))), z)), SW.value(WU.U64{X.b32(cb), 0}), S.bit_value(cb), carry_value(cb))))
      main(SW.value(lo), SW.value(hi), SW.value(ml), SW.value(mh), SW.value(il), SW.value(ih), SW.value(l), SW.value(h), SW.value(H), SW.value(X.add(l, il)), S.bit_value(cb), SW.value(H2), h1, h2, h3, h4, M128.fit64(X.add(l, il)), M128.fit64(H2))

def m128(+a: WU.U64, +b: WU.U64) -> {Nat.add(SW.value(X.pfst(X.mul128(a, b))), C.shift(64n, SW.value(X.psnd(X.mul128(a, b))))) == Nat.mul(SW.value(a), SW.value(b)) : Nat}:
  match a b:
    case WU.U64{+al, +ah} WU.U64{+bl, +bh}:
      M128.m128_value(al, ah, bl, bh)
