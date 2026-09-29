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

# mod 2^128, a + 2^64 b depends on b mod 2^64 = lb only
def low_hi(+k: Nat, +a: Nat, +b: Nat, +lb: Nat, +hlb: {lb == C.low(k, b) : Nat}) -> {C.low(Nat.add(k, k), Nat.add(a, C.shift(k, b))) == C.low(Nat.add(k, k), Nat.add(a, C.shift(k, lb))) : Nat}:
  +hb = C.high(k, b)
  +shb = C.shift(k, hb)
  +e0 = Equal.trans(Nat, b, Nat.add(C.low(k, b), shb), Nat.add(lb, shb), WW.low_high(k, b), Equal.cong(Nat, Nat, z => Nat.add(z, shb), C.low(k, b), lb, Equal.sym(Nat, lb, C.low(k, b), hlb)))
  +e1 = Equal.trans(Nat, C.shift(k, b), C.shift(k, Nat.add(lb, shb)), Nat.add(C.shift(k, lb), C.shift(k, shb)),
    Equal.cong(Nat, Nat, z => C.shift(k, z), b, Nat.add(lb, shb), e0),
    WW.shift_add(k, lb, shb))
  +e2 = Equal.sym(Nat, C.shift(Nat.add(k, k), hb), C.shift(k, shb), WW.shift_comp(k, k, hb))
  +sl = C.shift(k, lb)
  +sh2 = C.shift(Nat.add(k, k), hb)
  +e3 = Equal.trans(Nat, Nat.add(a, C.shift(k, b)), Nat.add(a, Nat.add(sl, sh2)), Nat.add(Nat.add(a, sl), sh2),
    Equal.cong(Nat, Nat, z => Nat.add(a, z), C.shift(k, b), Nat.add(sl, sh2),
      Equal.trans(Nat, C.shift(k, b), Nat.add(sl, C.shift(k, shb)), Nat.add(sl, sh2), e1,
        Equal.cong(Nat, Nat, z => Nat.add(sl, z), C.shift(k, shb), sh2, e2))),
    Equal.sym(Nat, Nat.add(Nat.add(a, sl), sh2), Nat.add(a, Nat.add(sl, sh2)), NA.add_assoc(a, sl, sh2)))
  Equal.trans(Nat, C.low(Nat.add(k, k), Nat.add(a, C.shift(k, b))), C.low(Nat.add(k, k), Nat.add(Nat.add(a, sl), sh2)), C.low(Nat.add(k, k), Nat.add(a, sl)),
    Equal.cong(Nat, Nat, z => C.low(Nat.add(k, k), z), Nat.add(a, C.shift(k, b)), Nat.add(Nat.add(a, sl), sh2), e3),
    WW.low_add_shift(Nat.add(k, k), Nat.add(a, sl), hb))

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
def shx(+k: Nat, +h: Nat, +p2: Nat, +p1: Nat, +i: Nat, +c: Nat, +p3: Nat) -> {C.shift(k, Nat.add(Nat.add(Nat.add(Nat.add(h, Nat.add(p2, p1)), i), c), C.shift(k, p3))) == Nat.add(Nat.add(Nat.add(Nat.add(C.shift(k, h), Nat.add(C.shift(k, p2), C.shift(k, p1))), C.shift(k, i)), C.shift(k, c)), C.shift(k, C.shift(k, p3))) : Nat}:
  +w1 = Nat.add(Nat.add(h, Nat.add(p2, p1)), i)
  +ew1 = Equal.trans(Nat, C.shift(k, w1), Nat.add(C.shift(k, Nat.add(h, Nat.add(p2, p1))), C.shift(k, i)), Nat.add(Nat.add(C.shift(k, h), Nat.add(C.shift(k, p2), C.shift(k, p1))), C.shift(k, i)),
    WW.shift_add(k, Nat.add(h, Nat.add(p2, p1)), i),
    Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(k, i)), C.shift(k, Nat.add(h, Nat.add(p2, p1))), Nat.add(C.shift(k, h), Nat.add(C.shift(k, p2), C.shift(k, p1))),
      Equal.trans(Nat, C.shift(k, Nat.add(h, Nat.add(p2, p1))), Nat.add(C.shift(k, h), C.shift(k, Nat.add(p2, p1))), Nat.add(C.shift(k, h), Nat.add(C.shift(k, p2), C.shift(k, p1))),
        WW.shift_add(k, h, Nat.add(p2, p1)),
        Equal.cong(Nat, Nat, z => Nat.add(C.shift(k, h), z), C.shift(k, Nat.add(p2, p1)), Nat.add(C.shift(k, p2), C.shift(k, p1)), WW.shift_add(k, p2, p1)))))
  Equal.trans(Nat, C.shift(k, Nat.add(Nat.add(w1, c), C.shift(k, p3))), Nat.add(C.shift(k, Nat.add(w1, c)), C.shift(k, C.shift(k, p3))), Nat.add(Nat.add(Nat.add(Nat.add(C.shift(k, h), Nat.add(C.shift(k, p2), C.shift(k, p1))), C.shift(k, i)), C.shift(k, c)), C.shift(k, C.shift(k, p3))),
    WW.shift_add(k, Nat.add(w1, c), C.shift(k, p3)),
    Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(k, C.shift(k, p3))), C.shift(k, Nat.add(w1, c)), Nat.add(Nat.add(Nat.add(C.shift(k, h), Nat.add(C.shift(k, p2), C.shift(k, p1))), C.shift(k, i)), C.shift(k, c)),
      Equal.trans(Nat, C.shift(k, Nat.add(w1, c)), Nat.add(C.shift(k, w1), C.shift(k, c)), Nat.add(Nat.add(Nat.add(C.shift(k, h), Nat.add(C.shift(k, p2), C.shift(k, p1))), C.shift(k, i)), C.shift(k, c)),
        WW.shift_add(k, w1, c),
        Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(k, c)), C.shift(k, w1), Nat.add(Nat.add(C.shift(k, h), Nat.add(C.shift(k, p2), C.shift(k, p1))), C.shift(k, i)), ew1))))

# ---- the step on values ----

# s * M + I == L + 2^64 Z for Z = ((((h + (P2 + P1)) + i) + c) + 2^64 P3)
def expand(+k: Nat, +vlo: Nat, +vhi: Nat, +vml: Nat, +vmh: Nat, +vil: Nat, +vih: Nat, +vl: Nat, +vh: Nat, +L: Nat, +c: Nat, +h1: {Nat.add(vl, C.shift(k, vh)) == Nat.mul(vlo, vml) : Nat}, +h3: {Nat.add(vl, vil) == Nat.add(L, C.shift(k, c)) : Nat}) -> {Nat.add(Nat.mul(Nat.add(vlo, C.shift(k, vhi)), Nat.add(vml, C.shift(k, vmh))), Nat.add(vil, C.shift(k, vih))) == Nat.add(L, C.shift(k, Nat.add(Nat.add(Nat.add(Nat.add(vh, Nat.add(Nat.mul(vhi, vml), Nat.mul(vlo, vmh))), vih), c), C.shift(k, Nat.mul(vhi, vmh))))) : Nat}:
  +P1 = Nat.mul(vlo, vmh)
  +P2 = Nat.mul(vhi, vml)
  +P3 = Nat.mul(vhi, vmh)
  +a = vl
  +b = vil
  +cc = C.shift(k, vh)
  +d = C.shift(k, P1)
  +e = C.shift(k, P2)
  +f = C.shift(k, vih)
  +g = C.shift(k, C.shift(k, P3))
  +W0 = Nat.add(Nat.add(cc, Nat.add(e, d)), f)
  +s1 = Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(vlo, C.shift(k, vhi)), Nat.add(vml, C.shift(k, vmh))), Nat.add(b, f)), Nat.add(Nat.add(Nat.add(Nat.mul(vlo, vml), d), Nat.add(e, g)), Nat.add(b, f)), Nat.add(Nat.add(Nat.add(Nat.add(a, cc), d), Nat.add(e, g)), Nat.add(b, f)),
    Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(b, f)), Nat.mul(Nat.add(vlo, C.shift(k, vhi)), Nat.add(vml, C.shift(k, vmh))), Nat.add(Nat.add(Nat.mul(vlo, vml), d), Nat.add(e, g)), WW.expand_k(k, vlo, vhi, vml, vmh)),
    Equal.cong(Nat, Nat, z => Nat.add(Nat.add(Nat.add(z, d), Nat.add(e, g)), Nat.add(b, f)), Nat.mul(vlo, vml), Nat.add(a, cc), Equal.sym(Nat, Nat.add(a, cc), Nat.mul(vlo, vml), h1)))
  +s2 = Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.add(a, cc), d), Nat.add(e, g)), Nat.add(b, f)), Nat.add(Nat.add(a, b), Nat.add(W0, g)), Nat.add(Nat.add(L, C.shift(k, c)), Nat.add(W0, g)),
    perm7(a, b, cc, d, e, f, g),
    Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(W0, g)), Nat.add(a, b), Nat.add(L, C.shift(k, c)), h3))
  +s3 = Equal.trans(Nat, Nat.add(Nat.add(L, C.shift(k, c)), Nat.add(W0, g)), Nat.add(L, Nat.add(Nat.add(W0, C.shift(k, c)), g)), Nat.add(L, C.shift(k, Nat.add(Nat.add(Nat.add(Nat.add(vh, Nat.add(P2, P1)), vih), c), C.shift(k, P3)))),
    swap3(L, C.shift(k, c), W0, g),
    Equal.cong(Nat, Nat, z => Nat.add(L, z), Nat.add(Nat.add(W0, C.shift(k, c)), g), C.shift(k, Nat.add(Nat.add(Nat.add(Nat.add(vh, Nat.add(P2, P1)), vih), c), C.shift(k, P3))),
      Equal.sym(Nat, C.shift(k, Nat.add(Nat.add(Nat.add(Nat.add(vh, Nat.add(P2, P1)), vih), c), C.shift(k, P3))), Nat.add(Nat.add(W0, C.shift(k, c)), g), shx(k, vh, P2, P1, vih, c, P3))))
  Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(vlo, C.shift(k, vhi)), Nat.add(vml, C.shift(k, vmh))), Nat.add(b, f)), Nat.add(Nat.add(Nat.add(Nat.add(a, cc), d), Nat.add(e, g)), Nat.add(b, f)), Nat.add(L, C.shift(k, Nat.add(Nat.add(Nat.add(Nat.add(vh, Nat.add(P2, P1)), vih), c), C.shift(k, P3)))), s1,
    Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.add(a, cc), d), Nat.add(e, g)), Nat.add(b, f)), Nat.add(Nat.add(L, C.shift(k, c)), Nat.add(W0, g)), Nat.add(L, C.shift(k, Nat.add(Nat.add(Nat.add(Nat.add(vh, Nat.add(P2, P1)), vih), c), C.shift(k, P3)))), s2, s3))

def eqm_of(+k: Nat, +v: Nat, +x: Nat, +e: {v == C.low(k, x) : Nat}) -> {C.low(k, v) == C.low(k, x) : Nat}:
  Equal.trans(Nat, C.low(k, v), C.low(k, C.low(k, x)), C.low(k, x), Equal.cong(Nat, Nat, z => C.low(k, z), v, C.low(k, x), e), low_low(k, x))

# the new high word is Z mod 2^64 (t, vH, u: the sums of the implementation)
def high_word(+k: Nat, +vh: Nat, +p2: Nat, +p1: Nat, +p3: Nat, +vih: Nat, +c: Nat, +t: Nat, +vH: Nat, +u: Nat, +vH2: Nat, +hT: {C.low(k, t) == C.low(k, Nat.add(p2, p1)) : Nat}, +hH: {C.low(k, vH) == C.low(k, Nat.add(vh, t)) : Nat}, +hU: {C.low(k, u) == C.low(k, Nat.add(vH, vih)) : Nat}, +hV: {vH2 == C.low(k, Nat.add(u, c)) : Nat}) -> {C.low(k, Nat.add(Nat.add(Nat.add(Nat.add(vh, Nat.add(p2, p1)), vih), c), C.shift(k, p3))) == vH2 : Nat}:
  +S = Nat.add(p2, p1)
  +V = Nat.add(vh, S)
  +W1 = Nat.add(V, vih)
  +eH = Equal.trans(Nat, C.low(k, vH), C.low(k, Nat.add(vh, t)), C.low(k, V), hH, low_add(k, vh, vh, t, S, {==}, hT))
  +eU = Equal.trans(Nat, C.low(k, u), C.low(k, Nat.add(vH, vih)), C.low(k, W1), hU, low_add(k, vH, V, vih, vih, eH, {==}))
  +eZ = Equal.trans(Nat, C.low(k, Nat.add(Nat.add(W1, c), C.shift(k, p3))), C.low(k, Nat.add(W1, c)), C.low(k, Nat.add(u, c)),
    WW.low_add_shift(k, Nat.add(W1, c), p3),
    Equal.sym(Nat, C.low(k, Nat.add(u, c)), C.low(k, Nat.add(W1, c)), low_add(k, u, W1, c, c, eU, {==})))
  Equal.trans(Nat, C.low(k, Nat.add(Nat.add(W1, c), C.shift(k, p3))), C.low(k, Nat.add(u, c)), vH2, eZ, Equal.sym(Nat, vH2, C.low(k, Nat.add(u, c)), hV))

# THEOREM on values: the limb results are the LCG step mod 2^128 (the state
# s, multiplier mul and increment inc given by their limbs)
def step_value(+k: Nat, +vlo: Nat, +vhi: Nat, +vml: Nat, +vmh: Nat, +vil: Nat, +vih: Nat, +vl: Nat, +vh: Nat, +t: Nat, +vH: Nat, +u: Nat, +L: Nat, +c: Nat, +vH2: Nat, +s: Nat, +mul: Nat, +inc: Nat, +hs: {s == Nat.add(vlo, C.shift(k, vhi)) : Nat}, +hm: {mul == Nat.add(vml, C.shift(k, vmh)) : Nat}, +hi: {inc == Nat.add(vil, C.shift(k, vih)) : Nat}, +h1: {Nat.add(vl, C.shift(k, vh)) == Nat.mul(vlo, vml) : Nat}, +hT: {C.low(k, t) == C.low(k, Nat.add(Nat.mul(vhi, vml), Nat.mul(vlo, vmh))) : Nat}, +hH: {C.low(k, vH) == C.low(k, Nat.add(vh, t)) : Nat}, +hU: {C.low(k, u) == C.low(k, Nat.add(vH, vih)) : Nat}, +hV: {vH2 == C.low(k, Nat.add(u, c)) : Nat}, +h3: {Nat.add(vl, vil) == Nat.add(L, C.shift(k, c)) : Nat}, +hL: {C.fits(k, L) == True{} : Bool}, +hH2: {C.fits(k, vH2) == True{} : Bool}) -> {Nat.add(L, C.shift(k, vH2)) == C.low(Nat.add(k, k), Nat.add(Nat.mul(s, mul), inc)) : Nat}:
  +p1 = Nat.mul(vlo, vmh)
  +p2 = Nat.mul(vhi, vml)
  +p3 = Nat.mul(vhi, vmh)
  +Z = Nat.add(Nat.add(Nat.add(Nat.add(vh, Nat.add(p2, p1)), vih), c), C.shift(k, p3))
  +SX = Nat.add(Nat.mul(Nat.add(vlo, C.shift(k, vhi)), Nat.add(vml, C.shift(k, vmh))), Nat.add(vil, C.shift(k, vih)))
  +SMI = Nat.add(Nat.mul(s, mul), inc)
  +LS = Nat.add(L, C.shift(k, vH2))
  +eS = Equal.trans(Nat, SMI, Nat.add(Nat.mul(Nat.add(vlo, C.shift(k, vhi)), mul), inc), SX,
    Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(z, mul), inc), s, Nat.add(vlo, C.shift(k, vhi)), hs),
    Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(vlo, C.shift(k, vhi)), mul), inc), Nat.add(Nat.mul(Nat.add(vlo, C.shift(k, vhi)), Nat.add(vml, C.shift(k, vmh))), inc), SX,
      Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(Nat.add(vlo, C.shift(k, vhi)), z), inc), mul, Nat.add(vml, C.shift(k, vmh)), hm),
      Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(Nat.add(vlo, C.shift(k, vhi)), Nat.add(vml, C.shift(k, vmh))), z), inc, Nat.add(vil, C.shift(k, vih)), hi)))
  +eZ = Equal.trans(Nat, SMI, SX, Nat.add(L, C.shift(k, Z)), eS, expand(k, vlo, vhi, vml, vmh, vil, vih, vl, vh, L, c, h1, h3))
  +hw = high_word(k, vh, p2, p1, p3, vih, c, t, vH, u, vH2, hT, hH, hU, hV)
  +e1 = Equal.trans(Nat, C.low(Nat.add(k, k), SMI), C.low(Nat.add(k, k), Nat.add(L, C.shift(k, Z))), C.low(Nat.add(k, k), LS),
    Equal.cong(Nat, Nat, z => C.low(Nat.add(k, k), z), SMI, Nat.add(L, C.shift(k, Z)), eZ),
    low_hi(k, L, Z, vH2, Equal.sym(Nat, C.low(k, Z), vH2, hw)))
  Equal.sym(Nat, C.low(Nat.add(k, k), SMI), LS, Equal.trans(Nat, C.low(Nat.add(k, k), SMI), C.low(Nat.add(k, k), LS), LS, e1, WW.low_fit(Nat.add(k, k), LS, WW.limbs_fit(k, k, L, vH2, hL, hH2))))
