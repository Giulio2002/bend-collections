import Base
import ../../../spec/lib/common.bend as C
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../natural/sqrtn.bend as SQ
import ./width.bend as WW
import ./natcmp.bend as NC
import ./natfuel.bend as NF

# Integer square roots: isqrt(n) is the unique s with s^2 <= n < (s+1)^2,
# and isqrt(n * 4^j) cut at bit j is isqrt(n), exact exactly when isqrt(n) is.

def sqm(+a: Nat) -> {Nat.pow(a, 2n) == Nat.mul(a, a) : Nat}:
  Equal.cong(Nat, Nat, z => Nat.mul(a, z), Nat.mul(a, 1n), a, NA.mul_one(a))

def isl(+n: Nat) -> {Nat.is_le(Nat.mul(M.isqrt(n), M.isqrt(n)), n) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(z, n) == True{} : Bool}, Nat.pow(M.isqrt(n), 2n), Nat.mul(M.isqrt(n), M.isqrt(n)), sqm(M.isqrt(n)), SQ.isqrt_le(n))

def ilt(+n: Nat) -> {Nat.is_lt(n, Nat.mul(1n+M.isqrt(n), 1n+M.isqrt(n))) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(n, z) == True{} : Bool}, Nat.pow(1n+M.isqrt(n), 2n), Nat.mul(1n+M.isqrt(n), 1n+M.isqrt(n)), sqm(1n+M.isqrt(n)), SQ.lt_succ_isqrt(n))

def mle2(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +hab: {Nat.is_le(a, b) == True{} : Bool}, +hcd: {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_le(Nat.mul(a, c), Nat.mul(b, d)) == True{} : Bool}:
  +l1 = NF.mul_le_r(a, c, d, hcd)
  +l2 = L.subst(Nat, z => {Nat.is_le(z, Nat.mul(d, b)) == True{} : Bool}, Nat.mul(d, a), Nat.mul(a, d), NA.mul_comm(d, a), NF.mul_le_r(d, a, b, hab))
  N.le_trans(Nat.mul(a, c), Nat.mul(a, d), Nat.mul(b, d), l1, L.subst(Nat, z => {Nat.is_le(Nat.mul(a, d), z) == True{} : Bool}, Nat.mul(d, b), Nat.mul(b, d), NA.mul_comm(d, b), l2))

def sqmono(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.mul(a, a), Nat.mul(b, b)) == True{} : Bool}:
  mle2(a, b, a, b, h, h)

def ige_c(+n: Nat, +s: Nat, +h: {Nat.is_le(Nat.mul(s, s), n) == True{} : Bool}, +c: Bool, +hc: {Nat.is_le(s, M.isqrt(n)) == c : Bool}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      +l1 = N.lt_succ_le_succ(M.isqrt(n), s, N.not_le_lt(s, M.isqrt(n), hc))
      +l2 = N.le_trans(Nat.mul(1n+M.isqrt(n), 1n+M.isqrt(n)), Nat.mul(s, s), n, sqmono(1n+M.isqrt(n), s, l1), h)
      NC.absurd_tf({False{} == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_le(Nat.mul(1n+M.isqrt(n), 1n+M.isqrt(n)), n), True{}, Equal.sym(Bool, Nat.is_le(Nat.mul(1n+M.isqrt(n), 1n+M.isqrt(n)), n), False{}, N.lt_not_le(n, Nat.mul(1n+M.isqrt(n), 1n+M.isqrt(n)), ilt(n))), l2))

def isqrt_ge(+n: Nat, +s: Nat, +h: {Nat.is_le(Nat.mul(s, s), n) == True{} : Bool}) -> {Nat.is_le(s, M.isqrt(n)) == True{} : Bool}:
  ige_c(n, s, h, Nat.is_le(s, M.isqrt(n)), {==})

def ilt_c(+n: Nat, +s: Nat, +h: {Nat.is_lt(n, Nat.mul(s, s)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_lt(M.isqrt(n), s) == c : Bool}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      +l1 = N.not_lt_le(M.isqrt(n), s, hc)
      +l2 = N.le_trans(Nat.mul(s, s), Nat.mul(M.isqrt(n), M.isqrt(n)), n, sqmono(s, M.isqrt(n), l1), isl(n))
      NC.absurd_tf({False{} == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_le(Nat.mul(s, s), n), True{}, Equal.sym(Bool, Nat.is_le(Nat.mul(s, s), n), False{}, N.lt_not_le(n, Nat.mul(s, s), h)), l2))

def isqrt_lt(+n: Nat, +s: Nat, +h: {Nat.is_lt(n, Nat.mul(s, s)) == True{} : Bool}) -> {Nat.is_lt(M.isqrt(n), s) == True{} : Bool}:
  ilt_c(n, s, h, Nat.is_lt(M.isqrt(n), s), {==})

def isqrt_char(+n: Nat, +s: Nat, +h1: {Nat.is_le(Nat.mul(s, s), n) == True{} : Bool}, +h2: {Nat.is_lt(n, Nat.mul(1n+s, 1n+s)) == True{} : Bool}) -> {M.isqrt(n) == s : Nat}:
  N.le_antisym(M.isqrt(n), s, N.lt_succ_le(M.isqrt(n), s, isqrt_lt(n, 1n+s, h2)), isqrt_ge(n, s, h1))

# shifting a square by j on both factors
def sh_sq(+j: Nat, +a: Nat) -> {Nat.mul(C.shift(j, a), C.shift(j, a)) == C.shift(j, C.shift(j, Nat.mul(a, a))) : Nat}:
  Equal.trans(Nat, Nat.mul(C.shift(j, a), C.shift(j, a)), C.shift(j, Nat.mul(a, C.shift(j, a))), C.shift(j, C.shift(j, Nat.mul(a, a))), WW.shift_mul_l(j, a, C.shift(j, a)), Equal.cong(Nat, Nat, z => C.shift(j, z), Nat.mul(a, C.shift(j, a)), C.shift(j, Nat.mul(a, a)), WW.shift_mul_r(j, a, a)))

def le_sh2(+j: Nat, +a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(C.shift(j, C.shift(j, a)), C.shift(j, C.shift(j, b))) == True{} : Bool}:
  WW.shift_mono(j, C.shift(j, a), C.shift(j, b), WW.shift_mono(j, a, b, h))

def lt_sh2(+j: Nat, +a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(C.shift(j, C.shift(j, a)), C.shift(j, C.shift(j, b))) == True{} : Bool}:
  WW.shift_lt(j, C.shift(j, a), C.shift(j, b), WW.shift_lt(j, a, b, h))

# isqrt(n * 4^j) lies in [isqrt(n) * 2^j, (isqrt(n) + 1) * 2^j)
def sc_lo(+n: Nat, +j: Nat) -> {Nat.is_le(C.shift(j, M.isqrt(n)), M.isqrt(C.shift(j, C.shift(j, n)))) == True{} : Bool}:
  isqrt_ge(C.shift(j, C.shift(j, n)), C.shift(j, M.isqrt(n)), L.subst(Nat, z => {Nat.is_le(z, C.shift(j, C.shift(j, n))) == True{} : Bool}, C.shift(j, C.shift(j, Nat.mul(M.isqrt(n), M.isqrt(n)))), Nat.mul(C.shift(j, M.isqrt(n)), C.shift(j, M.isqrt(n))), Equal.sym(Nat, Nat.mul(C.shift(j, M.isqrt(n)), C.shift(j, M.isqrt(n))), C.shift(j, C.shift(j, Nat.mul(M.isqrt(n), M.isqrt(n)))), sh_sq(j, M.isqrt(n))), le_sh2(j, Nat.mul(M.isqrt(n), M.isqrt(n)), n, isl(n))))

def sc_hi(+n: Nat, +j: Nat) -> {Nat.is_lt(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, 1n+M.isqrt(n))) == True{} : Bool}:
  isqrt_lt(C.shift(j, C.shift(j, n)), C.shift(j, 1n+M.isqrt(n)), L.subst(Nat, z => {Nat.is_lt(C.shift(j, C.shift(j, n)), z) == True{} : Bool}, C.shift(j, C.shift(j, Nat.mul(1n+M.isqrt(n), 1n+M.isqrt(n)))), Nat.mul(C.shift(j, 1n+M.isqrt(n)), C.shift(j, 1n+M.isqrt(n))), Equal.sym(Nat, Nat.mul(C.shift(j, 1n+M.isqrt(n)), C.shift(j, 1n+M.isqrt(n))), C.shift(j, C.shift(j, Nat.mul(1n+M.isqrt(n), 1n+M.isqrt(n)))), sh_sq(j, 1n+M.isqrt(n))), lt_sh2(j, n, Nat.mul(1n+M.isqrt(n), 1n+M.isqrt(n)), ilt(n))))

def sc_eq(+n: Nat, +j: Nat) -> {Nat.add(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), C.shift(j, M.isqrt(n))) == M.isqrt(C.shift(j, C.shift(j, n))) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), C.shift(j, M.isqrt(n))), Nat.add(C.shift(j, M.isqrt(n)), Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n)))), M.isqrt(C.shift(j, C.shift(j, n))), NA.add_comm(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), C.shift(j, M.isqrt(n))), N.sub_add(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n)), sc_lo(n, j)))

def sc_fit(+n: Nat, +j: Nat) -> {C.fits(j, Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n)))) == True{} : Bool}:
  +e1 = Equal.trans(Nat, C.shift(j, 1n+M.isqrt(n)), C.shift(j, Nat.add(1n, M.isqrt(n))), Nat.add(C.shift(j, 1n), C.shift(j, M.isqrt(n))), {==}, WW.shift_add(j, 1n, M.isqrt(n)))
  +h1 = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(C.shift(j, 1n), C.shift(j, M.isqrt(n)))) == True{} : Bool}, M.isqrt(C.shift(j, C.shift(j, n))), Nat.add(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), C.shift(j, M.isqrt(n))), Equal.sym(Nat, Nat.add(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), C.shift(j, M.isqrt(n))), M.isqrt(C.shift(j, C.shift(j, n))), sc_eq(n, j)), L.subst(Nat, z => {Nat.is_lt(M.isqrt(C.shift(j, C.shift(j, n))), z) == True{} : Bool}, C.shift(j, 1n+M.isqrt(n)), Nat.add(C.shift(j, 1n), C.shift(j, M.isqrt(n))), e1, sc_hi(n, j)))
  +h2 = Equal.trans(Bool, Nat.is_lt(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), C.shift(j, 1n)), Nat.is_lt(Nat.add(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), C.shift(j, M.isqrt(n))), Nat.add(C.shift(j, 1n), C.shift(j, M.isqrt(n)))), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), C.shift(j, M.isqrt(n))), Nat.add(C.shift(j, 1n), C.shift(j, M.isqrt(n)))), Nat.is_lt(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), C.shift(j, 1n)), WW.lt_cancel_r(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), C.shift(j, 1n), C.shift(j, M.isqrt(n)))), h1)
  WW.fits_one(j, 1n, {==}, Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), h2)

def sc_high(+n: Nat, +j: Nat) -> {C.high(j, M.isqrt(C.shift(j, C.shift(j, n)))) == M.isqrt(n) : Nat}:
  Equal.trans(Nat, C.high(j, M.isqrt(C.shift(j, C.shift(j, n)))), C.high(j, Nat.add(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), C.shift(j, M.isqrt(n)))), M.isqrt(n), Equal.cong(Nat, Nat, z => C.high(j, z), M.isqrt(C.shift(j, C.shift(j, n))), Nat.add(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), C.shift(j, M.isqrt(n))), Equal.sym(Nat, Nat.add(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), C.shift(j, M.isqrt(n))), M.isqrt(C.shift(j, C.shift(j, n))), sc_eq(n, j))), WW.high_u(j, Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), M.isqrt(n), sc_fit(n, j)))

def sc_low(+n: Nat, +j: Nat) -> {C.low(j, M.isqrt(C.shift(j, C.shift(j, n)))) == Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))) : Nat}:
  Equal.trans(Nat, C.low(j, M.isqrt(C.shift(j, C.shift(j, n)))), C.low(j, Nat.add(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), C.shift(j, M.isqrt(n)))), Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), Equal.cong(Nat, Nat, z => C.low(j, z), M.isqrt(C.shift(j, C.shift(j, n))), Nat.add(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), C.shift(j, M.isqrt(n))), Equal.sym(Nat, Nat.add(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), C.shift(j, M.isqrt(n))), M.isqrt(C.shift(j, C.shift(j, n))), sc_eq(n, j))), WW.low_u(j, Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), M.isqrt(n), sc_fit(n, j)))

def eq_sh(+k: Nat, +a: Nat, +b: Nat) -> {Nat.is_eq(C.shift(k, a), C.shift(k, b)) == Nat.is_eq(a, b) : Bool}:
  Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), Nat.cmp(C.shift(k, a), C.shift(k, b)), Nat.cmp(a, b), NC.cmp_shift(k, a, b))

def eq_sh2(+j: Nat, +a: Nat, +b: Nat) -> {Nat.is_eq(C.shift(j, C.shift(j, a)), C.shift(j, C.shift(j, b))) == Nat.is_eq(a, b) : Bool}:
  Equal.trans(Bool, Nat.is_eq(C.shift(j, C.shift(j, a)), C.shift(j, C.shift(j, b))), Nat.is_eq(C.shift(j, a), C.shift(j, b)), Nat.is_eq(a, b), eq_sh(j, C.shift(j, a), C.shift(j, b)), eq_sh(j, a, b))

def sqlt(+a: Nat) -> {Nat.is_lt(Nat.mul(a, a), Nat.mul(1n+a, 1n+a)) == True{} : Bool}:
  +l1 = NF.mul_le_r(a, a, 1n+a, N.le_succ(a))
  +l2 = L.subst(Nat, z => {Nat.is_le(Nat.mul(a, 1n+a), z) == True{} : Bool}, Nat.add(Nat.mul(a, 1n+a), a), Nat.add(a, Nat.mul(a, 1n+a)), NA.add_comm(Nat.mul(a, 1n+a), a), N.le_add_right(Nat.mul(a, 1n+a), a))
  N.le_lt_succ(Nat.mul(a, a), Nat.add(a, Nat.mul(a, 1n+a)), N.le_trans(Nat.mul(a, a), Nat.mul(a, 1n+a), Nat.add(a, Nat.mul(a, 1n+a)), l1, l2))

def FR_or_t(+b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sub_z(+a: Nat, +b: Nat, +h: {a == b : Nat}) -> {Nat.sub(a, b) == 0n : Nat}:
  Equal.trans(Nat, Nat.sub(a, b), Nat.sub(b, b), 0n, Equal.cong(Nat, Nat, z => Nat.sub(z, b), a, b, h), N.sub_self(b))


def sc_x_f(+n: Nat, +j: Nat, +hc: {Nat.is_eq(Nat.mul(M.isqrt(n), M.isqrt(n)), n) == False{} : Bool}, +d: Bool, +hd: {Nat.is_eq(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), 0n) == d : Bool}) -> {Bool.or(Bool.not(Nat.is_eq(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), 0n)), Bool.not(Nat.is_eq(Nat.mul(M.isqrt(C.shift(j, C.shift(j, n))), M.isqrt(C.shift(j, C.shift(j, n)))), C.shift(j, C.shift(j, n))))) == True{} : Bool}:
  match d:
    case True{}:
      +er = N.eq_from_is_eq(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), 0n, hd)
      +et = Equal.trans(Nat, M.isqrt(C.shift(j, C.shift(j, n))), Nat.add(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), C.shift(j, M.isqrt(n))), C.shift(j, M.isqrt(n)), Equal.sym(Nat, Nat.add(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), C.shift(j, M.isqrt(n))), M.isqrt(C.shift(j, C.shift(j, n))), sc_eq(n, j)), Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(j, M.isqrt(n))), Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), 0n, er))
      +eT = Equal.trans(Nat, Nat.mul(M.isqrt(C.shift(j, C.shift(j, n))), M.isqrt(C.shift(j, C.shift(j, n)))), Nat.mul(C.shift(j, M.isqrt(n)), C.shift(j, M.isqrt(n))), C.shift(j, C.shift(j, Nat.mul(M.isqrt(n), M.isqrt(n)))), Equal.trans(Nat, Nat.mul(M.isqrt(C.shift(j, C.shift(j, n))), M.isqrt(C.shift(j, C.shift(j, n)))), Nat.mul(C.shift(j, M.isqrt(n)), M.isqrt(C.shift(j, C.shift(j, n)))), Nat.mul(C.shift(j, M.isqrt(n)), C.shift(j, M.isqrt(n))), Equal.cong(Nat, Nat, z => Nat.mul(z, M.isqrt(C.shift(j, C.shift(j, n)))), M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n)), et), Equal.cong(Nat, Nat, z => Nat.mul(C.shift(j, M.isqrt(n)), z), M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n)), et)), sh_sq(j, M.isqrt(n)))
      +b1 = Equal.cong(Nat, Bool, z => Bool.or(Bool.not(Nat.is_eq(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), 0n)), Bool.not(Nat.is_eq(z, C.shift(j, C.shift(j, n))))), Nat.mul(M.isqrt(C.shift(j, C.shift(j, n))), M.isqrt(C.shift(j, C.shift(j, n)))), C.shift(j, C.shift(j, Nat.mul(M.isqrt(n), M.isqrt(n)))), eT)
      +b2 = Equal.cong(Bool, Bool, t => Bool.or(Bool.not(Nat.is_eq(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), 0n)), Bool.not(t)), Nat.is_eq(C.shift(j, C.shift(j, Nat.mul(M.isqrt(n), M.isqrt(n)))), C.shift(j, C.shift(j, n))), False{}, Equal.trans(Bool, Nat.is_eq(C.shift(j, C.shift(j, Nat.mul(M.isqrt(n), M.isqrt(n)))), C.shift(j, C.shift(j, n))), Nat.is_eq(Nat.mul(M.isqrt(n), M.isqrt(n)), n), False{}, eq_sh2(j, Nat.mul(M.isqrt(n), M.isqrt(n)), n), hc))
      Equal.trans(Bool, Bool.or(Bool.not(Nat.is_eq(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), 0n)), Bool.not(Nat.is_eq(Nat.mul(M.isqrt(C.shift(j, C.shift(j, n))), M.isqrt(C.shift(j, C.shift(j, n)))), C.shift(j, C.shift(j, n))))), Bool.or(Bool.not(Nat.is_eq(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), 0n)), Bool.not(Nat.is_eq(C.shift(j, C.shift(j, Nat.mul(M.isqrt(n), M.isqrt(n)))), C.shift(j, C.shift(j, n))))), True{}, b1, Equal.trans(Bool, Bool.or(Bool.not(Nat.is_eq(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), 0n)), Bool.not(Nat.is_eq(C.shift(j, C.shift(j, Nat.mul(M.isqrt(n), M.isqrt(n)))), C.shift(j, C.shift(j, n))))), Bool.or(Bool.not(Nat.is_eq(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), 0n)), True{}), True{}, b2, FR_or_t(Bool.not(Nat.is_eq(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), 0n)))))
    case False{}:
      Equal.cong(Bool, Bool, t => Bool.or(Bool.not(t), Bool.not(Nat.is_eq(Nat.mul(M.isqrt(C.shift(j, C.shift(j, n))), M.isqrt(C.shift(j, C.shift(j, n)))), C.shift(j, C.shift(j, n))))), Nat.is_eq(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), 0n), False{}, hd)

def sc_x_c(+n: Nat, +j: Nat, +c: Bool, +hc: {Nat.is_eq(Nat.mul(M.isqrt(n), M.isqrt(n)), n) == c : Bool}) -> {Bool.or(Bool.not(Nat.is_eq(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), 0n)), Bool.not(Nat.is_eq(Nat.mul(M.isqrt(C.shift(j, C.shift(j, n))), M.isqrt(C.shift(j, C.shift(j, n)))), C.shift(j, C.shift(j, n))))) == Bool.not(c) : Bool}:
  match c:
    case True{}:
      +e0 = N.eq_from_is_eq(Nat.mul(M.isqrt(n), M.isqrt(n)), n, hc)
      +eN = Equal.trans(Nat, Nat.mul(C.shift(j, M.isqrt(n)), C.shift(j, M.isqrt(n))), C.shift(j, C.shift(j, Nat.mul(M.isqrt(n), M.isqrt(n)))), C.shift(j, C.shift(j, n)), sh_sq(j, M.isqrt(n)), Equal.cong(Nat, Nat, z => C.shift(j, C.shift(j, z)), Nat.mul(M.isqrt(n), M.isqrt(n)), n, e0))
      +h1 = L.subst(Nat, z => {Nat.is_le(Nat.mul(C.shift(j, M.isqrt(n)), C.shift(j, M.isqrt(n))), z) == True{} : Bool}, Nat.mul(C.shift(j, M.isqrt(n)), C.shift(j, M.isqrt(n))), C.shift(j, C.shift(j, n)), eN, N.le_refl(Nat.mul(C.shift(j, M.isqrt(n)), C.shift(j, M.isqrt(n)))))
      +h2 = L.subst(Nat, z => {Nat.is_lt(z, Nat.mul(1n+C.shift(j, M.isqrt(n)), 1n+C.shift(j, M.isqrt(n)))) == True{} : Bool}, Nat.mul(C.shift(j, M.isqrt(n)), C.shift(j, M.isqrt(n))), C.shift(j, C.shift(j, n)), eN, sqlt(C.shift(j, M.isqrt(n))))
      +et = isqrt_char(C.shift(j, C.shift(j, n)), C.shift(j, M.isqrt(n)), h1, h2)
      +er = sub_z(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n)), et)
      +eT = Equal.trans(Nat, Nat.mul(M.isqrt(C.shift(j, C.shift(j, n))), M.isqrt(C.shift(j, C.shift(j, n)))), Nat.mul(C.shift(j, M.isqrt(n)), C.shift(j, M.isqrt(n))), C.shift(j, C.shift(j, n)), Equal.trans(Nat, Nat.mul(M.isqrt(C.shift(j, C.shift(j, n))), M.isqrt(C.shift(j, C.shift(j, n)))), Nat.mul(C.shift(j, M.isqrt(n)), M.isqrt(C.shift(j, C.shift(j, n)))), Nat.mul(C.shift(j, M.isqrt(n)), C.shift(j, M.isqrt(n))), Equal.cong(Nat, Nat, z => Nat.mul(z, M.isqrt(C.shift(j, C.shift(j, n)))), M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n)), et), Equal.cong(Nat, Nat, z => Nat.mul(C.shift(j, M.isqrt(n)), z), M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n)), et)), eN)
      +b1 = Equal.cong(Nat, Bool, z => Bool.or(Bool.not(Nat.is_eq(z, 0n)), Bool.not(Nat.is_eq(Nat.mul(M.isqrt(C.shift(j, C.shift(j, n))), M.isqrt(C.shift(j, C.shift(j, n)))), C.shift(j, C.shift(j, n))))), Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), 0n, er)
      +b2 = Equal.cong(Nat, Bool, z => Bool.or(False{}, Bool.not(Nat.is_eq(z, C.shift(j, C.shift(j, n))))), Nat.mul(M.isqrt(C.shift(j, C.shift(j, n))), M.isqrt(C.shift(j, C.shift(j, n)))), C.shift(j, C.shift(j, n)), eT)
      Equal.trans(Bool, Bool.or(Bool.not(Nat.is_eq(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), 0n)), Bool.not(Nat.is_eq(Nat.mul(M.isqrt(C.shift(j, C.shift(j, n))), M.isqrt(C.shift(j, C.shift(j, n)))), C.shift(j, C.shift(j, n))))), Bool.or(False{}, Bool.not(Nat.is_eq(Nat.mul(M.isqrt(C.shift(j, C.shift(j, n))), M.isqrt(C.shift(j, C.shift(j, n)))), C.shift(j, C.shift(j, n))))), False{}, b1, Equal.trans(Bool, Bool.or(False{}, Bool.not(Nat.is_eq(Nat.mul(M.isqrt(C.shift(j, C.shift(j, n))), M.isqrt(C.shift(j, C.shift(j, n)))), C.shift(j, C.shift(j, n))))), Bool.or(False{}, Bool.not(Nat.is_eq(C.shift(j, C.shift(j, n)), C.shift(j, C.shift(j, n))))), False{}, b2, Equal.cong(Bool, Bool, t => Bool.or(False{}, Bool.not(t)), Nat.is_eq(C.shift(j, C.shift(j, n)), C.shift(j, C.shift(j, n))), True{}, N.is_eq_refl(C.shift(j, C.shift(j, n))))))
    case False{}:
      sc_x_f(n, j, hc, Nat.is_eq(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), 0n), {==})

def sc_x(+n: Nat, +j: Nat) -> {Bool.or(Bool.not(Nat.is_eq(Nat.sub(M.isqrt(C.shift(j, C.shift(j, n))), C.shift(j, M.isqrt(n))), 0n)), Bool.not(Nat.is_eq(Nat.mul(M.isqrt(C.shift(j, C.shift(j, n))), M.isqrt(C.shift(j, C.shift(j, n)))), C.shift(j, C.shift(j, n))))) == Bool.not(Nat.is_eq(Nat.mul(M.isqrt(n), M.isqrt(n)), n)) : Bool}:
  sc_x_c(n, j, Nat.is_eq(Nat.mul(M.isqrt(n), M.isqrt(n)), n), {==})
