import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../natural/arith.bend as NR
import ./width.bend as WW
import ./natcmp.bend as NC
import ./u32laws.bend as LW
import ./w64add.bend as WA
import ./w64isq.bend as ISQ
import ./f64round.bend as FR
import ./f64sqa.bend as AQ
import ./f64sqw.bend as QW
import ./w64mul.bend as W64M
import ./w64div.bend as W64D
import ../natural/sqrtn.bend as SQ2

# Facts about s = isqrt(nh) for 2^60 <= nh < 2^62 and the Karatsuba step's
# words (r = nh - s^2, 2 s, the quotient digit) used by f64sqr.bend.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def mone(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.mul(one, one) == one : Nat}:
  L.subst(Nat, z => {Nat.mul(z, z) == z : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})

def one_le(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_le(1n, one) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})

# (2^k)^2 as one shift
def psq(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat) -> {Nat.mul(C.shift(k, one), C.shift(k, one)) == C.shift(Nat.add(k, k), one) : Nat}:
  Equal.trans(Nat, Nat.mul(C.shift(k, one), C.shift(k, one)), C.shift(k, C.shift(k, Nat.mul(one, one))), C.shift(Nat.add(k, k), one), AQ.sh_sq(k, one), Equal.trans(Nat, C.shift(k, C.shift(k, Nat.mul(one, one))), C.shift(k, C.shift(k, one)), C.shift(Nat.add(k, k), one), Equal.cong(Nat, Nat, z => C.shift(k, C.shift(k, z)), Nat.mul(one, one), one, mone(one, h1)), Equal.sym(Nat, C.shift(Nat.add(k, k), one), C.shift(k, C.shift(k, one)), WW.shift_comp(k, k, one))))

def lo_val(+w: WU.U64, +h: {C.fits(32n, SW.value(w)) == True{} : Bool}) -> {v(X.lo(w)) == SW.value(w) : Nat}:
  match w:
    case WU.U64{+l, +hh}:
      Equal.trans(Nat, v(l), C.low(32n, SW.value(WU.U64{l, hh})), SW.value(WU.U64{l, hh}), Equal.sym(Nat, C.low(32n, SW.value(WU.U64{l, hh})), v(l), WW.low_u(32n, v(l), v(hh), LW.vb(l))), WW.low_fit(32n, SW.value(WU.U64{l, hh}), h))

def shmk(+a: Nat, +b: Nat, +x: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(C.shift(a, x), C.shift(b, x)) == True{} : Bool}:
  +h0 = WW.shift_mono(a, x, C.shift(Nat.sub(b, a), x), WW.shift_ge(Nat.sub(b, a), x))
  L.subst(Nat, z => {Nat.is_le(C.shift(a, x), z) == True{} : Bool}, C.shift(a, C.shift(Nat.sub(b, a), x)), C.shift(b, x), Equal.sym(Nat, C.shift(b, x), C.shift(a, C.shift(Nat.sub(b, a), x)), NC.sh_split(b, a, x, h)), h0)

def p_lt(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat) -> {Nat.is_lt(C.shift(k, one), C.shift(1n+k, one)) == True{} : Bool}:
  +g = N.le_trans(1n, one, C.shift(k, one), one_le(one, h1), WW.shift_ge(k, one))
  +l = N.lt_add_left(0n, C.shift(k, one), C.shift(k, one), N.lt_le_trans(0n, 1n, C.shift(k, one), {==}, g))
  L.subst(Nat, z => {Nat.is_lt(C.shift(k, one), z) == True{} : Bool}, Nat.add(C.shift(k, one), C.shift(k, one)), C.shift(1n+k, one), Equal.sym(Nat, Nat.double(C.shift(k, one)), Nat.add(C.shift(k, one), C.shift(k, one)), NA.double_self(C.shift(k, one))), L.subst(Nat, z => {Nat.is_lt(z, Nat.add(C.shift(k, one), C.shift(k, one))) == True{} : Bool}, Nat.add(C.shift(k, one), 0n), C.shift(k, one), N.add_zero(C.shift(k, one)), l))

def vn62(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}) -> {Nat.is_lt(SW.value(nh), C.shift(62n, one)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(SW.value(nh), C.shift(62n, one)), C.fits(62n, SW.value(nh)), True{}, FR.lt_fit(62n, one, h1, SW.value(nh)), h62)

def vn60(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {Nat.is_le(C.shift(60n, one), SW.value(nh)) == True{} : Bool}:
  N.not_lt_le(SW.value(nh), C.shift(60n, one), Equal.trans(Bool, Nat.is_lt(SW.value(nh), C.shift(60n, one)), C.fits(60n, SW.value(nh)), False{}, FR.lt_fit(60n, one, h1, SW.value(nh)), h60))

def iv31(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {Nat.is_lt(M.isqrt(SW.value(nh)), C.shift(31n, one)) == True{} : Bool}:
  AQ.isqrt_lt(SW.value(nh), C.shift(31n, one), L.subst(Nat, z => {Nat.is_lt(SW.value(nh), z) == True{} : Bool}, C.shift(62n, one), Nat.mul(C.shift(31n, one), C.shift(31n, one)), Equal.sym(Nat, Nat.mul(C.shift(31n, one), C.shift(31n, one)), C.shift(62n, one), psq(one, h1, 31n)), vn62(one, h1, nh, h62)))

def iw_v(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {SW.value(X.isqrt(nh)) == M.isqrt(SW.value(nh)) : Nat}:
  ISQ.isqrt_value(nh)

def iw32(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {C.fits(32n, SW.value(X.isqrt(nh))) == True{} : Bool}:
  +l = N.lt_trans(M.isqrt(SW.value(nh)), C.shift(31n, one), C.shift(32n, one), iv31(one, h1, nh, h62, h60), p_lt(one, h1, 31n))
  WW.fits_one(32n, one, h1, SW.value(X.isqrt(nh)), L.subst(Nat, z => {Nat.is_lt(z, C.shift(32n, one)) == True{} : Bool}, M.isqrt(SW.value(nh)), SW.value(X.isqrt(nh)), Equal.sym(Nat, SW.value(X.isqrt(nh)), M.isqrt(SW.value(nh)), iw_v(one, h1, nh, h62, h60)), l))

def lo_iv(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {v(X.lo(X.isqrt(nh))) == M.isqrt(SW.value(nh)) : Nat}:
  Equal.trans(Nat, v(X.lo(X.isqrt(nh))), SW.value(X.isqrt(nh)), M.isqrt(SW.value(nh)), lo_val(X.isqrt(nh), iw32(one, h1, nh, h62, h60)), iw_v(one, h1, nh, h62, h60))

def plus1(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {Nat.add(v(X.lo(X.isqrt(nh))), v(1)) == 1n+M.isqrt(SW.value(nh)) : Nat}:
  Equal.trans(Nat, Nat.add(v(X.lo(X.isqrt(nh))), 1n), Nat.add(M.isqrt(SW.value(nh)), 1n), 1n+M.isqrt(SW.value(nh)), Equal.cong(Nat, Nat, z => Nat.add(z, 1n), v(X.lo(X.isqrt(nh))), M.isqrt(SW.value(nh)), lo_iv(one, h1, nh, h62, h60)), Equal.trans(Nat, Nat.add(M.isqrt(SW.value(nh)), 1n), 1n+Nat.add(M.isqrt(SW.value(nh)), 0n), 1n+M.isqrt(SW.value(nh)), N.add_succ(M.isqrt(SW.value(nh)), 0n), N.succ_cong(Nat.add(M.isqrt(SW.value(nh)), 0n), M.isqrt(SW.value(nh)), N.add_zero(M.isqrt(SW.value(nh))))))

def add1_v(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {v(U32.add(X.lo(X.isqrt(nh)), 1)) == 1n+M.isqrt(SW.value(nh)) : Nat}:
  +l = N.le_lt_trans(1n+M.isqrt(SW.value(nh)), C.shift(31n, one), C.shift(32n, one), N.lt_succ_le_succ(M.isqrt(SW.value(nh)), C.shift(31n, one), iv31(one, h1, nh, h62, h60)), p_lt(one, h1, 31n))
  +f = WW.fits_one(32n, one, h1, Nat.add(v(X.lo(X.isqrt(nh))), v(1)), L.subst(Nat, z => {Nat.is_lt(z, C.shift(32n, one)) == True{} : Bool}, 1n+M.isqrt(SW.value(nh)), Nat.add(v(X.lo(X.isqrt(nh))), v(1)), Equal.sym(Nat, Nat.add(v(X.lo(X.isqrt(nh))), v(1)), 1n+M.isqrt(SW.value(nh)), plus1(one, h1, nh, h62, h60)), l))
  Equal.trans(Nat, v(U32.add(X.lo(X.isqrt(nh)), 1)), Nat.add(v(X.lo(X.isqrt(nh))), v(1)), 1n+M.isqrt(SW.value(nh)), WA.add_exact(one, h1, X.lo(X.isqrt(nh)), 1, f), plus1(one, h1, nh, h62, h60))

# r0 = (isqrt(nh) + 1) * 2^32
def r0_v(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {SW.value(WU.U64{0, U32.add(X.lo(X.isqrt(nh)), 1)}) == C.shift(32n, Nat.add(one, M.isqrt(SW.value(nh)))) : Nat}:
  +e0 = L.subst(Nat, z => {v(U32.add(X.lo(X.isqrt(nh)), 1)) == Nat.add(z, M.isqrt(SW.value(nh))) : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), add1_v(one, h1, nh, h62, h60))
  Equal.cong(Nat, Nat, z => C.shift(32n, z), v(U32.add(X.lo(X.isqrt(nh)), 1)), Nat.add(one, M.isqrt(SW.value(nh))), e0)

def nn_eq(+nh: WU.U64) -> {C.shift(64n, SW.value(nh)) == C.shift(32n, C.shift(32n, SW.value(nh))) : Nat}:
  WW.shift_comp(32n, 32n, SW.value(nh))

def s_lo(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {Nat.is_le(C.shift(32n, M.isqrt(SW.value(nh))), M.isqrt(C.shift(64n, SW.value(nh)))) == True{} : Bool}:
  AQ.isqrt_ge(C.shift(64n, SW.value(nh)), C.shift(32n, M.isqrt(SW.value(nh))), L.subst(Nat, z => {Nat.is_le(z, C.shift(64n, SW.value(nh))) == True{} : Bool}, C.shift(32n, C.shift(32n, Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))))), Nat.mul(C.shift(32n, M.isqrt(SW.value(nh))), C.shift(32n, M.isqrt(SW.value(nh)))), Equal.sym(Nat, Nat.mul(C.shift(32n, M.isqrt(SW.value(nh))), C.shift(32n, M.isqrt(SW.value(nh)))), C.shift(32n, C.shift(32n, Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))))), AQ.sh_sq(32n, M.isqrt(SW.value(nh)))), L.subst(Nat, z => {Nat.is_le(C.shift(32n, C.shift(32n, Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))))), z) == True{} : Bool}, C.shift(32n, C.shift(32n, SW.value(nh))), C.shift(64n, SW.value(nh)), Equal.sym(Nat, C.shift(64n, SW.value(nh)), C.shift(32n, C.shift(32n, SW.value(nh))), nn_eq(nh)), AQ.le_sh2(32n, Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), SW.value(nh), AQ.isl(SW.value(nh))))))

# shift(32, isqrt nh) <= S < r0
def ilt1(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {Nat.is_lt(SW.value(nh), Nat.mul(Nat.add(one, M.isqrt(SW.value(nh))), Nat.add(one, M.isqrt(SW.value(nh))))) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(SW.value(nh), Nat.mul(Nat.add(z, M.isqrt(SW.value(nh))), Nat.add(z, M.isqrt(SW.value(nh))))) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), AQ.ilt(SW.value(nh)))

def s_hi(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}, +r0w: WU.U64, +hR0: {SW.value(r0w) == C.shift(32n, Nat.add(one, M.isqrt(SW.value(nh)))) : Nat}, +hhi: {U32.is_zero(X.hi(r0w)) == False{} : Bool}) -> {Nat.is_lt(M.isqrt(C.shift(64n, SW.value(nh))), SW.value(r0w)) == True{} : Bool}:
  +l1 = AQ.lt_sh2(32n, SW.value(nh), Nat.mul(Nat.add(one, M.isqrt(SW.value(nh))), Nat.add(one, M.isqrt(SW.value(nh)))), ilt1(one, h1, nh, h62, h60))
  +e1 = Equal.trans(Nat, Nat.mul(SW.value(r0w), SW.value(r0w)), Nat.mul(C.shift(32n, Nat.add(one, M.isqrt(SW.value(nh)))), C.shift(32n, Nat.add(one, M.isqrt(SW.value(nh))))), C.shift(32n, C.shift(32n, Nat.mul(Nat.add(one, M.isqrt(SW.value(nh))), Nat.add(one, M.isqrt(SW.value(nh)))))), Equal.trans(Nat, Nat.mul(SW.value(r0w), SW.value(r0w)), Nat.mul(C.shift(32n, Nat.add(one, M.isqrt(SW.value(nh)))), SW.value(r0w)), Nat.mul(C.shift(32n, Nat.add(one, M.isqrt(SW.value(nh)))), C.shift(32n, Nat.add(one, M.isqrt(SW.value(nh))))), Equal.cong(Nat, Nat, z => Nat.mul(z, SW.value(r0w)), SW.value(r0w), C.shift(32n, Nat.add(one, M.isqrt(SW.value(nh)))), hR0), Equal.cong(Nat, Nat, z => Nat.mul(C.shift(32n, Nat.add(one, M.isqrt(SW.value(nh)))), z), SW.value(r0w), C.shift(32n, Nat.add(one, M.isqrt(SW.value(nh)))), hR0)), AQ.sh_sq(32n, Nat.add(one, M.isqrt(SW.value(nh)))))
  AQ.isqrt_lt(C.shift(64n, SW.value(nh)), SW.value(r0w), L.subst(Nat, z => {Nat.is_lt(z, Nat.mul(SW.value(r0w), SW.value(r0w))) == True{} : Bool}, C.shift(32n, C.shift(32n, SW.value(nh))), C.shift(64n, SW.value(nh)), Equal.sym(Nat, C.shift(64n, SW.value(nh)), C.shift(32n, C.shift(32n, SW.value(nh))), nn_eq(nh)), L.subst(Nat, z => {Nat.is_lt(C.shift(32n, C.shift(32n, SW.value(nh))), z) == True{} : Bool}, C.shift(32n, C.shift(32n, Nat.mul(Nat.add(one, M.isqrt(SW.value(nh))), Nat.add(one, M.isqrt(SW.value(nh)))))), Nat.mul(SW.value(r0w), SW.value(r0w)), Equal.sym(Nat, Nat.mul(SW.value(r0w), SW.value(r0w)), C.shift(32n, C.shift(32n, Nat.mul(Nat.add(one, M.isqrt(SW.value(nh))), Nat.add(one, M.isqrt(SW.value(nh)))))), e1), l1)))

# S >= 2^62
def s62(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {Nat.is_le(C.shift(62n, one), M.isqrt(C.shift(64n, SW.value(nh)))) == True{} : Bool}:
  +e1 = Equal.trans(Nat, Nat.mul(C.shift(62n, one), C.shift(62n, one)), C.shift(Nat.add(62n, 62n), one), C.shift(64n, C.shift(60n, one)), psq(one, h1, 62n), WW.shift_comp(64n, 60n, one))
  AQ.isqrt_ge(C.shift(64n, SW.value(nh)), C.shift(62n, one), L.subst(Nat, z => {Nat.is_le(z, C.shift(64n, SW.value(nh))) == True{} : Bool}, C.shift(64n, C.shift(60n, one)), Nat.mul(C.shift(62n, one), C.shift(62n, one)), Equal.sym(Nat, Nat.mul(C.shift(62n, one), C.shift(62n, one)), C.shift(64n, C.shift(60n, one)), e1), WW.shift_mono(64n, C.shift(60n, one), SW.value(nh), vn60(one, h1, nh, h62, h60))))

def r0_sd(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}, +r0w: WU.U64, +hR0: {SW.value(r0w) == C.shift(32n, Nat.add(one, M.isqrt(SW.value(nh)))) : Nat}, +hhi: {U32.is_zero(X.hi(r0w)) == False{} : Bool}) -> {Nat.add(M.isqrt(C.shift(64n, SW.value(nh))), Nat.sub(SW.value(r0w), M.isqrt(C.shift(64n, SW.value(nh))))) == SW.value(r0w) : Nat}:
  N.sub_add(SW.value(r0w), M.isqrt(C.shift(64n, SW.value(nh))), N.lt_le(M.isqrt(C.shift(64n, SW.value(nh))), SW.value(r0w), s_hi(one, h1, nh, h62, h60, r0w, hR0, hhi)))

def r0_hi(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {U32.is_zero(X.hi(WU.U64{0, U32.add(X.lo(X.isqrt(nh)), 1)})) == False{} : Bool}:
  Equal.trans(Bool, U32.is_zero(U32.add(X.lo(X.isqrt(nh)), 1)), Nat.is_eq(v(U32.add(X.lo(X.isqrt(nh)), 1)), 0n), False{}, LW.zero_nat(U32.add(X.lo(X.isqrt(nh)), 1)), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), v(U32.add(X.lo(X.isqrt(nh)), 1)), 1n+M.isqrt(SW.value(nh)), add1_v(one, h1, nh, h62, h60)))

def r0_63(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}, +r0w: WU.U64, +hR0: {SW.value(r0w) == C.shift(32n, Nat.add(one, M.isqrt(SW.value(nh)))) : Nat}, +hhi: {U32.is_zero(X.hi(r0w)) == False{} : Bool}) -> {Nat.is_le(SW.value(r0w), C.shift(63n, one)) == True{} : Bool}:
  +l0 = N.lt_succ_le_succ(M.isqrt(SW.value(nh)), C.shift(31n, one), iv31(one, h1, nh, h62, h60))
  +l1 = L.subst(Nat, z => {Nat.is_le(Nat.add(z, M.isqrt(SW.value(nh))), C.shift(31n, one)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), l0)
  +l2 = WW.shift_mono(32n, Nat.add(one, M.isqrt(SW.value(nh))), C.shift(31n, one), l1)
  L.subst(Nat, z => {Nat.is_le(z, C.shift(63n, one)) == True{} : Bool}, C.shift(32n, Nat.add(one, M.isqrt(SW.value(nh)))), SW.value(r0w), Equal.sym(Nat, SW.value(r0w), C.shift(32n, Nat.add(one, M.isqrt(SW.value(nh)))), hR0), L.subst(Nat, z => {Nat.is_le(C.shift(32n, Nat.add(one, M.isqrt(SW.value(nh)))), z) == True{} : Bool}, C.shift(32n, C.shift(31n, one)), C.shift(63n, one), Equal.sym(Nat, C.shift(63n, one), C.shift(32n, C.shift(31n, one)), WW.shift_comp(32n, 31n, one)), l2))

# the quotient digits give Q = floor(nh * 2^64 / r0)

# ---- the Karatsuba (SqrtRem) step: s = isqrt(nh), r = nh - s^2, D = 2 s ----

def not_t(+x: Bool, +h: {Bool.not(x) == True{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, LW.true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case False{}:
      {==}

# q D <= x < (q + 1) D for q = x / D
def dq_le(+x: Nat, +D: Nat, +hD: {Nat.is_lt(0n, D) == True{} : Bool}) -> {Nat.is_le(Nat.mul(Nat.div(x, D), D), x) == True{} : Bool}:
  match D:
    case 0n:
      Empty.absurd({Nat.is_le(Nat.mul(Nat.div(x, 0n), 0n), x) == True{} : Bool}, N.lt_zero_absurd(0n, hD))
    case 1n+ +dp:
      L.subst(Nat, z => {Nat.is_le(Nat.mul(Nat.div(x, 1n+dp), 1n+dp), z) == True{} : Bool}, Nat.add(Nat.mul(Nat.div(x, 1n+dp), 1n+dp), Nat.mod(x, 1n+dp)), x, Equal.sym(Nat, x, Nat.add(Nat.mul(Nat.div(x, 1n+dp), 1n+dp), Nat.mod(x, 1n+dp)), NR.dm_eq(dp, x)), N.le_add_right(Nat.mul(Nat.div(x, 1n+dp), 1n+dp), Nat.mod(x, 1n+dp)))

def dq_lt(+x: Nat, +D: Nat, +hD: {Nat.is_lt(0n, D) == True{} : Bool}) -> {Nat.is_lt(x, Nat.mul(1n+Nat.div(x, D), D)) == True{} : Bool}:
  match D:
    case 0n:
      Empty.absurd({Nat.is_lt(x, Nat.mul(1n+Nat.div(x, 0n), 0n)) == True{} : Bool}, N.lt_zero_absurd(0n, hD))
    case 1n+ +dp:
      +m = Nat.mul(Nat.div(x, 1n+dp), 1n+dp)
      +h1 = Equal.trans(Bool, Nat.is_lt(Nat.add(m, Nat.mod(x, 1n+dp)), Nat.add(m, 1n+dp)), Nat.is_lt(Nat.mod(x, 1n+dp), 1n+dp), True{}, WW.lt_cancel_l(m, Nat.mod(x, 1n+dp), 1n+dp), NR.dm_lt(dp, x))
      +h2 = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(m, 1n+dp)) == True{} : Bool}, Nat.add(m, Nat.mod(x, 1n+dp)), x, Equal.sym(Nat, x, Nat.add(m, Nat.mod(x, 1n+dp)), NR.dm_eq(dp, x)), h1)
      L.subst(Nat, z => {Nat.is_lt(x, z) == True{} : Bool}, Nat.add(m, 1n+dp), Nat.add(1n+dp, m), NA.add_comm(m, 1n+dp), h2)

def s_v(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {v(X.lo(X.isqrt(nh))) == M.isqrt(SW.value(nh)) : Nat}:
  lo_iv(one, h1, nh, h62, h60)

def hn_v(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {Nat.add(Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))))) == SW.value(nh) : Nat}:
  N.sub_add(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), AQ.isl(SW.value(nh)))

def mm_v(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {SW.value(X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))) == Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))) : Nat}:
  Equal.trans(Nat, SW.value(X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))), Nat.mul(v(X.lo(X.isqrt(nh))), v(X.lo(X.isqrt(nh)))), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), W64M.mul32_value(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh))), Equal.trans(Nat, Nat.mul(v(X.lo(X.isqrt(nh))), v(X.lo(X.isqrt(nh)))), Nat.mul(M.isqrt(SW.value(nh)), v(X.lo(X.isqrt(nh)))), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), Equal.cong(Nat, Nat, z => Nat.mul(z, v(X.lo(X.isqrt(nh)))), v(X.lo(X.isqrt(nh))), M.isqrt(SW.value(nh)), s_v(one, h1, nh, h62, h60)), Equal.cong(Nat, Nat, z => Nat.mul(M.isqrt(SW.value(nh)), z), v(X.lo(X.isqrt(nh))), M.isqrt(SW.value(nh)), s_v(one, h1, nh, h62, h60))))

def w_v(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {SW.value(X.sub(nh, X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh))))) == Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))) : Nat}:
  +h = L.subst(Nat, z => {Nat.is_le(z, SW.value(nh)) == True{} : Bool}, Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), SW.value(X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))), Equal.sym(Nat, SW.value(X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), mm_v(one, h1, nh, h62, h60)), AQ.isl(SW.value(nh)))
  Equal.trans(Nat, SW.value(X.sub(nh, X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh))))), Nat.sub(SW.value(nh), SW.value(X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh))))), Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), WA.sub_value(nh, X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh))), h), Equal.cong(Nat, Nat, z => Nat.sub(SW.value(nh), z), SW.value(X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), mm_v(one, h1, nh, h62, h60)))

# r <= 2 s, as nh < (s + 1)^2
def r_le(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {Nat.is_le(Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))) == True{} : Bool}:
  +e1 = Equal.trans(Nat, Nat.add(Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), Nat.add(Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))))), SW.value(nh), NA.add_comm(Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), hn_v(one, h1, nh, h62, h60))
  +h1 = L.subst(Nat, z => {Nat.is_lt(z, Nat.mul(1n+M.isqrt(SW.value(nh)), 1n+M.isqrt(SW.value(nh)))) == True{} : Bool}, SW.value(nh), Nat.add(Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), Equal.sym(Nat, Nat.add(Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), SW.value(nh), e1), AQ.ilt(SW.value(nh)))
  +h2 = L.subst(Nat, z => {Nat.is_lt(Nat.add(Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), z) == True{} : Bool}, Nat.mul(1n+M.isqrt(SW.value(nh)), 1n+M.isqrt(SW.value(nh))), 1n+Nat.add(Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), SQ2.succ_mul_succ(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), h1)
  +h3 = Equal.trans(Bool, Nat.is_lt(Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), 1n+Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), Nat.is_lt(Nat.add(Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), Nat.add(1n+Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))))), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), Nat.add(1n+Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))))), Nat.is_lt(Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), 1n+Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), WW.lt_cancel_r(Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), 1n+Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))))), h2)
  N.lt_succ_le(Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), h3)

# 2 s < 2^32
def d_lt(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {Nat.is_lt(Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), C.shift(32n, one)) == True{} : Bool}:
  +h = iv31(one, h1, nh, h62, h60)
  +S31 = C.shift(31n, one)
  +l2 = N.lt_le_trans(Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), Nat.add(S31, M.isqrt(SW.value(nh))), Nat.add(S31, S31), N.lt_add_r2(M.isqrt(SW.value(nh)), S31, M.isqrt(SW.value(nh)), h), N.le_add_left(M.isqrt(SW.value(nh)), S31, S31, N.lt_le(M.isqrt(SW.value(nh)), S31, h)))
  L.subst(Nat, z => {Nat.is_lt(Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), z) == True{} : Bool}, Nat.add(C.shift(31n, one), C.shift(31n, one)), C.shift(32n, one), Equal.sym(Nat, C.shift(32n, one), Nat.add(C.shift(31n, one), C.shift(31n, one)), NA.double_self(C.shift(31n, one))), l2)

def dw_v(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {v(U32.add(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))) == Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))) : Nat}:
  +e = Equal.trans(Nat, Nat.add(v(X.lo(X.isqrt(nh))), v(X.lo(X.isqrt(nh)))), Nat.add(M.isqrt(SW.value(nh)), v(X.lo(X.isqrt(nh)))), Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), Equal.cong(Nat, Nat, z => Nat.add(z, v(X.lo(X.isqrt(nh)))), v(X.lo(X.isqrt(nh))), M.isqrt(SW.value(nh)), s_v(one, h1, nh, h62, h60)), Equal.cong(Nat, Nat, z => Nat.add(M.isqrt(SW.value(nh)), z), v(X.lo(X.isqrt(nh))), M.isqrt(SW.value(nh)), s_v(one, h1, nh, h62, h60)))
  +f = WW.fits_one(32n, one, h1, Nat.add(v(X.lo(X.isqrt(nh))), v(X.lo(X.isqrt(nh)))), L.subst(Nat, z => {Nat.is_lt(z, C.shift(32n, one)) == True{} : Bool}, Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), Nat.add(v(X.lo(X.isqrt(nh))), v(X.lo(X.isqrt(nh)))), Equal.sym(Nat, Nat.add(v(X.lo(X.isqrt(nh))), v(X.lo(X.isqrt(nh)))), Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), e), d_lt(one, h1, nh, h62, h60)))
  Equal.trans(Nat, v(U32.add(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))), Nat.add(v(X.lo(X.isqrt(nh))), v(X.lo(X.isqrt(nh)))), Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), WA.add_exact(one, h1, X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)), f), e)

# 2 s > 0, as nh >= 2^60
def d_pos(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {Nat.is_lt(0n, Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))) == True{} : Bool}:
  +h1n = N.le_trans(1n, C.shift(60n, one), SW.value(nh), L.subst(Nat, o => {Nat.is_le(o, C.shift(60n, one)) == True{} : Bool}, one, 1n, h1, WW.shift_ge(60n, one)), vn60(one, h1, nh, h62, h60))
  +hs = AQ.isqrt_ge(SW.value(nh), 1n, h1n)
  N.lt_le_trans(0n, 1n, Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), {==}, N.le_trans(1n, M.isqrt(SW.value(nh)), Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), hs, N.le_add_right(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))))

def dw_nz(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {U32.is_zero(U32.add(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))) == False{} : Bool}:
  +e = Equal.trans(Bool, U32.is_zero(U32.add(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))), Nat.is_eq(v(U32.add(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))), 0n), Nat.is_eq(Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), 0n), LW.zero_nat(U32.add(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), v(U32.add(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))), Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), dw_v(one, h1, nh, h62, h60)))
  +h = Equal.trans(Bool, Bool.not(Nat.is_eq(Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), 0n)), Nat.is_lt(0n, Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), True{}, Equal.sym(Bool, Nat.is_lt(0n, Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), Bool.not(Nat.is_eq(Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), 0n)), QW.ltz(Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))))), d_pos(one, h1, nh, h62, h60))
  Equal.trans(Bool, U32.is_zero(U32.add(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))), Nat.is_eq(Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), 0n), False{}, e, not_t(Nat.is_eq(Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), 0n), h))

def lo_w(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {v(X.lo(X.sub(nh, X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))))) == Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))) : Nat}:
  +hr = N.le_lt_trans(Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), C.shift(32n, one), r_le(one, h1, nh, h62, h60), d_lt(one, h1, nh, h62, h60))
  +f = WW.fits_one(32n, one, h1, SW.value(X.sub(nh, X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh))))), L.subst(Nat, z => {Nat.is_lt(z, C.shift(32n, one)) == True{} : Bool}, Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), SW.value(X.sub(nh, X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh))))), Equal.sym(Nat, SW.value(X.sub(nh, X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh))))), Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), w_v(one, h1, nh, h62, h60)), hr))
  Equal.trans(Nat, v(X.lo(X.sub(nh, X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))))), SW.value(X.sub(nh, X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh))))), Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), lo_val(X.sub(nh, X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))), f), w_v(one, h1, nh, h62, h60))

def q_v(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {SW.value(X.fst_q(X.div32(WU.U64{0, X.lo(X.sub(nh, X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))))}, U32.add(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))))) == Nat.div(C.shift(32n, Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))))), Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))) : Nat}:
  Equal.trans(Nat, SW.value(X.fst_q(X.div32(WU.U64{0, X.lo(X.sub(nh, X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))))}, U32.add(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))))), Nat.div(C.shift(32n, v(X.lo(X.sub(nh, X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh))))))), v(U32.add(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh))))), Nat.div(C.shift(32n, Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))))), Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), W64D.div32_quot(WU.U64{0, X.lo(X.sub(nh, X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))))}, U32.add(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh))), dw_nz(one, h1, nh, h62, h60)), Equal.trans(Nat, Nat.div(C.shift(32n, v(X.lo(X.sub(nh, X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh))))))), v(U32.add(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh))))), Nat.div(C.shift(32n, Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))))), v(U32.add(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh))))), Nat.div(C.shift(32n, Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))))), Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), Equal.cong(Nat, Nat, z => Nat.div(C.shift(32n, z), v(U32.add(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh))))), v(X.lo(X.sub(nh, X.mul32(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))))), Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), lo_w(one, h1, nh, h62, h60)), Equal.cong(Nat, Nat, z => Nat.div(C.shift(32n, Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))))), z), v(U32.add(X.lo(X.isqrt(nh)), X.lo(X.isqrt(nh)))), Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), dw_v(one, h1, nh, h62, h60))))

def hq_le(+one: Nat, +h1: {one == 1n : Nat}, +nh: WU.U64, +h62: {C.fits(62n, SW.value(nh)) == True{} : Bool}, +h60: {C.fits(60n, SW.value(nh)) == False{} : Bool}) -> {Nat.is_le(Nat.mul(Nat.div(C.shift(32n, Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))))), Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))), C.shift(32n, Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh)))))) == True{} : Bool}:
  dq_le(C.shift(32n, Nat.sub(SW.value(nh), Nat.mul(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))))), Nat.add(M.isqrt(SW.value(nh)), M.isqrt(SW.value(nh))), d_pos(one, h1, nh, h62, h60))
