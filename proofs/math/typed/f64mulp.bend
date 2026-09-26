import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../lib/word.bend as WD
import ../natural/arith.bend as NR
import ./width.bend as WW
import ./w64add.bend as WA
import ./w64sh.bend as SH
import ./f64bits.bend as FB
import ./f64round.bend as FR
import ./f64rtools.bend as RT

# Pieces of SoftFloat's f64_mul and roundPackToF64 used by the arithmetic
# proofs: the sticky OR into bit 0, the one-bit renormalization of rp62, and
# exact products of 53-bit significands.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# or_bit(a, b) is jam(a, b)
def orv_c(+l: U32, +h: U32, +b: Bool) -> {SW.value(X.or_bit(WU.U64{l, h}, b)) == SW.jam(SW.value(WU.U64{l, h}), SF.b2n(b)) : Nat}:
  match b:
    case True{}:
      +s31 = C.shift(31n, v(h))
      +e1 = Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(32n, v(h))), v(U32.or(l, 1)), 1n+Nat.double(C.half(v(l))), SH.or1(l))
      +eh = WW.half_dbl(v(l), s31)
      +e2 = Equal.trans(Nat, Nat.add(1n+Nat.double(C.half(v(l))), C.shift(32n, v(h))), 1n+Nat.add(Nat.double(C.half(v(l))), Nat.double(s31)), 1n+Nat.double(C.half(SW.value(WU.U64{l, h}))), NA.add_assoc(1n, Nat.double(C.half(v(l))), Nat.double(s31)), Equal.trans(Nat, 1n+Nat.add(Nat.double(C.half(v(l))), Nat.double(s31)), 1n+Nat.double(Nat.add(C.half(v(l)), s31)), 1n+Nat.double(C.half(SW.value(WU.U64{l, h}))), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.double(C.half(v(l))), Nat.double(s31)), Nat.double(Nat.add(C.half(v(l)), s31)), Equal.sym(Nat, Nat.double(Nat.add(C.half(v(l)), s31)), Nat.add(Nat.double(C.half(v(l))), Nat.double(s31)), NA.double_add(C.half(v(l)), s31))), Equal.cong(Nat, Nat, z => 1n+Nat.double(z), Nat.add(C.half(v(l)), s31), C.half(SW.value(WU.U64{l, h})), Equal.sym(Nat, C.half(SW.value(WU.U64{l, h})), Nat.add(C.half(v(l)), s31), eh))))
      +e3 = Equal.sym(Nat, SW.jam(SW.value(WU.U64{l, h}), 1n), 1n+Nat.double(C.half(SW.value(WU.U64{l, h}))), SH.jam1_k(SW.value(WU.U64{l, h}), Nat.mod(SW.value(WU.U64{l, h}), 2n), {==}, NR.dm_lt(1n, SW.value(WU.U64{l, h}))))
      Equal.trans(Nat, Nat.add(v(U32.or(l, 1)), C.shift(32n, v(h))), Nat.add(1n+Nat.double(C.half(v(l))), C.shift(32n, v(h))), SW.jam(SW.value(WU.U64{l, h}), 1n), e1, Equal.trans(Nat, Nat.add(1n+Nat.double(C.half(v(l))), C.shift(32n, v(h))), 1n+Nat.double(C.half(SW.value(WU.U64{l, h}))), SW.jam(SW.value(WU.U64{l, h}), 1n), e2, e3))
    case False{}:
      Equal.trans(Nat, Nat.add(v(U32.or(l, 0)), C.shift(32n, v(h))), SW.value(WU.U64{l, h}), SW.jam(SW.value(WU.U64{l, h}), 0n), Equal.cong(U32, Nat, z => Nat.add(v(z), C.shift(32n, v(h))), U32.or(l, 0), l, SH.or0(l)), Equal.sym(Nat, SW.jam(SW.value(WU.U64{l, h}), 0n), SW.value(WU.U64{l, h}), SH.jam0_m(SW.value(WU.U64{l, h}), Nat.mod(SW.value(WU.U64{l, h}), 2n), {==}, NR.dm_lt(1n, SW.value(WU.U64{l, h})))))

def orv(+a: WU.U64, +b: Bool) -> {SW.value(X.or_bit(a, b)) == SW.jam(SW.value(a), SF.b2n(b)) : Nat}:
  match a:
    case WU.U64{+l, +h}:
      orv_c(l, h, b)

def minz(+r: Nat) -> {Nat.min(r, 0n) == 0n : Nat}:
  match r:
    case 0n:
      {==}
    case 1n+ +rp:
      {==}

# jam reads only whether r is zero
def jmin(+q: Nat, +r: Nat) -> {SW.jam(q, SF.b2n(Bool.not(Nat.is_eq(r, 0n)))) == SW.jam(q, r) : Nat}:
  match r:
    case 0n:
      {==}
    case 1n+ +rp:
      Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(2n, Nat.div(q, 2n)), Nat.max(Nat.mod(q, 2n), z)), 1n, Nat.min(1n+rp, 1n), Equal.sym(Nat, 1n+Nat.min(rp, 0n), 1n, Equal.cong(Nat, Nat, z => 1n+z, Nat.min(rp, 0n), 0n, minz(rp))))

# ---- rp62: a significand in [2^61, 2^63) renormalized to bit 62 ----

def lt62(+one: Nat, +h1: {one == 1n : Nat}, +sig: WU.U64, +c: U32, +hc: {c == U32{WD.pw(32n, 30n)} : U32}) -> {X.lt(sig, WU.U64{0, c}) == C.fits(62n, SW.value(sig)) : Bool}:
  l1 = WA.lt_value(sig, WU.U64{0, c})
  +ec = Equal.trans(Nat, C.shift(32n, v(c)), C.shift(32n, C.shift(30n, one)), C.shift(62n, one), Equal.cong(Nat, Nat, z => C.shift(32n, z), v(c), C.shift(30n, one), FB.pwv(30n, {==}, one, h1, c, hc)), Equal.sym(Nat, C.shift(62n, one), C.shift(32n, C.shift(30n, one)), WW.shift_comp(32n, 30n, one)))
  Equal.trans(Bool, X.lt(sig, WU.U64{0, c}), Nat.is_lt(SW.value(sig), C.shift(32n, v(c))), C.fits(62n, SW.value(sig)), l1, Equal.trans(Bool, Nat.is_lt(SW.value(sig), C.shift(32n, v(c))), Nat.is_lt(SW.value(sig), C.shift(62n, one)), C.fits(62n, SW.value(sig)), Equal.cong(Nat, Bool, z => Nat.is_lt(SW.value(sig), z), C.shift(32n, v(c)), C.shift(62n, one), ec), FR.lt_fit(62n, one, h1, SW.value(sig))))

def rp62_c(+s: Bool, +e: Nat, +sig: WU.U64, +x: Nat, +hx: {Nat.add(x, 2180n) == e : Nat}, +hx1: {Nat.is_le(1n, x) == True{} : Bool}, +h61: {C.fits(61n, SW.value(sig)) == False{} : Bool}, +h63: {C.fits(63n, SW.value(sig)) == True{} : Bool}, +f: Bool, +hf: {C.fits(62n, SW.value(sig)) == f : Bool}) -> {F.rp62_pick(s, e, sig, f) == SF.round(s, SW.value(sig), x) : F.F64}:
  match f:
    case True{}:
      +Vs = SW.value(sig)
      +d = X.add(sig, sig)
      a1 = WA.add_value(sig, sig)
      +f63 = L.subst(Nat, z => {C.fits(63n, z) == True{} : Bool}, Nat.add(0n, C.shift(1n, Vs)), Nat.double(Vs), {==}, WW.limbs_fit(1n, 62n, 0n, Vs, FR.fz(1n), hf))
      +eVV = Equal.sym(Nat, Nat.double(Vs), Nat.add(Vs, Vs), NA.double_self(Vs))
      +ed = Equal.trans(Nat, SW.value(d), C.low(64n, Nat.add(Vs, Vs)), Nat.double(Vs), a1, Equal.trans(Nat, C.low(64n, Nat.add(Vs, Vs)), C.low(64n, Nat.double(Vs)), Nat.double(Vs), Equal.cong(Nat, Nat, z => C.low(64n, z), Nat.add(Vs, Vs), Nat.double(Vs), eVV), WW.low_fit(64n, Nat.double(Vs), SH.fits_mono(63n, 64n, Nat.double(Vs), {==}, f63))))
      +f62 = Equal.trans(Bool, C.fits(62n, Nat.double(Vs)), C.fits(61n, Vs), False{}, RT.fit_td(61n, 0n, Vs, {==}), h61)
      +h62d = L.subst(Nat, z => {C.fits(62n, z) == False{} : Bool}, Nat.double(Vs), SW.value(d), Equal.sym(Nat, SW.value(d), Nat.double(Vs), ed), f62)
      +h63d = L.subst(Nat, z => {C.fits(63n, z) == True{} : Bool}, Nat.double(Vs), SW.value(d), Equal.sym(Nat, SW.value(d), Nat.double(Vs), ed), f63)
      +ex = Equal.trans(Nat, Nat.add(Nat.sub(x, 1n), 2180n), Nat.sub(Nat.add(x, 2180n), 1n), Nat.sub(e, 1n), Equal.sym(Nat, Nat.sub(Nat.add(x, 2180n), 1n), Nat.add(Nat.sub(x, 1n), 2180n), FR.sub_add_r(x, 2180n, 1n, hx1)), Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), Nat.add(x, 2180n), e, hx))
      +r1 = FR.round_pack(s, Nat.sub(e, 1n), d, Nat.sub(x, 1n), ex, h62d, h63d)
      +r2 = Equal.cong(Nat, F.F64, z => SF.round(s, z, Nat.sub(x, 1n)), SW.value(d), C.shift(1n, Vs), ed)
      +r3 = RT.round_shift(s, 1n, Vs, Nat.sub(x, 1n))
      +r4 = Equal.cong(Nat, F.F64, z => SF.round(s, Vs, z), Nat.add(Nat.sub(x, 1n), 1n), x, Equal.trans(Nat, Nat.add(Nat.sub(x, 1n), 1n), Nat.add(1n, Nat.sub(x, 1n)), x, NA.add_comm(Nat.sub(x, 1n), 1n), N.sub_add(x, 1n, hx1)))
      Equal.trans(F.F64, F.round_pack(s, Nat.sub(e, 1n), d), SF.round(s, SW.value(d), Nat.sub(x, 1n)), SF.round(s, Vs, x), r1, Equal.trans(F.F64, SF.round(s, SW.value(d), Nat.sub(x, 1n)), SF.round(s, C.shift(1n, Vs), Nat.sub(x, 1n)), SF.round(s, Vs, x), r2, Equal.trans(F.F64, SF.round(s, C.shift(1n, Vs), Nat.sub(x, 1n)), SF.round(s, Vs, Nat.add(Nat.sub(x, 1n), 1n)), SF.round(s, Vs, x), r3, r4)))
    case False{}:
      FR.round_pack(s, e, sig, x, hx, hf, h63)

def rp62_g(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +e: Nat, +sig: WU.U64, +x: Nat, +hx: {Nat.add(x, 2180n) == e : Nat}, +hx1: {Nat.is_le(1n, x) == True{} : Bool}, +h61: {C.fits(61n, SW.value(sig)) == False{} : Bool}, +h63: {C.fits(63n, SW.value(sig)) == True{} : Bool}, +c: U32, +hc: {c == U32{WD.pw(32n, 30n)} : U32}) -> {F.rp62_pick(s, e, sig, X.lt(sig, WU.U64{0, c})) == SF.round(s, SW.value(sig), x) : F.F64}:
  +el = lt62(one, h1, sig, c, hc)
  Equal.trans(F.F64, F.rp62_pick(s, e, sig, X.lt(sig, WU.U64{0, c})), F.rp62_pick(s, e, sig, C.fits(62n, SW.value(sig))), SF.round(s, SW.value(sig), x), Equal.cong(Bool, F.F64, t => F.rp62_pick(s, e, sig, t), X.lt(sig, WU.U64{0, c}), C.fits(62n, SW.value(sig)), el), rp62_c(s, e, sig, x, hx, hx1, h61, h63, C.fits(62n, SW.value(sig)), {==}))

# SoftFloat's rp62(s, e, sig) for sig in [2^61, 2^63) is round(s, sig, e - 2180)
def rp62(+s: Bool, +e: Nat, +sig: WU.U64, +x: Nat, +hx: {Nat.add(x, 2180n) == e : Nat}, +hx1: {Nat.is_le(1n, x) == True{} : Bool}, +h61: {C.fits(61n, SW.value(sig)) == False{} : Bool}, +h63: {C.fits(63n, SW.value(sig)) == True{} : Bool}) -> {F.rp62(s, e, sig) == SF.round(s, SW.value(sig), x) : F.F64}:
  rp62_g(1n, {==}, s, e, sig, x, hx, hx1, h61, h63, 1073741824, {==})
