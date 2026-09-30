import Base
import ./f64round.bend as FR
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ../../lib/word.bend as WD
import ../../../src/math/natural.bend as M
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../natural/arith.bend as NR
import ./natcmp.bend as NC
import ./width.bend as WW
import ./w64sh.bend as SH
import ./f64bits.bend as FB
import ./f64rtools.bend as RT

# Small F64 lemmas shared by the division and the square-root proofs. They
# live here so that the square-root root does not import (and re-check) the
# division proofs.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def fval_g(+xl: U32, +xh: U32, +m: U32, +hm: {m == U32{WD.mask(32n, 20n)} : U32}) -> {SW.value(WU.U64{xl, U32.and(xh, m)}) == SF.frac(F.Bits{xl, xh}) : Nat}:
  Equal.cong(Nat, Nat, z => Nat.add(v(xl), C.shift(32n, z)), v(U32.and(xh, m)), C.low(20n, v(xh)), FB.andm(xh, 20n, m, hm))

def hea(+xl: U32, +xh: U32) -> {F.exp_field(F.Bits{xl, xh}) == SF.efield(F.Bits{xl, xh}) : Nat}:
  FB.ef_g(1n, {==}, xh, 1048576, {==}, 2047, {==})

def hfr(+xl: U32, +xh: U32) -> {SW.value(F.frac(F.Bits{xl, xh})) == SF.frac(F.Bits{xl, xh}) : Nat}:
  fval_g(xl, xh, 1048575, {==})

def non(+x: F.F64, +b: Bool) -> {F.nan_or(x, b) == SF.pick(F.F64, b, F.nan(), x) : F.F64}:
  match b:
    case True{}:
      Equal.trans(F.F64, F.nan_or(x, True{}), F.nan(), SF.pick(F.F64, True{}, F.nan(), x), {==}, Equal.sym(F.F64, SF.pick(F.F64, True{}, F.nan(), x), F.nan(), FR.pk_t(F.F64, F.nan(), x)))
    case False{}:
      Equal.trans(F.F64, F.nan_or(x, False{}), x, SF.pick(F.F64, False{}, F.nan(), x), {==}, Equal.sym(F.F64, SF.pick(F.F64, False{}, F.nan(), x), x, FR.pk_f(F.F64, F.nan(), x)))

def nfit_mono_c(+a: Nat, +b: Nat, +x: Nat, +hab: {Nat.is_le(a, b) == True{} : Bool}, +h: {C.fits(b, x) == False{} : Bool}, +c: Bool, +hc: {C.fits(a, x) == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      Equal.trans(Bool, True{}, C.fits(b, x), False{}, Equal.sym(Bool, C.fits(b, x), True{}, SH.fits_mono(a, b, x, hab, hc)), h)
    case False{}:
      {==}

def nfit_mono(+a: Nat, +b: Nat, +x: Nat, +hab: {Nat.is_le(a, b) == True{} : Bool}, +h: {C.fits(b, x) == False{} : Bool}) -> {C.fits(a, x) == False{} : Bool}:
  nfit_mono_c(a, b, x, hab, h, C.fits(a, x), {==})

def dm2(+l: Bool, +r: Bool) -> {Bool.or(Bool.not(r), Bool.not(l)) == Bool.not(Bool.and(l, r)) : Bool}:
  match l r:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def add_lt2(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a, a), Nat.add(b, b)) == True{} : Bool}:
  +l1 = Equal.trans(Bool, Nat.is_lt(Nat.add(a, a), Nat.add(a, b)), Nat.is_lt(a, b), True{}, WW.lt_cancel_l(a, a, b), h)
  +l2 = Equal.trans(Bool, Nat.is_lt(Nat.add(a, b), Nat.add(b, b)), Nat.is_lt(a, b), True{}, WW.lt_cancel_r(a, b, b), h)
  N.lt_trans(Nat.add(a, a), Nat.add(a, b), Nat.add(b, b), l1, l2)

def add_eq0(+a: Nat, +b: Nat) -> {Nat.is_eq(Nat.add(a, b), 0n) == Bool.and(Nat.is_eq(a, 0n), Nat.is_eq(b, 0n)) : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+ +ap:
      {==}

def shl_v(+a: WU.U64, +k: Nat, +j: Nat, +hk: {Nat.is_lt(k, 64n) == True{} : Bool}, +hj: {Nat.is_le(Nat.add(k, j), 64n) == True{} : Bool}, +ha: {C.fits(j, SW.value(a)) == True{} : Bool}) -> {SW.value(X.shl(a, k)) == C.shift(k, SW.value(a)) : Nat}:
  sv = SH.shl_value(a, k, hk)
  +f = SH.fits_mono(Nat.add(k, j), 64n, C.shift(k, SW.value(a)), hj, Equal.trans(Bool, C.fits(Nat.add(k, j), C.shift(k, SW.value(a))), C.fits(j, SW.value(a)), True{}, RT.fits_sh(k, j, SW.value(a)), ha))
  Equal.trans(Nat, SW.value(X.shl(a, k)), C.low(64n, C.shift(k, SW.value(a))), C.shift(k, SW.value(a)), sv, WW.low_fit(64n, C.shift(k, SW.value(a)), f))

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

def jmin(+q: Nat, +r: Nat) -> {SW.jam(q, SF.b2n(Bool.not(Nat.is_eq(r, 0n)))) == SW.jam(q, r) : Nat}:
  match r:
    case 0n:
      {==}
    case 1n+ +rp:
      Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(2n, Nat.div(q, 2n)), Nat.max(Nat.mod(q, 2n), z)), 1n, Nat.min(1n+rp, 1n), Equal.sym(Nat, 1n+Nat.min(rp, 0n), 1n, Equal.cong(Nat, Nat, z => 1n+z, Nat.min(rp, 0n), 0n, minz(rp))))

def nlb(+s: Bool, +k: Nat, +m: Nat, +x: Nat, +hk: {C.fits(k, m) == False{} : Bool}, +c: Bool, +hc: {Nat.is_le(1n+k, M.bit_length(m)) == c : Bool}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      +h1 = N.lt_succ_le(M.bit_length(m), k, N.not_le_lt(1n+k, M.bit_length(m), hc))
      NC.absurd_tf({False{} == True{} : Bool}, Equal.trans(Bool, False{}, C.fits(k, m), True{}, Equal.sym(Bool, C.fits(k, m), False{}, hk), SH.fits_mono(M.bit_length(m), k, m, h1, RT.bl_fit(m))))

def nfit_bl(+k: Nat, +m: Nat, +hk: {C.fits(k, m) == False{} : Bool}) -> {Nat.is_le(1n+k, M.bit_length(m)) == True{} : Bool}:
  nlb(False{}, k, m, 0n, hk, Nat.is_le(1n+k, M.bit_length(m)), {==})
