import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ../../lib/word.bend as WD
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
      {==}
    case False{}:
      {==}

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
