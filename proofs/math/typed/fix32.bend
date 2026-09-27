import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/generic.bend as SG
import ../../../spec/math/fixed.bend as SF
import ../../../src/math/w64.bend as X
import ../../../src/math/fixed.bend as F
import ../../../src/math/generic.bend as GN
import ../../../src/math/instances.bend as I
import ../../../src/math/num.bend as NM
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/arith.bend as AR
import ../../lib/word.bend as WD
import ../../lib/u32.bend as U3
import ../../lib/u32div.bend as UD
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../natural/arith.bend as R
import ../natural/modpow.bend as MP
import ../natural/bits.bend as B
import ./width.bend as WW
import ./w64add.bend as WA
import ../u64/u64.bend as P64
import ./w64sh.bend as SH
import ./w64est.bend as WE
import ./shrn.bend as SHN
import ./u32laws.bend as LW
import ./u32int.bend as UI
import ./f64bits.bend as FB
import ./fixgen.bend as G

# The U32 clauses of spec/math/fixed.bend (Rust's u32 checked_*,
# wrapping_*, saturating_*, overflowing_* families) from Base's U32
# operations through their values: U32.add and U32.sub with their carry
# (w64add.bend's acons / sub_cons, HACL*'s addcarry / subborrow lemmas),
# U32.mul modulo 2^32 (w64sh.bend's mul_low), the long division of
# proofs/lib/u32div.bend and the generic pow of u32int.bend.

def vs(+s: U32) -> Nat:
  U32.to_nat(s)

# ---- the largest value 2^32 - 1 (1 kept as one, compared as a U32) ----

def zero_add(+x: Nat) -> {Nat.add(0n, x) == x : Nat}:
  Equal.trans(Nat, Nat.add(0n, x), Nat.add(x, 0n), x, N.add_comm(0n, x), N.add_zero(x))

def topw(+one: Nat, +h1: {one == 1n : Nat}, +w: U32, +pw: {w == U32{WD.mask(32n, 32n)} : U32}) -> {Bool.and(C.fits(32n, SG.u32_val(w)), Bool.not(C.fits(32n, 1n+SG.u32_val(w)))) == True{} : Bool}:
  +S = C.shift(32n, one)
  +e1 = Equal.cong(Nat, Bool, t => C.fits(32n, t), 1n+SG.u32_val(w), S, WE.m32(one, h1, w, pw))
  +e2 = Equal.cong(Nat, Bool, t => C.fits(32n, t), S, Nat.add(0n, S), Equal.sym(Nat, Nat.add(0n, S), S, zero_add(S)))
  G.top_ok(32n, SG.u32_val(w), LW.vb(w), Equal.trans(Bool, C.fits(32n, 1n+SG.u32_val(w)), C.fits(32n, S), False{}, e1, Equal.trans(Bool, C.fits(32n, S), C.fits(32n, Nat.add(0n, S)), False{}, e2, WW.unfit_one(32n, one, h1, 0n))))

def top(+one: Nat, +h1: {one == 1n : Nat}) -> {Bool.and(C.fits(32n, SG.u32_val(F.u32_max())), Bool.not(C.fits(32n, 1n+SG.u32_val(F.u32_max())))) == True{} : Bool}:
  L.subst(U32, t => {Bool.and(C.fits(32n, SG.u32_val(t)), Bool.not(C.fits(32n, 1n+SG.u32_val(t)))) == True{} : Bool}, 4294967295, F.u32_max(), {==}, topw(one, h1, 4294967295, {==}))

# ---- the operations modulo 2^32 ----

def add_low(+x: U32, +y: U32) -> {SG.u32_val(U32.add(x, y)) == C.low(32n, Nat.add(SG.u32_val(x), SG.u32_val(y))) : Nat}:
  +c = WA.bv(P64.carry32(x, y))
  +e = Equal.cong(Nat, Nat, t => C.low(32n, t), Nat.add(SG.u32_val(x), SG.u32_val(y)), Nat.add(SG.u32_val(U32.add(x, y)), C.shift(32n, c)), Equal.sym(Nat, Nat.add(SG.u32_val(U32.add(x, y)), C.shift(32n, c)), Nat.add(SG.u32_val(x), SG.u32_val(y)), WA.acons(x, y)))
  Equal.sym(Nat, C.low(32n, Nat.add(SG.u32_val(x), SG.u32_val(y))), SG.u32_val(U32.add(x, y)), Equal.trans(Nat, C.low(32n, Nat.add(SG.u32_val(x), SG.u32_val(y))), C.low(32n, Nat.add(SG.u32_val(U32.add(x, y)), C.shift(32n, c))), SG.u32_val(U32.add(x, y)), e, WW.low_u(32n, SG.u32_val(U32.add(x, y)), c, LW.vb(U32.add(x, y)))))

def mul_low(+x: U32, +y: U32) -> {SG.u32_val(U32.mul(x, y)) == C.low(32n, Nat.mul(SG.u32_val(x), SG.u32_val(y))) : Nat}:
  SH.mul_low(x, y)

def add_over(+a: U32, +b: U32) -> {F.u32_add_over(a, b) == Bool.not(C.fits(32n, Nat.add(SG.u32_val(a), SG.u32_val(b)))) : Bool}:
  LW.tests_add_over(a, b)

def mul_over(+a: U32, +b: U32) -> {F.u32_mul_over(a, b) == Bool.not(C.fits(32n, Nat.mul(SG.u32_val(a), SG.u32_val(b)))) : Bool}:
  LW.tests_mul_over(a, b)

def lt_nat(+a: U32, +b: U32) -> {U32.is_lt(a, b) == Nat.is_lt(SG.u32_val(a), SG.u32_val(b)) : Bool}:
  U3.is_lt_nat(a, b)

# ---- add, mul ----

def checked_add(+a: U32, +b: U32) -> SF.CheckedAdd.value(~U32, ~SG.u32_val, ~F.u32_checked_add, 32n, a, b):
  G.chk_fit(~U32, ~SG.u32_val, 32n, Nat.add(SG.u32_val(a), SG.u32_val(b)), U32.add(a, b), F.u32_add_over(a, b), add_over(a, b), add_low(a, b), C.fits(32n, Nat.add(SG.u32_val(a), SG.u32_val(b))), {==})

def wrapping_add(+a: U32, +b: U32) -> SF.WrappingAdd.value(~U32, ~SG.u32_val, ~F.u32_wrapping_add, 32n, a, b):
  add_low(a, b)

def saturating_add(+a: U32, +b: U32) -> SF.SaturatingAdd.value(~U32, ~SG.u32_val, ~F.u32_saturating_add, 32n, a, b):
  G.sat_fit(~U32, ~SG.u32_val, 32n, Nat.add(SG.u32_val(a), SG.u32_val(b)), U32.add(a, b), F.u32_max(), F.u32_add_over(a, b), add_over(a, b), add_low(a, b), top(1n, {==}), C.fits(32n, Nat.add(SG.u32_val(a), SG.u32_val(b))), {==})

def overflowing_add_value(+a: U32, +b: U32) -> SF.OverflowingAdd.value(~U32, ~SG.u32_val, ~F.u32_overflowing_add, 32n, a, b):
  add_low(a, b)

def overflowing_add_flag(+a: U32, +b: U32) -> SF.OverflowingAdd.flag(~U32, ~SG.u32_val, ~F.u32_overflowing_add, 32n, a, b):
  add_over(a, b)

def checked_mul(+a: U32, +b: U32) -> SF.CheckedMul.value(~U32, ~SG.u32_val, ~F.u32_checked_mul, 32n, a, b):
  G.chk_fit(~U32, ~SG.u32_val, 32n, Nat.mul(SG.u32_val(a), SG.u32_val(b)), U32.mul(a, b), F.u32_mul_over(a, b), mul_over(a, b), mul_low(a, b), C.fits(32n, Nat.mul(SG.u32_val(a), SG.u32_val(b))), {==})

def wrapping_mul(+a: U32, +b: U32) -> SF.WrappingMul.value(~U32, ~SG.u32_val, ~F.u32_wrapping_mul, 32n, a, b):
  mul_low(a, b)

def saturating_mul(+a: U32, +b: U32) -> SF.SaturatingMul.value(~U32, ~SG.u32_val, ~F.u32_saturating_mul, 32n, a, b):
  G.sat_fit(~U32, ~SG.u32_val, 32n, Nat.mul(SG.u32_val(a), SG.u32_val(b)), U32.mul(a, b), F.u32_max(), F.u32_mul_over(a, b), mul_over(a, b), mul_low(a, b), top(1n, {==}), C.fits(32n, Nat.mul(SG.u32_val(a), SG.u32_val(b))), {==})

def overflowing_mul_value(+a: U32, +b: U32) -> SF.OverflowingMul.value(~U32, ~SG.u32_val, ~F.u32_overflowing_mul, 32n, a, b):
  mul_low(a, b)

def overflowing_mul_flag(+a: U32, +b: U32) -> SF.OverflowingMul.flag(~U32, ~SG.u32_val, ~F.u32_overflowing_mul, 32n, a, b):
  mul_over(a, b)

# ---- sub ----

def sub_exact(+a: U32, +b: U32, +h: {Nat.is_le(SG.u32_val(b), SG.u32_val(a)) == True{} : Bool}) -> {SG.u32_val(U32.sub(a, b)) == Nat.sub(SG.u32_val(a), SG.u32_val(b)) : Nat}:
  LW.ops_sub(a, b, h)

def csub(+a: U32, +b: U32, +ok: Bool, +hok: {Nat.is_le(SG.u32_val(b), SG.u32_val(a)) == ok : Bool}) -> {SF.mval(~U32, ~SG.u32_val, F.opt(U32, U32.is_lt(a, b), U32.sub(a, b))) == SF.keep(ok, Nat.sub(SG.u32_val(a), SG.u32_val(b))) : Maybe<&2, Nat>}:
  match ok:
    case True{}:
      G.some_of(~U32, ~SG.u32_val, U32.is_lt(a, b), Equal.trans(Bool, U32.is_lt(a, b), Nat.is_lt(SG.u32_val(a), SG.u32_val(b)), False{}, lt_nat(a, b), N.le_not_lt(SG.u32_val(a), SG.u32_val(b), hok)), U32.sub(a, b), Nat.sub(SG.u32_val(a), SG.u32_val(b)), sub_exact(a, b, hok))
    case False{}:
      G.none_of(~U32, ~SG.u32_val, U32.is_lt(a, b), Equal.trans(Bool, U32.is_lt(a, b), Nat.is_lt(SG.u32_val(a), SG.u32_val(b)), True{}, lt_nat(a, b), N.not_le_lt(SG.u32_val(b), SG.u32_val(a), hok)), U32.sub(a, b))

def checked_sub(+a: U32, +b: U32) -> SF.CheckedSub.value(~U32, ~SG.u32_val, ~F.u32_checked_sub, a, b):
  csub(a, b, Nat.is_le(SG.u32_val(b), SG.u32_val(a)), {==})

def sub_big(+n: Nat, +d: Nat, +h: {Nat.is_le(n, d) == True{} : Bool}) -> {Nat.sub(n, d) == 0n : Nat}:
  match n d:
    case 0n _:
      R.zsub(d)
    case 1n+np 0n:
      Empty.absurd({Nat.sub(1n+np, 0n) == 0n : Nat}, L.false_true(h))
    case 1n+ +np 1n+ +dp:
      sub_big(np, dp, h)

def ssub(+a: U32, +b: U32, +c: Bool, +hn: {Nat.is_lt(SG.u32_val(a), SG.u32_val(b)) == c : Bool}) -> {SG.u32_val(F.pick(U32, c, 0, U32.sub(a, b))) == Nat.sub(SG.u32_val(a), SG.u32_val(b)) : Nat}:
  match c:
    case True{}:
      Equal.sym(Nat, Nat.sub(SG.u32_val(a), SG.u32_val(b)), 0n, sub_big(SG.u32_val(a), SG.u32_val(b), N.lt_le(SG.u32_val(a), SG.u32_val(b), hn)))
    case False{}:
      sub_exact(a, b, N.not_lt_le(SG.u32_val(a), SG.u32_val(b), hn))

def saturating_sub(+a: U32, +b: U32) -> SF.SaturatingSub.value(~U32, ~SG.u32_val, ~F.u32_saturating_sub, a, b):
  ssub(a, b, U32.is_lt(a, b), Equal.sym(Bool, U32.is_lt(a, b), Nat.is_lt(SG.u32_val(a), SG.u32_val(b)), lt_nat(a, b)))

def overflowing_sub_flag(+a: U32, +b: U32) -> SF.OverflowingSub.flag(~U32, ~SG.u32_val, ~F.u32_overflowing_sub, a, b):
  lt_nat(a, b)

def bo_bn(+one: Nat, +h1: {one == 1n : Nat}, +c: Bool) -> {WD.bo(c, one) == SF.bn(c) : Nat}:
  match c:
    case True{}:
      h1
    case False{}:
      {==}

def wsub_g(+one: Nat, +h1: {one == 1n : Nat}, +a: U32, +b: U32) -> {Nat.add(SG.u32_val(U32.sub(a, b)), SG.u32_val(b)) == Nat.add(SG.u32_val(a), C.shift(32n, SF.bn(Nat.is_lt(SG.u32_val(a), SG.u32_val(b))))) : Nat}:
  +e1 = Equal.cong(Bool, Nat, t => Nat.add(SG.u32_val(a), C.shift(32n, WD.bo(t, one))), U32.is_lt(a, b), Nat.is_lt(SG.u32_val(a), SG.u32_val(b)), lt_nat(a, b))
  +e2 = Equal.cong(Nat, Nat, t => Nat.add(SG.u32_val(a), C.shift(32n, t)), WD.bo(Nat.is_lt(SG.u32_val(a), SG.u32_val(b)), one), SF.bn(Nat.is_lt(SG.u32_val(a), SG.u32_val(b))), bo_bn(one, h1, Nat.is_lt(SG.u32_val(a), SG.u32_val(b))))
  Equal.trans(Nat, Nat.add(SG.u32_val(U32.sub(a, b)), SG.u32_val(b)), Nat.add(SG.u32_val(a), C.shift(32n, WD.bo(U32.is_lt(a, b), one))), Nat.add(SG.u32_val(a), C.shift(32n, SF.bn(Nat.is_lt(SG.u32_val(a), SG.u32_val(b))))), WA.sub_cons(one, h1, a, b), Equal.trans(Nat, Nat.add(SG.u32_val(a), C.shift(32n, WD.bo(U32.is_lt(a, b), one))), Nat.add(SG.u32_val(a), C.shift(32n, WD.bo(Nat.is_lt(SG.u32_val(a), SG.u32_val(b)), one))), Nat.add(SG.u32_val(a), C.shift(32n, SF.bn(Nat.is_lt(SG.u32_val(a), SG.u32_val(b))))), e1, e2))

def wrapping_sub(+a: U32, +b: U32) -> SF.WrappingSub.value(~U32, ~SG.u32_val, ~F.u32_wrapping_sub, 32n, a, b):
  wsub_g(1n, {==}, a, b)

def overflowing_sub_value(+a: U32, +b: U32) -> SF.OverflowingSub.value(~U32, ~SG.u32_val, ~F.u32_overflowing_sub, 32n, a, b):
  wsub_g(1n, {==}, a, b)

# ---- div, rem ----

def cdiv(+a: U32, +b: U32, +z: Bool, +hz: {U32.is_zero(b) == z : Bool}, +ez: {Nat.is_eq(SG.u32_val(b), 0n) == z : Bool}) -> {SF.mval(~U32, ~SG.u32_val, F.opt(U32, z, U32.div(a, b))) == SF.keep(Bool.not(Nat.is_eq(SG.u32_val(b), 0n)), Nat.div(SG.u32_val(a), SG.u32_val(b))) : Maybe<&2, Nat>}:
  match z:
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(SG.u32_val(b), 0n), False{}, ez) : {SF.mval(~U32, ~SG.u32_val, F.opt(U32, False{}, U32.div(a, b))) == SF.keep(Bool.not(_), Nat.div(SG.u32_val(a), SG.u32_val(b))) : Maybe<&2, Nat>}
      G.some_of(~U32, ~SG.u32_val, False{}, {==}, U32.div(a, b), Nat.div(SG.u32_val(a), SG.u32_val(b)), UD.div_nat(a, b, hz))
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(SG.u32_val(b), 0n), True{}, ez) : {SF.mval(~U32, ~SG.u32_val, F.opt(U32, True{}, U32.div(a, b))) == SF.keep(Bool.not(_), Nat.div(SG.u32_val(a), SG.u32_val(b))) : Maybe<&2, Nat>}
      {==}

def checked_div(+a: U32, +b: U32) -> SF.CheckedDiv.value(~U32, ~SG.u32_val, ~F.u32_checked_div, a, b):
  cdiv(a, b, U32.is_zero(b), {==}, Equal.sym(Bool, U32.is_zero(b), Nat.is_eq(SG.u32_val(b), 0n), LW.zero_nat(b)))

def crem(+a: U32, +b: U32, +z: Bool, +hz: {U32.is_zero(b) == z : Bool}, +ez: {Nat.is_eq(SG.u32_val(b), 0n) == z : Bool}) -> {SF.mval(~U32, ~SG.u32_val, F.opt(U32, z, U32.mod(a, b))) == SF.keep(Bool.not(Nat.is_eq(SG.u32_val(b), 0n)), Nat.mod(SG.u32_val(a), SG.u32_val(b))) : Maybe<&2, Nat>}:
  match z:
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(SG.u32_val(b), 0n), False{}, ez) : {SF.mval(~U32, ~SG.u32_val, F.opt(U32, False{}, U32.mod(a, b))) == SF.keep(Bool.not(_), Nat.mod(SG.u32_val(a), SG.u32_val(b))) : Maybe<&2, Nat>}
      G.some_of(~U32, ~SG.u32_val, False{}, {==}, U32.mod(a, b), Nat.mod(SG.u32_val(a), SG.u32_val(b)), UD.mod_nat(a, b, hz))
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(SG.u32_val(b), 0n), True{}, ez) : {SF.mval(~U32, ~SG.u32_val, F.opt(U32, True{}, U32.mod(a, b))) == SF.keep(Bool.not(_), Nat.mod(SG.u32_val(a), SG.u32_val(b))) : Maybe<&2, Nat>}
      {==}

def checked_rem(+a: U32, +b: U32) -> SF.CheckedRem.value(~U32, ~SG.u32_val, ~F.u32_checked_rem, a, b):
  crem(a, b, U32.is_zero(b), {==}, Equal.sym(Bool, U32.is_zero(b), Nat.is_eq(SG.u32_val(b), 0n), LW.zero_nat(b)))

# ---- shifts: the amount masked to s mod 32 ----

def am(+s: U32) -> {U32.to_nat(U32.and(s, 31)) == Nat.mod(vs(s), 32n) : Nat}:
  Equal.trans(Nat, U32.to_nat(U32.and(s, 31)), C.low(5n, vs(s)), Nat.mod(vs(s), 32n), FB.andm(s, 5n, 31, {==}), G.low_mod(5n, vs(s), 31n, {==}))

def am_small(+s: U32, +h: {Nat.is_lt(vs(s), 32n) == True{} : Bool}) -> {U32.to_nat(U32.and(s, 31)) == vs(s) : Nat}:
  Equal.trans(Nat, U32.to_nat(U32.and(s, 31)), Nat.mod(vs(s), 32n), vs(s), am(s), R.mod_of(0n, 31n, vs(s), h))

def lt32(+s: U32) -> {U32.is_lt(s, 32) == Nat.is_lt(vs(s), 32n) : Bool}:
  U3.is_lt_nat(s, 32)

def wrapping_shl(+a: U32, +s: U32) -> SF.WrappingShl.value(~U32, ~SG.u32_val, ~F.u32_wrapping_shl, 32n, a, s):
  %Equal.sym(Nat, U32.to_nat(U32.and(s, 31)), Nat.mod(vs(s), 32n), am(s)) : {SG.u32_val(U32.mul(a, X.pow2(_))) == C.low(32n, C.shift(Nat.mod(vs(s), 32n), SG.u32_val(a))) : Nat}
  SH.mul_p2(a, Nat.mod(vs(s), 32n), R.dm_lt(31n, vs(s)))

def wrapping_shr(+a: U32, +s: U32) -> SF.WrappingShr.value(~U32, ~SG.u32_val, ~F.u32_wrapping_shr, 32n, a, s):
  %Equal.sym(Nat, U32.to_nat(U32.and(s, 31)), Nat.mod(vs(s), 32n), am(s)) : {SG.u32_val(U32.shrn(a, _)) == C.high(Nat.mod(vs(s), 32n), SG.u32_val(a)) : Nat}
  SHN.shrn_high(a, Nat.mod(vs(s), 32n))

def overflowing_shl_value(+a: U32, +s: U32) -> SF.OverflowingShl.value(~U32, ~SG.u32_val, ~F.u32_overflowing_shl, 32n, a, s):
  wrapping_shl(a, s)

def overflowing_shr_value(+a: U32, +s: U32) -> SF.OverflowingShr.value(~U32, ~SG.u32_val, ~F.u32_overflowing_shr, 32n, a, s):
  wrapping_shr(a, s)

def overflowing_shl_flag(+a: U32, +s: U32) -> SF.OverflowingShl.flag(~U32, ~F.u32_overflowing_shl, a, s, 32n):
  G.bnot_eq(U32.is_lt(s, 32), Nat.is_lt(vs(s), 32n), lt32(s))

def overflowing_shr_flag(+a: U32, +s: U32) -> SF.OverflowingShr.flag(~U32, ~F.u32_overflowing_shr, a, s, 32n):
  G.bnot_eq(U32.is_lt(s, 32), Nat.is_lt(vs(s), 32n), lt32(s))

def cshl(+a: U32, +s: U32, +ok: Bool, +hok: {Nat.is_lt(vs(s), 32n) == ok : Bool}) -> {SF.mval(~U32, ~SG.u32_val, F.opt(U32, Bool.not(U32.is_lt(s, 32)), U32.mul(a, X.pow2(U32.to_nat(U32.and(s, 31)))))) == SF.keep(ok, C.low(32n, C.shift(vs(s), SG.u32_val(a)))) : Maybe<&2, Nat>}:
  match ok:
    case True{}:
      +hb = Equal.trans(Bool, U32.is_lt(s, 32), Nat.is_lt(vs(s), 32n), True{}, lt32(s), hok)
      +ev = Equal.trans(Nat, SG.u32_val(U32.mul(a, X.pow2(U32.to_nat(U32.and(s, 31))))), SG.u32_val(U32.mul(a, X.pow2(vs(s)))), C.low(32n, C.shift(vs(s), SG.u32_val(a))), Equal.cong(Nat, Nat, t => SG.u32_val(U32.mul(a, X.pow2(t))), U32.to_nat(U32.and(s, 31)), vs(s), am_small(s, hok)), SH.mul_p2(a, vs(s), hok))
      G.some_of(~U32, ~SG.u32_val, Bool.not(U32.is_lt(s, 32)), G.bnot_eq(U32.is_lt(s, 32), True{}, hb), U32.mul(a, X.pow2(U32.to_nat(U32.and(s, 31)))), C.low(32n, C.shift(vs(s), SG.u32_val(a))), ev)
    case False{}:
      +hb = Equal.trans(Bool, U32.is_lt(s, 32), Nat.is_lt(vs(s), 32n), False{}, lt32(s), hok)
      G.none_of(~U32, ~SG.u32_val, Bool.not(U32.is_lt(s, 32)), G.bnot_eq(U32.is_lt(s, 32), False{}, hb), U32.mul(a, X.pow2(U32.to_nat(U32.and(s, 31)))))

def checked_shl(+a: U32, +s: U32) -> SF.CheckedShl.value(~U32, ~SG.u32_val, ~F.u32_checked_shl, 32n, a, s):
  cshl(a, s, Nat.is_lt(vs(s), 32n), {==})

def cshr(+a: U32, +s: U32, +ok: Bool, +hok: {Nat.is_lt(vs(s), 32n) == ok : Bool}) -> {SF.mval(~U32, ~SG.u32_val, F.opt(U32, Bool.not(U32.is_lt(s, 32)), U32.shrn(a, U32.to_nat(U32.and(s, 31))))) == SF.keep(ok, C.high(vs(s), SG.u32_val(a))) : Maybe<&2, Nat>}:
  match ok:
    case True{}:
      +hb = Equal.trans(Bool, U32.is_lt(s, 32), Nat.is_lt(vs(s), 32n), True{}, lt32(s), hok)
      +ev = Equal.trans(Nat, SG.u32_val(U32.shrn(a, U32.to_nat(U32.and(s, 31)))), SG.u32_val(U32.shrn(a, vs(s))), C.high(vs(s), SG.u32_val(a)), Equal.cong(Nat, Nat, t => SG.u32_val(U32.shrn(a, t)), U32.to_nat(U32.and(s, 31)), vs(s), am_small(s, hok)), SHN.shrn_high(a, vs(s)))
      G.some_of(~U32, ~SG.u32_val, Bool.not(U32.is_lt(s, 32)), G.bnot_eq(U32.is_lt(s, 32), True{}, hb), U32.shrn(a, U32.to_nat(U32.and(s, 31))), C.high(vs(s), SG.u32_val(a)), ev)
    case False{}:
      +hb = Equal.trans(Bool, U32.is_lt(s, 32), Nat.is_lt(vs(s), 32n), False{}, lt32(s), hok)
      G.none_of(~U32, ~SG.u32_val, Bool.not(U32.is_lt(s, 32)), G.bnot_eq(U32.is_lt(s, 32), False{}, hb), U32.shrn(a, U32.to_nat(U32.and(s, 31))))

def checked_shr(+a: U32, +s: U32) -> SF.CheckedShr.value(~U32, ~SG.u32_val, ~F.u32_checked_shr, 32n, a, s):
  cshr(a, s, Nat.is_lt(vs(s), 32n), {==})

# ---- pow through the generic checked pow ----

def pw(+a: U32, +e: U32) -> Nat:
  Nat.pow(SG.u32_val(a), vs(e))

def gpow(+a: U32, +e: U32) -> Result<&2, &2, NM.NumError, U32>:
  GN.pow(~U32, ~I.u32_op, ~I.u32_is, a, vs(e))

def cpow(+a: U32, +e: U32, +ok: Bool, +hok: {C.fits(32n, pw(a, e)) == ok : Bool}) -> {SF.mval(~U32, ~SG.u32_val, F.res_opt(U32, gpow(a, e))) == SF.keep(ok, pw(a, e)) : Maybe<&2, Nat>}:
  match ok:
    case True{}:
      %Equal.sym(Result<&2, &2, NM.NumError, U32>, gpow(a, e), SG.checked(~U32, ~SG.u32_of, 32n, pw(a, e)), UI.pow_checked(a, vs(e))) : {SF.mval(~U32, ~SG.u32_val, F.res_opt(U32, _)) == Some{pw(a, e)} : Maybe<&2, Nat>}
      %Equal.sym(Bool, C.fits(32n, pw(a, e)), True{}, hok) : {SF.mval(~U32, ~SG.u32_val, F.res_opt(U32, SG.checked_pick(~U32, ~SG.u32_of, pw(a, e), _))) == Some{pw(a, e)} : Maybe<&2, Nat>}
      Equal.cong(Nat, Maybe<&2, Nat>, t => Some{t}, SG.u32_val(SG.u32_of(pw(a, e))), pw(a, e), LW.vo(pw(a, e), hok))
    case False{}:
      %Equal.sym(Result<&2, &2, NM.NumError, U32>, gpow(a, e), SG.checked(~U32, ~SG.u32_of, 32n, pw(a, e)), UI.pow_checked(a, vs(e))) : {SF.mval(~U32, ~SG.u32_val, F.res_opt(U32, _)) == None{} : Maybe<&2, Nat>}
      %Equal.sym(Bool, C.fits(32n, pw(a, e)), False{}, hok) : {SF.mval(~U32, ~SG.u32_val, F.res_opt(U32, SG.checked_pick(~U32, ~SG.u32_of, pw(a, e), _))) == None{} : Maybe<&2, Nat>}
      {==}

def checked_pow(+a: U32, +e: U32) -> SF.CheckedPow.value(~U32, ~SG.u32_val, ~F.u32_checked_pow, 32n, a, e):
  cpow(a, e, C.fits(32n, pw(a, e)), {==})

def spow(+top: U32, +ht: {Bool.and(C.fits(32n, SG.u32_val(top)), Bool.not(C.fits(32n, 1n+SG.u32_val(top)))) == True{} : Bool}, +a: U32, +e: U32, +ok: Bool, +hok: {C.fits(32n, pw(a, e)) == ok : Bool}) -> {SF.saturated(32n, pw(a, e), SG.u32_val(F.or_top(U32, top, F.res_opt(U32, gpow(a, e)))), ok) == True{} : Bool}:
  match ok:
    case True{}:
      %Equal.sym(Result<&2, &2, NM.NumError, U32>, gpow(a, e), SG.checked(~U32, ~SG.u32_of, 32n, pw(a, e)), UI.pow_checked(a, vs(e))) : {SF.saturated(32n, pw(a, e), SG.u32_val(F.or_top(U32, top, F.res_opt(U32, _))), True{}) == True{} : Bool}
      %Equal.sym(Bool, C.fits(32n, pw(a, e)), True{}, hok) : {SF.saturated(32n, pw(a, e), SG.u32_val(F.or_top(U32, top, F.res_opt(U32, SG.checked_pick(~U32, ~SG.u32_of, pw(a, e), _)))), True{}) == True{} : Bool}
      %Equal.sym(Nat, SG.u32_val(SG.u32_of(pw(a, e))), pw(a, e), LW.vo(pw(a, e), hok)) : {Nat.is_eq(_, pw(a, e)) == True{} : Bool}
      N.is_eq_refl(pw(a, e))
    case False{}:
      %Equal.sym(Result<&2, &2, NM.NumError, U32>, gpow(a, e), SG.checked(~U32, ~SG.u32_of, 32n, pw(a, e)), UI.pow_checked(a, vs(e))) : {SF.saturated(32n, pw(a, e), SG.u32_val(F.or_top(U32, top, F.res_opt(U32, _))), False{}) == True{} : Bool}
      %Equal.sym(Bool, C.fits(32n, pw(a, e)), False{}, hok) : {SF.saturated(32n, pw(a, e), SG.u32_val(F.or_top(U32, top, F.res_opt(U32, SG.checked_pick(~U32, ~SG.u32_of, pw(a, e), _)))), False{}) == True{} : Bool}
      ht

def saturating_pow(+a: U32, +e: U32) -> SF.SaturatingPow.value(~U32, ~SG.u32_val, ~F.u32_saturating_pow, 32n, a, e):
  spow(F.u32_max(), top(1n, {==}), a, e, C.fits(32n, pw(a, e)), {==})

def overflowing_pow_flag(+a: U32, +e: U32) -> SF.OverflowingPow.flag(~U32, ~SG.u32_val, ~F.u32_overflowing_pow, 32n, a, e):
  G.bad_res(~U32, ~SG.u32_of, 32n, pw(a, e), gpow(a, e), UI.pow_checked(a, vs(e)), C.fits(32n, pw(a, e)), {==})

# ---- wrapping pow: right-to-left binary exponentiation mod 2^32 ----

def lt_m(+mp: Nat, +hp: {C.pow2(32n) == 1n+mp : Nat}, +x: U32) -> {Nat.is_lt(SG.u32_val(x), 1n+mp) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(SG.u32_val(x), 1n+mp), Nat.is_lt(SG.u32_val(x), C.pow2(32n)), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(SG.u32_val(x), t), 1n+mp, C.pow2(32n), Equal.sym(Nat, C.pow2(32n), 1n+mp, hp)), WW.lt_of_fits(32n, SG.u32_val(x), LW.vb(x)))

def mul_m(+mp: Nat, +hp: {C.pow2(32n) == 1n+mp : Nat}, +x: U32, +y: U32) -> {SG.u32_val(U32.mul(x, y)) == Nat.mod(Nat.mul(SG.u32_val(x), SG.u32_val(y)), 1n+mp) : Nat}:
  Equal.trans(Nat, SG.u32_val(U32.mul(x, y)), C.low(32n, Nat.mul(SG.u32_val(x), SG.u32_val(y))), Nat.mod(Nat.mul(SG.u32_val(x), SG.u32_val(y)), 1n+mp), mul_low(x, y), G.low_mod(32n, Nat.mul(SG.u32_val(x), SG.u32_val(y)), mp, hp))

def wp_base(+mp: Nat, +hp: {C.pow2(32n) == 1n+mp : Nat}, +e: U32, +b: U32, +acc: U32, +h0: {vs(e) == 0n : Nat}) -> {SG.u32_val(acc) == Nat.mod(Nat.mul(SG.u32_val(acc), Nat.pow(SG.u32_val(b), vs(e))), 1n+mp) : Nat}:
  %Equal.sym(Nat, vs(e), 0n, h0) : {SG.u32_val(acc) == Nat.mod(Nat.mul(SG.u32_val(acc), Nat.pow(SG.u32_val(b), _)), 1n+mp) : Nat}
  %Equal.sym(Nat, Nat.mul(SG.u32_val(acc), 1n), SG.u32_val(acc), NA.mul_one(SG.u32_val(acc))) : {SG.u32_val(acc) == Nat.mod(_, 1n+mp) : Nat}
  Equal.sym(Nat, Nat.mod(SG.u32_val(acc), 1n+mp), SG.u32_val(acc), R.mod_of(0n, mp, SG.u32_val(acc), lt_m(mp, hp, acc)))

def wp_odd(+mp: Nat, +hp: {C.pow2(32n) == 1n+mp : Nat}, +e: U32, +b: U32, +acc: U32, +r: Nat, +hodd: {I.u32_odd(e) == Nat.is_eq(r, 1n) : Bool}, +hr: {Nat.is_lt(r, 2n) == True{} : Bool}) -> {SG.u32_val(F.pick(U32, I.u32_odd(e), U32.mul(acc, b), acc)) == M.pow_mod_odd(1n+mp, r, SG.u32_val(b), SG.u32_val(acc)) : Nat}:
  match r:
    case 0n:
      %Equal.sym(Bool, I.u32_odd(e), False{}, hodd) : {SG.u32_val(F.pick(U32, _, U32.mul(acc, b), acc)) == SG.u32_val(acc) : Nat}
      {==}
    case 1n:
      %Equal.sym(Bool, I.u32_odd(e), True{}, hodd) : {SG.u32_val(F.pick(U32, _, U32.mul(acc, b), acc)) == Nat.mod(Nat.mul(SG.u32_val(acc), SG.u32_val(b)), 1n+mp) : Nat}
      mul_m(mp, hp, acc, b)
    case 2n+ +q:
      Empty.absurd({SG.u32_val(F.pick(U32, I.u32_odd(e), U32.mul(acc, b), acc)) == M.pow_mod_odd(1n+mp, 2n+q, SG.u32_val(b), SG.u32_val(acc)) : Nat}, N.lt_zero_absurd(q, hr))

def half_e(+e: U32) -> {vs(U32.shr(e)) == Nat.div(vs(e), 2n) : Nat}:
  Equal.trans(Nat, vs(U32.shr(e)), C.half(vs(e)), Nat.div(vs(e), 2n), SHN.shrn_high(e, 1n), WA.half_div(vs(e)))

def wp_go(fuel: Nat, +mp: Nat, +hp: {C.pow2(32n) == 1n+mp : Nat}, +e: U32, +b: U32, +acc: U32, +z: Bool, +hz: {U32.is_zero(e) == z : Bool}, +he: {Nat.is_lt(vs(e), C.pow2(fuel)) == True{} : Bool}) -> {SG.u32_val(F.u32_wpow(fuel, e, b, acc, z)) == Nat.mod(Nat.mul(SG.u32_val(acc), Nat.pow(SG.u32_val(b), vs(e))), 1n+mp) : Nat}:
  match fuel z:
    case 0n _:
      wp_base(mp, hp, e, b, acc, G.lt1(vs(e), he))
    case 1n+f True{}:
      wp_base(mp, hp, e, b, acc, N.eq_from_is_eq(vs(e), 0n, Equal.trans(Bool, Nat.is_eq(vs(e), 0n), U32.is_zero(e), True{}, Equal.sym(Bool, U32.is_zero(e), Nat.is_eq(vs(e), 0n), LW.zero_nat(e)), hz)))
    case 1n+ +f False{}:
      +ve = vs(e)
      +e2 = Nat.div(ve, 2n)
      +bit = Nat.mod(ve, 2n)
      +m = {1n+mp : Nat}
      +acc2 = F.pick(U32, I.u32_odd(e), U32.mul(acc, b), acc)
      +he2 = Equal.trans(Bool, Nat.is_lt(vs(U32.shr(e)), C.pow2(f)), Nat.is_lt(C.half(ve), C.pow2(f)), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(t, C.pow2(f)), vs(U32.shr(e)), C.half(ve), SHN.shrn_high(e, 1n)), Equal.trans(Bool, Nat.is_lt(C.half(ve), C.pow2(f)), Nat.is_lt(ve, Nat.double(C.pow2(f))), True{}, WW.lt_half(ve, C.pow2(f)), he))
      +ih = wp_go(f, mp, hp, U32.shr(e), U32.mul(b, b), acc2, U32.is_zero(U32.shr(e)), {==}, he2)
      +ea = wp_odd(mp, hp, e, b, acc, bit, LW.tests_odd(e), B.half_rem(ve))
      +eb = mul_m(mp, hp, b, b)
      +x1 = Equal.cong(Nat, Nat, t => Nat.mod(Nat.mul(t, Nat.pow(SG.u32_val(U32.mul(b, b)), vs(U32.shr(e)))), m), SG.u32_val(acc2), M.pow_mod_odd(m, bit, SG.u32_val(b), SG.u32_val(acc)), ea)
      +x2 = Equal.cong(Nat, Nat, t => Nat.mod(Nat.mul(M.pow_mod_odd(m, bit, SG.u32_val(b), SG.u32_val(acc)), Nat.pow(t, vs(U32.shr(e)))), m), SG.u32_val(U32.mul(b, b)), Nat.mod(Nat.mul(SG.u32_val(b), SG.u32_val(b)), m), eb)
      +x3 = Equal.cong(Nat, Nat, t => Nat.mod(Nat.mul(M.pow_mod_odd(m, bit, SG.u32_val(b), SG.u32_val(acc)), Nat.pow(Nat.mod(Nat.mul(SG.u32_val(b), SG.u32_val(b)), m), t)), m), vs(U32.shr(e)), e2, half_e(e))
      +x4 = MP.pm_bit(mp, e2, bit, B.half_rem(ve), SG.u32_val(b), SG.u32_val(acc))
      +x5 = Equal.cong(Nat, Nat, t => Nat.mod(Nat.mul(SG.u32_val(acc), Nat.pow(SG.u32_val(b), t)), m), Nat.add(Nat.double(e2), bit), ve, Equal.sym(Nat, ve, Nat.add(Nat.double(e2), bit), B.half_eq(ve)))
      +L0 = Nat.mod(Nat.mul(SG.u32_val(acc2), Nat.pow(SG.u32_val(U32.mul(b, b)), vs(U32.shr(e)))), m)
      +L1 = Nat.mod(Nat.mul(M.pow_mod_odd(m, bit, SG.u32_val(b), SG.u32_val(acc)), Nat.pow(SG.u32_val(U32.mul(b, b)), vs(U32.shr(e)))), m)
      +L2 = Nat.mod(Nat.mul(M.pow_mod_odd(m, bit, SG.u32_val(b), SG.u32_val(acc)), Nat.pow(Nat.mod(Nat.mul(SG.u32_val(b), SG.u32_val(b)), m), vs(U32.shr(e)))), m)
      +L3 = Nat.mod(Nat.mul(M.pow_mod_odd(m, bit, SG.u32_val(b), SG.u32_val(acc)), Nat.pow(Nat.mod(Nat.mul(SG.u32_val(b), SG.u32_val(b)), m), e2)), m)
      +L4 = Nat.mod(Nat.mul(SG.u32_val(acc), Nat.pow(SG.u32_val(b), Nat.add(Nat.double(e2), bit))), m)
      +L5 = Nat.mod(Nat.mul(SG.u32_val(acc), Nat.pow(SG.u32_val(b), ve)), m)
      Equal.trans(Nat, SG.u32_val(F.u32_wpow(f, U32.shr(e), U32.mul(b, b), acc2, U32.is_zero(U32.shr(e)))), L0, L5, ih, Equal.trans(Nat, L0, L1, L5, x1, Equal.trans(Nat, L1, L2, L5, x2, Equal.trans(Nat, L2, L3, L5, x3, Equal.trans(Nat, L3, L4, L5, x4, x5)))))

def wp_top(+mp: Nat, +hp: {C.pow2(32n) == 1n+mp : Nat}, +a: U32, +e: U32) -> {SG.u32_val(F.u32_wrapping_pow(a, e)) == C.low(32n, pw(a, e)) : Nat}:
  +ih = wp_go(32n, mp, hp, e, a, 1, U32.is_zero(e), {==}, WW.lt_of_fits(32n, vs(e), LW.vb(e)))
  +e1 = Equal.cong(Nat, Nat, t => Nat.mod(t, 1n+mp), Nat.mul(1n, pw(a, e)), pw(a, e), AR.one_mul(pw(a, e)))
  Equal.trans(Nat, SG.u32_val(F.u32_wrapping_pow(a, e)), Nat.mod(Nat.mul(1n, pw(a, e)), 1n+mp), C.low(32n, pw(a, e)), ih, Equal.trans(Nat, Nat.mod(Nat.mul(1n, pw(a, e)), 1n+mp), Nat.mod(pw(a, e), 1n+mp), C.low(32n, pw(a, e)), e1, Equal.sym(Nat, C.low(32n, pw(a, e)), Nat.mod(pw(a, e), 1n+mp), G.low_mod(32n, pw(a, e), mp, hp))))

def wrapping_pow(+a: U32, +e: U32) -> SF.WrappingPow.value(~U32, ~SG.u32_val, ~F.u32_wrapping_pow, 32n, a, e):
  wp_top(Nat.sub(C.pow2(32n), 1n), SH.pow2_eq(32n), a, e)

def overflowing_pow_value(+a: U32, +e: U32) -> SF.OverflowingPow.value(~U32, ~SG.u32_val, ~F.u32_overflowing_pow, 32n, a, e):
  wrapping_pow(a, e)
