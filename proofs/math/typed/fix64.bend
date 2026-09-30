import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/generic.bend as SG
import ../../../spec/math/fixed.bend as SF
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../../src/math/fixed.bend as F
import ../../../src/math/generic.bend as GN
import ../../../src/math/instances.bend as I
import ../../../src/math/num.bend as NM
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../natural/modpow.bend as MP
import ../natural/bits.bend as B
import ./u32laws.bend as LW
import ./shrn.bend as SHN
import ../../lib/u32.bend as U3
import ../../lib/arith.bend as AR
import ../natural/arith.bend as R
import ./width.bend as WW
import ./w64add.bend as WA
import ./w64sh.bend as SH
import ./w64dmtop.bend as DT
import ./w64dmrem.bend as DR
import ./u64laws.bend as LV
import ./u64int.bend as UI
import ./u64mont.bend as MT
import ./f64bits.bend as FB
import ./fixgen.bend as G
import ../../lib/word.bend as WD
import ../../lib/logic.bend as L

# The U64 clauses of spec/math/fixed.bend (Rust's u64 checked_*, wrapping_*,
# saturating_*, overflowing_* families) from the proved two-limb clauses of
# spec/math/w64.bend (proofs/math/typed/w64add.bend, w64sh.bend,
# w64dmtop.bend, w64dmrem.bend) and the generic pow of u64int.bend, as
# HACL*'s Hacl.Spec.Bignum proves each word operation through its value.

def vs(+s: U32) -> Nat:
  U32.to_nat(s)

# ---- the largest value ----

def zero_add(+x: Nat) -> {Nat.add(0n, x) == x : Nat}:
  Equal.trans(Nat, Nat.add(0n, x), Nat.add(x, 0n), x, N.add_comm(0n, x), N.add_zero(x))

# The largest value 2^64 - 1 is built with its limbs abstract (w, the
# all-ones U32) and 1 kept as one: the checker must never unfold 2^64, and
# closed 64-bit values are only ever compared as U64s.

def top1w(+one: Nat, +h1: {one == 1n : Nat}, +w: U32, +pw: {w == U32{WD.mask(32n, 32n)} : U32}) -> {1n+SG.u64_val(WU.U64{w, w}) == C.shift(64n, one) : Nat}:
  MT.ones_v(one, h1, w, pw)

def top1(+one: Nat, +h1: {one == 1n : Nat}) -> {1n+SG.u64_val(F.u64_max()) == C.shift(64n, one) : Nat}:
  L.subst(WU.U64, t => {1n+SG.u64_val(t) == C.shift(64n, one) : Nat}, WU.U64{4294967295, 4294967295}, F.u64_max(), {==}, top1w(one, h1, 4294967295, {==}))

def topw(+one: Nat, +h1: {one == 1n : Nat}, +w: U32, +pw: {w == U32{WD.mask(32n, 32n)} : U32}) -> {Bool.and(C.fits(64n, SG.u64_val(WU.U64{w, w})), Bool.not(C.fits(64n, 1n+SG.u64_val(WU.U64{w, w})))) == True{} : Bool}:
  +m = {WU.U64{w, w} : WU.U64}
  +S = C.shift(64n, one)
  +e1 = Equal.cong(Nat, Bool, t => C.fits(64n, t), 1n+SG.u64_val(m), S, top1w(one, h1, w, pw))
  +e2 = Equal.cong(Nat, Bool, t => C.fits(64n, t), S, Nat.add(0n, S), Equal.sym(Nat, Nat.add(0n, S), S, zero_add(S)))
  G.top_ok(64n, SG.u64_val(m), LV.vb(m), Equal.trans(Bool, C.fits(64n, 1n+SG.u64_val(m)), C.fits(64n, S), False{}, e1, Equal.trans(Bool, C.fits(64n, S), C.fits(64n, Nat.add(0n, S)), False{}, e2, WW.unfit_one(64n, one, h1, 0n))))

def top(+one: Nat, +h1: {one == 1n : Nat}) -> {Bool.and(C.fits(64n, SG.u64_val(F.u64_max())), Bool.not(C.fits(64n, 1n+SG.u64_val(F.u64_max())))) == True{} : Bool}:
  L.subst(WU.U64, t => {Bool.and(C.fits(64n, SG.u64_val(t)), Bool.not(C.fits(64n, 1n+SG.u64_val(t)))) == True{} : Bool}, WU.U64{4294967295, 4294967295}, F.u64_max(), {==}, topw(one, h1, 4294967295, {==}))

# ---- add, mul ----

def checked_add(+a: WU.U64, +b: WU.U64) -> SF.CheckedAdd.value(~WU.U64, ~SG.u64_val, ~F.u64_checked_add, 64n, a, b):
  G.chk_fit(~WU.U64, ~SG.u64_val, 64n, Nat.add(SG.u64_val(a), SG.u64_val(b)), X.add(a, b), X.add_over(a, b), WA.add_over_value(a, b), WA.add_value(a, b), C.fits(64n, Nat.add(SG.u64_val(a), SG.u64_val(b))), {==})

def wrapping_add(+a: WU.U64, +b: WU.U64) -> SF.WrappingAdd.value(~WU.U64, ~SG.u64_val, ~F.u64_wrapping_add, 64n, a, b):
  WA.add_value(a, b)

def saturating_add(+a: WU.U64, +b: WU.U64) -> SF.SaturatingAdd.value(~WU.U64, ~SG.u64_val, ~F.u64_saturating_add, 64n, a, b):
  G.sat_fit(~WU.U64, ~SG.u64_val, 64n, Nat.add(SG.u64_val(a), SG.u64_val(b)), X.add(a, b), F.u64_max(), X.add_over(a, b), WA.add_over_value(a, b), WA.add_value(a, b), top(1n, {==}), C.fits(64n, Nat.add(SG.u64_val(a), SG.u64_val(b))), {==})

def overflowing_add_value(+a: WU.U64, +b: WU.U64) -> SF.OverflowingAdd.value(~WU.U64, ~SG.u64_val, ~F.u64_overflowing_add, 64n, a, b):
  WA.add_value(a, b)

def overflowing_add_flag(+a: WU.U64, +b: WU.U64) -> SF.OverflowingAdd.flag(~WU.U64, ~SG.u64_val, ~F.u64_overflowing_add, 64n, a, b):
  WA.add_over_value(a, b)

def checked_mul(+a: WU.U64, +b: WU.U64) -> SF.CheckedMul.value(~WU.U64, ~SG.u64_val, ~F.u64_checked_mul, 64n, a, b):
  G.chk_fit(~WU.U64, ~SG.u64_val, 64n, Nat.mul(SG.u64_val(a), SG.u64_val(b)), X.mul(a, b), X.mul_over(a, b), WA.mul_over_value(a, b), WA.mul_value(a, b), C.fits(64n, Nat.mul(SG.u64_val(a), SG.u64_val(b))), {==})

def wrapping_mul(+a: WU.U64, +b: WU.U64) -> SF.WrappingMul.value(~WU.U64, ~SG.u64_val, ~F.u64_wrapping_mul, 64n, a, b):
  WA.mul_value(a, b)

def saturating_mul(+a: WU.U64, +b: WU.U64) -> SF.SaturatingMul.value(~WU.U64, ~SG.u64_val, ~F.u64_saturating_mul, 64n, a, b):
  G.sat_fit(~WU.U64, ~SG.u64_val, 64n, Nat.mul(SG.u64_val(a), SG.u64_val(b)), X.mul(a, b), F.u64_max(), X.mul_over(a, b), WA.mul_over_value(a, b), WA.mul_value(a, b), top(1n, {==}), C.fits(64n, Nat.mul(SG.u64_val(a), SG.u64_val(b))), {==})

def overflowing_mul_value(+a: WU.U64, +b: WU.U64) -> SF.OverflowingMul.value(~WU.U64, ~SG.u64_val, ~F.u64_overflowing_mul, 64n, a, b):
  WA.mul_value(a, b)

def overflowing_mul_flag(+a: WU.U64, +b: WU.U64) -> SF.OverflowingMul.flag(~WU.U64, ~SG.u64_val, ~F.u64_overflowing_mul, 64n, a, b):
  WA.mul_over_value(a, b)

# ---- sub ----

def csub(+a: WU.U64, +b: WU.U64, +ok: Bool, +hok: {Nat.is_le(SG.u64_val(b), SG.u64_val(a)) == ok : Bool}) -> {SF.mval(~WU.U64, ~SG.u64_val, F.opt(WU.U64, X.lt(a, b), X.sub(a, b))) == SF.keep(ok, Nat.sub(SG.u64_val(a), SG.u64_val(b))) : Maybe<&2, Nat>}:
  match ok:
    case True{}:
      G.some_of(~WU.U64, ~SG.u64_val, X.lt(a, b), Equal.trans(Bool, X.lt(a, b), Nat.is_lt(SG.u64_val(a), SG.u64_val(b)), False{}, WA.lt_value(a, b), N.le_not_lt(SG.u64_val(a), SG.u64_val(b), hok)), X.sub(a, b), Nat.sub(SG.u64_val(a), SG.u64_val(b)), WA.sub_value(a, b, hok))
    case False{}:
      G.none_of(~WU.U64, ~SG.u64_val, X.lt(a, b), Equal.trans(Bool, X.lt(a, b), Nat.is_lt(SG.u64_val(a), SG.u64_val(b)), True{}, WA.lt_value(a, b), N.not_le_lt(SG.u64_val(b), SG.u64_val(a), hok)), X.sub(a, b))

def checked_sub(+a: WU.U64, +b: WU.U64) -> SF.CheckedSub.value(~WU.U64, ~SG.u64_val, ~F.u64_checked_sub, a, b):
  csub(a, b, Nat.is_le(SG.u64_val(b), SG.u64_val(a)), {==})

def sub_big(+n: Nat, +d: Nat, +h: {Nat.is_le(n, d) == True{} : Bool}) -> {Nat.sub(n, d) == 0n : Nat}:
  match n d:
    case 0n _:
      R.zsub(d)
    case 1n+np 0n:
      Empty.absurd({Nat.sub(1n+np, 0n) == 0n : Nat}, L.false_true(h))
    case 1n+ +np 1n+ +dp:
      sub_big(np, dp, h)

def ssub(+a: WU.U64, +b: WU.U64, +c: Bool, +hn: {Nat.is_lt(SG.u64_val(a), SG.u64_val(b)) == c : Bool}) -> {SG.u64_val(F.pick(WU.U64, c, F.u64_zero(), X.sub(a, b))) == Nat.sub(SG.u64_val(a), SG.u64_val(b)) : Nat}:
  match c:
    case True{}:
      Equal.sym(Nat, Nat.sub(SG.u64_val(a), SG.u64_val(b)), 0n, sub_big(SG.u64_val(a), SG.u64_val(b), N.lt_le(SG.u64_val(a), SG.u64_val(b), hn)))
    case False{}:
      WA.sub_value(a, b, N.not_lt_le(SG.u64_val(a), SG.u64_val(b), hn))

def saturating_sub(+a: WU.U64, +b: WU.U64) -> SF.SaturatingSub.value(~WU.U64, ~SG.u64_val, ~F.u64_saturating_sub, a, b):
  ssub(a, b, X.lt(a, b), Equal.sym(Bool, X.lt(a, b), Nat.is_lt(SG.u64_val(a), SG.u64_val(b)), WA.lt_value(a, b)))

def overflowing_sub_flag(+a: WU.U64, +b: WU.U64) -> SF.OverflowingSub.flag(~WU.U64, ~SG.u64_val, ~F.u64_overflowing_sub, a, b):
  WA.lt_value(a, b)

# ---- div, rem ----

def cdiv(+a: WU.U64, +b: WU.U64, +z: Bool, +hz: {X.is_zero(b) == z : Bool}) -> {SF.mval(~WU.U64, ~SG.u64_val, F.u64_cdiv(z, a, b)) == SF.keep(Bool.not(Nat.is_eq(SG.u64_val(b), 0n)), Nat.div(SG.u64_val(a), SG.u64_val(b))) : Maybe<&2, Nat>}:
  match z:
    case False{}:
      +ez = Equal.trans(Bool, Nat.is_eq(SG.u64_val(b), 0n), X.is_zero(b), z, Equal.sym(Bool, X.is_zero(b), Nat.is_eq(SG.u64_val(b), 0n), WA.is_zero_value(b)), hz)
      %Equal.sym(Bool, Nat.is_eq(SG.u64_val(b), 0n), False{}, ez) : {SF.mval(~WU.U64, ~SG.u64_val, F.u64_cdiv(False{}, a, b)) == SF.keep(Bool.not(_), Nat.div(SG.u64_val(a), SG.u64_val(b))) : Maybe<&2, Nat>}
      Equal.cong(Nat, Maybe<&2, Nat>, t => Some{t}, SG.u64_val(X.quot(a, b)), Nat.div(SG.u64_val(a), SG.u64_val(b)), DT.divmod_quot(a, b, hz))
    case True{}:
      +ez = Equal.trans(Bool, Nat.is_eq(SG.u64_val(b), 0n), X.is_zero(b), z, Equal.sym(Bool, X.is_zero(b), Nat.is_eq(SG.u64_val(b), 0n), WA.is_zero_value(b)), hz)
      %Equal.sym(Bool, Nat.is_eq(SG.u64_val(b), 0n), True{}, ez) : {SF.mval(~WU.U64, ~SG.u64_val, F.u64_cdiv(True{}, a, b)) == SF.keep(Bool.not(_), Nat.div(SG.u64_val(a), SG.u64_val(b))) : Maybe<&2, Nat>}
      {==}

def checked_div(+a: WU.U64, +b: WU.U64) -> SF.CheckedDiv.value(~WU.U64, ~SG.u64_val, ~F.u64_checked_div, a, b):
  cdiv(a, b, X.is_zero(b), {==})

def crem(+a: WU.U64, +b: WU.U64, +z: Bool, +hz: {X.is_zero(b) == z : Bool}) -> {SF.mval(~WU.U64, ~SG.u64_val, F.u64_crem(z, a, b)) == SF.keep(Bool.not(Nat.is_eq(SG.u64_val(b), 0n)), Nat.mod(SG.u64_val(a), SG.u64_val(b))) : Maybe<&2, Nat>}:
  match z:
    case False{}:
      +ez = Equal.trans(Bool, Nat.is_eq(SG.u64_val(b), 0n), X.is_zero(b), z, Equal.sym(Bool, X.is_zero(b), Nat.is_eq(SG.u64_val(b), 0n), WA.is_zero_value(b)), hz)
      %Equal.sym(Bool, Nat.is_eq(SG.u64_val(b), 0n), False{}, ez) : {SF.mval(~WU.U64, ~SG.u64_val, F.u64_crem(False{}, a, b)) == SF.keep(Bool.not(_), Nat.mod(SG.u64_val(a), SG.u64_val(b))) : Maybe<&2, Nat>}
      Equal.cong(Nat, Maybe<&2, Nat>, t => Some{t}, SG.u64_val(X.rem(a, b)), Nat.mod(SG.u64_val(a), SG.u64_val(b)), DR.divmod_rem(a, b, hz))
    case True{}:
      +ez = Equal.trans(Bool, Nat.is_eq(SG.u64_val(b), 0n), X.is_zero(b), z, Equal.sym(Bool, X.is_zero(b), Nat.is_eq(SG.u64_val(b), 0n), WA.is_zero_value(b)), hz)
      %Equal.sym(Bool, Nat.is_eq(SG.u64_val(b), 0n), True{}, ez) : {SF.mval(~WU.U64, ~SG.u64_val, F.u64_crem(True{}, a, b)) == SF.keep(Bool.not(_), Nat.mod(SG.u64_val(a), SG.u64_val(b))) : Maybe<&2, Nat>}
      {==}

def checked_rem(+a: WU.U64, +b: WU.U64) -> SF.CheckedRem.value(~WU.U64, ~SG.u64_val, ~F.u64_checked_rem, a, b):
  crem(a, b, X.is_zero(b), {==})

# ---- shifts: the amount masked to s mod 64 ----

def am(+s: U32) -> {U32.to_nat(U32.and(s, 63)) == Nat.mod(vs(s), 64n) : Nat}:
  Equal.trans(Nat, U32.to_nat(U32.and(s, 63)), C.low(6n, vs(s)), Nat.mod(vs(s), 64n), FB.andm(s, 6n, 63, {==}), G.low_mod(6n, vs(s), 63n, {==}))

def am_small(+s: U32, +h: {Nat.is_lt(vs(s), 64n) == True{} : Bool}) -> {U32.to_nat(U32.and(s, 63)) == vs(s) : Nat}:
  Equal.trans(Nat, U32.to_nat(U32.and(s, 63)), Nat.mod(vs(s), 64n), vs(s), am(s), R.mod_of(0n, 63n, vs(s), h))

def lt64(+s: U32) -> {U32.is_lt(s, 64) == Nat.is_lt(vs(s), 64n) : Bool}:
  U3.is_lt_nat(s, 64)

def wrapping_shl(+a: WU.U64, +s: U32) -> SF.WrappingShl.value(~WU.U64, ~SG.u64_val, ~F.u64_wrapping_shl, 64n, a, s):
  %Equal.sym(Nat, U32.to_nat(U32.and(s, 63)), Nat.mod(vs(s), 64n), am(s)) : {SG.u64_val(X.shl(a, _)) == C.low(64n, C.shift(Nat.mod(vs(s), 64n), SG.u64_val(a))) : Nat}
  SH.shl_value(a, Nat.mod(vs(s), 64n), R.dm_lt(63n, vs(s)))

def wrapping_shr(+a: WU.U64, +s: U32) -> SF.WrappingShr.value(~WU.U64, ~SG.u64_val, ~F.u64_wrapping_shr, 64n, a, s):
  %Equal.sym(Nat, U32.to_nat(U32.and(s, 63)), Nat.mod(vs(s), 64n), am(s)) : {SG.u64_val(X.shr(a, _)) == C.high(Nat.mod(vs(s), 64n), SG.u64_val(a)) : Nat}
  SH.shr_value(a, Nat.mod(vs(s), 64n))

def overflowing_shl_value(+a: WU.U64, +s: U32) -> SF.OverflowingShl.value(~WU.U64, ~SG.u64_val, ~F.u64_overflowing_shl, 64n, a, s):
  wrapping_shl(a, s)

def overflowing_shr_value(+a: WU.U64, +s: U32) -> SF.OverflowingShr.value(~WU.U64, ~SG.u64_val, ~F.u64_overflowing_shr, 64n, a, s):
  wrapping_shr(a, s)

def overflowing_shl_flag(+a: WU.U64, +s: U32) -> SF.OverflowingShl.flag(~WU.U64, ~F.u64_overflowing_shl, a, s, 64n):
  G.bnot_eq(U32.is_lt(s, 64), Nat.is_lt(vs(s), 64n), lt64(s))

def overflowing_shr_flag(+a: WU.U64, +s: U32) -> SF.OverflowingShr.flag(~WU.U64, ~F.u64_overflowing_shr, a, s, 64n):
  G.bnot_eq(U32.is_lt(s, 64), Nat.is_lt(vs(s), 64n), lt64(s))

def cshl(+a: WU.U64, +s: U32, +ok: Bool, +hok: {Nat.is_lt(vs(s), 64n) == ok : Bool}) -> {SF.mval(~WU.U64, ~SG.u64_val, F.opt(WU.U64, Bool.not(U32.is_lt(s, 64)), X.shl(a, U32.to_nat(U32.and(s, 63))))) == SF.keep(ok, C.low(64n, C.shift(vs(s), SG.u64_val(a)))) : Maybe<&2, Nat>}:
  match ok:
    case True{}:
      +hb = Equal.trans(Bool, U32.is_lt(s, 64), Nat.is_lt(vs(s), 64n), ok, lt64(s), hok)
      +ev = Equal.trans(Nat, SG.u64_val(X.shl(a, U32.to_nat(U32.and(s, 63)))), SG.u64_val(X.shl(a, vs(s))), C.low(64n, C.shift(vs(s), SG.u64_val(a))), Equal.cong(Nat, Nat, t => SG.u64_val(X.shl(a, t)), U32.to_nat(U32.and(s, 63)), vs(s), am_small(s, hok)), SH.shl_value(a, vs(s), hok))
      G.some_of(~WU.U64, ~SG.u64_val, Bool.not(U32.is_lt(s, 64)), G.bnot_eq(U32.is_lt(s, 64), True{}, hb), X.shl(a, U32.to_nat(U32.and(s, 63))), C.low(64n, C.shift(vs(s), SG.u64_val(a))), ev)
    case False{}:
      +hb = Equal.trans(Bool, U32.is_lt(s, 64), Nat.is_lt(vs(s), 64n), ok, lt64(s), hok)
      G.none_of(~WU.U64, ~SG.u64_val, Bool.not(U32.is_lt(s, 64)), G.bnot_eq(U32.is_lt(s, 64), False{}, hb), X.shl(a, U32.to_nat(U32.and(s, 63))))

def checked_shl(+a: WU.U64, +s: U32) -> SF.CheckedShl.value(~WU.U64, ~SG.u64_val, ~F.u64_checked_shl, 64n, a, s):
  cshl(a, s, Nat.is_lt(vs(s), 64n), {==})

def cshr(+a: WU.U64, +s: U32, +ok: Bool, +hok: {Nat.is_lt(vs(s), 64n) == ok : Bool}) -> {SF.mval(~WU.U64, ~SG.u64_val, F.opt(WU.U64, Bool.not(U32.is_lt(s, 64)), X.shr(a, U32.to_nat(U32.and(s, 63))))) == SF.keep(ok, C.high(vs(s), SG.u64_val(a))) : Maybe<&2, Nat>}:
  match ok:
    case True{}:
      +hb = Equal.trans(Bool, U32.is_lt(s, 64), Nat.is_lt(vs(s), 64n), ok, lt64(s), hok)
      +ev = Equal.trans(Nat, SG.u64_val(X.shr(a, U32.to_nat(U32.and(s, 63)))), SG.u64_val(X.shr(a, vs(s))), C.high(vs(s), SG.u64_val(a)), Equal.cong(Nat, Nat, t => SG.u64_val(X.shr(a, t)), U32.to_nat(U32.and(s, 63)), vs(s), am_small(s, hok)), SH.shr_value(a, vs(s)))
      G.some_of(~WU.U64, ~SG.u64_val, Bool.not(U32.is_lt(s, 64)), G.bnot_eq(U32.is_lt(s, 64), True{}, hb), X.shr(a, U32.to_nat(U32.and(s, 63))), C.high(vs(s), SG.u64_val(a)), ev)
    case False{}:
      +hb = Equal.trans(Bool, U32.is_lt(s, 64), Nat.is_lt(vs(s), 64n), ok, lt64(s), hok)
      G.none_of(~WU.U64, ~SG.u64_val, Bool.not(U32.is_lt(s, 64)), G.bnot_eq(U32.is_lt(s, 64), False{}, hb), X.shr(a, U32.to_nat(U32.and(s, 63))))

def checked_shr(+a: WU.U64, +s: U32) -> SF.CheckedShr.value(~WU.U64, ~SG.u64_val, ~F.u64_checked_shr, 64n, a, s):
  cshr(a, s, Nat.is_lt(vs(s), 64n), {==})

# ---- pow through the generic checked pow ----

def pw(+a: WU.U64, +e: U32) -> Nat:
  Nat.pow(SG.u64_val(a), vs(e))

def gpow(+a: WU.U64, +e: U32) -> Result<&2, &2, NM.NumError, WU.U64>:
  GN.pow(~WU.U64, ~I.u64_op, ~I.u64_is, a, vs(e))

def cpow(+a: WU.U64, +e: U32, +ok: Bool, +hok: {C.fits(64n, pw(a, e)) == ok : Bool}) -> {SF.mval(~WU.U64, ~SG.u64_val, F.res_opt(WU.U64, gpow(a, e))) == SF.keep(ok, pw(a, e)) : Maybe<&2, Nat>}:
  match ok:
    case True{}:
      %Equal.sym(Result<&2, &2, NM.NumError, WU.U64>, gpow(a, e), SG.checked(~WU.U64, ~SG.u64_of, 64n, pw(a, e)), UI.pow_checked(a, vs(e))) : {SF.mval(~WU.U64, ~SG.u64_val, F.res_opt(WU.U64, _)) == Some{pw(a, e)} : Maybe<&2, Nat>}
      %Equal.sym(Bool, C.fits(64n, pw(a, e)), True{}, hok) : {SF.mval(~WU.U64, ~SG.u64_val, F.res_opt(WU.U64, SG.checked_pick(~WU.U64, ~SG.u64_of, pw(a, e), _))) == Some{pw(a, e)} : Maybe<&2, Nat>}
      Equal.cong(Nat, Maybe<&2, Nat>, t => Some{t}, SG.u64_val(SG.u64_of(pw(a, e))), pw(a, e), LV.vo(pw(a, e), hok))
    case False{}:
      %Equal.sym(Result<&2, &2, NM.NumError, WU.U64>, gpow(a, e), SG.checked(~WU.U64, ~SG.u64_of, 64n, pw(a, e)), UI.pow_checked(a, vs(e))) : {SF.mval(~WU.U64, ~SG.u64_val, F.res_opt(WU.U64, _)) == None{} : Maybe<&2, Nat>}
      %Equal.sym(Bool, C.fits(64n, pw(a, e)), False{}, hok) : {SF.mval(~WU.U64, ~SG.u64_val, F.res_opt(WU.U64, SG.checked_pick(~WU.U64, ~SG.u64_of, pw(a, e), _))) == None{} : Maybe<&2, Nat>}
      {==}

def checked_pow(+a: WU.U64, +e: U32) -> SF.CheckedPow.value(~WU.U64, ~SG.u64_val, ~F.u64_checked_pow, 64n, a, e):
  cpow(a, e, C.fits(64n, pw(a, e)), {==})

def spow(+top: WU.U64, +ht: {Bool.and(C.fits(64n, SG.u64_val(top)), Bool.not(C.fits(64n, 1n+SG.u64_val(top)))) == True{} : Bool}, +a: WU.U64, +e: U32, +ok: Bool, +hok: {C.fits(64n, pw(a, e)) == ok : Bool}) -> {SF.saturated(64n, pw(a, e), SG.u64_val(F.or_top(WU.U64, top, F.res_opt(WU.U64, gpow(a, e)))), ok) == True{} : Bool}:
  match ok:
    case True{}:
      %Equal.sym(Result<&2, &2, NM.NumError, WU.U64>, gpow(a, e), SG.checked(~WU.U64, ~SG.u64_of, 64n, pw(a, e)), UI.pow_checked(a, vs(e))) : {SF.saturated(64n, pw(a, e), SG.u64_val(F.or_top(WU.U64, top, F.res_opt(WU.U64, _))), True{}) == True{} : Bool}
      %Equal.sym(Bool, C.fits(64n, pw(a, e)), True{}, hok) : {SF.saturated(64n, pw(a, e), SG.u64_val(F.or_top(WU.U64, top, F.res_opt(WU.U64, SG.checked_pick(~WU.U64, ~SG.u64_of, pw(a, e), _)))), True{}) == True{} : Bool}
      %Equal.sym(Nat, SG.u64_val(SG.u64_of(pw(a, e))), pw(a, e), LV.vo(pw(a, e), hok)) : {Nat.is_eq(_, pw(a, e)) == True{} : Bool}
      N.is_eq_refl(pw(a, e))
    case False{}:
      %Equal.sym(Result<&2, &2, NM.NumError, WU.U64>, gpow(a, e), SG.checked(~WU.U64, ~SG.u64_of, 64n, pw(a, e)), UI.pow_checked(a, vs(e))) : {SF.saturated(64n, pw(a, e), SG.u64_val(F.or_top(WU.U64, top, F.res_opt(WU.U64, _))), False{}) == True{} : Bool}
      %Equal.sym(Bool, C.fits(64n, pw(a, e)), False{}, hok) : {SF.saturated(64n, pw(a, e), SG.u64_val(F.or_top(WU.U64, top, F.res_opt(WU.U64, SG.checked_pick(~WU.U64, ~SG.u64_of, pw(a, e), _)))), False{}) == True{} : Bool}
      ht

def saturating_pow(+a: WU.U64, +e: U32) -> SF.SaturatingPow.value(~WU.U64, ~SG.u64_val, ~F.u64_saturating_pow, 64n, a, e):
  spow(F.u64_max(), top(1n, {==}), a, e, C.fits(64n, pw(a, e)), {==})

def opow(+a: WU.U64, +e: U32, +ok: Bool, +hok: {C.fits(64n, pw(a, e)) == ok : Bool}) -> {F.res_bad(WU.U64, gpow(a, e)) == Bool.not(ok) : Bool}:
  match ok:
    case True{}:
      %Equal.sym(Result<&2, &2, NM.NumError, WU.U64>, gpow(a, e), SG.checked(~WU.U64, ~SG.u64_of, 64n, pw(a, e)), UI.pow_checked(a, vs(e))) : {F.res_bad(WU.U64, _) == False{} : Bool}
      %Equal.sym(Bool, C.fits(64n, pw(a, e)), True{}, hok) : {F.res_bad(WU.U64, SG.checked_pick(~WU.U64, ~SG.u64_of, pw(a, e), _)) == False{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Result<&2, &2, NM.NumError, WU.U64>, gpow(a, e), SG.checked(~WU.U64, ~SG.u64_of, 64n, pw(a, e)), UI.pow_checked(a, vs(e))) : {F.res_bad(WU.U64, _) == True{} : Bool}
      %Equal.sym(Bool, C.fits(64n, pw(a, e)), False{}, hok) : {F.res_bad(WU.U64, SG.checked_pick(~WU.U64, ~SG.u64_of, pw(a, e), _)) == True{} : Bool}
      {==}

def overflowing_pow_flag(+a: WU.U64, +e: U32) -> SF.OverflowingPow.flag(~WU.U64, ~SG.u64_val, ~F.u64_overflowing_pow, 64n, a, e):
  opow(a, e, C.fits(64n, pw(a, e)), {==})

# ---- wrapping pow: right-to-left binary exponentiation mod 2^64 ----
# (natural.bend's pow_mod_go step, proved in proofs/math/natural/modpow.bend,
# run on the values with m = 2^64 = 1 + mp; e halves each step, so 32 steps
# cover every U32 exponent)

def lt_m(+mp: Nat, +hp: {C.pow2(64n) == 1n+mp : Nat}, +x: WU.U64) -> {Nat.is_lt(SG.u64_val(x), 1n+mp) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(SG.u64_val(x), 1n+mp), Nat.is_lt(SG.u64_val(x), C.pow2(64n)), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(SG.u64_val(x), t), 1n+mp, C.pow2(64n), Equal.sym(Nat, C.pow2(64n), 1n+mp, hp)), WW.lt_of_fits(64n, SG.u64_val(x), LV.vb(x)))

def mul_m(+mp: Nat, +hp: {C.pow2(64n) == 1n+mp : Nat}, +x: WU.U64, +y: WU.U64) -> {SG.u64_val(X.mul(x, y)) == Nat.mod(Nat.mul(SG.u64_val(x), SG.u64_val(y)), 1n+mp) : Nat}:
  Equal.trans(Nat, SG.u64_val(X.mul(x, y)), C.low(64n, Nat.mul(SG.u64_val(x), SG.u64_val(y))), Nat.mod(Nat.mul(SG.u64_val(x), SG.u64_val(y)), 1n+mp), WA.mul_value(x, y), G.low_mod(64n, Nat.mul(SG.u64_val(x), SG.u64_val(y)), mp, hp))

def wp_base(+mp: Nat, +hp: {C.pow2(64n) == 1n+mp : Nat}, +e: U32, +b: WU.U64, +acc: WU.U64, +h0: {vs(e) == 0n : Nat}) -> {SG.u64_val(acc) == Nat.mod(Nat.mul(SG.u64_val(acc), Nat.pow(SG.u64_val(b), vs(e))), 1n+mp) : Nat}:
  %Equal.sym(Nat, vs(e), 0n, h0) : {SG.u64_val(acc) == Nat.mod(Nat.mul(SG.u64_val(acc), Nat.pow(SG.u64_val(b), _)), 1n+mp) : Nat}
  %Equal.sym(Nat, Nat.mul(SG.u64_val(acc), 1n), SG.u64_val(acc), NA.mul_one(SG.u64_val(acc))) : {SG.u64_val(acc) == Nat.mod(_, 1n+mp) : Nat}
  Equal.sym(Nat, Nat.mod(SG.u64_val(acc), 1n+mp), SG.u64_val(acc), R.mod_of(0n, mp, SG.u64_val(acc), lt_m(mp, hp, acc)))

# the odd bit multiplies acc by b (pow_mod_odd on the values)
def wp_odd(+mp: Nat, +hp: {C.pow2(64n) == 1n+mp : Nat}, +e: U32, +b: WU.U64, +acc: WU.U64, +r: Nat, +hodd: {I.u32_odd(e) == Nat.is_eq(r, 1n) : Bool}, +hr: {Nat.is_lt(r, 2n) == True{} : Bool}) -> {SG.u64_val(F.pick(WU.U64, I.u32_odd(e), X.mul(acc, b), acc)) == M.pow_mod_odd(1n+mp, r, SG.u64_val(b), SG.u64_val(acc)) : Nat}:
  match r:
    case 0n:
      %Equal.sym(Bool, I.u32_odd(e), False{}, hodd) : {SG.u64_val(F.pick(WU.U64, _, X.mul(acc, b), acc)) == SG.u64_val(acc) : Nat}
      {==}
    case 1n:
      %Equal.sym(Bool, I.u32_odd(e), True{}, hodd) : {SG.u64_val(F.pick(WU.U64, _, X.mul(acc, b), acc)) == Nat.mod(Nat.mul(SG.u64_val(acc), SG.u64_val(b)), 1n+mp) : Nat}
      mul_m(mp, hp, acc, b)
    case 2n+ +q:
      Empty.absurd({SG.u64_val(F.pick(WU.U64, I.u32_odd(e), X.mul(acc, b), acc)) == M.pow_mod_odd(1n+mp, 2n+q, SG.u64_val(b), SG.u64_val(acc)) : Nat}, N.lt_zero_absurd(q, hr))

def half_e(+e: U32) -> {vs(U32.shr(e)) == Nat.div(vs(e), 2n) : Nat}:
  Equal.trans(Nat, vs(U32.shr(e)), C.half(vs(e)), Nat.div(vs(e), 2n), SHN.shrn_high(e, 1n), WA.half_div(vs(e)))

def wp_go(fuel: Nat, +mp: Nat, +hp: {C.pow2(64n) == 1n+mp : Nat}, +e: U32, +b: WU.U64, +acc: WU.U64, +z: Bool, +hz: {U32.is_zero(e) == z : Bool}, +he: {Nat.is_lt(vs(e), C.pow2(fuel)) == True{} : Bool}) -> {SG.u64_val(F.u64_wpow(fuel, e, b, acc, z)) == Nat.mod(Nat.mul(SG.u64_val(acc), Nat.pow(SG.u64_val(b), vs(e))), 1n+mp) : Nat}:
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
      +acc2 = F.pick(WU.U64, I.u32_odd(e), X.mul(acc, b), acc)
      +he2 = Equal.trans(Bool, Nat.is_lt(vs(U32.shr(e)), C.pow2(f)), Nat.is_lt(C.half(ve), C.pow2(f)), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(t, C.pow2(f)), vs(U32.shr(e)), C.half(ve), SHN.shrn_high(e, 1n)), Equal.trans(Bool, Nat.is_lt(C.half(ve), C.pow2(f)), Nat.is_lt(ve, Nat.double(C.pow2(f))), True{}, WW.lt_half(ve, C.pow2(f)), he))
      +ih = wp_go(f, mp, hp, U32.shr(e), X.mul(b, b), acc2, U32.is_zero(U32.shr(e)), {==}, he2)
      +ea = wp_odd(mp, hp, e, b, acc, bit, LW.tests_odd(e), B.half_rem(ve))
      +eb = mul_m(mp, hp, b, b)
      +x1 = Equal.cong(Nat, Nat, t => Nat.mod(Nat.mul(t, Nat.pow(SG.u64_val(X.mul(b, b)), vs(U32.shr(e)))), m), SG.u64_val(acc2), M.pow_mod_odd(m, bit, SG.u64_val(b), SG.u64_val(acc)), ea)
      +x2 = Equal.cong(Nat, Nat, t => Nat.mod(Nat.mul(M.pow_mod_odd(m, bit, SG.u64_val(b), SG.u64_val(acc)), Nat.pow(t, vs(U32.shr(e)))), m), SG.u64_val(X.mul(b, b)), Nat.mod(Nat.mul(SG.u64_val(b), SG.u64_val(b)), m), eb)
      +x3 = Equal.cong(Nat, Nat, t => Nat.mod(Nat.mul(M.pow_mod_odd(m, bit, SG.u64_val(b), SG.u64_val(acc)), Nat.pow(Nat.mod(Nat.mul(SG.u64_val(b), SG.u64_val(b)), m), t)), m), vs(U32.shr(e)), e2, half_e(e))
      +x4 = MP.pm_bit(mp, e2, bit, B.half_rem(ve), SG.u64_val(b), SG.u64_val(acc))
      +x5 = Equal.cong(Nat, Nat, t => Nat.mod(Nat.mul(SG.u64_val(acc), Nat.pow(SG.u64_val(b), t)), m), Nat.add(Nat.double(e2), bit), ve, Equal.sym(Nat, ve, Nat.add(Nat.double(e2), bit), B.half_eq(ve)))
      +L0 = Nat.mod(Nat.mul(SG.u64_val(acc2), Nat.pow(SG.u64_val(X.mul(b, b)), vs(U32.shr(e)))), m)
      +L1 = Nat.mod(Nat.mul(M.pow_mod_odd(m, bit, SG.u64_val(b), SG.u64_val(acc)), Nat.pow(SG.u64_val(X.mul(b, b)), vs(U32.shr(e)))), m)
      +L2 = Nat.mod(Nat.mul(M.pow_mod_odd(m, bit, SG.u64_val(b), SG.u64_val(acc)), Nat.pow(Nat.mod(Nat.mul(SG.u64_val(b), SG.u64_val(b)), m), vs(U32.shr(e)))), m)
      +L3 = Nat.mod(Nat.mul(M.pow_mod_odd(m, bit, SG.u64_val(b), SG.u64_val(acc)), Nat.pow(Nat.mod(Nat.mul(SG.u64_val(b), SG.u64_val(b)), m), e2)), m)
      +L4 = Nat.mod(Nat.mul(SG.u64_val(acc), Nat.pow(SG.u64_val(b), Nat.add(Nat.double(e2), bit))), m)
      +L5 = Nat.mod(Nat.mul(SG.u64_val(acc), Nat.pow(SG.u64_val(b), ve)), m)
      Equal.trans(Nat, SG.u64_val(F.u64_wpow(f, U32.shr(e), X.mul(b, b), acc2, U32.is_zero(U32.shr(e)))), L0, L5, ih, Equal.trans(Nat, L0, L1, L5, x1, Equal.trans(Nat, L1, L2, L5, x2, Equal.trans(Nat, L2, L3, L5, x3, Equal.trans(Nat, L3, L4, L5, x4, x5)))))

def wp_top(+mp: Nat, +hp: {C.pow2(64n) == 1n+mp : Nat}, +a: WU.U64, +e: U32) -> {SG.u64_val(F.u64_wrapping_pow(a, e)) == C.low(64n, pw(a, e)) : Nat}:
  +ih = wp_go(32n, mp, hp, e, a, WU.U64{1, 0}, U32.is_zero(e), {==}, WW.lt_of_fits(32n, vs(e), LW.vb(e)))
  +e1 = Equal.cong(Nat, Nat, t => Nat.mod(t, 1n+mp), Nat.mul(1n, pw(a, e)), pw(a, e), AR.one_mul(pw(a, e)))
  Equal.trans(Nat, SG.u64_val(F.u64_wrapping_pow(a, e)), Nat.mod(Nat.mul(1n, pw(a, e)), 1n+mp), C.low(64n, pw(a, e)), ih, Equal.trans(Nat, Nat.mod(Nat.mul(1n, pw(a, e)), 1n+mp), Nat.mod(pw(a, e), 1n+mp), C.low(64n, pw(a, e)), e1, Equal.sym(Nat, C.low(64n, pw(a, e)), Nat.mod(pw(a, e), 1n+mp), G.low_mod(64n, pw(a, e), mp, hp))))

def wrapping_pow(+a: WU.U64, +e: U32) -> SF.WrappingPow.value(~WU.U64, ~SG.u64_val, ~F.u64_wrapping_pow, 64n, a, e):
  wp_top(Nat.sub(C.pow2(64n), 1n), SH.pow2_eq(64n), a, e)

def overflowing_pow_value(+a: WU.U64, +e: U32) -> SF.OverflowingPow.value(~WU.U64, ~SG.u64_val, ~F.u64_overflowing_pow, 64n, a, e):
  wrapping_pow(a, e)

# ---- wrapping sub: a + (2^64 - 1 - b) + 1, with m == 2^64 - 1 abstract ----

def wsub_val(+m: WU.U64, +one: Nat, +h1: {one == 1n : Nat}, +hmo: {1n+SG.u64_val(m) == C.shift(64n, one) : Nat}, +a: WU.U64, +b: WU.U64) -> {SG.u64_val(X.add(X.add(a, X.sub(m, b)), WU.U64{1, 0})) == C.low(64n, Nat.add(Nat.add(SG.u64_val(a), Nat.sub(SG.u64_val(m), SG.u64_val(b))), 1n)) : Nat}:
  +S = C.shift(64n, one)
  +hlt = Equal.trans(Bool, Nat.is_lt(SG.u64_val(b), 1n+SG.u64_val(m)), Nat.is_lt(SG.u64_val(b), S), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(SG.u64_val(b), t), 1n+SG.u64_val(m), S, hmo), WW.lt_one(64n, one, h1, SG.u64_val(b), LV.vb(b)))
  +e2 = Equal.cong(Nat, Nat, t => C.low(64n, Nat.add(t, 1n)), SG.u64_val(X.add(a, X.sub(m, b))), C.low(64n, Nat.add(SG.u64_val(a), SG.u64_val(X.sub(m, b)))), WA.add_value(a, X.sub(m, b)))
  +e3 = G.low_add_low(64n, Nat.add(SG.u64_val(a), SG.u64_val(X.sub(m, b))), 1n)
  +e4 = Equal.cong(Nat, Nat, t => C.low(64n, Nat.add(Nat.add(SG.u64_val(a), t), 1n)), SG.u64_val(X.sub(m, b)), Nat.sub(SG.u64_val(m), SG.u64_val(b)), WA.sub_value(m, b, N.lt_succ_le(SG.u64_val(b), SG.u64_val(m), hlt)))
  Equal.trans(Nat, SG.u64_val(X.add(X.add(a, X.sub(m, b)), WU.U64{1, 0})), C.low(64n, Nat.add(SG.u64_val(X.add(a, X.sub(m, b))), 1n)), C.low(64n, Nat.add(Nat.add(SG.u64_val(a), Nat.sub(SG.u64_val(m), SG.u64_val(b))), 1n)), WA.add_value(X.add(a, X.sub(m, b)), WU.U64{1, 0}), Equal.trans(Nat, C.low(64n, Nat.add(SG.u64_val(X.add(a, X.sub(m, b))), 1n)), C.low(64n, Nat.add(C.low(64n, Nat.add(SG.u64_val(a), SG.u64_val(X.sub(m, b)))), 1n)), C.low(64n, Nat.add(Nat.add(SG.u64_val(a), Nat.sub(SG.u64_val(m), SG.u64_val(b))), 1n)), e2, Equal.trans(Nat, C.low(64n, Nat.add(C.low(64n, Nat.add(SG.u64_val(a), SG.u64_val(X.sub(m, b)))), 1n)), C.low(64n, Nat.add(Nat.add(SG.u64_val(a), SG.u64_val(X.sub(m, b))), 1n)), C.low(64n, Nat.add(Nat.add(SG.u64_val(a), Nat.sub(SG.u64_val(m), SG.u64_val(b))), 1n)), e3, e4)))

def wsub_g(+one: Nat, +h1: {one == 1n : Nat}, +m: WU.U64, +hmo: {1n+SG.u64_val(m) == C.shift(64n, one) : Nat}, +a: WU.U64, +b: WU.U64) -> {Nat.add(SG.u64_val(X.add(X.add(a, X.sub(m, b)), WU.U64{1, 0})), SG.u64_val(b)) == Nat.add(SG.u64_val(a), C.shift(64n, SF.bn(Nat.is_lt(SG.u64_val(a), SG.u64_val(b))))) : Nat}:
  +S = C.shift(64n, one)
  +d = Nat.add(Nat.add(SG.u64_val(a), Nat.sub(SG.u64_val(m), SG.u64_val(b))), 1n)
  +hlt = Equal.trans(Bool, Nat.is_lt(SG.u64_val(b), 1n+SG.u64_val(m)), Nat.is_lt(SG.u64_val(b), S), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(SG.u64_val(b), t), 1n+SG.u64_val(m), S, hmo), WW.lt_one(64n, one, h1, SG.u64_val(b), LV.vb(b)))
  +ed = G.plus_one(SG.u64_val(a), Nat.sub(SG.u64_val(m), SG.u64_val(b)), SG.u64_val(b), SG.u64_val(m), S, N.sub_add(SG.u64_val(m), SG.u64_val(b), N.lt_succ_le(SG.u64_val(b), SG.u64_val(m), hlt)), hmo)
  %Equal.sym(Nat, SG.u64_val(X.add(X.add(a, X.sub(m, b)), WU.U64{1, 0})), C.low(64n, d), wsub_val(m, one, h1, hmo, a, b)) : {Nat.add(_, SG.u64_val(b)) == Nat.add(SG.u64_val(a), C.shift(64n, SF.bn(Nat.is_lt(SG.u64_val(a), SG.u64_val(b))))) : Nat}
  G.wsub(64n, one, h1, SG.u64_val(a), SG.u64_val(b), d, ed, LV.vb(a), Nat.is_lt(SG.u64_val(a), SG.u64_val(b)), {==})

def wsub_eq(+a: WU.U64, +b: WU.U64) -> {Nat.add(SG.u64_val(F.u64_wsub(a, b)), SG.u64_val(b)) == Nat.add(SG.u64_val(a), C.shift(64n, SF.bn(Nat.is_lt(SG.u64_val(a), SG.u64_val(b))))) : Nat}:
  wsub_g(1n, {==}, F.u64_max(), top1(1n, {==}), a, b)

def wrapping_sub(+a: WU.U64, +b: WU.U64) -> SF.WrappingSub.value(~WU.U64, ~SG.u64_val, ~F.u64_wrapping_sub, 64n, a, b):
  wsub_eq(a, b)

def overflowing_sub_value(+a: WU.U64, +b: WU.U64) -> SF.OverflowingSub.value(~WU.U64, ~SG.u64_val, ~F.u64_overflowing_sub, 64n, a, b):
  wsub_eq(a, b)
