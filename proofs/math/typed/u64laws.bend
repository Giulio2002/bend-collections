import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/instances.bend as SI
import ../../../spec/math/generic.bend as SG
import ../../../spec/math/w64.bend as SW
import ../../../src/math/instances.bend as I
import ../../../src/math/num.bend as NM
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ./width.bend as WW
import ./u32laws.bend as LW
import ./w64mul.bend as W64M
import ./w64add.bend as WA
import ./w64dmtop.bend as DT
import ./w64dmrem.bend as DR
import ./w64mmtop.bend as MMT
import ./w64isq.bend as ISQ
import ./w64sh.bend as SH

# The seventeen instance laws of spec/math/instances.bend at U64, from the
# proved clauses of spec/math/w64.bend, and the value model (every U64 is
# of_nat of its value, values below 2^64 round-trip).

def v(+x: WU.U64) -> Nat:
  SG.u64_val(x)

def true_ne_false(+h: {True{} == False{} : Bool}) -> Empty:
  LW.true_ne_false(h)

def vb(+x: WU.U64) -> {C.fits(64n, v(x)) == True{} : Bool}:
  match x:
    case WU.U64{+l, +h}:
      WW.limbs_fit(32n, 32n, LW.v(l), LW.v(h), LW.vb(l), LW.vb(h))

def val_lt(+K: Nat, +hK: {K == 64n : Nat}, +x: WU.U64) -> {Nat.is_lt(v(x), C.pow2(K)) == True{} : Bool}:
  WW.lt_of_fits(K, v(x), L.subst(Nat, z => {C.fits(z, v(x)) == True{} : Bool}, 64n, K, Equal.sym(Nat, K, 64n, hK), vb(x)))

def rt(+x: WU.U64) -> {SG.u64_of(v(x)) == x : WU.U64}:
  match x:
    case WU.U64{+l, +h}:
      +el = WW.low_u(32n, LW.v(l), LW.v(h), LW.vb(l))
      +eh = WW.high_u(32n, LW.v(l), LW.v(h), LW.vb(l))
      +e1 = Equal.trans(U32, U32.from_nat(C.low(32n, v(WU.U64{l, h}))), U32.from_nat(LW.v(l)), l, Equal.cong(Nat, U32, z => U32.from_nat(z), C.low(32n, v(WU.U64{l, h})), LW.v(l), el), LW.rt(l))
      +e2 = Equal.trans(U32, U32.from_nat(C.high(32n, v(WU.U64{l, h}))), U32.from_nat(LW.v(h)), h, Equal.cong(Nat, U32, z => U32.from_nat(z), C.high(32n, v(WU.U64{l, h})), LW.v(h), eh), LW.rt(h))
      Equal.trans(WU.U64, WU.U64{U32.from_nat(C.low(32n, v(WU.U64{l, h}))), U32.from_nat(C.high(32n, v(WU.U64{l, h})))}, WU.U64{l, U32.from_nat(C.high(32n, v(WU.U64{l, h})))}, WU.U64{l, h}, Equal.cong(U32, WU.U64, z => WU.U64{z, U32.from_nat(C.high(32n, v(WU.U64{l, h})))}, U32.from_nat(C.low(32n, v(WU.U64{l, h}))), l, e1), Equal.cong(U32, WU.U64, z => WU.U64{l, z}, U32.from_nat(C.high(32n, v(WU.U64{l, h}))), h, e2))

def vo(+n: Nat, +h: {C.fits(64n, n) == True{} : Bool}) -> {v(SG.u64_of(n)) == n : Nat}:
  +hl = WW.low_fits(32n, n)
  +hh = SH.fits_high(32n, 32n, n, h)
  +e1 = Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(32n, U32.to_nat(U32.from_nat(C.high(32n, n))))), U32.to_nat(U32.from_nat(C.low(32n, n))), C.low(32n, n), LW.vo(C.low(32n, n), hl))
  +e2 = Equal.cong(Nat, Nat, z => Nat.add(C.low(32n, n), C.shift(32n, z)), U32.to_nat(U32.from_nat(C.high(32n, n))), C.high(32n, n), LW.vo(C.high(32n, n), hh))
  Equal.trans(Nat, Nat.add(U32.to_nat(U32.from_nat(C.low(32n, n))), C.shift(32n, U32.to_nat(U32.from_nat(C.high(32n, n))))), Nat.add(C.low(32n, n), C.shift(32n, U32.to_nat(U32.from_nat(C.high(32n, n))))), n, e1, Equal.trans(Nat, Nat.add(C.low(32n, n), C.shift(32n, U32.to_nat(U32.from_nat(C.high(32n, n))))), Nat.add(C.low(32n, n), C.shift(32n, C.high(32n, n))), n, e2, Equal.sym(Nat, n, Nat.add(C.low(32n, n), C.shift(32n, C.high(32n, n))), WW.low_high(32n, n))))

# ---- the laws ----

def ops_zero() -> SI.Ops.zero(~WU.U64, ~I.u64_op, ~SG.u64_val):
  SH.val0(0)

def ops_one() -> SI.Ops.one(~WU.U64, ~I.u64_op, ~SG.u64_val):
  SH.val0(1)

def ops_abs(+x: WU.U64) -> SI.Ops.abs(~WU.U64, ~I.u64_op, x):
  {==}

def tests_lt(+a: WU.U64, +b: WU.U64) -> SI.Tests.lt(~WU.U64, ~I.u64_is, ~SG.u64_val, a, b):
  WA.lt_value(a, b)

def tests_is_zero(+a: WU.U64) -> SI.Tests.is_zero(~WU.U64, ~I.u64_is, ~SG.u64_val, a):
  WA.is_zero_value(a)

def tests_odd(+a: WU.U64) -> SI.Tests.odd(~WU.U64, ~I.u64_is, ~SG.u64_val, a):
  WA.odd_value(a)

def tests_add_over(+a: WU.U64, +b: WU.U64) -> SI.Tests.add_over(~WU.U64, ~I.u64_is, ~SG.u64_val, 64n, a, b):
  WA.add_over_value(a, b)

def tests_mul_over(+a: WU.U64, +b: WU.U64) -> SI.Tests.mul_over(~WU.U64, ~I.u64_is, ~SG.u64_val, 64n, a, b):
  WA.mul_over_value(a, b)

def ops_sub(+a: WU.U64, +b: WU.U64, +h: {Nat.is_le(SG.u64_val(b), SG.u64_val(a)) == True{} : Bool}) -> SI.Ops.sub(~WU.U64, ~I.u64_op, ~SG.u64_val, a, b, h):
  WA.sub_value(a, b, h)

def ops_half(+a: WU.U64) -> SI.Ops.half(~WU.U64, ~I.u64_op, ~SG.u64_val, a):
  WA.half_value(a)

def nzb(+b: WU.U64, +h: {Nat.is_eq(SG.u64_val(b), 0n) == False{} : Bool}) -> {X.is_zero(b) == False{} : Bool}:
  Equal.trans(Bool, X.is_zero(b), Nat.is_eq(v(b), 0n), False{}, WA.is_zero_value(b), h)

def ops_quot(+a: WU.U64, +b: WU.U64, +h: {Nat.is_eq(SG.u64_val(b), 0n) == False{} : Bool}) -> SI.Ops.quot(~WU.U64, ~I.u64_op, ~SG.u64_val, a, b, h):
  DT.divmod_quot(a, b, nzb(b, h))

def ops_rem(+a: WU.U64, +b: WU.U64, +h: {Nat.is_eq(SG.u64_val(b), 0n) == False{} : Bool}) -> SI.Ops.rem(~WU.U64, ~I.u64_op, ~SG.u64_val, a, b, h):
  DR.divmod_rem(a, b, nzb(b, h))

def not_f(+x: Bool, +h: {Bool.not(x) == False{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, true_ne_false(h))

def ops_add(+a: WU.U64, +b: WU.U64, +h: {I.u64_is(NM.AddOver{a, b}) == False{} : Bool}) -> SI.Ops.add(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, a, b, h):
  +hf = not_f(C.fits(64n, Nat.add(v(a), v(b))), Equal.trans(Bool, Bool.not(C.fits(64n, Nat.add(v(a), v(b)))), X.add_over(a, b), False{}, Equal.sym(Bool, X.add_over(a, b), Bool.not(C.fits(64n, Nat.add(v(a), v(b)))), WA.add_over_value(a, b)), h))
  Equal.trans(Nat, v(X.add(a, b)), C.low(64n, Nat.add(v(a), v(b))), Nat.add(v(a), v(b)), WA.add_value(a, b), WW.low_fit(64n, Nat.add(v(a), v(b)), hf))

def ops_mul(+a: WU.U64, +b: WU.U64, +h: {I.u64_is(NM.MulOver{a, b}) == False{} : Bool}) -> SI.Ops.mul(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, a, b, h):
  +hf = not_f(C.fits(64n, Nat.mul(v(a), v(b))), Equal.trans(Bool, Bool.not(C.fits(64n, Nat.mul(v(a), v(b)))), X.mul_over(a, b), False{}, Equal.sym(Bool, X.mul_over(a, b), Bool.not(C.fits(64n, Nat.mul(v(a), v(b)))), WA.mul_over_value(a, b)), h))
  Equal.trans(Nat, v(X.mul(a, b)), C.low(64n, Nat.mul(v(a), v(b))), Nat.mul(v(a), v(b)), WA.mul_value(a, b), WW.low_fit(64n, Nat.mul(v(a), v(b)), hf))

def ops_mulmod(+a: WU.U64, +b: WU.U64, +m: WU.U64, +ha: {Nat.is_lt(SG.u64_val(a), SG.u64_val(m)) == True{} : Bool}, +hb: {Nat.is_lt(SG.u64_val(b), SG.u64_val(m)) == True{} : Bool}) -> SI.Ops.mulmod(~WU.U64, ~I.u64_op, ~SG.u64_val, a, b, m, ha, hb):
  MMT.mulmod_value(a, b, m, ha, hb)

def ops_sqrt(+a: WU.U64) -> SI.Ops.sqrt(~WU.U64, ~I.u64_op, ~SG.u64_val, a):
  ISQ.isqrt_value(a)

def pow2_c(+k: Nat, +hk: {Nat.is_lt(k, 64n) == True{} : Bool}, +c: Bool, +hc: {Nat.is_lt(k, 32n) == c : Bool}) -> {v(X.w_pow2(k, c)) == C.pow2(k) : Nat}:
  match c:
    case True{}:
      Equal.trans(Nat, v(WU.U64{X.pow2(k), 0}), U32.to_nat(X.pow2(k)), C.pow2(k), SH.val0(X.pow2(k)), SH.p2v(k, hc))
    case False{}:
      +hge = N.not_lt_le(k, 32n, hc)
      +d = Nat.sub(k, 32n)
      +ek = N.sub_add(k, 32n, hge)
      +hd = L.subst(Nat, z => {Nat.is_lt(d, z) == True{} : Bool}, Nat.sub(64n, 32n), 32n, {==}, WW.sub_lt_sub(k, 64n, 32n, hk, hge))
      Equal.trans(Nat, C.shift(32n, U32.to_nat(X.pow2(d))), C.shift(32n, C.pow2(d)), C.pow2(k), Equal.cong(Nat, Nat, z => C.shift(32n, z), U32.to_nat(X.pow2(d)), C.pow2(d), SH.p2v(d, hd)), Equal.trans(Nat, C.shift(32n, C.pow2(d)), C.pow2(Nat.add(32n, d)), C.pow2(k), WW.shift_pow2(32n, d), Equal.cong(Nat, Nat, z => C.pow2(z), Nat.add(32n, d), k, ek)))

def ops_pow2(+k: Nat, +hk: {Nat.is_lt(k, 64n) == True{} : Bool}) -> SI.Ops.pow2(~WU.U64, ~I.u64_op, ~SG.u64_val, 64n, k, hk):
  pow2_c(k, hk, Nat.is_lt(k, 32n), {==})
