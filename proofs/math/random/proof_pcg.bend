import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../spec/math/random/pcg.bend as SP
import ../../../spec/math/random.bend as SRM
import ../../../src/math/u64.bend as WU
import ../../../src/math/w64.bend as X
import ../../../src/math/random/pcg.bend as P
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../typed/width.bend as WW
import ../typed/w64add.bend as WA
import ../typed/w64sh.bend as SH
import ./pcg/xor.bend as XO
import ../../lib/lemmas/spec/numeric.bend as S
import ../typed/w64m128.bend as M128
import ./pcg/step.bend as ST
import ./pcg/impl.bend as IM

# Entry point: `bend proofs/math/random/proof_pcg.bend` checks the PCG clauses
# of spec/math/random.bend under the clause's name, for every state and every
# multiplier and increment; no holes, no axioms. One step of
# src/math/random/pcg.bend is the 128-bit LCG (the width-generic algebra is in
# pcg/step.bend, instantiated at 64 in pcg/impl.bend) and its DXSM output is
# spec/math/random/pcg.bend's dxsm: xor with a right shift, products mod 2^64
# and "or 1" on the low word, each by its value lemma. The factors of each
# product stay variables (mulg), so no product is ever normalized, and the
# clause types are stated once (a clause type is expensive to normalize).
# The other clauses are checked by proofs/math/random/proof.bend,
# proof_draws.bend and proof_float.bend.

def PCG.step(+mh: WU.U64, +ml: WU.U64, +ih: WU.U64, +il: WU.U64, +p: P.PCG) -> SRM.PCG.step(mh, ml, ih, il, p):
  match p:
    case P.P{+hi, +lo}:
      IM.step_pair(mh, ml, ih, il, hi, lo, X.mul128(lo, ml), IM.m128(lo, ml))

def PCG.constants(+p: P.PCG) -> SRM.PCG.constants(p):
  {==}

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# x ^ (x >> k)
def xs(+a: WU.U64, +k: Nat) -> {SW.value(P.xor64(a, X.shr(a, k))) == SP.xor_bits(64n, SW.value(a), C.high(k, SW.value(a))) : Nat}:
  Equal.trans(Nat, SW.value(P.xor64(a, X.shr(a, k))), SP.xor_bits(64n, SW.value(a), SW.value(X.shr(a, k))), SP.xor_bits(64n, SW.value(a), C.high(k, SW.value(a))),
    XO.xor64_value(a, X.shr(a, k)),
    Equal.cong(Nat, Nat, z => SP.xor_bits(64n, SW.value(a), z), SW.value(X.shr(a, k)), C.high(k, SW.value(a)), SH.shr_value(a, k)))

def plus1(+x: Nat) -> {Nat.add(x, 1n) == 1n+x : Nat}:
  Equal.trans(Nat, Nat.add(x, 1n), 1n+Nat.add(x, 0n), 1n+x, NA.add_succ(x, 0n), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(x, 0n), x, NA.add_zero(x)))

# lo | 1
def or_value(+lo: WU.U64) -> {SW.value(WU.U64{U32.or(X.lo(lo), 1), X.hi(lo)}) == Nat.add(Nat.double(C.half(SW.value(lo))), 1n) : Nat}:
  match lo:
    case WU.U64{+l, +h}:
      +vl = v(l)
      +vh = v(h)
      +D = Nat.add(Nat.double(C.half(vl)), C.shift(32n, vh))
      +e1 = Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(32n, vh)), v(U32.or(l, 1)), 1n+Nat.double(C.half(vl)), SH.or1(l))
      +e2 = Equal.cong(Nat, Nat, z => 1n+z, D, Nat.double(Nat.add(C.half(vl), C.shift(31n, vh))), Equal.sym(Nat, Nat.double(Nat.add(C.half(vl), C.shift(31n, vh))), D, NA.double_add(C.half(vl), C.shift(31n, vh))))
      +e3 = Equal.cong(Nat, Nat, z => 1n+Nat.double(z), Nat.add(C.half(vl), C.shift(31n, vh)), C.half(Nat.add(vl, C.shift(32n, vh))), Equal.sym(Nat, C.half(Nat.add(vl, C.shift(32n, vh))), Nat.add(C.half(vl), C.shift(31n, vh)), WW.half_dbl(vl, C.shift(31n, vh))))
      +e4 = Equal.sym(Nat, Nat.add(Nat.double(C.half(Nat.add(vl, C.shift(32n, vh)))), 1n), 1n+Nat.double(C.half(Nat.add(vl, C.shift(32n, vh)))), plus1(Nat.double(C.half(Nat.add(vl, C.shift(32n, vh))))))
      Equal.trans(Nat, Nat.add(v(U32.or(l, 1)), C.shift(32n, vh)), 1n+D, Nat.add(Nat.double(C.half(Nat.add(vl, C.shift(32n, vh)))), 1n), e1,
        Equal.trans(Nat, 1n+D, 1n+Nat.double(Nat.add(C.half(vl), C.shift(31n, vh))), Nat.add(Nat.double(C.half(Nat.add(vl, C.shift(32n, vh)))), 1n), e2,
          Equal.trans(Nat, 1n+Nat.double(Nat.add(C.half(vl), C.shift(31n, vh))), 1n+Nat.double(C.half(Nat.add(vl, C.shift(32n, vh)))), Nat.add(Nat.double(C.half(Nat.add(vl, C.shift(32n, vh)))), 1n), e3, e4)))

# the value of a product mod 2^64 from the values of its factors; the
# factors stay variables here, so no product is ever normalized
def mulg(+x: WU.U64, +o: WU.U64, +xv: Nat, +hx: {SW.value(x) == xv : Nat}, +ov: Nat, +ho: {SW.value(o) == ov : Nat}) -> {SW.value(X.mul(x, o)) == C.low(64n, Nat.mul(xv, ov)) : Nat}:
  Equal.trans(Nat, SW.value(X.mul(x, o)), C.low(64n, Nat.mul(SW.value(x), SW.value(o))), C.low(64n, Nat.mul(xv, ov)), WA.mul_value(x, o),
    Equal.trans(Nat, C.low(64n, Nat.mul(SW.value(x), SW.value(o))), C.low(64n, Nat.mul(xv, SW.value(o))), C.low(64n, Nat.mul(xv, ov)),
      Equal.cong(Nat, Nat, z => C.low(64n, Nat.mul(z, SW.value(o))), SW.value(x), xv, hx),
      Equal.cong(Nat, Nat, z => C.low(64n, Nat.mul(xv, z)), SW.value(o), ov, ho)))

def xs32(+h: WU.U64) -> {SW.value(P.xor64(h, X.shr(h, 32n))) == SP.xor_bits(64n, SW.value(h), C.high(32n, SW.value(h))) : Nat}:
  xs(h, 32n)

def xs48(+h: WU.U64) -> {SW.value(P.xor64(h, X.shr(h, 48n))) == SP.xor_bits(64n, SW.value(h), C.high(48n, SW.value(h))) : Nat}:
  xs(h, 48n)

# x ^ (x >> 48) for a word of value t
def xt(+H: WU.U64, +t: Nat, +ht: {SW.value(H) == t : Nat}) -> {SW.value(P.xor64(H, X.shr(H, 48n))) == SP.xor_bits(64n, t, C.high(48n, t)) : Nat}:
  Equal.trans(Nat, SW.value(P.xor64(H, X.shr(H, 48n))), SP.xor_bits(64n, SW.value(H), C.high(48n, SW.value(H))), SP.xor_bits(64n, t, C.high(48n, t)),
    xs48(H), Equal.cong(Nat, Nat, z => SP.xor_bits(64n, z, C.high(48n, z)), SW.value(H), t, ht))

# the first half's value is t
def half1(+cm: WU.U64, +hi: WU.U64, +t: Nat, +ht: {t == SP.dxsm1(SW.value(cm), SW.value(hi)) : Nat}) -> {SW.value(X.mul(P.xor64(hi, X.shr(hi, 32n)), cm)) == t : Nat}:
  Equal.trans(Nat, SW.value(X.mul(P.xor64(hi, X.shr(hi, 32n)), cm)), SP.dxsm1(SW.value(cm), SW.value(hi)), t,
    mulg(P.xor64(hi, X.shr(hi, 32n)), cm, SP.xor_bits(64n, SW.value(hi), C.high(32n, SW.value(hi))), xs32(hi), SW.value(cm), {==}),
    Equal.sym(Nat, t, SP.dxsm1(SW.value(cm), SW.value(hi)), ht))

# THEOREM (PCG.output)
# values are known (x ^ x >> 48 with x of value t, and lo | 1)
def PCG.output(+cm: WU.U64, +hi: WU.U64, +lo: WU.U64, +t: Nat, +ht: {t == SP.dxsm1(SW.value(cm), SW.value(hi)) : Nat}) -> SRM.PCG.output(cm, hi, lo, t, ht):
  +H = X.mul(P.xor64(hi, X.shr(hi, 32n)), cm)
  mulg(P.xor64(H, X.shr(H, 48n)), WU.U64{U32.or(X.lo(lo), 1), X.hi(lo)}, SP.xor_bits(64n, t, C.high(48n, t)), xt(H, t, half1(cm, hi, t, ht)), Nat.add(Nat.double(C.half(SW.value(lo))), 1n), or_value(lo))
