import Base
import ../../../../spec/lib/common.bend as C
import ../../../../spec/math/w64.bend as SW
import ../../../../spec/math/random/pcg.bend as SP
import ../../../../src/math/u64.bend as WU
import ../../../../src/math/w64.bend as X
import ../../../../src/math/random/pcg.bend as P
import ../../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../typed/width.bend as WW
import ../../typed/w64add.bend as WA
import ../../typed/w64sh.bend as SH
import ./xor.bend as XO

# The DXSM output of src/math/random/pcg.bend (dxsm_with) is SP.dxsm on
# the values, for every multiplier: xor with a right shift, products mod
# 2^64 and "or 1" on the low word, each by its value lemma.

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

def d2(+h: WU.U64, +lo: WU.U64) -> {SW.value(P.dxsm2(h, lo)) == SP.dxsm3(SW.value(h), SW.value(lo)) : Nat}:
  +x = P.xor64(h, X.shr(h, 48n))
  +o = WU.U64{U32.or(X.lo(lo), 1), X.hi(lo)}
  Equal.trans(Nat, SW.value(X.mul(x, o)), C.low(64n, Nat.mul(SW.value(x), SW.value(o))), SP.dxsm3(SW.value(h), SW.value(lo)),
    WA.mul_value(x, o),
    Equal.trans(Nat, C.low(64n, Nat.mul(SW.value(x), SW.value(o))), C.low(64n, Nat.mul(SP.xor_bits(64n, SW.value(h), C.high(48n, SW.value(h))), SW.value(o))), SP.dxsm3(SW.value(h), SW.value(lo)),
      Equal.cong(Nat, Nat, z => C.low(64n, Nat.mul(z, SW.value(o))), SW.value(x), SP.xor_bits(64n, SW.value(h), C.high(48n, SW.value(h))), xs(h, 48n)),
      Equal.cong(Nat, Nat, z => C.low(64n, Nat.mul(SP.xor_bits(64n, SW.value(h), C.high(48n, SW.value(h))), z)), SW.value(o), Nat.add(Nat.double(C.half(SW.value(lo))), 1n), or_value(lo))))

# THEOREM: dxsm_with is DXSM on values
def output(+cm: WU.U64, +hi: WU.U64, +lo: WU.U64) -> {SW.value(P.dxsm_with(cm, hi, lo)) == SP.dxsm(SW.value(cm), SW.value(hi), SW.value(lo)) : Nat}:
  +x = P.xor64(hi, X.shr(hi, 32n))
  +h1 = X.mul(x, cm)
  +eh = Equal.trans(Nat, SW.value(h1), C.low(64n, Nat.mul(SW.value(x), SW.value(cm))), C.low(64n, Nat.mul(SP.xor_bits(64n, SW.value(hi), C.high(32n, SW.value(hi))), SW.value(cm))),
    WA.mul_value(x, cm),
    Equal.cong(Nat, Nat, z => C.low(64n, Nat.mul(z, SW.value(cm))), SW.value(x), SP.xor_bits(64n, SW.value(hi), C.high(32n, SW.value(hi))), xs(hi, 32n)))
  Equal.trans(Nat, SW.value(P.dxsm2(h1, lo)), SP.dxsm3(SW.value(h1), SW.value(lo)), SP.dxsm(SW.value(cm), SW.value(hi), SW.value(lo)),
    d2(h1, lo),
    Equal.cong(Nat, Nat, z => SP.dxsm3(z, SW.value(lo)), SW.value(h1), C.low(64n, Nat.mul(SP.xor_bits(64n, SW.value(hi), C.high(32n, SW.value(hi))), SW.value(cm))), eh))
