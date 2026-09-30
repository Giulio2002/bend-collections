import Base
import ../../../../spec/lib/common.bend as C
import ../../../../spec/math/w64.bend as SW
import ../../../../spec/math/random/pcg.bend as SP
import ../../../../src/math/u64.bend as WU
import ../../../../src/math/w64.bend as X
import ../../../../src/math/random/pcg.bend as P
import ../../../lib/lemmas/spec/numeric.bend as S
import ../../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../../lib/u32alg.bend as A
import ../../typed/width.bend as WW
import ../../typed/w64add.bend as WA
import ../../typed/w64m128.bend as M128
import ../../typed/w64mul.bend as W64M
import ../../typed/w64sh.bend as SH

import ./step.bend as ST
import ../../../../spec/math/random.bend as SR

# The implementation's words of one PCG step against ST.main.

def eqm_of(+v: Nat, +x: Nat, +e: {v == C.low(64n, x) : Nat}) -> {C.low(64n, v) == C.low(64n, x) : Nat}:
  ST.eqm_of(64n, v, x, e)

# ---- the implementation's words ----

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def carry_value(+c: Bool) -> {SW.value(WU.U64{X.b32(c), 0}) == S.bit_value(c) : Nat}:
  Equal.trans(Nat, SW.value(WU.U64{X.b32(c), 0}), v(X.b32(c)), S.bit_value(c), SH.val0(X.b32(c)), W64M.b32_v(c))

# the cross products mod 2^64
def fT(+hi: WU.U64, +lo: WU.U64, +ml: WU.U64, +mh: WU.U64) -> {C.low(64n, SW.value(X.add(X.mul(hi, ml), X.mul(lo, mh)))) == C.low(64n, Nat.add(Nat.mul(SW.value(hi), SW.value(ml)), Nat.mul(SW.value(lo), SW.value(mh)))) : Nat}:
  +m1 = X.mul(hi, ml)
  +m2 = X.mul(lo, mh)
  Equal.trans(Nat, C.low(64n, SW.value(X.add(m1, m2))), C.low(64n, Nat.add(SW.value(m1), SW.value(m2))), C.low(64n, Nat.add(Nat.mul(SW.value(hi), SW.value(ml)), Nat.mul(SW.value(lo), SW.value(mh)))),
    eqm_of(SW.value(X.add(m1, m2)), Nat.add(SW.value(m1), SW.value(m2)), WA.add_value(m1, m2)),
    ST.low_add(64n, SW.value(m1), Nat.mul(SW.value(hi), SW.value(ml)), SW.value(m2), Nat.mul(SW.value(lo), SW.value(mh)), eqm_of(SW.value(m1), Nat.mul(SW.value(hi), SW.value(ml)), WA.mul_value(hi, ml)), eqm_of(SW.value(m2), Nat.mul(SW.value(lo), SW.value(mh)), WA.mul_value(lo, mh))))

# a sum mod 2^64
def fS(+a: WU.U64, +b: WU.U64) -> {C.low(64n, SW.value(X.add(a, b))) == C.low(64n, Nat.add(SW.value(a), SW.value(b))) : Nat}:
  eqm_of(SW.value(X.add(a, b)), Nat.add(SW.value(a), SW.value(b)), WA.add_value(a, b))

# adding the carry
def fV(+a: WU.U64, +cb: Bool) -> {SW.value(X.add(a, WU.U64{X.b32(cb), 0})) == C.low(64n, Nat.add(SW.value(a), S.bit_value(cb))) : Nat}:
  Equal.trans(Nat, SW.value(X.add(a, WU.U64{X.b32(cb), 0})), C.low(64n, Nat.add(SW.value(a), SW.value(WU.U64{X.b32(cb), 0}))), C.low(64n, Nat.add(SW.value(a), S.bit_value(cb))),
    WA.add_value(a, WU.U64{X.b32(cb), 0}),
    Equal.cong(Nat, Nat, z => C.low(64n, Nat.add(SW.value(a), z)), SW.value(WU.U64{X.b32(cb), 0}), S.bit_value(cb), carry_value(cb)))

# one step for any product pair (l, h) with l + 2^64 h == lo * ml (the pair
# is abstract here, so the checker never unfolds the 128-bit product)
def step_pair(+mh: WU.U64, +ml: WU.U64, +ih: WU.U64, +il: WU.U64, +hi: WU.U64, +lo: WU.U64, pr: WU.U64 & WU.U64, +h1: {Nat.add(SW.value(X.pfst(pr)), C.shift(64n, SW.value(X.psnd(pr)))) == Nat.mul(SW.value(lo), SW.value(ml)) : Nat}) -> {SR.value128(P.step_mul(mh, ml, ih, il, hi, lo, pr)) == C.low(Nat.add(64n, 64n), Nat.add(Nat.mul(SR.value128(P.P{hi, lo}), SR.value128(P.P{mh, ml})), SR.value128(P.P{ih, il}))) : Nat}:
  match pr:
    case Tuple{+l, +h}:
      +T = X.add(X.mul(hi, ml), X.mul(lo, mh))
      +H = X.add(h, T)
      +H1 = X.add(H, ih)
      +cb = X.add_over(l, il)
      +H2 = X.add(H1, WU.U64{X.b32(cb), 0})
      +L = X.add(l, il)
      ST.step_value(64n, SW.value(lo), SW.value(hi), SW.value(ml), SW.value(mh), SW.value(il), SW.value(ih), SW.value(l), SW.value(h), SW.value(T), SW.value(H), SW.value(H1), SW.value(L), S.bit_value(cb), SW.value(H2), SR.value128(P.P{hi, lo}), SR.value128(P.P{mh, ml}), SR.value128(P.P{ih, il}), {==}, {==}, {==},
        h1, fT(hi, lo, ml, mh), fS(h, T), fS(H, ih), fV(H1, cb), M128.add_split(l, il), M128.fit64(L), M128.fit64(H2))

def m128(+a: WU.U64, +b: WU.U64) -> {Nat.add(SW.value(X.pfst(X.mul128(a, b))), C.shift(64n, SW.value(X.psnd(X.mul128(a, b))))) == Nat.mul(SW.value(a), SW.value(b)) : Nat}:
  match a b:
    case WU.U64{+al, +ah} WU.U64{+bl, +bh}:
      M128.m128_value(al, ah, bl, bh)
