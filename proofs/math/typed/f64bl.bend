import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/u64.bend as WU
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/u32.bend as U
import ../natural/bits.bend as BT
import ./width.bend as WW
import ./u32laws.bend as LW
import ./w64add.bend as WA
import ./w64sh.bend as SH
import ./natcmp.bend as NC

# Bit lengths and 64-bit words of naturals, for the f64 proofs.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def lbits(+k: Nat, +n: Nat) -> {F.low_bits(k, n) == C.low(k, n) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      +e1 = Equal.cong(Nat, Nat, z => Nat.add(z, Nat.double(F.low_bits(p, Nat.div(n, 2n)))), Nat.mod(n, 2n), C.bit(n), Equal.sym(Nat, C.bit(n), Nat.mod(n, 2n), WW.bit_mod(n)))
      +e2 = Equal.cong(Nat, Nat, z => Nat.add(C.bit(n), Nat.double(F.low_bits(p, z))), Nat.div(n, 2n), C.half(n), Equal.sym(Nat, C.half(n), Nat.div(n, 2n), WA.half_div(n)))
      +e3 = Equal.cong(Nat, Nat, z => Nat.add(C.bit(n), Nat.double(z)), F.low_bits(p, C.half(n)), C.low(p, C.half(n)), lbits(p, C.half(n)))
      Equal.trans(Nat, Nat.add(Nat.mod(n, 2n), Nat.double(F.low_bits(p, Nat.div(n, 2n)))), Nat.add(C.bit(n), Nat.double(F.low_bits(p, Nat.div(n, 2n)))), Nat.add(C.bit(n), Nat.double(C.low(p, C.half(n)))), e1, Equal.trans(Nat, Nat.add(C.bit(n), Nat.double(F.low_bits(p, Nat.div(n, 2n)))), Nat.add(C.bit(n), Nat.double(F.low_bits(p, C.half(n)))), Nat.add(C.bit(n), Nat.double(C.low(p, C.half(n)))), e2, e3))

def hbits(+k: Nat, +n: Nat) -> {F.high_bits(k, n) == C.high(k, n) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.trans(Nat, F.high_bits(p, Nat.div(n, 2n)), F.high_bits(p, C.half(n)), C.high(p, C.half(n)), Equal.cong(Nat, Nat, z => F.high_bits(p, z), Nat.div(n, 2n), C.half(n), Equal.sym(Nat, C.half(n), Nat.div(n, 2n), WA.half_div(n))), hbits(p, C.half(n)))

def wval(+n: Nat, +h64: {C.fits(64n, n) == True{} : Bool}) -> {SW.value(WU.U64{U32.from_nat(F.low_bits(32n, n)), U32.from_nat(F.high_bits(32n, n))}) == n : Nat}:
  +el = Equal.trans(Nat, v(U32.from_nat(F.low_bits(32n, n))), v(U32.from_nat(C.low(32n, n))), C.low(32n, n), Equal.cong(Nat, Nat, z => v(U32.from_nat(z)), F.low_bits(32n, n), C.low(32n, n), lbits(32n, n)), LW.vo(C.low(32n, n), WW.low_fits(32n, n)))
  +eh = Equal.trans(Nat, v(U32.from_nat(F.high_bits(32n, n))), v(U32.from_nat(C.high(32n, n))), C.high(32n, n), Equal.cong(Nat, Nat, z => v(U32.from_nat(z)), F.high_bits(32n, n), C.high(32n, n), hbits(32n, n)), LW.vo(C.high(32n, n), SH.fits_high(32n, 32n, n, h64)))
  Equal.trans(Nat, Nat.add(v(U32.from_nat(F.low_bits(32n, n))), C.shift(32n, v(U32.from_nat(F.high_bits(32n, n))))), Nat.add(C.low(32n, n), C.shift(32n, v(U32.from_nat(F.high_bits(32n, n))))), n, Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(32n, v(U32.from_nat(F.high_bits(32n, n))))), v(U32.from_nat(F.low_bits(32n, n))), C.low(32n, n), el), Equal.trans(Nat, Nat.add(C.low(32n, n), C.shift(32n, v(U32.from_nat(F.high_bits(32n, n))))), Nat.add(C.low(32n, n), C.shift(32n, C.high(32n, n))), n, Equal.cong(Nat, Nat, z => Nat.add(C.low(32n, n), C.shift(32n, z)), v(U32.from_nat(F.high_bits(32n, n))), C.high(32n, n), eh), Equal.sym(Nat, n, Nat.add(C.low(32n, n), C.shift(32n, C.high(32n, n))), WW.low_high(32n, n))))

# ---- the bit length of a nonzero n below 2^K ----

def bl_le_n(+K: Nat, +n: Nat, +hn: {C.fits(K, n) == True{} : Bool}, +hp: {Nat.is_le(C.pow2(1n+K), C.pow2(M.bit_length(n))) == True{} : Bool}) -> {False{} == True{} : Bool}:
  match n:
    case 0n:
      +h0 = BT.bit_length_zero()
      +hp2 = L.subst(Nat, z => {Nat.is_le(C.pow2(1n+K), C.pow2(z)) == True{} : Bool}, M.bit_length(0n), 0n, h0, hp)
      Equal.trans(Bool, False{}, Nat.is_le(C.pow2(1n+K), 1n), True{}, Equal.sym(Bool, Nat.is_le(C.pow2(1n+K), 1n), False{}, N.lt_not_le(1n, C.pow2(1n+K), N.le_lt_trans(1n, C.pow2(K), C.pow2(1n+K), N.pow2_pos(K), N.pow2_lt_succ(K)))), hp2)
    case 1n+ +np:
      +hd = N.double_lt(1n+np, C.pow2(K), WW.lt_of_fits(K, 1n+np, hn))
      +P = C.pow2(1n+K)
      Equal.trans(Bool, False{}, Nat.is_lt(P, P), True{}, Equal.sym(Bool, Nat.is_lt(P, P), False{}, N.lt_irrefl(P)), N.le_lt_trans(P, Nat.double(1n+np), P, N.le_trans(P, C.pow2(M.bit_length(1n+np)), Nat.double(1n+np), hp, BT.bit_length_le(np)), hd))

def bl_le(+K: Nat, +n: Nat, +hn: {C.fits(K, n) == True{} : Bool}, +c: Bool, +hc: {Nat.is_le(M.bit_length(n), K) == c : Bool}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      +hk = N.lt_succ_le_succ(K, M.bit_length(n), N.not_le_lt(M.bit_length(n), K, hc))
      +hp = N.pow2_mono(1n+K, M.bit_length(n), hk)
      bl_le_n(K, n, hn, hp)


def bl_pos(+n: Nat, +hz: {Nat.is_eq(n, 0n) == False{} : Bool}, +c: Nat, +hc: {M.bit_length(n) == c : Nat}) -> {Nat.is_le(1n, c) == True{} : Bool}:
  match c:
    case 0n:
      +h0 = L.subst(Nat, z => {Nat.is_lt(n, C.pow2(z)) == True{} : Bool}, M.bit_length(n), 0n, hc, BT.bit_length_lt(n))
      +e0 = U.lt_one_zero(n, h0)
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, LW.true_ne_false(Equal.trans(Bool, True{}, Nat.is_eq(n, 0n), False{}, Equal.sym(Bool, Nat.is_eq(n, 0n), True{}, L.subst(Nat, z => {Nat.is_eq(z, 0n) == True{} : Bool}, 0n, n, Equal.sym(Nat, n, 0n, e0), {==})), hz)))
    case 1n+ +cp:
      N.zero_le(cp)

def dle(+a: Nat, +c: Nat, +h: {Nat.is_le(Nat.double(a), Nat.double(c)) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(a, c), Nat.is_le(Nat.double(a), Nat.double(c)), True{}, Equal.cong(Cmp, Bool, t => Cmp.is_le(t), Nat.cmp(a, c), Nat.cmp(Nat.double(a), Nat.double(c)), Equal.sym(Cmp, Nat.cmp(Nat.double(a), Nat.double(c)), Nat.cmp(a, c), NC.cmp_dbl(a, c))), h)

def lower(+n: Nat, +hz: {Nat.is_eq(n, 0n) == False{} : Bool}) -> {Nat.is_le(C.pow2(Nat.sub(M.bit_length(n), 1n)), n) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_le(C.pow2(Nat.sub(M.bit_length(0n), 1n)), 0n) == True{} : Bool}, LW.true_ne_false(hz))
    case 1n+ +np:
      +B = M.bit_length(1n+np)
      +eb = N.sub_add(B, 1n, bl_pos(1n+np, hz, B, {==}))
      +h1 = L.subst(Nat, z => {Nat.is_le(C.pow2(z), Nat.double(1n+np)) == True{} : Bool}, B, 1n+Nat.sub(B, 1n), Equal.sym(Nat, 1n+Nat.sub(B, 1n), B, eb), BT.bit_length_le(np))
      dle(C.pow2(Nat.sub(B, 1n)), 1n+np, h1)

