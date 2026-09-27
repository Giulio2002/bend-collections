import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/generic.bend as SG
import ../../../spec/math/fixed.bend as SF
import ../../../spec/math/number.bend as SN
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../../src/math/fixed.bend as F
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/u32div.bend as UD
import ../natural/arith.bend as R
import ./width.bend as WW
import ./shrn.bend as SHN
import ./u32laws.bend as LW
import ./fixgen.bend as G

# bit_count (Python int.bit_count, Rust count_ones) for U32 and U64 against
# spec/math/number.bend's ones(w, n): the 1 bits of n split at any width
# (ones(a + b, n) == ones(a, n) + ones(b, n >> a), Mathlib Nat.bits_append),
# depend only on the low a bits, and a nibble's count is the 16-entry table.

# ---- ones over a split ----

def bit_bit(+n: Nat) -> {C.bit(C.bit(n)) == C.bit(n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+ +q:
      bit_bit(q)

def half_bit(+n: Nat) -> {C.half(C.bit(n)) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+ +q:
      half_bit(q)

# only the a low bits count
def ones_low(+a: Nat, +n: Nat) -> {SN.ones(a, C.low(a, n)) == SN.ones(a, n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+ +p:
      +y = C.low(p, C.half(n))
      +eb = Equal.trans(Nat, C.bit(Nat.add(C.bit(n), Nat.double(y))), C.bit(C.bit(n)), C.bit(n), WW.bit_dbl(C.bit(n), y), bit_bit(n))
      +eh = Equal.trans(Nat, C.half(Nat.add(C.bit(n), Nat.double(y))), Nat.add(C.half(C.bit(n)), y), y, WW.half_dbl(C.bit(n), y), Equal.cong(Nat, Nat, t => Nat.add(t, y), C.half(C.bit(n)), 0n, half_bit(n)))
      %Equal.sym(Nat, C.bit(Nat.add(C.bit(n), Nat.double(y))), C.bit(n), eb) : {Nat.add(_, SN.ones(p, C.half(Nat.add(C.bit(n), Nat.double(y))))) == Nat.add(C.bit(n), SN.ones(p, C.half(n))) : Nat}
      %Equal.sym(Nat, C.half(Nat.add(C.bit(n), Nat.double(y))), y, eh) : {Nat.add(C.bit(n), SN.ones(p, _)) == Nat.add(C.bit(n), SN.ones(p, C.half(n))) : Nat}
      Equal.cong(Nat, Nat, t => Nat.add(C.bit(n), t), SN.ones(p, y), SN.ones(p, C.half(n)), ones_low(p, C.half(n)))

def ones_add(+a: Nat, +b: Nat, +n: Nat) -> {SN.ones(Nat.add(a, b), n) == Nat.add(SN.ones(a, n), SN.ones(b, C.high(a, n))) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(0n, SN.ones(b, n)), SN.ones(b, n), Equal.trans(Nat, Nat.add(0n, SN.ones(b, n)), Nat.add(SN.ones(b, n), 0n), SN.ones(b, n), N.add_comm(0n, SN.ones(b, n)), N.add_zero(SN.ones(b, n))))
    case 1n+ +p:
      +ih = ones_add(p, b, C.half(n))
      Equal.trans(Nat, Nat.add(C.bit(n), SN.ones(Nat.add(p, b), C.half(n))), Nat.add(C.bit(n), Nat.add(SN.ones(p, C.half(n)), SN.ones(b, C.high(p, C.half(n))))), Nat.add(Nat.add(C.bit(n), SN.ones(p, C.half(n))), SN.ones(b, C.high(p, C.half(n)))), Equal.cong(Nat, Nat, t => Nat.add(C.bit(n), t), SN.ones(Nat.add(p, b), C.half(n)), Nat.add(SN.ones(p, C.half(n)), SN.ones(b, C.high(p, C.half(n)))), ih), Equal.sym(Nat, Nat.add(Nat.add(C.bit(n), SN.ones(p, C.half(n))), SN.ones(b, C.high(p, C.half(n)))), Nat.add(C.bit(n), Nat.add(SN.ones(p, C.half(n)), SN.ones(b, C.high(p, C.half(n))))), N.add_assoc(C.bit(n), SN.ones(p, C.half(n)), SN.ones(b, C.high(p, C.half(n))))))

# ---- U32: a nibble at a time ----

def ones4_eq(+n: Nat, +h: {Nat.is_lt(n, 16n) == True{} : Bool}) -> {F.ones4(n) == SN.ones(4n, n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      {==}
    case 15n:
      {==}
    case 16n+m:
      Empty.absurd({F.ones4(16n+m) == SN.ones(4n, 16n+m) : Nat}, N.lt_zero_absurd(m, h))

def nib_low(+x: U32) -> {U32.to_nat(U32.mod(x, 16)) == C.low(4n, U32.to_nat(x)) : Nat}:
  Equal.trans(Nat, U32.to_nat(U32.mod(x, 16)), Nat.mod(U32.to_nat(x), 16n), C.low(4n, U32.to_nat(x)), UD.mod_nat(x, 16, {==}), Equal.sym(Nat, C.low(4n, U32.to_nat(x)), Nat.mod(U32.to_nat(x), 16n), G.low_mod(4n, U32.to_nat(x), 15n, {==})))

def nib_ones(+x: U32) -> {F.ones4(U32.to_nat(U32.mod(x, 16))) == SN.ones(4n, U32.to_nat(x)) : Nat}:
  +hl = Equal.trans(Bool, Nat.is_lt(U32.to_nat(U32.mod(x, 16)), 16n), Nat.is_lt(Nat.mod(U32.to_nat(x), 16n), 16n), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(t, 16n), U32.to_nat(U32.mod(x, 16)), Nat.mod(U32.to_nat(x), 16n), UD.mod_nat(x, 16, {==})), R.dm_lt(15n, U32.to_nat(x)))
  Equal.trans(Nat, F.ones4(U32.to_nat(U32.mod(x, 16))), SN.ones(4n, U32.to_nat(U32.mod(x, 16))), SN.ones(4n, U32.to_nat(x)), ones4_eq(U32.to_nat(U32.mod(x, 16)), hl), Equal.trans(Nat, SN.ones(4n, U32.to_nat(U32.mod(x, 16))), SN.ones(4n, C.low(4n, U32.to_nat(x))), SN.ones(4n, U32.to_nat(x)), Equal.cong(Nat, Nat, t => SN.ones(4n, t), U32.to_nat(U32.mod(x, 16)), C.low(4n, U32.to_nat(x)), nib_low(x)), ones_low(4n, U32.to_nat(x))))

# 4 k
def q4(k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+p:
      Nat.add(4n, q4(p))

def bc_go(+k: Nat, +x: U32) -> {F.u32_bc_go(k, x) == SN.ones(q4(k), U32.to_nat(x)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      +vx = U32.to_nat(x)
      +ih = Equal.trans(Nat, F.u32_bc_go(p, U32.shrn(x, 4n)), SN.ones(q4(p), U32.to_nat(U32.shrn(x, 4n))), SN.ones(q4(p), C.high(4n, vx)), bc_go(p, U32.shrn(x, 4n)), Equal.cong(Nat, Nat, t => SN.ones(q4(p), t), U32.to_nat(U32.shrn(x, 4n)), C.high(4n, vx), SHN.shrn_high(x, 4n)))
      +e1 = Equal.cong(Nat, Nat, t => Nat.add(t, F.u32_bc_go(p, U32.shrn(x, 4n))), F.ones4(U32.to_nat(U32.mod(x, 16))), SN.ones(4n, vx), nib_ones(x))
      +e2 = Equal.cong(Nat, Nat, t => Nat.add(SN.ones(4n, vx), t), F.u32_bc_go(p, U32.shrn(x, 4n)), SN.ones(q4(p), C.high(4n, vx)), ih)
      Equal.trans(Nat, Nat.add(F.ones4(U32.to_nat(U32.mod(x, 16))), F.u32_bc_go(p, U32.shrn(x, 4n))), Nat.add(SN.ones(4n, vx), F.u32_bc_go(p, U32.shrn(x, 4n))), SN.ones(Nat.add(4n, q4(p)), vx), e1, Equal.trans(Nat, Nat.add(SN.ones(4n, vx), F.u32_bc_go(p, U32.shrn(x, 4n))), Nat.add(SN.ones(4n, vx), SN.ones(q4(p), C.high(4n, vx))), SN.ones(Nat.add(4n, q4(p)), vx), e2, Equal.sym(Nat, SN.ones(Nat.add(4n, q4(p)), vx), Nat.add(SN.ones(4n, vx), SN.ones(q4(p), C.high(4n, vx))), ones_add(4n, q4(p), vx))))

def u32_bit_count(+a: U32) -> SF.BitCount.value(~U32, ~SG.u32_val, ~F.u32_bit_count, 32n, a):
  bc_go(8n, a)

# ---- U64: the two limbs ----

def u64_bit_count(+a: WU.U64) -> SF.BitCount.value(~WU.U64, ~SG.u64_val, ~F.u64_bit_count, 64n, a):
  match a:
    case WU.U64{+l, +h}:
      +vl = U32.to_nat(l)
      +vh = U32.to_nat(h)
      +n = Nat.add(vl, C.shift(32n, vh))
      +e1 = Equal.trans(Nat, SN.ones(32n, vl), SN.ones(32n, C.low(32n, n)), SN.ones(32n, n), Equal.cong(Nat, Nat, t => SN.ones(32n, t), vl, C.low(32n, n), Equal.sym(Nat, C.low(32n, n), vl, WW.low_u(32n, vl, vh, LW.vb(l)))), ones_low(32n, n))
      +e2 = Equal.cong(Nat, Nat, t => SN.ones(32n, t), vh, C.high(32n, n), Equal.sym(Nat, C.high(32n, n), vh, WW.high_u(32n, vl, vh, LW.vb(l))))
      +e3 = Equal.trans(Nat, Nat.add(F.u32_bit_count(l), F.u32_bit_count(h)), Nat.add(SN.ones(32n, vl), F.u32_bit_count(h)), Nat.add(SN.ones(32n, vl), SN.ones(32n, vh)), Equal.cong(Nat, Nat, t => Nat.add(t, F.u32_bit_count(h)), F.u32_bit_count(l), SN.ones(32n, vl), bc_go(8n, l)), Equal.cong(Nat, Nat, t => Nat.add(SN.ones(32n, vl), t), F.u32_bit_count(h), SN.ones(32n, vh), bc_go(8n, h)))
      +e4 = Equal.trans(Nat, Nat.add(SN.ones(32n, vl), SN.ones(32n, vh)), Nat.add(SN.ones(32n, n), SN.ones(32n, vh)), Nat.add(SN.ones(32n, n), SN.ones(32n, C.high(32n, n))), Equal.cong(Nat, Nat, t => Nat.add(t, SN.ones(32n, vh)), SN.ones(32n, vl), SN.ones(32n, n), e1), Equal.cong(Nat, Nat, t => Nat.add(SN.ones(32n, n), t), SN.ones(32n, vh), SN.ones(32n, C.high(32n, n)), e2))
      Equal.trans(Nat, Nat.add(F.u32_bit_count(l), F.u32_bit_count(h)), Nat.add(SN.ones(32n, n), SN.ones(32n, C.high(32n, n))), SN.ones(Nat.add(32n, 32n), n), Equal.trans(Nat, Nat.add(F.u32_bit_count(l), F.u32_bit_count(h)), Nat.add(SN.ones(32n, vl), SN.ones(32n, vh)), Nat.add(SN.ones(32n, n), SN.ones(32n, C.high(32n, n))), e3, e4), Equal.sym(Nat, SN.ones(Nat.add(32n, 32n), n), Nat.add(SN.ones(32n, n), SN.ones(32n, C.high(32n, n))), ones_add(32n, 32n, n)))
