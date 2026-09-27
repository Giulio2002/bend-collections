import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/generic.bend as SG
import ../../../spec/math/fixed.bend as SF
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../../src/math/fixed.bend as F
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/list.bend as LL
import ../../lib/u32.bend as U3
import ../../lib/u32div.bend as UD
import ./width.bend as WW
import ./w64add.bend as WA
import ./w64sh.bend as SH
import ./shrn.bend as SHN
import ./u32laws.bend as LW
import ./u64laws.bend as LV
import ./fixgen.bend as G
import ./fix32.bend as P32

# to_bytes / from_bytes (Python int.to_bytes / int.from_bytes, Rust
# to_le_bytes / from_le_bytes) for U32 and U64 against spec/math/fixed.bend:
# byte k is the base-256 digit low(8, high(8k, x)); parsing is Horner's
# rule b0 + 256 (b1 + 256 (...)) with every partial value bounded by
# 2^(8j), so no step overflows; digits split at any byte boundary
# (Mathlib Nat.digits_append).

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def con_eq(+x: Nat, +y: Nat, xs: List<&2, Nat>, ys: List<&2, Nat>, +ex: {x == y : Nat}, +ets: {xs == ys : List<&2, Nat>}) -> {Con{x, xs} == Con{y, ys} : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, Con{x, xs}, Con{y, xs}, Con{y, ys}, Equal.cong(Nat, List<&2, Nat>, t => Con{t, xs}, x, y, ex), Equal.cong(List<&2, Nat>, List<&2, Nat>, t => Con{y, t}, xs, ys, ets))

# ---- to_bytes ----

def byte_v(+x: U32, +k: Nat) -> {v(F.byte32(x, k)) == C.low(8n, C.high(Nat.mul(8n, k), v(x))) : Nat}:
  +y = U32.shrn(x, Nat.mul(8n, k))
  Equal.trans(Nat, v(U32.mod(y, 256)), Nat.mod(v(y), 256n), C.low(8n, C.high(Nat.mul(8n, k), v(x))), UD.mod_nat(y, 256, {==}), Equal.trans(Nat, Nat.mod(v(y), 256n), Nat.mod(C.high(Nat.mul(8n, k), v(x)), 256n), C.low(8n, C.high(Nat.mul(8n, k), v(x))), Equal.cong(Nat, Nat, t => Nat.mod(t, 256n), v(y), C.high(Nat.mul(8n, k), v(x)), SHN.shrn_high(x, Nat.mul(8n, k))), Equal.sym(Nat, C.low(8n, C.high(Nat.mul(8n, k), v(x))), Nat.mod(C.high(Nat.mul(8n, k), v(x)), 256n), G.low_mod(8n, C.high(Nat.mul(8n, k), v(x)), 255n, {==}))))

def to_le32(+x: U32) -> {SF.nats(F.u32_to_bytes_le(x)) == SF.le_digits(4n, v(x)) : List<&2, Nat>}:
  con_eq(v(F.byte32(x, 0n)), C.low(8n, v(x)), [v(F.byte32(x, 1n)), v(F.byte32(x, 2n)), v(F.byte32(x, 3n))], SF.le_digits(3n, C.high(8n, v(x))), byte_v(x, 0n),
    con_eq(v(F.byte32(x, 1n)), C.low(8n, C.high(8n, v(x))), [v(F.byte32(x, 2n)), v(F.byte32(x, 3n))], SF.le_digits(2n, C.high(8n, C.high(8n, v(x)))), byte_v(x, 1n),
      con_eq(v(F.byte32(x, 2n)), C.low(8n, C.high(8n, C.high(8n, v(x)))), [v(F.byte32(x, 3n))], SF.le_digits(1n, C.high(8n, C.high(8n, C.high(8n, v(x))))), byte_v(x, 2n),
        con_eq(v(F.byte32(x, 3n)), C.low(8n, C.high(8n, C.high(8n, C.high(8n, v(x))))), [], [], byte_v(x, 3n), {==}))))

def to_be32(+x: U32) -> {SF.nats(F.u32_to_bytes_be(x)) == C.reverse(Nat, SF.le_digits(4n, v(x))) : List<&2, Nat>}:
  con_eq(v(F.byte32(x, 3n)), C.low(8n, C.high(8n, C.high(8n, C.high(8n, v(x))))), [v(F.byte32(x, 2n)), v(F.byte32(x, 1n)), v(F.byte32(x, 0n))], [C.low(8n, C.high(8n, C.high(8n, v(x)))), C.low(8n, C.high(8n, v(x))), C.low(8n, v(x))], byte_v(x, 3n),
    con_eq(v(F.byte32(x, 2n)), C.low(8n, C.high(8n, C.high(8n, v(x)))), [v(F.byte32(x, 1n)), v(F.byte32(x, 0n))], [C.low(8n, C.high(8n, v(x))), C.low(8n, v(x))], byte_v(x, 2n),
      con_eq(v(F.byte32(x, 1n)), C.low(8n, C.high(8n, v(x))), [v(F.byte32(x, 0n))], [C.low(8n, v(x))], byte_v(x, 1n),
        con_eq(v(F.byte32(x, 0n)), C.low(8n, v(x)), [], [], byte_v(x, 0n), {==}))))

def u32_to_le(+a: U32) -> SF.ToBytes.le(~U32, ~SG.u32_val, ~F.u32_to_bytes_le, 4n, a):
  to_le32(a)

def u32_to_be(+a: U32) -> SF.ToBytes.be(~U32, ~SG.u32_val, ~F.u32_to_bytes_be, 4n, a):
  to_be32(a)

# ---- from_bytes: one Horner digit at a time ----

# every value in r fits k bits
def bnd(+k: Nat, r: Maybe<&2, Nat>) -> Bool:
  match r:
    case Some{+n}:
      C.fits(k, n)
    case None{}:
      True{}

def fb(+b: U32) -> {C.fits(8n, v(b)) == F.is_byte(b) : Bool}:
  Equal.trans(Bool, C.fits(8n, v(b)), Nat.is_lt(v(b), 256n), F.is_byte(b), WW.fits_lt(8n, v(b)), Equal.sym(Bool, U32.is_lt(b, 256), Nat.is_lt(v(b), 256n), U3.is_lt_nat(b, 256)))

# b + 256 z fits 8 + k bits (Horner's step)
def step_fits(+k: Nat, +b: Nat, +z: Nat, +hb: {C.fits(8n, b) == True{} : Bool}, +hz: {C.fits(k, z) == True{} : Bool}) -> {C.fits(Nat.add(8n, k), Nat.add(b, C.shift(8n, z))) == True{} : Bool}:
  WW.limbs_fit(8n, k, b, z, hb, hz)

def to32(+k: Nat, +hk: {Nat.is_le(Nat.add(8n, k), 32n) == True{} : Bool}, +n: Nat, +h: {C.fits(Nat.add(8n, k), n) == True{} : Bool}) -> {C.fits(32n, n) == True{} : Bool}:
  SH.fits_mono(Nat.add(8n, k), 32n, n, hk, h)

def step32(+k: Nat, +hk: {Nat.is_le(Nat.add(8n, k), 32n) == True{} : Bool}, +z: U32, +hz: {C.fits(k, v(z)) == True{} : Bool}, +b: U32, +hb: {C.fits(8n, v(b)) == True{} : Bool}) -> {v(U32.add(b, U32.mul(z, 256))) == Nat.add(v(b), C.shift(8n, v(z))) : Nat}:
  +sz = C.shift(8n, v(z))
  +f0 = Equal.trans(Bool, C.fits(32n, sz), C.fits(32n, Nat.add(0n, sz)), True{}, Equal.cong(Nat, Bool, t => C.fits(32n, t), sz, Nat.add(0n, sz), Equal.sym(Nat, Nat.add(0n, sz), sz, P32.zero_add(sz))), to32(k, hk, Nat.add(0n, sz), step_fits(k, 0n, v(z), {==}, hz)))
  +em = Equal.trans(Nat, v(U32.mul(z, 256)), C.low(32n, Nat.mul(v(z), 256n)), sz, P32.mul_low(z, 256), Equal.trans(Nat, C.low(32n, Nat.mul(v(z), 256n)), C.low(32n, sz), sz, Equal.cong(Nat, Nat, t => C.low(32n, t), Nat.mul(v(z), 256n), sz, Equal.sym(Nat, sz, Nat.mul(v(z), 256n), WW.shift_mul(8n, v(z)))), WW.low_fit(32n, sz, f0)))
  +ea = Equal.trans(Nat, v(U32.add(b, U32.mul(z, 256))), C.low(32n, Nat.add(v(b), v(U32.mul(z, 256)))), C.low(32n, Nat.add(v(b), sz)), P32.add_low(b, U32.mul(z, 256)), Equal.cong(Nat, Nat, t => C.low(32n, Nat.add(v(b), t)), v(U32.mul(z, 256)), sz, em))
  Equal.trans(Nat, v(U32.add(b, U32.mul(z, 256))), C.low(32n, Nat.add(v(b), sz)), Nat.add(v(b), sz), ea, WW.low_fit(32n, Nat.add(v(b), sz), to32(k, hk, Nat.add(v(b), sz), step_fits(k, v(b), v(z), hb, hz))))

def d32_some(+k: Nat, +hk: {Nat.is_le(Nat.add(8n, k), 32n) == True{} : Bool}, +z: U32, +hz: {C.fits(k, v(z)) == True{} : Bool}, +b: U32, +c: Bool, +hc: {F.is_byte(b) == c : Bool}) -> {SF.mval(~U32, ~SG.u32_val, F.dig32(Some{z}, c, b)) == SF.digit_on(Some{v(z)}, C.fits(8n, v(b)), v(b)) : Maybe<&2, Nat>}:
  match c:
    case True{}:
      +hb = Equal.trans(Bool, C.fits(8n, v(b)), F.is_byte(b), True{}, fb(b), hc)
      %Equal.sym(Bool, C.fits(8n, v(b)), True{}, hb) : {SF.mval(~U32, ~SG.u32_val, F.dig32(Some{z}, True{}, b)) == SF.digit_on(Some{v(z)}, _, v(b)) : Maybe<&2, Nat>}
      Equal.cong(Nat, Maybe<&2, Nat>, t => Some{t}, v(U32.add(b, U32.mul(z, 256))), Nat.add(v(b), C.shift(8n, v(z))), step32(k, hk, z, hz, b, hb))
    case False{}:
      +hb = Equal.trans(Bool, C.fits(8n, v(b)), F.is_byte(b), False{}, fb(b), hc)
      %Equal.sym(Bool, C.fits(8n, v(b)), False{}, hb) : {SF.mval(~U32, ~SG.u32_val, F.dig32(Some{z}, False{}, b)) == SF.digit_on(Some{v(z)}, _, v(b)) : Maybe<&2, Nat>}
      {==}

def d32_sbnd(+k: Nat, +hk: {Nat.is_le(Nat.add(8n, k), 32n) == True{} : Bool}, +z: U32, +hz: {C.fits(k, v(z)) == True{} : Bool}, +b: U32, +c: Bool, +hc: {F.is_byte(b) == c : Bool}) -> {bnd(Nat.add(8n, k), SF.mval(~U32, ~SG.u32_val, F.dig32(Some{z}, c, b))) == True{} : Bool}:
  match c:
    case True{}:
      +hb = Equal.trans(Bool, C.fits(8n, v(b)), F.is_byte(b), True{}, fb(b), hc)
      %Equal.sym(Nat, v(U32.add(b, U32.mul(z, 256))), Nat.add(v(b), C.shift(8n, v(z))), step32(k, hk, z, hz, b, hb)) : {C.fits(Nat.add(8n, k), _) == True{} : Bool}
      step_fits(k, v(b), v(z), hb, hz)
    case False{}:
      {==}

def d32_val(+k: Nat, +hk: {Nat.is_le(Nat.add(8n, k), 32n) == True{} : Bool}, r: Maybe<&2, U32>, +hr: {bnd(k, SF.mval(~U32, ~SG.u32_val, r)) == True{} : Bool}, +b: U32) -> {SF.mval(~U32, ~SG.u32_val, F.dig32(r, F.is_byte(b), b)) == SF.digit_on(SF.mval(~U32, ~SG.u32_val, r), C.fits(8n, v(b)), v(b)) : Maybe<&2, Nat>}:
  match r:
    case Some{+z}:
      d32_some(k, hk, z, hr, b, F.is_byte(b), {==})
    case None{}:
      {==}

def d32_bnd(+k: Nat, +hk: {Nat.is_le(Nat.add(8n, k), 32n) == True{} : Bool}, r: Maybe<&2, U32>, +hr: {bnd(k, SF.mval(~U32, ~SG.u32_val, r)) == True{} : Bool}, +b: U32) -> {bnd(Nat.add(8n, k), SF.mval(~U32, ~SG.u32_val, F.dig32(r, F.is_byte(b), b))) == True{} : Bool}:
  match r:
    case Some{+z}:
      d32_sbnd(k, hk, z, hr, b, F.is_byte(b), {==})
    case None{}:
      {==}

def from4_ok(+b0: U32, +b1: U32, +b2: U32, +b3: U32) -> {SF.mval(~U32, ~SG.u32_val, F.from4(b0, b1, b2, b3)) == SF.from_le(4n, [v(b0), v(b1), v(b2), v(b3)]) : Maybe<&2, Nat>}:
  +r0 = {Some{0} : Maybe<&2, U32>}
  +r1 = F.dig32(r0, F.is_byte(b3), b3)
  +r2 = F.dig32(r1, F.is_byte(b2), b2)
  +r3 = F.dig32(r2, F.is_byte(b1), b1)
  +M0 = SF.mval(~U32, ~SG.u32_val, r0)
  +M1 = SF.mval(~U32, ~SG.u32_val, r1)
  +M2 = SF.mval(~U32, ~SG.u32_val, r2)
  +M3 = SF.mval(~U32, ~SG.u32_val, r3)
  +f0 = C.fits(8n, v(b0))
  +f1 = C.fits(8n, v(b1))
  +f2 = C.fits(8n, v(b2))
  +f3 = C.fits(8n, v(b3))
  +bd1 = d32_bnd(0n, {==}, r0, {==}, b3)
  +bd2 = d32_bnd(8n, {==}, r1, bd1, b2)
  +bd3 = d32_bnd(16n, {==}, r2, bd2, b1)
  +S1 = SF.digit_on(M0, f3, v(b3))
  +S2 = SF.digit_on(S1, f2, v(b2))
  +S3 = SF.digit_on(S2, f1, v(b1))
  +e1 = d32_val(0n, {==}, r0, {==}, b3)
  +e2 = Equal.trans(Maybe<&2, Nat>, M2, SF.digit_on(M1, f2, v(b2)), S2, d32_val(8n, {==}, r1, bd1, b2), Equal.cong(Maybe<&2, Nat>, Maybe<&2, Nat>, t => SF.digit_on(t, f2, v(b2)), M1, S1, e1))
  +e3 = Equal.trans(Maybe<&2, Nat>, M3, SF.digit_on(M2, f1, v(b1)), S3, d32_val(16n, {==}, r2, bd2, b1), Equal.cong(Maybe<&2, Nat>, Maybe<&2, Nat>, t => SF.digit_on(t, f1, v(b1)), M2, S2, e2))
  Equal.trans(Maybe<&2, Nat>, SF.mval(~U32, ~SG.u32_val, F.dig32(r3, F.is_byte(b0), b0)), SF.digit_on(M3, f0, v(b0)), SF.digit_on(S3, f0, v(b0)), d32_val(24n, {==}, r3, bd3, b0), Equal.cong(Maybe<&2, Nat>, Maybe<&2, Nat>, t => SF.digit_on(t, f0, v(b0)), M3, S3, e3))

# any other length parses to None
def fl_len(+k: Nat, xs: List<&2, Nat>, +h: {Nat.is_eq(C.length(Nat, xs), k) == False{} : Bool}) -> {SF.from_le(k, xs) == None{} : Maybe<&2, Nat>}:
  match k xs:
    case 0n Nil{}:
      Empty.absurd({SF.from_le(0n, Nil{}) == None{} : Maybe<&2, Nat>}, L.true_false(h))
    case 0n Con{+x, t}:
      {==}
    case 1n+ +p Nil{}:
      {==}
    case 1n+ +p Con{+x, t}:
      %Equal.sym(Maybe<&2, Nat>, SF.from_le(p, t), None{}, fl_len(p, t, h)) : {SF.digit_on(_, C.fits(8n, x), x) == None{} : Maybe<&2, Nat>}
      {==}

def rev_none(+k: Nat, +xs: List<&2, Nat>, +h: {Nat.is_eq(C.length(Nat, xs), k) == False{} : Bool}) -> {SF.from_le(k, C.reverse(Nat, xs)) == None{} : Maybe<&2, Nat>}:
  fl_len(k, C.reverse(Nat, xs), Equal.trans(Bool, Nat.is_eq(C.length(Nat, C.reverse(Nat, xs)), k), Nat.is_eq(C.length(Nat, xs), k), False{}, Equal.cong(Nat, Bool, t => Nat.is_eq(t, k), C.length(Nat, C.reverse(Nat, xs)), C.length(Nat, xs), LL.length_rev(Nat, xs)), h))

# the list cases: exactly four bytes, or None on both sides
def fle4(+b0: U32, +b1: U32, +b2: U32, +b3: U32, t: List<&2, U32>) -> {SF.mval(~U32, ~SG.u32_val, F.u32_from_bytes_le(Con{b0, Con{b1, Con{b2, Con{b3, t}}}})) == SF.from_le(4n, SF.nats(Con{b0, Con{b1, Con{b2, Con{b3, t}}}})) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      from4_ok(b0, b1, b2, b3)
    case Con{+b4, t5}:
      {==}

def fle3(+b0: U32, +b1: U32, +b2: U32, t: List<&2, U32>) -> {SF.mval(~U32, ~SG.u32_val, F.u32_from_bytes_le(Con{b0, Con{b1, Con{b2, t}}})) == SF.from_le(4n, SF.nats(Con{b0, Con{b1, Con{b2, t}}})) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+b3, t4}:
      fle4(b0, b1, b2, b3, t4)

def fle2(+b0: U32, +b1: U32, t: List<&2, U32>) -> {SF.mval(~U32, ~SG.u32_val, F.u32_from_bytes_le(Con{b0, Con{b1, t}})) == SF.from_le(4n, SF.nats(Con{b0, Con{b1, t}})) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+b2, t3}:
      fle3(b0, b1, b2, t3)

def fle1(+b0: U32, t: List<&2, U32>) -> {SF.mval(~U32, ~SG.u32_val, F.u32_from_bytes_le(Con{b0, t})) == SF.from_le(4n, SF.nats(Con{b0, t})) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+b1, t2}:
      fle2(b0, b1, t2)

def u32_from_le(bs: List<&2, U32>) -> SF.FromBytes.le(~U32, ~SG.u32_val, ~F.u32_from_bytes_le, 4n, bs):
  match bs:
    case Nil{}:
      {==}
    case Con{+b0, t}:
      fle1(b0, t)

def fbe4(+b3: U32, +b2: U32, +b1: U32, +b0: U32, t: List<&2, U32>) -> {SF.mval(~U32, ~SG.u32_val, F.u32_from_bytes_be(Con{b3, Con{b2, Con{b1, Con{b0, t}}}})) == SF.from_le(4n, C.reverse(Nat, SF.nats(Con{b3, Con{b2, Con{b1, Con{b0, t}}}}))) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      from4_ok(b0, b1, b2, b3)
    case Con{+b4, t5}:
      Equal.sym(Maybe<&2, Nat>, SF.from_le(4n, C.reverse(Nat, SF.nats(Con{b3, Con{b2, Con{b1, Con{b0, Con{b4, t5}}}}}))), None{}, rev_none(4n, SF.nats(Con{b3, Con{b2, Con{b1, Con{b0, Con{b4, t5}}}}}), {==}))

def fbe3(+b3: U32, +b2: U32, +b1: U32, t: List<&2, U32>) -> {SF.mval(~U32, ~SG.u32_val, F.u32_from_bytes_be(Con{b3, Con{b2, Con{b1, t}}})) == SF.from_le(4n, C.reverse(Nat, SF.nats(Con{b3, Con{b2, Con{b1, t}}}))) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+b0, t4}:
      fbe4(b3, b2, b1, b0, t4)

def fbe2(+b3: U32, +b2: U32, t: List<&2, U32>) -> {SF.mval(~U32, ~SG.u32_val, F.u32_from_bytes_be(Con{b3, Con{b2, t}})) == SF.from_le(4n, C.reverse(Nat, SF.nats(Con{b3, Con{b2, t}}))) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+b1, t3}:
      fbe3(b3, b2, b1, t3)

def fbe1(+b3: U32, t: List<&2, U32>) -> {SF.mval(~U32, ~SG.u32_val, F.u32_from_bytes_be(Con{b3, t})) == SF.from_le(4n, C.reverse(Nat, SF.nats(Con{b3, t}))) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+b2, t2}:
      fbe2(b3, b2, t2)

def u32_from_be(bs: List<&2, U32>) -> SF.FromBytes.be(~U32, ~SG.u32_val, ~F.u32_from_bytes_be, 4n, bs):
  match bs:
    case Nil{}:
      {==}
    case Con{+b3, t}:
      fbe1(b3, t)

# ---- U64: digits split at the limb boundary ----

def w8(k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+p:
      Nat.add(8n, w8(p))

def fits0(+n: Nat, +h: {C.fits(0n, n) == True{} : Bool}) -> {n == 0n : Nat}:
  N.eq_from_is_eq(n, 0n, h)

def dsplit(+a: Nat, +b: Nat, +lo: Nat, +hi: Nat, +hlo: {C.fits(w8(a), lo) == True{} : Bool}) -> {SF.le_digits(Nat.add(a, b), Nat.add(lo, C.shift(w8(a), hi))) == C.append(Nat, SF.le_digits(a, lo), SF.le_digits(b, hi)) : List<&2, Nat>}:
  match a:
    case 0n:
      %Equal.sym(Nat, lo, 0n, fits0(lo, hlo)) : {SF.le_digits(b, Nat.add(_, hi)) == SF.le_digits(b, hi) : List<&2, Nat>}
      {==}
    case 1n+ +p:
      +Q = C.shift(w8(p), hi)
      +ets = Equal.trans(List<&2, Nat>, SF.le_digits(Nat.add(p, b), C.high(8n, Nat.add(lo, C.shift(8n, Q)))), SF.le_digits(Nat.add(p, b), Nat.add(C.high(8n, lo), Q)), C.append(Nat, SF.le_digits(p, C.high(8n, lo)), SF.le_digits(b, hi)), Equal.cong(Nat, List<&2, Nat>, t => SF.le_digits(Nat.add(p, b), t), C.high(8n, Nat.add(lo, C.shift(8n, Q))), Nat.add(C.high(8n, lo), Q), WW.high_add_shift(8n, lo, Q)), dsplit(p, b, C.high(8n, lo), hi, SH.fits_high(8n, w8(p), lo, hlo)))
      %Equal.sym(Nat, C.shift(Nat.add(8n, w8(p)), hi), C.shift(8n, Q), WW.shift_comp(8n, w8(p), hi)) : {SF.le_digits(Nat.add(1n+p, b), Nat.add(lo, _)) == C.append(Nat, SF.le_digits(1n+p, lo), SF.le_digits(b, hi)) : List<&2, Nat>}
      con_eq(C.low(8n, Nat.add(lo, C.shift(8n, Q))), C.low(8n, lo), SF.le_digits(Nat.add(p, b), C.high(8n, Nat.add(lo, C.shift(8n, Q)))), C.append(Nat, SF.le_digits(p, C.high(8n, lo)), SF.le_digits(b, hi)), WW.low_add_shift(8n, lo, Q), ets)

def u64_to_le(+a: WU.U64) -> SF.ToBytes.le(~WU.U64, ~SG.u64_val, ~F.u64_to_bytes_le, 8n, a):
  match a:
    case WU.U64{+l, +h}:
      +A = SF.nats(F.u32_to_bytes_le(l))
      +B = SF.nats(F.u32_to_bytes_le(h))
      +e1 = Equal.trans(List<&2, Nat>, C.append(Nat, A, B), C.append(Nat, SF.le_digits(4n, v(l)), B), C.append(Nat, SF.le_digits(4n, v(l)), SF.le_digits(4n, v(h))), Equal.cong(List<&2, Nat>, List<&2, Nat>, t => C.append(Nat, t, B), A, SF.le_digits(4n, v(l)), to_le32(l)), Equal.cong(List<&2, Nat>, List<&2, Nat>, t => C.append(Nat, SF.le_digits(4n, v(l)), t), B, SF.le_digits(4n, v(h)), to_le32(h)))
      Equal.trans(List<&2, Nat>, C.append(Nat, A, B), C.append(Nat, SF.le_digits(4n, v(l)), SF.le_digits(4n, v(h))), SF.le_digits(Nat.add(4n, 4n), Nat.add(v(l), C.shift(w8(4n), v(h)))), e1, Equal.sym(List<&2, Nat>, SF.le_digits(Nat.add(4n, 4n), Nat.add(v(l), C.shift(w8(4n), v(h)))), C.append(Nat, SF.le_digits(4n, v(l)), SF.le_digits(4n, v(h))), dsplit(4n, 4n, v(l), v(h), LW.vb(l))))

def u64_to_be(+a: WU.U64) -> SF.ToBytes.be(~WU.U64, ~SG.u64_val, ~F.u64_to_bytes_be, 8n, a):
  match a:
    case WU.U64{+l, +h}:
      +Dl = SF.le_digits(4n, v(l))
      +Dh = SF.le_digits(4n, v(h))
      +A = SF.nats(F.u32_to_bytes_be(h))
      +B = SF.nats(F.u32_to_bytes_be(l))
      +e1 = Equal.trans(List<&2, Nat>, C.append(Nat, A, B), C.append(Nat, C.reverse(Nat, Dh), B), C.append(Nat, C.reverse(Nat, Dh), C.reverse(Nat, Dl)), Equal.cong(List<&2, Nat>, List<&2, Nat>, t => C.append(Nat, t, B), A, C.reverse(Nat, Dh), to_be32(h)), Equal.cong(List<&2, Nat>, List<&2, Nat>, t => C.append(Nat, C.reverse(Nat, Dh), t), B, C.reverse(Nat, Dl), to_be32(l)))
      +e2 = Equal.sym(List<&2, Nat>, C.reverse(Nat, C.append(Nat, Dl, Dh)), C.append(Nat, C.reverse(Nat, Dh), C.reverse(Nat, Dl)), LL.rev_append(Nat, Dl, Dh))
      +e3 = Equal.cong(List<&2, Nat>, List<&2, Nat>, t => C.reverse(Nat, t), C.append(Nat, Dl, Dh), SF.le_digits(Nat.add(4n, 4n), Nat.add(v(l), C.shift(w8(4n), v(h)))), Equal.sym(List<&2, Nat>, SF.le_digits(Nat.add(4n, 4n), Nat.add(v(l), C.shift(w8(4n), v(h)))), C.append(Nat, Dl, Dh), dsplit(4n, 4n, v(l), v(h), LW.vb(l))))
      Equal.trans(List<&2, Nat>, C.append(Nat, A, B), C.append(Nat, C.reverse(Nat, Dh), C.reverse(Nat, Dl)), C.reverse(Nat, SF.le_digits(Nat.add(4n, 4n), Nat.add(v(l), C.shift(w8(4n), v(h))))), e1, Equal.trans(List<&2, Nat>, C.append(Nat, C.reverse(Nat, Dh), C.reverse(Nat, Dl)), C.reverse(Nat, C.append(Nat, Dl, Dh)), C.reverse(Nat, SF.le_digits(Nat.add(4n, 4n), Nat.add(v(l), C.shift(w8(4n), v(h))))), e2, e3))

# ---- U64 from_bytes: Horner's rule on U64 values ----

def to64(+k: Nat, +hk: {Nat.is_le(Nat.add(8n, k), 64n) == True{} : Bool}, +n: Nat, +h: {C.fits(Nat.add(8n, k), n) == True{} : Bool}) -> {C.fits(64n, n) == True{} : Bool}:
  SH.fits_mono(Nat.add(8n, k), 64n, n, hk, h)

def step64(+k: Nat, +hk: {Nat.is_le(Nat.add(8n, k), 64n) == True{} : Bool}, +z: WU.U64, +hz: {C.fits(k, SG.u64_val(z)) == True{} : Bool}, +b: U32, +hb: {C.fits(8n, v(b)) == True{} : Bool}) -> {SG.u64_val(X.add(WU.U64{b, 0}, X.mul(z, WU.U64{256, 0}))) == Nat.add(v(b), C.shift(8n, SG.u64_val(z))) : Nat}:
  +vz = SG.u64_val(z)
  +sz = C.shift(8n, vz)
  +mz = X.mul(z, WU.U64{256, 0})
  +bz = {WU.U64{b, 0} : WU.U64}
  +f0 = Equal.trans(Bool, C.fits(64n, sz), C.fits(64n, Nat.add(0n, sz)), True{}, Equal.cong(Nat, Bool, t => C.fits(64n, t), sz, Nat.add(0n, sz), Equal.sym(Nat, Nat.add(0n, sz), sz, P32.zero_add(sz))), to64(k, hk, Nat.add(0n, sz), step_fits(k, 0n, vz, {==}, hz)))
  +em = Equal.trans(Nat, SG.u64_val(mz), C.low(64n, Nat.mul(vz, 256n)), sz, WA.mul_value(z, WU.U64{256, 0}), Equal.trans(Nat, C.low(64n, Nat.mul(vz, 256n)), C.low(64n, sz), sz, Equal.cong(Nat, Nat, t => C.low(64n, t), Nat.mul(vz, 256n), sz, Equal.sym(Nat, sz, Nat.mul(vz, 256n), WW.shift_mul(8n, vz))), WW.low_fit(64n, sz, f0)))
  +eb2 = Equal.trans(Nat, SG.u64_val(bz), Nat.add(v(b), 0n), v(b), {==}, N.add_zero(v(b)))
  +ea = Equal.trans(Nat, SG.u64_val(X.add(bz, mz)), C.low(64n, Nat.add(SG.u64_val(bz), SG.u64_val(mz))), C.low(64n, Nat.add(v(b), sz)), WA.add_value(bz, mz), Equal.trans(Nat, C.low(64n, Nat.add(SG.u64_val(bz), SG.u64_val(mz))), C.low(64n, Nat.add(v(b), SG.u64_val(mz))), C.low(64n, Nat.add(v(b), sz)), Equal.cong(Nat, Nat, t => C.low(64n, Nat.add(t, SG.u64_val(mz))), SG.u64_val(bz), v(b), eb2), Equal.cong(Nat, Nat, t => C.low(64n, Nat.add(v(b), t)), SG.u64_val(mz), sz, em)))
  Equal.trans(Nat, SG.u64_val(X.add(bz, mz)), C.low(64n, Nat.add(v(b), sz)), Nat.add(v(b), sz), ea, WW.low_fit(64n, Nat.add(v(b), sz), to64(k, hk, Nat.add(v(b), sz), step_fits(k, v(b), vz, hb, hz))))

def d64_some(+k: Nat, +hk: {Nat.is_le(Nat.add(8n, k), 64n) == True{} : Bool}, +z: WU.U64, +hz: {C.fits(k, SG.u64_val(z)) == True{} : Bool}, +b: U32, +c: Bool, +hc: {F.is_byte(b) == c : Bool}) -> {SF.mval(~WU.U64, ~SG.u64_val, F.dig64(Some{z}, c, b)) == SF.digit_on(Some{SG.u64_val(z)}, C.fits(8n, v(b)), v(b)) : Maybe<&2, Nat>}:
  match c:
    case True{}:
      +hb = Equal.trans(Bool, C.fits(8n, v(b)), F.is_byte(b), True{}, fb(b), hc)
      %Equal.sym(Bool, C.fits(8n, v(b)), True{}, hb) : {SF.mval(~WU.U64, ~SG.u64_val, F.dig64(Some{z}, True{}, b)) == SF.digit_on(Some{SG.u64_val(z)}, _, v(b)) : Maybe<&2, Nat>}
      Equal.cong(Nat, Maybe<&2, Nat>, t => Some{t}, SG.u64_val(X.add(WU.U64{b, 0}, X.mul(z, WU.U64{256, 0}))), Nat.add(v(b), C.shift(8n, SG.u64_val(z))), step64(k, hk, z, hz, b, hb))
    case False{}:
      +hb = Equal.trans(Bool, C.fits(8n, v(b)), F.is_byte(b), False{}, fb(b), hc)
      %Equal.sym(Bool, C.fits(8n, v(b)), False{}, hb) : {SF.mval(~WU.U64, ~SG.u64_val, F.dig64(Some{z}, False{}, b)) == SF.digit_on(Some{SG.u64_val(z)}, _, v(b)) : Maybe<&2, Nat>}
      {==}

def d64_sbnd(+k: Nat, +hk: {Nat.is_le(Nat.add(8n, k), 64n) == True{} : Bool}, +z: WU.U64, +hz: {C.fits(k, SG.u64_val(z)) == True{} : Bool}, +b: U32, +c: Bool, +hc: {F.is_byte(b) == c : Bool}) -> {bnd(Nat.add(8n, k), SF.mval(~WU.U64, ~SG.u64_val, F.dig64(Some{z}, c, b))) == True{} : Bool}:
  match c:
    case True{}:
      +hb = Equal.trans(Bool, C.fits(8n, v(b)), F.is_byte(b), True{}, fb(b), hc)
      %Equal.sym(Nat, SG.u64_val(X.add(WU.U64{b, 0}, X.mul(z, WU.U64{256, 0}))), Nat.add(v(b), C.shift(8n, SG.u64_val(z))), step64(k, hk, z, hz, b, hb)) : {C.fits(Nat.add(8n, k), _) == True{} : Bool}
      step_fits(k, v(b), SG.u64_val(z), hb, hz)
    case False{}:
      {==}

def d64_val(+k: Nat, +hk: {Nat.is_le(Nat.add(8n, k), 64n) == True{} : Bool}, r: Maybe<&2, WU.U64>, +hr: {bnd(k, SF.mval(~WU.U64, ~SG.u64_val, r)) == True{} : Bool}, +b: U32) -> {SF.mval(~WU.U64, ~SG.u64_val, F.dig64(r, F.is_byte(b), b)) == SF.digit_on(SF.mval(~WU.U64, ~SG.u64_val, r), C.fits(8n, v(b)), v(b)) : Maybe<&2, Nat>}:
  match r:
    case Some{+z}:
      d64_some(k, hk, z, hr, b, F.is_byte(b), {==})
    case None{}:
      {==}

def d64_bnd(+k: Nat, +hk: {Nat.is_le(Nat.add(8n, k), 64n) == True{} : Bool}, r: Maybe<&2, WU.U64>, +hr: {bnd(k, SF.mval(~WU.U64, ~SG.u64_val, r)) == True{} : Bool}, +b: U32) -> {bnd(Nat.add(8n, k), SF.mval(~WU.U64, ~SG.u64_val, F.dig64(r, F.is_byte(b), b))) == True{} : Bool}:
  match r:
    case Some{+z}:
      d64_sbnd(k, hk, z, hr, b, F.is_byte(b), {==})
    case None{}:
      {==}

# one Horner step on both sides, carrying the bound
def hstep(+k: Nat, +hk: {Nat.is_le(Nat.add(8n, k), 64n) == True{} : Bool}, r: Maybe<&2, WU.U64>, +S: Maybe<&2, Nat>, +es: {SF.mval(~WU.U64, ~SG.u64_val, r) == S : Maybe<&2, Nat>}, +hr: {bnd(k, SF.mval(~WU.U64, ~SG.u64_val, r)) == True{} : Bool}, +b: U32) -> {SF.mval(~WU.U64, ~SG.u64_val, F.dig64(r, F.is_byte(b), b)) == SF.digit_on(S, C.fits(8n, v(b)), v(b)) : Maybe<&2, Nat>}:
  Equal.trans(Maybe<&2, Nat>, SF.mval(~WU.U64, ~SG.u64_val, F.dig64(r, F.is_byte(b), b)), SF.digit_on(SF.mval(~WU.U64, ~SG.u64_val, r), C.fits(8n, v(b)), v(b)), SF.digit_on(S, C.fits(8n, v(b)), v(b)), d64_val(k, hk, r, hr, b), Equal.cong(Maybe<&2, Nat>, Maybe<&2, Nat>, t => SF.digit_on(t, C.fits(8n, v(b)), v(b)), SF.mval(~WU.U64, ~SG.u64_val, r), S, es))

def from8_ok(+b0: U32, +b1: U32, +b2: U32, +b3: U32, +b4: U32, +b5: U32, +b6: U32, +b7: U32) -> {SF.mval(~WU.U64, ~SG.u64_val, F.dig64(F.dig64(F.dig64(F.dig64(F.dig64(F.dig64(F.dig64(F.dig64(Some{WU.U64{0, 0}}, F.is_byte(b7), b7), F.is_byte(b6), b6), F.is_byte(b5), b5), F.is_byte(b4), b4), F.is_byte(b3), b3), F.is_byte(b2), b2), F.is_byte(b1), b1), F.is_byte(b0), b0)) == SF.from_le(8n, [v(b0), v(b1), v(b2), v(b3), v(b4), v(b5), v(b6), v(b7)]) : Maybe<&2, Nat>}:
  +r0 = {Some{WU.U64{0, 0}} : Maybe<&2, WU.U64>}
  +r1 = F.dig64(r0, F.is_byte(b7), b7)
  +r2 = F.dig64(r1, F.is_byte(b6), b6)
  +r3 = F.dig64(r2, F.is_byte(b5), b5)
  +r4 = F.dig64(r3, F.is_byte(b4), b4)
  +r5 = F.dig64(r4, F.is_byte(b3), b3)
  +r6 = F.dig64(r5, F.is_byte(b2), b2)
  +r7 = F.dig64(r6, F.is_byte(b1), b1)
  +S0 = {Some{0n} : Maybe<&2, Nat>}
  +S1 = SF.digit_on(S0, C.fits(8n, v(b7)), v(b7))
  +S2 = SF.digit_on(S1, C.fits(8n, v(b6)), v(b6))
  +S3 = SF.digit_on(S2, C.fits(8n, v(b5)), v(b5))
  +S4 = SF.digit_on(S3, C.fits(8n, v(b4)), v(b4))
  +S5 = SF.digit_on(S4, C.fits(8n, v(b3)), v(b3))
  +S6 = SF.digit_on(S5, C.fits(8n, v(b2)), v(b2))
  +S7 = SF.digit_on(S6, C.fits(8n, v(b1)), v(b1))
  +c1 = d64_bnd(0n, {==}, r0, {==}, b7)
  +c2 = d64_bnd(8n, {==}, r1, c1, b6)
  +c3 = d64_bnd(16n, {==}, r2, c2, b5)
  +c4 = d64_bnd(24n, {==}, r3, c3, b4)
  +c5 = d64_bnd(32n, {==}, r4, c4, b3)
  +c6 = d64_bnd(40n, {==}, r5, c5, b2)
  +c7 = d64_bnd(48n, {==}, r6, c6, b1)
  +e1 = hstep(0n, {==}, r0, S0, {==}, {==}, b7)
  +e2 = hstep(8n, {==}, r1, S1, e1, c1, b6)
  +e3 = hstep(16n, {==}, r2, S2, e2, c2, b5)
  +e4 = hstep(24n, {==}, r3, S3, e3, c3, b4)
  +e5 = hstep(32n, {==}, r4, S4, e4, c4, b3)
  +e6 = hstep(40n, {==}, r5, S5, e5, c5, b2)
  +e7 = hstep(48n, {==}, r6, S6, e6, c6, b1)
  hstep(56n, {==}, r7, S7, e7, c7, b0)

# the list cases at U64: exactly eight bytes, or None on both sides

def gle8(+x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32, t: List<&2, U32>) -> {SF.mval(~WU.U64, ~SG.u64_val, F.u64_from_bytes_le(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, t}}}}}}}})) == SF.from_le(8n, SF.nats(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, t}}}}}}}})) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      from8_ok(x0, x1, x2, x3, x4, x5, x6, x7)
    case Con{+x8, t9}:
      {==}

def gle7(+x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, t: List<&2, U32>) -> {SF.mval(~WU.U64, ~SG.u64_val, F.u64_from_bytes_le(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, t}}}}}}})) == SF.from_le(8n, SF.nats(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, t}}}}}}})) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+x7, tn}:
      gle8(x0, x1, x2, x3, x4, x5, x6, x7, tn)

def gle6(+x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, t: List<&2, U32>) -> {SF.mval(~WU.U64, ~SG.u64_val, F.u64_from_bytes_le(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, t}}}}}})) == SF.from_le(8n, SF.nats(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, t}}}}}})) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+x6, tn}:
      gle7(x0, x1, x2, x3, x4, x5, x6, tn)

def gle5(+x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32, t: List<&2, U32>) -> {SF.mval(~WU.U64, ~SG.u64_val, F.u64_from_bytes_le(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, t}}}}})) == SF.from_le(8n, SF.nats(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, t}}}}})) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+x5, tn}:
      gle6(x0, x1, x2, x3, x4, x5, tn)

def gle4(+x0: U32, +x1: U32, +x2: U32, +x3: U32, t: List<&2, U32>) -> {SF.mval(~WU.U64, ~SG.u64_val, F.u64_from_bytes_le(Con{x0, Con{x1, Con{x2, Con{x3, t}}}})) == SF.from_le(8n, SF.nats(Con{x0, Con{x1, Con{x2, Con{x3, t}}}})) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+x4, tn}:
      gle5(x0, x1, x2, x3, x4, tn)

def gle3(+x0: U32, +x1: U32, +x2: U32, t: List<&2, U32>) -> {SF.mval(~WU.U64, ~SG.u64_val, F.u64_from_bytes_le(Con{x0, Con{x1, Con{x2, t}}})) == SF.from_le(8n, SF.nats(Con{x0, Con{x1, Con{x2, t}}})) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+x3, tn}:
      gle4(x0, x1, x2, x3, tn)

def gle2(+x0: U32, +x1: U32, t: List<&2, U32>) -> {SF.mval(~WU.U64, ~SG.u64_val, F.u64_from_bytes_le(Con{x0, Con{x1, t}})) == SF.from_le(8n, SF.nats(Con{x0, Con{x1, t}})) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+x2, tn}:
      gle3(x0, x1, x2, tn)

def gle1(+x0: U32, t: List<&2, U32>) -> {SF.mval(~WU.U64, ~SG.u64_val, F.u64_from_bytes_le(Con{x0, t})) == SF.from_le(8n, SF.nats(Con{x0, t})) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+x1, tn}:
      gle2(x0, x1, tn)

def u64_from_le(bs: List<&2, U32>) -> SF.FromBytes.le(~WU.U64, ~SG.u64_val, ~F.u64_from_bytes_le, 8n, bs):
  match bs:
    case Nil{}:
      {==}
    case Con{+x0, t}:
      gle1(x0, t)

def gbe8(+x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32, t: List<&2, U32>) -> {SF.mval(~WU.U64, ~SG.u64_val, F.u64_from_bytes_be(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, t}}}}}}}})) == SF.from_le(8n, C.reverse(Nat, SF.nats(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, t}}}}}}}}))) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      from8_ok(x7, x6, x5, x4, x3, x2, x1, x0)
    case Con{+x8, t9}:
      Equal.sym(Maybe<&2, Nat>, SF.from_le(8n, C.reverse(Nat, SF.nats(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, t9}}}}}}}}}))), None{}, rev_none(8n, SF.nats(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, t9}}}}}}}}}), {==}))

def gbe7(+x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, t: List<&2, U32>) -> {SF.mval(~WU.U64, ~SG.u64_val, F.u64_from_bytes_be(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, t}}}}}}})) == SF.from_le(8n, C.reverse(Nat, SF.nats(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, t}}}}}}}))) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+x7, tn}:
      gbe8(x0, x1, x2, x3, x4, x5, x6, x7, tn)

def gbe6(+x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, t: List<&2, U32>) -> {SF.mval(~WU.U64, ~SG.u64_val, F.u64_from_bytes_be(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, t}}}}}})) == SF.from_le(8n, C.reverse(Nat, SF.nats(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, t}}}}}}))) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+x6, tn}:
      gbe7(x0, x1, x2, x3, x4, x5, x6, tn)

def gbe5(+x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32, t: List<&2, U32>) -> {SF.mval(~WU.U64, ~SG.u64_val, F.u64_from_bytes_be(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, t}}}}})) == SF.from_le(8n, C.reverse(Nat, SF.nats(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, t}}}}}))) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+x5, tn}:
      gbe6(x0, x1, x2, x3, x4, x5, tn)

def gbe4(+x0: U32, +x1: U32, +x2: U32, +x3: U32, t: List<&2, U32>) -> {SF.mval(~WU.U64, ~SG.u64_val, F.u64_from_bytes_be(Con{x0, Con{x1, Con{x2, Con{x3, t}}}})) == SF.from_le(8n, C.reverse(Nat, SF.nats(Con{x0, Con{x1, Con{x2, Con{x3, t}}}}))) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+x4, tn}:
      gbe5(x0, x1, x2, x3, x4, tn)

def gbe3(+x0: U32, +x1: U32, +x2: U32, t: List<&2, U32>) -> {SF.mval(~WU.U64, ~SG.u64_val, F.u64_from_bytes_be(Con{x0, Con{x1, Con{x2, t}}})) == SF.from_le(8n, C.reverse(Nat, SF.nats(Con{x0, Con{x1, Con{x2, t}}}))) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+x3, tn}:
      gbe4(x0, x1, x2, x3, tn)

def gbe2(+x0: U32, +x1: U32, t: List<&2, U32>) -> {SF.mval(~WU.U64, ~SG.u64_val, F.u64_from_bytes_be(Con{x0, Con{x1, t}})) == SF.from_le(8n, C.reverse(Nat, SF.nats(Con{x0, Con{x1, t}}))) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+x2, tn}:
      gbe3(x0, x1, x2, tn)

def gbe1(+x0: U32, t: List<&2, U32>) -> {SF.mval(~WU.U64, ~SG.u64_val, F.u64_from_bytes_be(Con{x0, t})) == SF.from_le(8n, C.reverse(Nat, SF.nats(Con{x0, t}))) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+x1, tn}:
      gbe2(x0, x1, tn)

def u64_from_be(bs: List<&2, U32>) -> SF.FromBytes.be(~WU.U64, ~SG.u64_val, ~F.u64_from_bytes_be, 8n, bs):
  match bs:
    case Nil{}:
      {==}
    case Con{+x0, t}:
      gbe1(x0, t)
