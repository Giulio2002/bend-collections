import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ./width.bend as WW
import ./u32laws.bend as LW
import ./w64add.bend as WA
import ./f64bits.bend as FB
import ./natcmp.bend as NC
import ./w64sh.bend as SH
import ../../lib/u32.bend as U
import ../../lib/u32half.bend as UH
import ../../lib/u32alg.bend as A
import ../../lib/word.bend as WD
import ../../lib/lemmas/spec/numeric.bend as S
import ../../../src/math/natural.bend as M
import ../natural/bits.bend as BT

# Rounding to nearest, ties to even, on binary64: the lemmas behind
# SoftFloat's roundPackToF64. A rounding by k bits depends only on the
# quotient and on how the remainder compares with half the divisor, so
# jamming the bits below the rounding point into one sticky bit keeps the
# result (the sticky-bit argument of Flocq's Round_NE / inbetween theory,
# Boldo and Melquiond; Goldberg, "What every computer scientist should know
# about floating-point arithmetic", 1991). The pattern of a finite double
# is (s * 2^11 + field) * 2^52 + fraction, one integer N below 2^63 with
# the sign on top: bits(s, N).

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# ---- a double as sign and a 63-bit integer ----

def bits(+s: Bool, +n: Nat) -> F.F64:
  F.Bits{U32.from_nat(C.low(32n, n)), U32.from_nat(Nat.add(C.high(32n, n), C.shift(31n, SF.b2n(s))))}

def enc_bits(+s: Bool, +ef: Nat, +f: Nat) -> {SF.encode(s, ef, f) == bits(s, Nat.add(f, C.shift(52n, ef))) : F.F64}:
  +t = C.shift(20n, ef)
  +n = Nat.add(f, C.shift(52n, ef))
  +b = C.shift(31n, SF.b2n(s))
  +e52 = WW.shift_comp(32n, 20n, ef)
  +el = Equal.trans(Nat, C.low(32n, n), C.low(32n, Nat.add(f, C.shift(32n, t))), C.low(32n, f), Equal.cong(Nat, Nat, z => C.low(32n, Nat.add(f, z)), C.shift(52n, ef), C.shift(32n, t), e52), WW.low_add_shift(32n, f, t))
  +eh0 = Equal.trans(Nat, C.high(32n, n), C.high(32n, Nat.add(f, C.shift(32n, t))), Nat.add(C.high(32n, f), t), Equal.cong(Nat, Nat, z => C.high(32n, Nat.add(f, z)), C.shift(52n, ef), C.shift(32n, t), e52), WW.high_add_shift(32n, f, t))
  +eh = Equal.trans(Nat, Nat.add(C.high(32n, n), b), Nat.add(Nat.add(C.high(32n, f), t), b), Nat.add(C.high(32n, f), C.shift(20n, Nat.add(ef, C.shift(11n, SF.b2n(s))))), Equal.cong(Nat, Nat, z => Nat.add(z, b), C.high(32n, n), Nat.add(C.high(32n, f), t), eh0), FB.fold(C.high(32n, f), ef, SF.b2n(s)))
  +e = Equal.trans(F.F64, bits(s, n), F.Bits{U32.from_nat(C.low(32n, f)), U32.from_nat(Nat.add(C.high(32n, n), b))}, SF.encode(s, ef, f), Equal.cong(Nat, F.F64, z => F.Bits{U32.from_nat(z), U32.from_nat(Nat.add(C.high(32n, n), b))}, C.low(32n, n), C.low(32n, f), el), Equal.cong(Nat, F.F64, z => F.Bits{U32.from_nat(C.low(32n, f)), U32.from_nat(z)}, Nat.add(C.high(32n, n), b), Nat.add(C.high(32n, f), C.shift(20n, Nat.add(ef, C.shift(11n, SF.b2n(s))))), eh))
  Equal.sym(F.F64, bits(s, n), SF.encode(s, ef, f), e)

# ---- rounding by k bits depends on the quotient and a comparison ----

def rne_c(+q: Nat, +c: Cmp) -> Nat:
  Nat.add(q, SF.b2n(Bool.or(Cmp.is_lt(SF.flip(c)), Bool.and(Cmp.is_eq(c), Nat.is_eq(Nat.mod(q, 2n), 1n)))))

def rne_cmp(+q: Nat, +r: Nat, +h: Nat) -> {SF.rne_up(q, r, h) == rne_c(q, Nat.cmp(r, h)) : Nat}:
  Equal.cong(Cmp, Nat, t => Nat.add(q, SF.b2n(Bool.or(Cmp.is_lt(t), Bool.and(Cmp.is_eq(Nat.cmp(r, h)), Nat.is_eq(Nat.mod(q, 2n), 1n))))), Nat.cmp(h, r), SF.flip(Nat.cmp(r, h)), Equal.sym(Cmp, SF.flip(Nat.cmp(r, h)), Nat.cmp(h, r), NC.cmp_flip(r, h)))

def lex_assoc(+x: Cmp, +y: Cmp, +z: Cmp) -> {NC.lex(NC.lex(x, y), z) == NC.lex(x, NC.lex(y, z)) : Cmp}:
  match x:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def fz(+d: Nat) -> {C.fits(d, 0n) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+ +p:
      fz(p)

def small(+t: Nat, +ht: {Nat.is_le(t, 1n) == True{} : Bool}) -> {C.fits(1n, t) == True{} : Bool}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+ +q:
      NC.absurd_tf({C.fits(1n, 2n+q) == True{} : Bool}, ht)

def bit_small(+t: Nat, +ht: {Nat.is_le(t, 1n) == True{} : Bool}) -> {C.bit(t) == t : Nat}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+ +q:
      NC.absurd_tf({C.bit(2n+q) == 2n+q : Nat}, ht)

def half_small(+t: Nat, +ht: {Nat.is_le(t, 1n) == True{} : Bool}) -> {C.half(t) == 0n : Nat}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+ +q:
      NC.absurd_tf({C.half(2n+q) == 0n : Nat}, ht)

def max_le1(+b: Nat, +l: Nat, +hb: {Nat.is_le(b, 1n) == True{} : Bool}) -> {Nat.is_le(Nat.max(b, Nat.min(l, 1n)), 1n) == True{} : Bool}:
  match b l:
    case 0n 0n:
      {==}
    case 0n 1n+ +lp:
      match lp:
        case 0n:
          {==}
        case 1n+ +lq:
          {==}
    case 1n 0n:
      {==}
    case 1n 1n+ +lp:
      match lp:
        case 0n:
          {==}
        case 1n+ +lq:
          {==}
    case 2n+ +q _:
      NC.absurd_tf({Nat.is_le(Nat.max(2n+q, Nat.min(l, 1n)), 1n) == True{} : Bool}, hb)

# the sticky bit merges the parity bit with "some lower bit is set"
def tl(+b: Nat, +l: Nat, +hb: {Nat.is_le(b, 1n) == True{} : Bool}) -> {NC.lex(Nat.cmp(b, 0n), Nat.cmp(l, 0n)) == Nat.cmp(Nat.max(b, Nat.min(l, 1n)), 0n) : Cmp}:
  match b l:
    case 0n 0n:
      {==}
    case 0n 1n+ +lp:
      {==}
    case 1n 0n:
      {==}
    case 1n 1n+ +lp:
      {==}
    case 2n+ +q _:
      NC.absurd_tf({NC.lex(Nat.cmp(2n+q, 0n), Nat.cmp(l, 0n)) == Nat.cmp(Nat.max(2n+q, Nat.min(l, 1n)), 0n) : Cmp}, hb)

# jam(H, L) is H with bit 0 replaced by t = max(bit H, [L > 0])
def jam_form(+h: Nat, +l: Nat) -> {SW.jam(h, l) == Nat.add(Nat.max(C.bit(h), Nat.min(l, 1n)), Nat.double(C.half(h))) : Nat}:
  +t = Nat.max(C.bit(h), Nat.min(l, 1n))
  +e1 = Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(2n, z), Nat.max(Nat.mod(h, 2n), Nat.min(l, 1n))), Nat.div(h, 2n), C.half(h), Equal.sym(Nat, C.half(h), Nat.div(h, 2n), WA.half_div(h)))
  +e2 = Equal.cong(Nat, Nat, z => Nat.add(z, Nat.max(Nat.mod(h, 2n), Nat.min(l, 1n))), Nat.mul(2n, C.half(h)), Nat.double(C.half(h)), Equal.sym(Nat, Nat.double(C.half(h)), Nat.mul(2n, C.half(h)), NA.double_mul(C.half(h))))
  +e3 = Equal.cong(Nat, Nat, z => Nat.add(Nat.double(C.half(h)), Nat.max(z, Nat.min(l, 1n))), Nat.mod(h, 2n), C.bit(h), Equal.sym(Nat, C.bit(h), Nat.mod(h, 2n), WW.bit_mod(h)))
  +e4 = NA.add_comm(Nat.double(C.half(h)), t)
  Equal.trans(Nat, SW.jam(h, l), Nat.add(Nat.mul(2n, C.half(h)), Nat.max(Nat.mod(h, 2n), Nat.min(l, 1n))), Nat.add(t, Nat.double(C.half(h))), e1, Equal.trans(Nat, Nat.add(Nat.mul(2n, C.half(h)), Nat.max(Nat.mod(h, 2n), Nat.min(l, 1n))), Nat.add(Nat.double(C.half(h)), Nat.max(Nat.mod(h, 2n), Nat.min(l, 1n))), Nat.add(t, Nat.double(C.half(h))), e2, Equal.trans(Nat, Nat.add(Nat.double(C.half(h)), Nat.max(Nat.mod(h, 2n), Nat.min(l, 1n))), Nat.add(Nat.double(C.half(h)), t), Nat.add(t, Nat.double(C.half(h))), e3, e4)))

# rounding m by K + D bits is rounding jam(m >> D, m mod 2^D) by K bits, K >= 2
def sticky(+i: Nat, +D: Nat, +m: Nat) -> {SF.rne(m, Nat.add(2n+i, D)) == SF.rne(SW.jam(C.high(D, m), C.low(D, m)), 2n+i) : Nat}:
  +eA = NA.add_comm(D, 2n+i)
  +qm = Equal.trans(Nat, C.high(Nat.add(2n+i, D), m), C.high(Nat.add(D, 2n+i), m), C.high(2n+i, C.high(D, m)), Equal.cong(Nat, Nat, z => C.high(z, m), Nat.add(2n+i, D), Nat.add(D, 2n+i), Equal.sym(Nat, Nat.add(D, 2n+i), Nat.add(2n+i, D), eA)), WW.high_comp(2n+i, D, m))
  +rm = Equal.trans(Nat, C.low(Nat.add(2n+i, D), m), C.low(Nat.add(D, 2n+i), m), Nat.add(C.low(D, m), C.shift(D, C.low(2n+i, C.high(D, m)))), Equal.cong(Nat, Nat, z => C.low(z, m), Nat.add(2n+i, D), Nat.add(D, 2n+i), Equal.sym(Nat, Nat.add(D, 2n+i), Nat.add(2n+i, D), eA)), FB.low_split(D, 2n+i, m))
  +hm = Equal.trans(Nat, C.shift(Nat.add(1n+i, D), 1n), C.shift(Nat.add(D, 1n+i), 1n), C.shift(D, C.shift(1n+i, 1n)), Equal.cong(Nat, Nat, z => C.shift(z, 1n), Nat.add(1n+i, D), Nat.add(D, 1n+i), NA.add_comm(1n+i, D)), WW.shift_comp(D, 1n+i, 1n))
  +c1 = Equal.trans(Cmp, Nat.cmp(C.low(Nat.add(2n+i, D), m), C.shift(Nat.add(1n+i, D), 1n)), Nat.cmp(Nat.add(C.low(D, m), C.shift(D, C.low(2n+i, C.high(D, m)))), C.shift(Nat.add(1n+i, D), 1n)), Nat.cmp(Nat.add(C.low(D, m), C.shift(D, C.low(2n+i, C.high(D, m)))), C.shift(D, C.shift(1n+i, 1n))), Equal.cong(Nat, Cmp, z => Nat.cmp(z, C.shift(Nat.add(1n+i, D), 1n)), C.low(Nat.add(2n+i, D), m), Nat.add(C.low(D, m), C.shift(D, C.low(2n+i, C.high(D, m)))), rm), Equal.cong(Nat, Cmp, z => Nat.cmp(Nat.add(C.low(D, m), C.shift(D, C.low(2n+i, C.high(D, m)))), z), C.shift(Nat.add(1n+i, D), 1n), C.shift(D, C.shift(1n+i, 1n)), hm))
  +c2 = NC.cmp_limbs(D, C.low(D, m), C.low(2n+i, C.high(D, m)), 0n, C.shift(1n+i, 1n), WW.low_fits(D, m), fz(D))
  +c3 = Equal.cong(Cmp, Cmp, z => NC.lex(z, Nat.cmp(C.low(D, m), 0n)), Nat.cmp(C.low(2n+i, C.high(D, m)), C.shift(1n+i, 1n)), NC.lex(Nat.cmp(C.low(1n+i, C.half(C.high(D, m))), C.shift(i, 1n)), Nat.cmp(C.bit(C.high(D, m)), 0n)), NC.cmp_limbs(1n, C.bit(C.high(D, m)), C.low(1n+i, C.half(C.high(D, m))), 0n, C.shift(i, 1n), small(C.bit(C.high(D, m)), WW.bit_le1(C.high(D, m))), fz(1n)))
  +c4 = lex_assoc(Nat.cmp(C.low(1n+i, C.half(C.high(D, m))), C.shift(i, 1n)), Nat.cmp(C.bit(C.high(D, m)), 0n), Nat.cmp(C.low(D, m), 0n))
  +c5 = Equal.cong(Cmp, Cmp, z => NC.lex(Nat.cmp(C.low(1n+i, C.half(C.high(D, m))), C.shift(i, 1n)), z), NC.lex(Nat.cmp(C.bit(C.high(D, m)), 0n), Nat.cmp(C.low(D, m), 0n)), Nat.cmp(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), 0n), tl(C.bit(C.high(D, m)), C.low(D, m), WW.bit_le1(C.high(D, m))))
  +cm = Equal.trans(Cmp, Nat.cmp(C.low(Nat.add(2n+i, D), m), C.shift(Nat.add(1n+i, D), 1n)), Nat.cmp(Nat.add(C.low(D, m), C.shift(D, C.low(2n+i, C.high(D, m)))), C.shift(D, C.shift(1n+i, 1n))), NC.lex(Nat.cmp(C.low(1n+i, C.half(C.high(D, m))), C.shift(i, 1n)), Nat.cmp(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), 0n)), c1, Equal.trans(Cmp, Nat.cmp(Nat.add(C.low(D, m), C.shift(D, C.low(2n+i, C.high(D, m)))), C.shift(D, C.shift(1n+i, 1n))), NC.lex(Nat.cmp(C.low(2n+i, C.high(D, m)), C.shift(1n+i, 1n)), Nat.cmp(C.low(D, m), 0n)), NC.lex(Nat.cmp(C.low(1n+i, C.half(C.high(D, m))), C.shift(i, 1n)), Nat.cmp(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), 0n)), c2, Equal.trans(Cmp, NC.lex(Nat.cmp(C.low(2n+i, C.high(D, m)), C.shift(1n+i, 1n)), Nat.cmp(C.low(D, m), 0n)), NC.lex(NC.lex(Nat.cmp(C.low(1n+i, C.half(C.high(D, m))), C.shift(i, 1n)), Nat.cmp(C.bit(C.high(D, m)), 0n)), Nat.cmp(C.low(D, m), 0n)), NC.lex(Nat.cmp(C.low(1n+i, C.half(C.high(D, m))), C.shift(i, 1n)), Nat.cmp(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), 0n)), c3, Equal.trans(Cmp, NC.lex(NC.lex(Nat.cmp(C.low(1n+i, C.half(C.high(D, m))), C.shift(i, 1n)), Nat.cmp(C.bit(C.high(D, m)), 0n)), Nat.cmp(C.low(D, m), 0n)), NC.lex(Nat.cmp(C.low(1n+i, C.half(C.high(D, m))), C.shift(i, 1n)), NC.lex(Nat.cmp(C.bit(C.high(D, m)), 0n), Nat.cmp(C.low(D, m), 0n))), NC.lex(Nat.cmp(C.low(1n+i, C.half(C.high(D, m))), C.shift(i, 1n)), Nat.cmp(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), 0n)), c4, c5))))
  +lhs = Equal.trans(Nat, SF.rne_up(C.high(Nat.add(2n+i, D), m), C.low(Nat.add(2n+i, D), m), C.shift(Nat.add(1n+i, D), 1n)), rne_c(C.high(Nat.add(2n+i, D), m), Nat.cmp(C.low(Nat.add(2n+i, D), m), C.shift(Nat.add(1n+i, D), 1n))), rne_c(C.high(2n+i, C.high(D, m)), NC.lex(Nat.cmp(C.low(1n+i, C.half(C.high(D, m))), C.shift(i, 1n)), Nat.cmp(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), 0n))), rne_cmp(C.high(Nat.add(2n+i, D), m), C.low(Nat.add(2n+i, D), m), C.shift(Nat.add(1n+i, D), 1n)), Equal.trans(Nat, rne_c(C.high(Nat.add(2n+i, D), m), Nat.cmp(C.low(Nat.add(2n+i, D), m), C.shift(Nat.add(1n+i, D), 1n))), rne_c(C.high(2n+i, C.high(D, m)), Nat.cmp(C.low(Nat.add(2n+i, D), m), C.shift(Nat.add(1n+i, D), 1n))), rne_c(C.high(2n+i, C.high(D, m)), NC.lex(Nat.cmp(C.low(1n+i, C.half(C.high(D, m))), C.shift(i, 1n)), Nat.cmp(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), 0n))), Equal.cong(Nat, Nat, z => rne_c(z, Nat.cmp(C.low(Nat.add(2n+i, D), m), C.shift(Nat.add(1n+i, D), 1n))), C.high(Nat.add(2n+i, D), m), C.high(2n+i, C.high(D, m)), qm), Equal.cong(Cmp, Nat, z => rne_c(C.high(2n+i, C.high(D, m)), z), Nat.cmp(C.low(Nat.add(2n+i, D), m), C.shift(Nat.add(1n+i, D), 1n)), NC.lex(Nat.cmp(C.low(1n+i, C.half(C.high(D, m))), C.shift(i, 1n)), Nat.cmp(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), 0n)), cm)))
  +jf = jam_form(C.high(D, m), C.low(D, m))
  +hbt = max_le1(C.bit(C.high(D, m)), C.low(D, m), WW.bit_le1(C.high(D, m)))
  +hJ = Equal.trans(Nat, C.half(SW.jam(C.high(D, m), C.low(D, m))), C.half(Nat.add(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), Nat.double(C.half(C.high(D, m))))), C.half(C.high(D, m)), Equal.cong(Nat, Nat, z => C.half(z), SW.jam(C.high(D, m), C.low(D, m)), Nat.add(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), Nat.double(C.half(C.high(D, m)))), jf), Equal.trans(Nat, C.half(Nat.add(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), Nat.double(C.half(C.high(D, m))))), Nat.add(C.half(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n))), C.half(C.high(D, m))), C.half(C.high(D, m)), WW.half_dbl(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), C.half(C.high(D, m))), Equal.cong(Nat, Nat, z => Nat.add(z, C.half(C.high(D, m))), C.half(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n))), 0n, half_small(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), hbt))))
  +bJ = Equal.trans(Nat, C.bit(SW.jam(C.high(D, m), C.low(D, m))), C.bit(Nat.add(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), Nat.double(C.half(C.high(D, m))))), Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), Equal.cong(Nat, Nat, z => C.bit(z), SW.jam(C.high(D, m), C.low(D, m)), Nat.add(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), Nat.double(C.half(C.high(D, m)))), jf), Equal.trans(Nat, C.bit(Nat.add(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), Nat.double(C.half(C.high(D, m))))), C.bit(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n))), Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), WW.bit_dbl(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), C.half(C.high(D, m))), bit_small(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), hbt)))
  +qJ = Equal.cong(Nat, Nat, z => C.high(1n+i, z), C.half(SW.jam(C.high(D, m), C.low(D, m))), C.half(C.high(D, m)), hJ)
  +lJ = Equal.trans(Nat, Nat.add(C.bit(SW.jam(C.high(D, m), C.low(D, m))), Nat.double(C.low(1n+i, C.half(SW.jam(C.high(D, m), C.low(D, m)))))), Nat.add(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), Nat.double(C.low(1n+i, C.half(SW.jam(C.high(D, m), C.low(D, m)))))), Nat.add(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), Nat.double(C.low(1n+i, C.half(C.high(D, m))))), Equal.cong(Nat, Nat, z => Nat.add(z, Nat.double(C.low(1n+i, C.half(SW.jam(C.high(D, m), C.low(D, m)))))), C.bit(SW.jam(C.high(D, m), C.low(D, m))), Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), bJ), Equal.cong(Nat, Nat, z => Nat.add(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), Nat.double(C.low(1n+i, z))), C.half(SW.jam(C.high(D, m), C.low(D, m))), C.half(C.high(D, m)), hJ))
  +cJ = Equal.trans(Cmp, Nat.cmp(C.low(2n+i, SW.jam(C.high(D, m), C.low(D, m))), C.shift(1n+i, 1n)), Nat.cmp(Nat.add(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), Nat.double(C.low(1n+i, C.half(C.high(D, m))))), C.shift(1n+i, 1n)), NC.lex(Nat.cmp(C.low(1n+i, C.half(C.high(D, m))), C.shift(i, 1n)), Nat.cmp(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), 0n)), Equal.cong(Nat, Cmp, z => Nat.cmp(z, C.shift(1n+i, 1n)), C.low(2n+i, SW.jam(C.high(D, m), C.low(D, m))), Nat.add(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), Nat.double(C.low(1n+i, C.half(C.high(D, m))))), lJ), NC.cmp_limbs(1n, Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), C.low(1n+i, C.half(C.high(D, m))), 0n, C.shift(i, 1n), small(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), hbt), fz(1n)))
  +rhs = Equal.trans(Nat, SF.rne_up(C.high(2n+i, SW.jam(C.high(D, m), C.low(D, m))), C.low(2n+i, SW.jam(C.high(D, m), C.low(D, m))), C.shift(1n+i, 1n)), rne_c(C.high(2n+i, SW.jam(C.high(D, m), C.low(D, m))), Nat.cmp(C.low(2n+i, SW.jam(C.high(D, m), C.low(D, m))), C.shift(1n+i, 1n))), rne_c(C.high(2n+i, C.high(D, m)), NC.lex(Nat.cmp(C.low(1n+i, C.half(C.high(D, m))), C.shift(i, 1n)), Nat.cmp(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), 0n))), rne_cmp(C.high(2n+i, SW.jam(C.high(D, m), C.low(D, m))), C.low(2n+i, SW.jam(C.high(D, m), C.low(D, m))), C.shift(1n+i, 1n)), Equal.trans(Nat, rne_c(C.high(2n+i, SW.jam(C.high(D, m), C.low(D, m))), Nat.cmp(C.low(2n+i, SW.jam(C.high(D, m), C.low(D, m))), C.shift(1n+i, 1n))), rne_c(C.high(2n+i, C.high(D, m)), Nat.cmp(C.low(2n+i, SW.jam(C.high(D, m), C.low(D, m))), C.shift(1n+i, 1n))), rne_c(C.high(2n+i, C.high(D, m)), NC.lex(Nat.cmp(C.low(1n+i, C.half(C.high(D, m))), C.shift(i, 1n)), Nat.cmp(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), 0n))), Equal.cong(Nat, Nat, z => rne_c(z, Nat.cmp(C.low(2n+i, SW.jam(C.high(D, m), C.low(D, m))), C.shift(1n+i, 1n))), C.high(2n+i, SW.jam(C.high(D, m), C.low(D, m))), C.high(2n+i, C.high(D, m)), qJ), Equal.cong(Cmp, Nat, z => rne_c(C.high(2n+i, C.high(D, m)), z), Nat.cmp(C.low(2n+i, SW.jam(C.high(D, m), C.low(D, m))), C.shift(1n+i, 1n)), NC.lex(Nat.cmp(C.low(1n+i, C.half(C.high(D, m))), C.shift(i, 1n)), Nat.cmp(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), 0n)), cJ)))
  Equal.trans(Nat, SF.rne_up(C.high(Nat.add(2n+i, D), m), C.low(Nat.add(2n+i, D), m), C.shift(Nat.add(1n+i, D), 1n)), rne_c(C.high(2n+i, C.high(D, m)), NC.lex(Nat.cmp(C.low(1n+i, C.half(C.high(D, m))), C.shift(i, 1n)), Nat.cmp(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), 0n))), SF.rne_up(C.high(2n+i, SW.jam(C.high(D, m), C.low(D, m))), C.low(2n+i, SW.jam(C.high(D, m), C.low(D, m))), C.shift(1n+i, 1n)), lhs, Equal.sym(Nat, SF.rne_up(C.high(2n+i, SW.jam(C.high(D, m), C.low(D, m))), C.low(2n+i, SW.jam(C.high(D, m), C.low(D, m))), C.shift(1n+i, 1n)), rne_c(C.high(2n+i, C.high(D, m)), NC.lex(Nat.cmp(C.low(1n+i, C.half(C.high(D, m))), C.shift(i, 1n)), Nat.cmp(Nat.max(C.bit(C.high(D, m)), Nat.min(C.low(D, m), 1n)), 0n))), rhs))

# ---- SoftFloat's rounding increment: add half an ulp, shift, clear bit 0 on a tie ----

def fits_add1(+k: Nat, +a: Nat, +b: Nat, +ha: {C.fits(k, a) == True{} : Bool}, +hb: {C.fits(k, b) == True{} : Bool}) -> {C.fits(1n+k, Nat.add(a, b)) == True{} : Bool}:
  +P = C.pow2(k)
  +h1 = N.lt_add_r2(a, P, b, WW.lt_of_fits(k, a, ha))
  +h2 = N.lt_add_left(b, P, P, WW.lt_of_fits(k, b, hb))
  +h3 = N.lt_trans(Nat.add(a, b), Nat.add(P, b), Nat.add(P, P), h1, h2)
  +h4 = L.subst(Nat, z => {Nat.is_lt(Nat.add(a, b), z) == True{} : Bool}, Nat.add(P, P), Nat.double(P), Equal.sym(Nat, Nat.double(P), Nat.add(P, P), NA.double_self(P)), h3)
  WW.fits_of_lt(1n+k, Nat.add(a, b), h4)

def bit_le_self(+n: Nat) -> {Nat.is_le(C.bit(n), n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+ +q:
      N.le_trans(C.bit(q), q, 2n+q, bit_le_self(q), N.le_trans(q, 1n+q, 2n+q, N.le_succ(q), N.le_succ(1n+q)))

def sub_add_r(+a: Nat, +b: Nat, +m: Nat, +h: {Nat.is_le(m, a) == True{} : Bool}) -> {Nat.sub(Nat.add(a, b), m) == Nat.add(Nat.sub(a, m), b) : Nat}:
  +d = Nat.sub(a, m)
  Equal.trans(Nat, Nat.sub(Nat.add(a, b), m), Nat.sub(Nat.add(Nat.add(m, d), b), m), Nat.add(d, b), Equal.cong(Nat, Nat, z => Nat.sub(Nat.add(z, b), m), a, Nat.add(m, d), Equal.sym(Nat, Nat.add(m, d), a, N.sub_add(a, m, h))), Equal.trans(Nat, Nat.sub(Nat.add(Nat.add(m, d), b), m), Nat.sub(Nat.add(m, Nat.add(d, b)), m), Nat.add(d, b), Equal.cong(Nat, Nat, z => Nat.sub(z, m), Nat.add(Nat.add(m, d), b), Nat.add(m, Nat.add(d, b)), NA.add_assoc(m, d, b)), N.add_sub_cancel(m, Nat.add(d, b))))

# the value of clear0(r, b): r, or r with bit 0 cleared
def cvb(+l: U32, +h: U32, +b: Bool) -> {SW.value(X.clear0(WU.U64{l, h}, b)) == SF.pick(Nat, b, Nat.sub(SW.value(WU.U64{l, h}), Nat.mod(SW.value(WU.U64{l, h}), 2n)), SW.value(WU.U64{l, h})) : Nat}:
  match b:
    case True{}:
      +vl = v(l)
      +S32 = C.shift(32n, v(h))
      +m = Nat.mod(vl, 2n)
      +em = LW.odd_val(l)
      +hle = L.subst(Nat, z => {Nat.is_le(z, vl) == True{} : Bool}, C.bit(vl), m, WW.bit_mod(vl), bit_le_self(vl))
      +hle2 = L.subst(Nat, z => {Nat.is_le(z, vl) == True{} : Bool}, m, v(U32.and(l, 1)), Equal.sym(Nat, v(U32.and(l, 1)), m, em), hle)
      +es2 = Equal.trans(Nat, v(U32.sub(l, U32.and(l, 1))), Nat.sub(vl, v(U32.and(l, 1))), Nat.sub(vl, m), U.sub_nat(l, U32.and(l, 1), hle2), Equal.cong(Nat, Nat, z => Nat.sub(vl, z), v(U32.and(l, 1)), m, em))
      +e1 = Equal.cong(Nat, Nat, z => Nat.add(z, S32), v(U32.sub(l, U32.and(l, 1))), Nat.sub(vl, m), es2)
      +eo = WW.odd_limb(31n, vl, v(h))
      +e2 = Equal.trans(Nat, Nat.sub(Nat.add(vl, S32), Nat.mod(Nat.add(vl, S32), 2n)), Nat.sub(Nat.add(vl, S32), m), Nat.add(Nat.sub(vl, m), S32), Equal.cong(Nat, Nat, z => Nat.sub(Nat.add(vl, S32), z), Nat.mod(Nat.add(vl, S32), 2n), m, eo), sub_add_r(vl, S32, m, hle))
      Equal.trans(Nat, Nat.add(v(U32.sub(l, U32.and(l, 1))), S32), Nat.add(Nat.sub(vl, m), S32), Nat.sub(Nat.add(vl, S32), Nat.mod(Nat.add(vl, S32), 2n)), e1, Equal.sym(Nat, Nat.sub(Nat.add(vl, S32), Nat.mod(Nat.add(vl, S32), 2n)), Nat.add(Nat.sub(vl, m), S32), e2))
    case False{}:
      +vl = v(l)
      +e0 = FB.andm(l, 0n, 0, {==})
      +hle = L.subst(Nat, z => {Nat.is_le(z, vl) == True{} : Bool}, 0n, v(U32.and(l, 0)), Equal.sym(Nat, v(U32.and(l, 0)), 0n, e0), N.zero_le(vl))
      +es2 = Equal.trans(Nat, v(U32.sub(l, U32.and(l, 0))), Nat.sub(vl, v(U32.and(l, 0))), vl, U.sub_nat(l, U32.and(l, 0), hle), Equal.trans(Nat, Nat.sub(vl, v(U32.and(l, 0))), Nat.sub(vl, 0n), vl, Equal.cong(Nat, Nat, z => Nat.sub(vl, z), v(U32.and(l, 0)), 0n, e0), N.sub_zero(vl)))
      Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(32n, v(h))), v(U32.sub(l, U32.and(l, 0))), vl, es2)

def cv(+r: WU.U64, +b: Bool) -> {SW.value(X.clear0(r, b)) == SF.pick(Nat, b, Nat.sub(SW.value(r), Nat.mod(SW.value(r), 2n)), SW.value(r)) : Nat}:
  match r:
    case WU.U64{+l, +h}:
      cvb(l, h, b)

# the tie test reads the low 10 bits
def tie_v(+l: U32, +h: U32) -> {U32.is_eq(U32.and(l, 1023), 512) == Nat.is_eq(C.low(10n, SW.value(WU.U64{l, h})), 512n) : Bool}:
  +e1 = LW.eq_nat(U32.and(l, 1023), 512)
  +e2 = Equal.cong(Nat, Bool, z => Nat.is_eq(z, 512n), v(U32.and(l, 1023)), C.low(10n, v(l)), FB.andm(l, 10n, 1023, {==}))
  +e3 = Equal.trans(Nat, C.low(10n, Nat.add(v(l), C.shift(32n, v(h)))), C.low(10n, Nat.add(v(l), C.shift(10n, C.shift(22n, v(h))))), C.low(10n, v(l)), Equal.cong(Nat, Nat, z => C.low(10n, Nat.add(v(l), z)), C.shift(32n, v(h)), C.shift(10n, C.shift(22n, v(h))), WW.shift_comp(10n, 22n, v(h))), WW.low_add_shift(10n, v(l), C.shift(22n, v(h))))
  Equal.trans(Bool, U32.is_eq(U32.and(l, 1023), 512), Nat.is_eq(C.low(10n, v(l)), 512n), Nat.is_eq(C.low(10n, SW.value(WU.U64{l, h})), 512n), Equal.trans(Bool, U32.is_eq(U32.and(l, 1023), 512), Nat.is_eq(v(U32.and(l, 1023)), 512n), Nat.is_eq(C.low(10n, v(l)), 512n), e1, e2), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 512n), C.low(10n, v(l)), C.low(10n, SW.value(WU.U64{l, h})), Equal.sym(Nat, C.low(10n, SW.value(WU.U64{l, h})), C.low(10n, v(l)), e3)))

def parq(+q: Nat) -> {Nat.add(q, SF.b2n(Nat.is_eq(C.bit(q), 1n))) == Nat.double(C.half(Nat.add(q, 1n))) : Nat}:
  match q:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+ +p:
      Equal.cong(Nat, Nat, z => 2n+z, Nat.add(p, SF.b2n(Nat.is_eq(C.bit(p), 1n))), Nat.double(C.half(Nat.add(p, 1n))), parq(p))

def subm(+n: Nat) -> {Nat.sub(n, Nat.mod(n, 2n)) == Nat.double(C.half(n)) : Nat}:
  Equal.trans(Nat, Nat.sub(n, Nat.mod(n, 2n)), Nat.sub(n, C.bit(n)), Nat.double(C.half(n)), Equal.cong(Nat, Nat, z => Nat.sub(n, z), Nat.mod(n, 2n), C.bit(n), Equal.sym(Nat, C.bit(n), Nat.mod(n, 2n), WW.bit_mod(n))), Equal.trans(Nat, Nat.sub(n, C.bit(n)), Nat.sub(Nat.add(C.bit(n), Nat.double(C.half(n))), C.bit(n)), Nat.double(C.half(n)), Equal.cong(Nat, Nat, z => Nat.sub(z, C.bit(n)), n, Nat.add(C.bit(n), Nat.double(C.half(n))), WW.hb(n)), N.add_sub_cancel(C.bit(n), Nat.double(C.half(n)))))

def rp_c(+q0: Nat, +r0: Nat, +hr: {C.fits(10n, r0) == True{} : Bool}, +c: Cmp, +hc: {Nat.cmp(r0, 512n) == c : Cmp}) -> {SF.pick(Nat, Nat.is_eq(r0, 512n), Nat.sub(Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), Nat.mod(Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), 2n)), Nat.add(q0, C.high(10n, Nat.add(r0, 512n)))) == SF.rne_up(q0, r0, 512n) : Nat}:
  match c:
    case LT{}:
      +hlt = NC.lt_of_cmp(r0, 512n, hc)
      +he = Equal.cong(Cmp, Bool, t => Cmp.is_eq(t), Nat.cmp(r0, 512n), LT{}, hc)
      +hg = Equal.cong(Cmp, Bool, t => Cmp.is_lt(t), Nat.cmp(512n, r0), GT{}, Equal.trans(Cmp, Nat.cmp(512n, r0), SF.flip(Nat.cmp(r0, 512n)), GT{}, Equal.sym(Cmp, SF.flip(Nat.cmp(r0, 512n)), Nat.cmp(512n, r0), NC.cmp_flip(r0, 512n)), Equal.cong(Cmp, Cmp, t => SF.flip(t), Nat.cmp(r0, 512n), LT{}, hc)))
      +f = WW.fits_of_lt(10n, Nat.add(r0, 512n), N.lt_add_r2(r0, 512n, 512n, hlt))
      +h0 = N.eq_from_is_eq(C.high(10n, Nat.add(r0, 512n)), 0n, f)
      +l1 = Equal.cong(Bool, Nat, t => SF.pick(Nat, t, Nat.sub(Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), Nat.mod(Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), 2n)), Nat.add(q0, C.high(10n, Nat.add(r0, 512n)))), Nat.is_eq(r0, 512n), False{}, he)
      +l2 = Equal.cong(Nat, Nat, z => Nat.add(q0, z), C.high(10n, Nat.add(r0, 512n)), 0n, h0)
      +r1 = Equal.cong(Bool, Nat, t => Nat.add(q0, SF.b2n(Bool.or(t, Bool.and(Nat.is_eq(r0, 512n), Nat.is_eq(Nat.mod(q0, 2n), 1n))))), Nat.is_lt(512n, r0), False{}, hg)
      +r2 = Equal.cong(Bool, Nat, t => Nat.add(q0, SF.b2n(Bool.or(False{}, Bool.and(t, Nat.is_eq(Nat.mod(q0, 2n), 1n))))), Nat.is_eq(r0, 512n), False{}, he)
      Equal.trans(Nat, SF.pick(Nat, Nat.is_eq(r0, 512n), Nat.sub(Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), Nat.mod(Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), 2n)), Nat.add(q0, C.high(10n, Nat.add(r0, 512n)))), Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), SF.rne_up(q0, r0, 512n), l1, Equal.trans(Nat, Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), Nat.add(q0, 0n), SF.rne_up(q0, r0, 512n), l2, Equal.sym(Nat, SF.rne_up(q0, r0, 512n), Nat.add(q0, 0n), Equal.trans(Nat, SF.rne_up(q0, r0, 512n), Nat.add(q0, SF.b2n(Bool.or(False{}, Bool.and(Nat.is_eq(r0, 512n), Nat.is_eq(Nat.mod(q0, 2n), 1n))))), Nat.add(q0, 0n), r1, r2))))
    case GT{}:
      +hgt = NC.lt_of_gt(r0, 512n, hc)
      +he = Equal.cong(Cmp, Bool, t => Cmp.is_eq(t), Nat.cmp(r0, 512n), GT{}, hc)
      +d = Nat.sub(r0, 512n)
      +ed = N.sub_add(r0, 512n, N.lt_le(512n, r0, hgt))
      +ex = Equal.trans(Nat, Nat.add(r0, 512n), Nat.add(Nat.add(512n, d), 512n), Nat.add(d, C.shift(10n, 1n)), Equal.cong(Nat, Nat, z => Nat.add(z, 512n), r0, Nat.add(512n, d), Equal.sym(Nat, Nat.add(512n, d), r0, ed)), Equal.trans(Nat, Nat.add(Nat.add(512n, d), 512n), Nat.add(512n, Nat.add(d, 512n)), Nat.add(d, C.shift(10n, 1n)), NA.add_assoc(512n, d, 512n), Equal.trans(Nat, Nat.add(512n, Nat.add(d, 512n)), Nat.add(1024n, d), Nat.add(d, C.shift(10n, 1n)), Equal.cong(Nat, Nat, z => Nat.add(512n, z), Nat.add(d, 512n), Nat.add(512n, d), NA.add_comm(d, 512n)), NA.add_comm(1024n, d))))
      +hd = SH.fits_lek(10n, d, r0, UH.sub_le(r0, 512n), hr)
      +h1 = Equal.trans(Nat, C.high(10n, Nat.add(r0, 512n)), C.high(10n, Nat.add(d, C.shift(10n, 1n))), 1n, Equal.cong(Nat, Nat, z => C.high(10n, z), Nat.add(r0, 512n), Nat.add(d, C.shift(10n, 1n)), ex), WW.high_u(10n, d, 1n, hd))
      +l1 = Equal.cong(Bool, Nat, t => SF.pick(Nat, t, Nat.sub(Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), Nat.mod(Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), 2n)), Nat.add(q0, C.high(10n, Nat.add(r0, 512n)))), Nat.is_eq(r0, 512n), False{}, he)
      +l2 = Equal.cong(Nat, Nat, z => Nat.add(q0, z), C.high(10n, Nat.add(r0, 512n)), 1n, h1)
      +r1 = Equal.cong(Bool, Nat, t => Nat.add(q0, SF.b2n(Bool.or(t, Bool.and(Nat.is_eq(r0, 512n), Nat.is_eq(Nat.mod(q0, 2n), 1n))))), Nat.is_lt(512n, r0), True{}, hgt)
      Equal.trans(Nat, SF.pick(Nat, Nat.is_eq(r0, 512n), Nat.sub(Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), Nat.mod(Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), 2n)), Nat.add(q0, C.high(10n, Nat.add(r0, 512n)))), Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), SF.rne_up(q0, r0, 512n), l1, Equal.trans(Nat, Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), Nat.add(q0, 1n), SF.rne_up(q0, r0, 512n), l2, Equal.sym(Nat, SF.rne_up(q0, r0, 512n), Nat.add(q0, 1n), r1)))
    case EQ{}:
      +er = NC.eq_of_cmp(r0, 512n, hc)
      +b1 = subm(Nat.add(q0, 1n))
      +b2 = Equal.trans(Nat, Nat.add(q0, SF.b2n(Nat.is_eq(Nat.mod(q0, 2n), 1n))), Nat.add(q0, SF.b2n(Nat.is_eq(C.bit(q0), 1n))), Nat.double(C.half(Nat.add(q0, 1n))), Equal.cong(Nat, Nat, z => Nat.add(q0, SF.b2n(Nat.is_eq(z, 1n))), Nat.mod(q0, 2n), C.bit(q0), Equal.sym(Nat, C.bit(q0), Nat.mod(q0, 2n), WW.bit_mod(q0))), parq(q0))
      +base = Equal.trans(Nat, Nat.sub(Nat.add(q0, 1n), Nat.mod(Nat.add(q0, 1n), 2n)), Nat.double(C.half(Nat.add(q0, 1n))), Nat.add(q0, SF.b2n(Nat.is_eq(Nat.mod(q0, 2n), 1n))), b1, Equal.sym(Nat, Nat.add(q0, SF.b2n(Nat.is_eq(Nat.mod(q0, 2n), 1n))), Nat.double(C.half(Nat.add(q0, 1n))), b2))
      L.subst(Nat, z => {SF.pick(Nat, Nat.is_eq(z, 512n), Nat.sub(Nat.add(q0, C.high(10n, Nat.add(z, 512n))), Nat.mod(Nat.add(q0, C.high(10n, Nat.add(z, 512n))), 2n)), Nat.add(q0, C.high(10n, Nat.add(z, 512n)))) == SF.rne_up(q0, z, 512n) : Nat}, 512n, r0, Equal.sym(Nat, r0, 512n, er), base)

# the rounded significand of roundPackToF64 is rne(sig, 10)
def rpv(+l: U32, +h: U32, +hS: {C.fits(63n, SW.value(WU.U64{l, h})) == True{} : Bool}) -> {SW.value(X.clear0(X.shr(X.add(WU.U64{l, h}, WU.U64{512, 0}), 10n), U32.is_eq(U32.and(l, 1023), 512))) == SF.rne(SW.value(WU.U64{l, h}), 10n) : Nat}:
  a1 = WA.add_value(WU.U64{l, h}, WU.U64{512, 0})
  +ev1 = Equal.trans(Nat, SW.value(X.add(WU.U64{l, h}, WU.U64{512, 0})), C.low(64n, Nat.add(SW.value(WU.U64{l, h}), 512n)), Nat.add(SW.value(WU.U64{l, h}), 512n), a1, WW.low_fit(64n, Nat.add(SW.value(WU.U64{l, h}), 512n), fits_add1(63n, SW.value(WU.U64{l, h}), 512n, hS, {==})))
  s1 = SH.shr_value(X.add(WU.U64{l, h}, WU.U64{512, 0}), 10n)
  +ev2 = Equal.trans(Nat, SW.value(X.shr(X.add(WU.U64{l, h}, WU.U64{512, 0}), 10n)), C.high(10n, SW.value(X.add(WU.U64{l, h}, WU.U64{512, 0}))), C.high(10n, Nat.add(SW.value(WU.U64{l, h}), 512n)), s1, Equal.cong(Nat, Nat, z => C.high(10n, z), SW.value(X.add(WU.U64{l, h}, WU.U64{512, 0})), Nat.add(SW.value(WU.U64{l, h}), 512n), ev1))
  +sp = Equal.trans(Nat, C.high(10n, Nat.add(SW.value(WU.U64{l, h}), 512n)), C.high(10n, Nat.add(Nat.add(C.low(10n, SW.value(WU.U64{l, h})), C.shift(10n, C.high(10n, SW.value(WU.U64{l, h})))), 512n)), Nat.add(C.high(10n, SW.value(WU.U64{l, h})), C.high(10n, Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n))), Equal.cong(Nat, Nat, z => C.high(10n, Nat.add(z, 512n)), SW.value(WU.U64{l, h}), Nat.add(C.low(10n, SW.value(WU.U64{l, h})), C.shift(10n, C.high(10n, SW.value(WU.U64{l, h})))), WW.low_high(10n, SW.value(WU.U64{l, h}))), Equal.trans(Nat, C.high(10n, Nat.add(Nat.add(C.low(10n, SW.value(WU.U64{l, h})), C.shift(10n, C.high(10n, SW.value(WU.U64{l, h})))), 512n)), C.high(10n, Nat.add(Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n), C.shift(10n, C.high(10n, SW.value(WU.U64{l, h}))))), Nat.add(C.high(10n, SW.value(WU.U64{l, h})), C.high(10n, Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n))), Equal.cong(Nat, Nat, z => C.high(10n, z), Nat.add(Nat.add(C.low(10n, SW.value(WU.U64{l, h})), C.shift(10n, C.high(10n, SW.value(WU.U64{l, h})))), 512n), Nat.add(Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n), C.shift(10n, C.high(10n, SW.value(WU.U64{l, h})))), A.add_rot(C.low(10n, SW.value(WU.U64{l, h})), C.shift(10n, C.high(10n, SW.value(WU.U64{l, h}))), 512n)), Equal.trans(Nat, C.high(10n, Nat.add(Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n), C.shift(10n, C.high(10n, SW.value(WU.U64{l, h}))))), Nat.add(C.high(10n, Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n)), C.high(10n, SW.value(WU.U64{l, h}))), Nat.add(C.high(10n, SW.value(WU.U64{l, h})), C.high(10n, Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n))), WW.high_add_shift(10n, Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n), C.high(10n, SW.value(WU.U64{l, h}))), NA.add_comm(C.high(10n, Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n)), C.high(10n, SW.value(WU.U64{l, h}))))))
  +ev3 = Equal.trans(Nat, SW.value(X.shr(X.add(WU.U64{l, h}, WU.U64{512, 0}), 10n)), C.high(10n, Nat.add(SW.value(WU.U64{l, h}), 512n)), Nat.add(C.high(10n, SW.value(WU.U64{l, h})), C.high(10n, Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n))), ev2, sp)
  +ec = cv(X.shr(X.add(WU.U64{l, h}, WU.U64{512, 0}), 10n), U32.is_eq(U32.and(l, 1023), 512))
  +e4 = Equal.cong(Nat, Nat, z => SF.pick(Nat, U32.is_eq(U32.and(l, 1023), 512), Nat.sub(z, Nat.mod(z, 2n)), z), SW.value(X.shr(X.add(WU.U64{l, h}, WU.U64{512, 0}), 10n)), Nat.add(C.high(10n, SW.value(WU.U64{l, h})), C.high(10n, Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n))), ev3)
  +e5 = Equal.cong(Bool, Nat, t => SF.pick(Nat, t, Nat.sub(Nat.add(C.high(10n, SW.value(WU.U64{l, h})), C.high(10n, Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n))), Nat.mod(Nat.add(C.high(10n, SW.value(WU.U64{l, h})), C.high(10n, Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n))), 2n)), Nat.add(C.high(10n, SW.value(WU.U64{l, h})), C.high(10n, Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n)))), U32.is_eq(U32.and(l, 1023), 512), Nat.is_eq(C.low(10n, SW.value(WU.U64{l, h})), 512n), tie_v(l, h))
  Equal.trans(Nat, SW.value(X.clear0(X.shr(X.add(WU.U64{l, h}, WU.U64{512, 0}), 10n), U32.is_eq(U32.and(l, 1023), 512))), SF.pick(Nat, U32.is_eq(U32.and(l, 1023), 512), Nat.sub(SW.value(X.shr(X.add(WU.U64{l, h}, WU.U64{512, 0}), 10n)), Nat.mod(SW.value(X.shr(X.add(WU.U64{l, h}, WU.U64{512, 0}), 10n)), 2n)), SW.value(X.shr(X.add(WU.U64{l, h}, WU.U64{512, 0}), 10n))), SF.rne_up(C.high(10n, SW.value(WU.U64{l, h})), C.low(10n, SW.value(WU.U64{l, h})), 512n), ec, Equal.trans(Nat, SF.pick(Nat, U32.is_eq(U32.and(l, 1023), 512), Nat.sub(SW.value(X.shr(X.add(WU.U64{l, h}, WU.U64{512, 0}), 10n)), Nat.mod(SW.value(X.shr(X.add(WU.U64{l, h}, WU.U64{512, 0}), 10n)), 2n)), SW.value(X.shr(X.add(WU.U64{l, h}, WU.U64{512, 0}), 10n))), SF.pick(Nat, U32.is_eq(U32.and(l, 1023), 512), Nat.sub(Nat.add(C.high(10n, SW.value(WU.U64{l, h})), C.high(10n, Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n))), Nat.mod(Nat.add(C.high(10n, SW.value(WU.U64{l, h})), C.high(10n, Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n))), 2n)), Nat.add(C.high(10n, SW.value(WU.U64{l, h})), C.high(10n, Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n)))), SF.rne_up(C.high(10n, SW.value(WU.U64{l, h})), C.low(10n, SW.value(WU.U64{l, h})), 512n), e4, Equal.trans(Nat, SF.pick(Nat, U32.is_eq(U32.and(l, 1023), 512), Nat.sub(Nat.add(C.high(10n, SW.value(WU.U64{l, h})), C.high(10n, Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n))), Nat.mod(Nat.add(C.high(10n, SW.value(WU.U64{l, h})), C.high(10n, Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n))), 2n)), Nat.add(C.high(10n, SW.value(WU.U64{l, h})), C.high(10n, Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n)))), SF.pick(Nat, Nat.is_eq(C.low(10n, SW.value(WU.U64{l, h})), 512n), Nat.sub(Nat.add(C.high(10n, SW.value(WU.U64{l, h})), C.high(10n, Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n))), Nat.mod(Nat.add(C.high(10n, SW.value(WU.U64{l, h})), C.high(10n, Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n))), 2n)), Nat.add(C.high(10n, SW.value(WU.U64{l, h})), C.high(10n, Nat.add(C.low(10n, SW.value(WU.U64{l, h})), 512n)))), SF.rne_up(C.high(10n, SW.value(WU.U64{l, h})), C.low(10n, SW.value(WU.U64{l, h})), 512n), e5, rp_c(C.high(10n, SW.value(WU.U64{l, h})), C.low(10n, SW.value(WU.U64{l, h})), WW.low_fits(10n, SW.value(WU.U64{l, h})), Nat.cmp(C.low(10n, SW.value(WU.U64{l, h})), 512n), {==}))))

# ---- packing: a 64-bit word whose value is n + 2^63 s is bits(s, n) ----

def bits_of(+s: Bool, +n: Nat, +w: WU.U64, +hw: {SW.value(w) == Nat.add(n, C.shift(63n, SF.b2n(s))) : Nat}) -> {F.pack64(w) == bits(s, n) : F.F64}:
  +lo = X.lo(w)
  +hi = X.hi(w)
  +t = C.shift(31n, SF.b2n(s))
  +e63 = WW.shift_comp(32n, 31n, SF.b2n(s))
  +ew = Equal.trans(Nat, Nat.add(v(lo), C.shift(32n, v(hi))), SW.value(w), Nat.add(n, C.shift(32n, t)), Equal.sym(Nat, SW.value(w), Nat.add(v(lo), C.shift(32n, v(hi))), WA.val_eta(w)), Equal.trans(Nat, SW.value(w), Nat.add(n, C.shift(63n, SF.b2n(s))), Nat.add(n, C.shift(32n, t)), hw, Equal.cong(Nat, Nat, z => Nat.add(n, z), C.shift(63n, SF.b2n(s)), C.shift(32n, t), e63)))
  +el = Equal.trans(Nat, C.low(32n, n), C.low(32n, Nat.add(n, C.shift(32n, t))), v(lo), Equal.sym(Nat, C.low(32n, Nat.add(n, C.shift(32n, t))), C.low(32n, n), WW.low_add_shift(32n, n, t)), Equal.trans(Nat, C.low(32n, Nat.add(n, C.shift(32n, t))), C.low(32n, Nat.add(v(lo), C.shift(32n, v(hi)))), v(lo), Equal.cong(Nat, Nat, z => C.low(32n, z), Nat.add(n, C.shift(32n, t)), Nat.add(v(lo), C.shift(32n, v(hi))), Equal.sym(Nat, Nat.add(v(lo), C.shift(32n, v(hi))), Nat.add(n, C.shift(32n, t)), ew)), WW.low_u(32n, v(lo), v(hi), LW.vb(lo))))
  +eh = Equal.trans(Nat, Nat.add(C.high(32n, n), t), C.high(32n, Nat.add(n, C.shift(32n, t))), v(hi), Equal.sym(Nat, C.high(32n, Nat.add(n, C.shift(32n, t))), Nat.add(C.high(32n, n), t), WW.high_add_shift(32n, n, t)), Equal.trans(Nat, C.high(32n, Nat.add(n, C.shift(32n, t))), C.high(32n, Nat.add(v(lo), C.shift(32n, v(hi)))), v(hi), Equal.cong(Nat, Nat, z => C.high(32n, z), Nat.add(n, C.shift(32n, t)), Nat.add(v(lo), C.shift(32n, v(hi))), Equal.sym(Nat, Nat.add(v(lo), C.shift(32n, v(hi))), Nat.add(n, C.shift(32n, t)), ew)), WW.high_u(32n, v(lo), v(hi), LW.vb(lo))))
  +ul = Equal.trans(U32, U32.from_nat(C.low(32n, n)), U32.from_nat(v(lo)), lo, Equal.cong(Nat, U32, z => U32.from_nat(z), C.low(32n, n), v(lo), el), LW.rt(lo))
  +uh = Equal.trans(U32, U32.from_nat(Nat.add(C.high(32n, n), t)), U32.from_nat(v(hi)), hi, Equal.cong(Nat, U32, z => U32.from_nat(z), Nat.add(C.high(32n, n), t), v(hi), eh), LW.rt(hi))
  +e = Equal.trans(F.F64, bits(s, n), F.Bits{lo, U32.from_nat(Nat.add(C.high(32n, n), t))}, F.Bits{lo, hi}, Equal.cong(U32, F.F64, z => F.Bits{z, U32.from_nat(Nat.add(C.high(32n, n), t))}, U32.from_nat(C.low(32n, n)), lo, ul), Equal.cong(U32, F.F64, z => F.Bits{lo, z}, U32.from_nat(Nat.add(C.high(32n, n), t)), hi, uh))
  Equal.sym(F.F64, bits(s, n), F.Bits{lo, hi}, e)

def sgn_pick(+s: Bool) -> {F.sgn(s) == SF.pick(U32, s, 2147483648, 0) : U32}:
  match s:
    case True{}:
      {==}
    case False{}:
      {==}

def pb(+s: Bool, +one: Nat, +h1: {one == 1n : Nat}) -> {SF.pick(Nat, s, one, 0n) == SF.b2n(s) : Nat}:
  match s:
    case True{}:
      h1
    case False{}:
      {==}

def sgv0(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +c: U32, +hc: {c == U32{WD.pw(32n, 31n)} : U32}) -> {v(SF.pick(U32, s, c, 0)) == C.shift(31n, SF.pick(Nat, s, one, 0n)) : Nat}:
  match s:
    case True{}:
      FB.pwv(31n, {==}, one, h1, c, hc)
    case False{}:
      {==}

def sgv(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +c: U32, +hc: {c == U32{WD.pw(32n, 31n)} : U32}) -> {v(SF.pick(U32, s, c, 0)) == C.shift(31n, SF.b2n(s)) : Nat}:
  Equal.trans(Nat, v(SF.pick(U32, s, c, 0)), C.shift(31n, SF.pick(Nat, s, one, 0n)), C.shift(31n, SF.b2n(s)), sgv0(one, h1, s, c, hc), Equal.cong(Nat, Nat, z => C.shift(31n, z), SF.pick(Nat, s, one, 0n), SF.b2n(s), pb(s, one, h1)))

def b2n_le(+s: Bool) -> {C.fits(1n, SF.b2n(s)) == True{} : Bool}:
  match s:
    case True{}:
      {==}
    case False{}:
      {==}

# a product below 2^32 is exact
def mulv(+one: Nat, +h1: {one == 1n : Nat}, +a: U32, +c: U32, +h: {Nat.is_lt(Nat.mul(v(a), v(c)), C.shift(32n, one)) == True{} : Bool}) -> {v(U32.mul(a, c)) == Nat.mul(v(a), v(c)) : Nat}:
  match a c:
    case U32{+x} U32{+y}:
      +ex = U.to_nat_word(x)
      +ey = U.to_nat_word(y)
      +es = Equal.trans(Nat, Nat.mul(v(U32{x}), v(U32{y})), Nat.mul(S.unsigned(32n, x), v(U32{y})), Nat.mul(S.unsigned(32n, x), S.unsigned(32n, y)), Equal.cong(Nat, Nat, z => Nat.mul(z, v(U32{y})), v(U32{x}), S.unsigned(32n, x), ex), Equal.cong(Nat, Nat, z => Nat.mul(S.unsigned(32n, x), z), v(U32{y}), S.unsigned(32n, y), ey))
      +h2 = L.subst(Nat, z => {Nat.is_lt(z, C.shift(32n, one)) == True{} : Bool}, Nat.mul(v(U32{x}), v(U32{y})), Nat.mul(S.unsigned(32n, x), S.unsigned(32n, y)), es, h)
      +h3 = L.subst(Nat, z => {Nat.is_lt(Nat.mul(S.unsigned(32n, x), S.unsigned(32n, y)), z) == True{} : Bool}, C.shift(32n, one), S.scale_binary(32n, one), Equal.sym(Nat, S.scale_binary(32n, one), C.shift(32n, one), FB.sb(32n, one)), h2)
      +m = Word.mul(32n, x, y)
      Equal.trans(Nat, U32.to_nat(U32{m}), S.unsigned(32n, m), Nat.mul(v(U32{x}), v(U32{y})), U.to_nat_word(m), Equal.trans(Nat, S.unsigned(32n, m), Nat.mul(S.unsigned(32n, x), S.unsigned(32n, y)), Nat.mul(v(U32{x}), v(U32{y})), WD.mul_exact(32n, one, h1, x, y, h3), Equal.sym(Nat, Nat.mul(v(U32{x}), v(U32{y})), Nat.mul(S.unsigned(32n, x), S.unsigned(32n, y)), es)))

# the high word of packToF64's addend: 2^31 s + 2^20 e
def hwv(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +e: Nat, +he: {C.fits(11n, e) == True{} : Bool}, +c31: U32, +hc31: {c31 == U32{WD.pw(32n, 31n)} : U32}, +c20: U32, +hc20: {c20 == U32{WD.pw(32n, 20n)} : U32}) -> {v(U32.add(SF.pick(U32, s, c31, 0), U32.mul(U32.from_nat(e), c20))) == Nat.add(C.shift(31n, SF.b2n(s)), C.shift(20n, e)) : Nat}:
  +efe = LW.vo(e, SH.fits_mono(11n, 32n, e, {==}, he))
  +ec = FB.pwv(20n, {==}, one, h1, c20, hc20)
  +ep = Equal.trans(Nat, Nat.mul(v(U32.from_nat(e)), v(c20)), Nat.mul(e, v(c20)), C.shift(20n, e), Equal.cong(Nat, Nat, z => Nat.mul(z, v(c20)), v(U32.from_nat(e)), e, efe), Equal.trans(Nat, Nat.mul(e, v(c20)), Nat.mul(e, C.shift(20n, one)), C.shift(20n, e), Equal.cong(Nat, Nat, z => Nat.mul(e, z), v(c20), C.shift(20n, one), ec), Equal.sym(Nat, C.shift(20n, e), Nat.mul(e, C.shift(20n, one)), WW.shift_mul_one(20n, one, h1, e))))
  +f31 = L.subst(Nat, z => {C.fits(31n, z) == True{} : Bool}, Nat.add(0n, C.shift(20n, e)), C.shift(20n, e), {==}, WW.limbs_fit(20n, 11n, 0n, e, fz(20n), he))
  +f32 = SH.fits_mono(31n, 32n, C.shift(20n, e), {==}, f31)
  +hl = L.subst(Nat, z => {Nat.is_lt(z, C.shift(32n, one)) == True{} : Bool}, C.shift(20n, e), Nat.mul(v(U32.from_nat(e)), v(c20)), Equal.sym(Nat, Nat.mul(v(U32.from_nat(e)), v(c20)), C.shift(20n, e), ep), WW.lt_one(32n, one, h1, C.shift(20n, e), f32))
  +emm = Equal.trans(Nat, v(U32.mul(U32.from_nat(e), c20)), Nat.mul(v(U32.from_nat(e)), v(c20)), C.shift(20n, e), mulv(one, h1, U32.from_nat(e), c20, hl), ep)
  +esg = sgv(one, h1, s, c31, hc31)
  +esum = Equal.trans(Nat, Nat.add(v(SF.pick(U32, s, c31, 0)), v(U32.mul(U32.from_nat(e), c20))), Nat.add(C.shift(31n, SF.b2n(s)), v(U32.mul(U32.from_nat(e), c20))), Nat.add(C.shift(31n, SF.b2n(s)), C.shift(20n, e)), Equal.cong(Nat, Nat, z => Nat.add(z, v(U32.mul(U32.from_nat(e), c20))), v(SF.pick(U32, s, c31, 0)), C.shift(31n, SF.b2n(s)), esg), Equal.cong(Nat, Nat, z => Nat.add(C.shift(31n, SF.b2n(s)), z), v(U32.mul(U32.from_nat(e), c20)), C.shift(20n, e), emm))
  +f2 = WW.limbs_fit(31n, 1n, C.shift(20n, e), SF.b2n(s), f31, b2n_le(s))
  +f3 = L.subst(Nat, z => {C.fits(32n, z) == True{} : Bool}, Nat.add(C.shift(20n, e), C.shift(31n, SF.b2n(s))), Nat.add(C.shift(31n, SF.b2n(s)), C.shift(20n, e)), NA.add_comm(C.shift(20n, e), C.shift(31n, SF.b2n(s))), f2)
  +hl2 = L.subst(Nat, z => {Nat.is_lt(z, C.shift(32n, one)) == True{} : Bool}, Nat.add(C.shift(31n, SF.b2n(s)), C.shift(20n, e)), Nat.add(v(SF.pick(U32, s, c31, 0)), v(U32.mul(U32.from_nat(e), c20))), Equal.sym(Nat, Nat.add(v(SF.pick(U32, s, c31, 0)), v(U32.mul(U32.from_nat(e), c20))), Nat.add(C.shift(31n, SF.b2n(s)), C.shift(20n, e)), esum), WW.lt_one(32n, one, h1, Nat.add(C.shift(31n, SF.b2n(s)), C.shift(20n, e)), f3))
  Equal.trans(Nat, v(U32.add(SF.pick(U32, s, c31, 0), U32.mul(U32.from_nat(e), c20))), Nat.add(v(SF.pick(U32, s, c31, 0)), v(U32.mul(U32.from_nat(e), c20))), Nat.add(C.shift(31n, SF.b2n(s)), C.shift(20n, e)), FB.addv(one, h1, SF.pick(U32, s, c31, 0), U32.mul(U32.from_nat(e), c20), hl2), esum)

# SoftFloat's packToF64: the pattern of (s, e, m) is bits(s, m + 2^52 e)
def pack_g(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +e: Nat, +he: {C.fits(11n, e) == True{} : Bool}, +m: WU.U64, +hn: {C.fits(63n, Nat.add(SW.value(m), C.shift(52n, e))) == True{} : Bool}, +c31: U32, +hc31: {c31 == U32{WD.pw(32n, 31n)} : U32}, +c20: U32, +hc20: {c20 == U32{WD.pw(32n, 20n)} : U32}) -> {F.pack64(X.add(WU.U64{0, U32.add(SF.pick(U32, s, c31, 0), U32.mul(U32.from_nat(e), c20))}, m)) == bits(s, Nat.add(SW.value(m), C.shift(52n, e))) : F.F64}:
  +ep = Equal.trans(Nat, SW.value(WU.U64{0, U32.add(SF.pick(U32, s, c31, 0), U32.mul(U32.from_nat(e), c20))}), C.shift(32n, Nat.add(C.shift(31n, SF.b2n(s)), C.shift(20n, e))), Nat.add(C.shift(63n, SF.b2n(s)), C.shift(52n, e)), Equal.cong(Nat, Nat, z => C.shift(32n, z), v(U32.add(SF.pick(U32, s, c31, 0), U32.mul(U32.from_nat(e), c20))), Nat.add(C.shift(31n, SF.b2n(s)), C.shift(20n, e)), hwv(one, h1, s, e, he, c31, hc31, c20, hc20)), Equal.trans(Nat, C.shift(32n, Nat.add(C.shift(31n, SF.b2n(s)), C.shift(20n, e))), Nat.add(C.shift(32n, C.shift(31n, SF.b2n(s))), C.shift(32n, C.shift(20n, e))), Nat.add(C.shift(63n, SF.b2n(s)), C.shift(52n, e)), WW.shift_add(32n, C.shift(31n, SF.b2n(s)), C.shift(20n, e)), Equal.trans(Nat, Nat.add(C.shift(32n, C.shift(31n, SF.b2n(s))), C.shift(32n, C.shift(20n, e))), Nat.add(C.shift(63n, SF.b2n(s)), C.shift(32n, C.shift(20n, e))), Nat.add(C.shift(63n, SF.b2n(s)), C.shift(52n, e)), Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(32n, C.shift(20n, e))), C.shift(32n, C.shift(31n, SF.b2n(s))), C.shift(63n, SF.b2n(s)), Equal.sym(Nat, C.shift(63n, SF.b2n(s)), C.shift(32n, C.shift(31n, SF.b2n(s))), WW.shift_comp(32n, 31n, SF.b2n(s)))), Equal.cong(Nat, Nat, z => Nat.add(C.shift(63n, SF.b2n(s)), z), C.shift(32n, C.shift(20n, e)), C.shift(52n, e), Equal.sym(Nat, C.shift(52n, e), C.shift(32n, C.shift(20n, e)), WW.shift_comp(32n, 20n, e))))))
  +es = Equal.trans(Nat, Nat.add(SW.value(WU.U64{0, U32.add(SF.pick(U32, s, c31, 0), U32.mul(U32.from_nat(e), c20))}), SW.value(m)), Nat.add(Nat.add(C.shift(63n, SF.b2n(s)), C.shift(52n, e)), SW.value(m)), Nat.add(Nat.add(SW.value(m), C.shift(52n, e)), C.shift(63n, SF.b2n(s))), Equal.cong(Nat, Nat, z => Nat.add(z, SW.value(m)), SW.value(WU.U64{0, U32.add(SF.pick(U32, s, c31, 0), U32.mul(U32.from_nat(e), c20))}), Nat.add(C.shift(63n, SF.b2n(s)), C.shift(52n, e)), ep), Equal.trans(Nat, Nat.add(Nat.add(C.shift(63n, SF.b2n(s)), C.shift(52n, e)), SW.value(m)), Nat.add(C.shift(63n, SF.b2n(s)), Nat.add(C.shift(52n, e), SW.value(m))), Nat.add(Nat.add(SW.value(m), C.shift(52n, e)), C.shift(63n, SF.b2n(s))), NA.add_assoc(C.shift(63n, SF.b2n(s)), C.shift(52n, e), SW.value(m)), Equal.trans(Nat, Nat.add(C.shift(63n, SF.b2n(s)), Nat.add(C.shift(52n, e), SW.value(m))), Nat.add(C.shift(63n, SF.b2n(s)), Nat.add(SW.value(m), C.shift(52n, e))), Nat.add(Nat.add(SW.value(m), C.shift(52n, e)), C.shift(63n, SF.b2n(s))), Equal.cong(Nat, Nat, z => Nat.add(C.shift(63n, SF.b2n(s)), z), Nat.add(C.shift(52n, e), SW.value(m)), Nat.add(SW.value(m), C.shift(52n, e)), NA.add_comm(C.shift(52n, e), SW.value(m))), NA.add_comm(C.shift(63n, SF.b2n(s)), Nat.add(SW.value(m), C.shift(52n, e))))))
  +f64 = WW.limbs_fit(63n, 1n, Nat.add(SW.value(m), C.shift(52n, e)), SF.b2n(s), hn, b2n_le(s))
  a1 = WA.add_value(WU.U64{0, U32.add(SF.pick(U32, s, c31, 0), U32.mul(U32.from_nat(e), c20))}, m)
  +ev = Equal.trans(Nat, SW.value(X.add(WU.U64{0, U32.add(SF.pick(U32, s, c31, 0), U32.mul(U32.from_nat(e), c20))}, m)), C.low(64n, Nat.add(SW.value(WU.U64{0, U32.add(SF.pick(U32, s, c31, 0), U32.mul(U32.from_nat(e), c20))}), SW.value(m))), Nat.add(Nat.add(SW.value(m), C.shift(52n, e)), C.shift(63n, SF.b2n(s))), a1, Equal.trans(Nat, C.low(64n, Nat.add(SW.value(WU.U64{0, U32.add(SF.pick(U32, s, c31, 0), U32.mul(U32.from_nat(e), c20))}), SW.value(m))), C.low(64n, Nat.add(Nat.add(SW.value(m), C.shift(52n, e)), C.shift(63n, SF.b2n(s)))), Nat.add(Nat.add(SW.value(m), C.shift(52n, e)), C.shift(63n, SF.b2n(s))), Equal.cong(Nat, Nat, z => C.low(64n, z), Nat.add(SW.value(WU.U64{0, U32.add(SF.pick(U32, s, c31, 0), U32.mul(U32.from_nat(e), c20))}), SW.value(m)), Nat.add(Nat.add(SW.value(m), C.shift(52n, e)), C.shift(63n, SF.b2n(s))), es), WW.low_fit(64n, Nat.add(Nat.add(SW.value(m), C.shift(52n, e)), C.shift(63n, SF.b2n(s))), f64)))
  bits_of(s, Nat.add(SW.value(m), C.shift(52n, e)), X.add(WU.U64{0, U32.add(SF.pick(U32, s, c31, 0), U32.mul(U32.from_nat(e), c20))}, m), ev)

def pack_v(+s: Bool, +e: Nat, +he: {C.fits(11n, e) == True{} : Bool}, +m: WU.U64, +hn: {C.fits(63n, Nat.add(SW.value(m), C.shift(52n, e))) == True{} : Bool}) -> {F.pack(s, e, m) == bits(s, Nat.add(SW.value(m), C.shift(52n, e))) : F.F64}:
  +e0 = Equal.cong(U32, F.F64, z => F.pack64(X.add(WU.U64{0, U32.add(z, U32.mul(U32.from_nat(e), 1048576))}, m)), F.sgn(s), SF.pick(U32, s, 2147483648, 0), sgn_pick(s))
  Equal.trans(F.F64, F.pack(s, e, m), F.pack64(X.add(WU.U64{0, U32.add(SF.pick(U32, s, 2147483648, 0), U32.mul(U32.from_nat(e), 1048576))}, m)), bits(s, Nat.add(SW.value(m), C.shift(52n, e))), e0, pack_g(1n, {==}, s, e, he, m, hn, 2147483648, {==}, 1048576, {==}))

def inf_v(+s: Bool) -> {F.inf(s) == SF.inf(s) : F.F64}:
  match s:
    case True{}:
      {==}
    case False{}:
      {==}

# ---- bit lengths and the bounds of the rounded significand ----

def bl_gt(+k: Nat, +n: Nat, +h1: {C.fits(k, n) == False{} : Bool}, +h2: {C.fits(1n+k, n) == True{} : Bool}, +hg: {Nat.is_le(C.pow2(2n+k), C.pow2(M.bit_length(n))) == True{} : Bool}) -> {M.bit_length(n) == 1n+k : Nat}:
  match n:
    case 0n:
      NC.absurd_tf({M.bit_length(0n) == 1n+k : Nat}, Equal.trans(Bool, False{}, C.fits(k, 0n), True{}, Equal.sym(Bool, C.fits(k, 0n), False{}, h1), fz(k)))
    case 1n+ +np:
      +P = C.pow2(2n+k)
      +hd = N.double_lt(1n+np, C.pow2(1n+k), WW.lt_of_fits(1n+k, 1n+np, h2))
      +hle = N.le_trans(P, C.pow2(M.bit_length(1n+np)), Nat.double(1n+np), hg, BT.bit_length_le(np))
      NC.absurd_tf({M.bit_length(1n+np) == 1n+k : Nat}, Equal.trans(Bool, False{}, Nat.is_lt(P, P), True{}, Equal.sym(Bool, Nat.is_lt(P, P), False{}, N.lt_irrefl(P)), N.le_lt_trans(P, Nat.double(1n+np), P, hle, hd)))

def bl_c(+k: Nat, +n: Nat, +h1: {C.fits(k, n) == False{} : Bool}, +h2: {C.fits(1n+k, n) == True{} : Bool}, +c: Cmp, +hc: {Nat.cmp(M.bit_length(n), 1n+k) == c : Cmp}) -> {M.bit_length(n) == 1n+k : Nat}:
  match c:
    case EQ{}:
      NC.eq_of_cmp(M.bit_length(n), 1n+k, hc)
    case LT{}:
      +hl = N.lt_succ_le(M.bit_length(n), k, NC.lt_of_cmp(M.bit_length(n), 1n+k, hc))
      +hn = N.lt_le_trans(n, C.pow2(M.bit_length(n)), C.pow2(k), BT.bit_length_lt(n), N.pow2_mono(M.bit_length(n), k, hl))
      NC.absurd_tf({M.bit_length(n) == 1n+k : Nat}, Equal.trans(Bool, False{}, C.fits(k, n), True{}, Equal.sym(Bool, C.fits(k, n), False{}, h1), WW.fits_of_lt(k, n, hn)))
    case GT{}:
      +hg = N.pow2_mono(2n+k, M.bit_length(n), N.lt_succ_le_succ(1n+k, M.bit_length(n), NC.lt_of_gt(M.bit_length(n), 1n+k, hc)))
      bl_gt(k, n, h1, h2, hg)

def bl63(+m: Nat, +h1: {C.fits(62n, m) == False{} : Bool}, +h2: {C.fits(63n, m) == True{} : Bool}) -> {M.bit_length(m) == 63n : Nat}:
  bl_c(62n, m, h1, h2, Nat.cmp(M.bit_length(m), 63n), {==})

def nz_of(+k: Nat, +m: Nat, +h1: {C.fits(k, m) == False{} : Bool}) -> {Nat.is_eq(m, 0n) == False{} : Bool}:
  match m:
    case 0n:
      NC.absurd_tf({Nat.is_eq(0n, 0n) == False{} : Bool}, Equal.trans(Bool, False{}, C.fits(k, 0n), True{}, Equal.sym(Bool, C.fits(k, 0n), False{}, h1), fz(k)))
    case 1n+ +mp:
      {==}

# fits(a + b, n) is fits(b, n >> a)
def fits_hc(+a: Nat, +b: Nat, +n: Nat) -> {C.fits(Nat.add(a, b), n) == C.fits(b, C.high(a, n)) : Bool}:
  Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), C.high(Nat.add(a, b), n), C.high(b, C.high(a, n)), WW.high_comp(b, a, n))

def b2n_le1(+c: Bool) -> {Nat.is_le(SF.b2n(c), 1n) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def rne_lb(+m: Nat) -> {Nat.is_le(C.high(10n, m), SF.rne(m, 10n)) == True{} : Bool}:
  N.le_add_right(C.high(10n, m), SF.b2n(Bool.or(Nat.is_lt(512n, C.low(10n, m)), Bool.and(Nat.is_eq(C.low(10n, m), 512n), Nat.is_eq(Nat.mod(C.high(10n, m), 2n), 1n)))))

def rne_ub(+m: Nat) -> {Nat.is_le(SF.rne(m, 10n), Nat.add(C.high(10n, m), 1n)) == True{} : Bool}:
  N.le_add_left(SF.b2n(Bool.or(Nat.is_lt(512n, C.low(10n, m)), Bool.and(Nat.is_eq(C.low(10n, m), 512n), Nat.is_eq(Nat.mod(C.high(10n, m), 2n), 1n)))), 1n, C.high(10n, m), b2n_le1(Bool.or(Nat.is_lt(512n, C.low(10n, m)), Bool.and(Nat.is_eq(C.low(10n, m), 512n), Nat.is_eq(Nat.mod(C.high(10n, m), 2n), 1n)))))

def succ_le(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, 1n), b) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(z, b) == True{} : Bool}, 1n+a, Nat.add(a, 1n), Equal.sym(Nat, Nat.add(a, 1n), 1n+a, Equal.trans(Nat, Nat.add(a, 1n), Nat.add(1n, a), 1n+a, NA.add_comm(a, 1n), {==})), N.lt_succ_le_succ(a, b, h))

# a 63-bit m rounds to at most 2^53
def rne_top(+one: Nat, +h1: {one == 1n : Nat}, +m: Nat, +hm: {C.fits(63n, m) == True{} : Bool}) -> {Nat.is_le(SF.rne(m, 10n), C.shift(53n, one)) == True{} : Bool}:
  +f = SH.fits_high(10n, 53n, m, hm)
  N.le_trans(SF.rne(m, 10n), Nat.add(C.high(10n, m), 1n), C.shift(53n, one), rne_ub(m), succ_le(C.high(10n, m), C.shift(53n, one), WW.lt_one(53n, one, h1, C.high(10n, m), f)))

def nfit_c(+k: Nat, +a: Nat, +r: Nat, +hle: {Nat.is_le(a, r) == True{} : Bool}, +f: {C.fits(k, a) == False{} : Bool}, +b: Bool, +hb: {C.fits(k, r) == b : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      NC.absurd_tf({True{} == False{} : Bool}, Equal.trans(Bool, False{}, C.fits(k, a), True{}, Equal.sym(Bool, C.fits(k, a), False{}, f), SH.fits_lek(k, a, r, hle, hb)))
    case False{}:
      {==}

def nfit(+k: Nat, +a: Nat, +r: Nat, +hle: {Nat.is_le(a, r) == True{} : Bool}, +f: {C.fits(k, a) == False{} : Bool}) -> {C.fits(k, r) == False{} : Bool}:
  nfit_c(k, a, r, hle, f, C.fits(k, r), {==})

# a normalized m (bit 62 set) rounds to a normal significand
def rne_norm(+m: Nat, +hm: {C.fits(62n, m) == False{} : Bool}) -> {C.fits(52n, SF.rne(m, 10n)) == False{} : Bool}:
  +f = Equal.trans(Bool, C.fits(52n, C.high(10n, m)), C.fits(62n, m), False{}, Equal.sym(Bool, C.fits(62n, m), C.fits(52n, C.high(10n, m)), fits_hc(10n, 52n, m)), hm)
  nfit(52n, C.high(10n, m), SF.rne(m, 10n), rne_lb(m), f)


# n < 2^k as fits
def lt_fit(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +n: Nat) -> {Nat.is_lt(n, C.shift(k, one)) == C.fits(k, n) : Bool}:
  +e2a = Equal.trans(Bool, Nat.is_lt(n, C.shift(k, 1n)), Nat.is_lt(n, C.pow2(k)), C.fits(k, n), Equal.cong(Nat, Bool, z => Nat.is_lt(n, z), C.shift(k, 1n), C.pow2(k), WW.shift_one(k)), Equal.sym(Bool, C.fits(k, n), Nat.is_lt(n, C.pow2(k)), WW.fits_lt(k, n)))
  L.subst(Nat, o => {Nat.is_lt(n, C.shift(k, o)) == C.fits(k, n) : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), e2a)



# ---- the spec's pack on a rounded significand q <= 2^53 at ulp u = 1926 + EF ----

def efv(+u: Nat, +EF: Nat, +hu: {Nat.add(EF, 1926n) == u : Nat}) -> {Nat.sub(Nat.add(u, 1075n), SF.zb()) == 1n+EF : Nat}:
  +e1 = Equal.cong(Nat, Nat, z => Nat.sub(Nat.add(z, 1075n), SF.zb()), u, Nat.add(EF, 1926n), Equal.sym(Nat, Nat.add(EF, 1926n), u, hu))
  +e2 = Equal.cong(Nat, Nat, z => Nat.sub(z, SF.zb()), Nat.add(Nat.add(EF, 1926n), 1075n), Nat.add(EF, 3001n), NA.add_assoc(EF, 1926n, 1075n))
  +e3 = Equal.cong(Nat, Nat, z => Nat.sub(z, SF.zb()), Nat.add(EF, 3001n), Nat.add(3001n, EF), NA.add_comm(EF, 3001n))
  Equal.trans(Nat, Nat.sub(Nat.add(u, 1075n), SF.zb()), Nat.sub(Nat.add(Nat.add(EF, 1926n), 1075n), SF.zb()), 1n+EF, e1, Equal.trans(Nat, Nat.sub(Nat.add(Nat.add(EF, 1926n), 1075n), SF.zb()), Nat.sub(Nat.add(EF, 3001n), SF.zb()), 1n+EF, e2, e3))

def ef2v(+u: Nat, +EF: Nat, +hu: {Nat.add(EF, 1926n) == u : Nat}) -> {Nat.sub(Nat.add(1n+u, 1075n), SF.zb()) == 2n+EF : Nat}:
  +e1 = Equal.cong(Nat, Nat, z => Nat.sub(Nat.add(1n+z, 1075n), SF.zb()), u, Nat.add(EF, 1926n), Equal.sym(Nat, Nat.add(EF, 1926n), u, hu))
  +e2 = Equal.cong(Nat, Nat, z => Nat.sub(z, SF.zb()), Nat.add(Nat.add(1n+EF, 1926n), 1075n), Nat.add(1n+EF, 3001n), NA.add_assoc(1n+EF, 1926n, 1075n))
  +e3 = Equal.cong(Nat, Nat, z => Nat.sub(z, SF.zb()), Nat.add(1n+EF, 3001n), Nat.add(3001n, 1n+EF), NA.add_comm(1n+EF, 3001n))
  Equal.trans(Nat, Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), Nat.sub(Nat.add(Nat.add(1n+EF, 1926n), 1075n), SF.zb()), 2n+EF, e1, Equal.trans(Nat, Nat.sub(Nat.add(Nat.add(1n+EF, 1926n), 1075n), SF.zb()), Nat.sub(Nat.add(1n+EF, 3001n), SF.zb()), 2n+EF, e2, e3))

def add1c(+a: Nat, +k: Nat) -> {Nat.add(a, k) == Nat.add(k, a) : Nat}:
  NA.add_comm(a, k)

# the high part of a q in [2^52, 2^53) is 1
def hi_one(+H0: Nat, +a: {Nat.is_eq(C.half(H0), 0n) == True{} : Bool}, +b: {Nat.is_eq(H0, 0n) == False{} : Bool}) -> {H0 == 1n : Nat}:
  match H0:
    case 0n:
      Empty.absurd({0n == 1n : Nat}, LW.true_ne_false(b))
    case 1n:
      {==}
    case 2n+ +p:
      NC.absurd_tf({2n+p == 1n : Nat}, a)

def f53h(+q: Nat) -> {C.fits(53n, q) == Nat.is_eq(C.half(C.high(52n, q)), 0n) : Bool}:
  fits_hc(52n, 1n, q)

def top_q(+one: Nat, +h1: {one == 1n : Nat}, +q: Nat, +hq: {Nat.is_le(q, C.shift(53n, one)) == True{} : Bool}, +hf: {C.fits(53n, q) == False{} : Bool}) -> {q == C.shift(52n, Nat.double(one)) : Nat}:
  +hlt = Equal.trans(Bool, Nat.is_lt(q, C.shift(53n, one)), C.fits(53n, q), False{}, lt_fit(53n, one, h1, q), hf)
  +hge = N.not_lt_le(q, C.shift(53n, one), hlt)
  Equal.trans(Nat, q, C.shift(53n, one), C.shift(52n, Nat.double(one)), N.le_antisym(q, C.shift(53n, one), hq, hge), Equal.sym(Nat, C.shift(52n, Nat.double(one)), C.shift(53n, one), WW.shift_dbl(52n, one)))

def pkg_c(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +q: Nat, +u: Nat, +EF: Nat, +hEF: {Nat.add(EF, 1926n) == u : Nat}, +hq: {Nat.is_le(q, C.shift(53n, one)) == True{} : Bool}, +f53: Bool, +h53: {C.fits(53n, q) == f53 : Bool}, +f52: Bool, +h52: {C.fits(52n, q) == f52 : Bool}, +h0: {Bool.or(Bool.not(f52), Nat.is_eq(EF, 0n)) == True{} : Bool}, +hov: {Nat.is_lt(Nat.add(EF, SF.pick(Nat, f53, 1n, 2n)), 2047n) == True{} : Bool}) -> {SF.pick(F.F64, f53, SF.pick(F.F64, f52, SF.encode(s, 0n, q), SF.pack_e(s, Nat.sub(Nat.add(u, 1075n), SF.zb()), C.low(52n, q))), SF.pack_e(s, Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), 0n)) == bits(s, Nat.add(q, C.shift(52n, EF))) : F.F64}:
  match f53 f52:
    case True{} True{}:
      +e0 = N.eq_from_is_eq(EF, 0n, h0)
      Equal.trans(F.F64, SF.encode(s, 0n, q), bits(s, Nat.add(q, C.shift(52n, 0n))), bits(s, Nat.add(q, C.shift(52n, EF))), enc_bits(s, 0n, q), Equal.cong(Nat, F.F64, z => bits(s, Nat.add(q, C.shift(52n, z))), 0n, EF, Equal.sym(Nat, EF, 0n, e0)))
    case True{} False{}:
      +eH = hi_one(C.high(52n, q), Equal.trans(Bool, Nat.is_eq(C.half(C.high(52n, q)), 0n), C.fits(53n, q), True{}, Equal.sym(Bool, C.fits(53n, q), Nat.is_eq(C.half(C.high(52n, q)), 0n), f53h(q)), h53), h52)
      +e1 = efv(u, EF, hEF)
      +eE = Equal.trans(Nat, Nat.sub(Nat.add(u, 1075n), SF.zb()), 1n+EF, Nat.add(C.high(52n, q), EF), e1, Equal.cong(Nat, Nat, z => Nat.add(z, EF), 1n, C.high(52n, q), Equal.sym(Nat, C.high(52n, q), 1n, eH)))
      +hle = Equal.trans(Bool, Nat.is_le(2047n, Nat.sub(Nat.add(u, 1075n), SF.zb())), Nat.is_le(2047n, 1n+EF), False{}, Equal.cong(Nat, Bool, z => Nat.is_le(2047n, z), Nat.sub(Nat.add(u, 1075n), SF.zb()), 1n+EF, e1), Equal.trans(Bool, Nat.is_le(2047n, 1n+EF), Bool.not(Nat.is_lt(1n+EF, 2047n)), False{}, FB.le_nlt(2047n, 1n+EF), Equal.cong(Bool, Bool, t => Bool.not(t), Nat.is_lt(1n+EF, 2047n), True{}, L.subst(Nat, z => {Nat.is_lt(z, 2047n) == True{} : Bool}, Nat.add(EF, 1n), 1n+EF, Equal.trans(Nat, Nat.add(EF, 1n), Nat.add(1n, EF), 1n+EF, NA.add_comm(EF, 1n), {==}), hov))))
      +p1 = Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.inf(s), SF.encode(s, Nat.sub(Nat.add(u, 1075n), SF.zb()), C.low(52n, q))), Nat.is_le(2047n, Nat.sub(Nat.add(u, 1075n), SF.zb())), False{}, hle)
      +p2 = enc_bits(s, Nat.sub(Nat.add(u, 1075n), SF.zb()), C.low(52n, q))
      +v1 = Equal.trans(Nat, Nat.add(C.low(52n, q), C.shift(52n, Nat.sub(Nat.add(u, 1075n), SF.zb()))), Nat.add(C.low(52n, q), C.shift(52n, Nat.add(C.high(52n, q), EF))), Nat.add(q, C.shift(52n, EF)), Equal.cong(Nat, Nat, z => Nat.add(C.low(52n, q), C.shift(52n, z)), Nat.sub(Nat.add(u, 1075n), SF.zb()), Nat.add(C.high(52n, q), EF), eE), Equal.trans(Nat, Nat.add(C.low(52n, q), C.shift(52n, Nat.add(C.high(52n, q), EF))), Nat.add(C.low(52n, q), Nat.add(C.shift(52n, C.high(52n, q)), C.shift(52n, EF))), Nat.add(q, C.shift(52n, EF)), Equal.cong(Nat, Nat, z => Nat.add(C.low(52n, q), z), C.shift(52n, Nat.add(C.high(52n, q), EF)), Nat.add(C.shift(52n, C.high(52n, q)), C.shift(52n, EF)), WW.shift_add(52n, C.high(52n, q), EF)), Equal.trans(Nat, Nat.add(C.low(52n, q), Nat.add(C.shift(52n, C.high(52n, q)), C.shift(52n, EF))), Nat.add(Nat.add(C.low(52n, q), C.shift(52n, C.high(52n, q))), C.shift(52n, EF)), Nat.add(q, C.shift(52n, EF)), Equal.sym(Nat, Nat.add(Nat.add(C.low(52n, q), C.shift(52n, C.high(52n, q))), C.shift(52n, EF)), Nat.add(C.low(52n, q), Nat.add(C.shift(52n, C.high(52n, q)), C.shift(52n, EF))), NA.add_assoc(C.low(52n, q), C.shift(52n, C.high(52n, q)), C.shift(52n, EF))), Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(52n, EF)), Nat.add(C.low(52n, q), C.shift(52n, C.high(52n, q))), q, Equal.sym(Nat, q, Nat.add(C.low(52n, q), C.shift(52n, C.high(52n, q))), WW.low_high(52n, q))))))
      +p3 = Equal.cong(Nat, F.F64, z => bits(s, z), Nat.add(C.low(52n, q), C.shift(52n, Nat.sub(Nat.add(u, 1075n), SF.zb()))), Nat.add(q, C.shift(52n, EF)), v1)
      Equal.trans(F.F64, SF.pack_e(s, Nat.sub(Nat.add(u, 1075n), SF.zb()), C.low(52n, q)), SF.encode(s, Nat.sub(Nat.add(u, 1075n), SF.zb()), C.low(52n, q)), bits(s, Nat.add(q, C.shift(52n, EF))), p1, Equal.trans(F.F64, SF.encode(s, Nat.sub(Nat.add(u, 1075n), SF.zb()), C.low(52n, q)), bits(s, Nat.add(C.low(52n, q), C.shift(52n, Nat.sub(Nat.add(u, 1075n), SF.zb())))), bits(s, Nat.add(q, C.shift(52n, EF))), p2, p3))
    case False{} _:
      +e1 = ef2v(u, EF, hEF)
      +eq = top_q(one, h1, q, hq, h53)
      +two = Nat.double(one)
      +eE = Equal.trans(Nat, Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), 2n+EF, Nat.add(two, EF), e1, Equal.cong(Nat, Nat, z => Nat.add(Nat.double(z), EF), 1n, one, Equal.sym(Nat, one, 1n, h1)))
      +hle = Equal.trans(Bool, Nat.is_le(2047n, Nat.sub(Nat.add(1n+u, 1075n), SF.zb())), Nat.is_le(2047n, 2n+EF), False{}, Equal.cong(Nat, Bool, z => Nat.is_le(2047n, z), Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), 2n+EF, e1), Equal.trans(Bool, Nat.is_le(2047n, 2n+EF), Bool.not(Nat.is_lt(2n+EF, 2047n)), False{}, FB.le_nlt(2047n, 2n+EF), Equal.cong(Bool, Bool, t => Bool.not(t), Nat.is_lt(2n+EF, 2047n), True{}, L.subst(Nat, z => {Nat.is_lt(z, 2047n) == True{} : Bool}, Nat.add(EF, 2n), 2n+EF, Equal.trans(Nat, Nat.add(EF, 2n), Nat.add(2n, EF), 2n+EF, NA.add_comm(EF, 2n), {==}), hov))))
      +p1 = Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.inf(s), SF.encode(s, Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), 0n)), Nat.is_le(2047n, Nat.sub(Nat.add(1n+u, 1075n), SF.zb())), False{}, hle)
      +p2 = enc_bits(s, Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), 0n)
      +v1 = Equal.trans(Nat, C.shift(52n, Nat.sub(Nat.add(1n+u, 1075n), SF.zb())), C.shift(52n, Nat.add(two, EF)), Nat.add(q, C.shift(52n, EF)), Equal.cong(Nat, Nat, z => C.shift(52n, z), Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), Nat.add(two, EF), eE), Equal.trans(Nat, C.shift(52n, Nat.add(two, EF)), Nat.add(C.shift(52n, two), C.shift(52n, EF)), Nat.add(q, C.shift(52n, EF)), WW.shift_add(52n, two, EF), Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(52n, EF)), C.shift(52n, two), q, Equal.sym(Nat, q, C.shift(52n, two), eq))))
      +p3 = Equal.cong(Nat, F.F64, z => bits(s, z), C.shift(52n, Nat.sub(Nat.add(1n+u, 1075n), SF.zb())), Nat.add(q, C.shift(52n, EF)), v1)
      Equal.trans(F.F64, SF.pack_e(s, Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), 0n), SF.encode(s, Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), 0n), bits(s, Nat.add(q, C.shift(52n, EF))), p1, Equal.trans(F.F64, SF.encode(s, Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), 0n), bits(s, Nat.add(0n, C.shift(52n, Nat.sub(Nat.add(1n+u, 1075n), SF.zb())))), bits(s, Nat.add(q, C.shift(52n, EF))), p2, p3))

def pkg(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +q: Nat, +u: Nat, +EF: Nat, +hEF: {Nat.add(EF, 1926n) == u : Nat}, +hq: {Nat.is_le(q, C.shift(53n, one)) == True{} : Bool}, +h0: {Bool.or(Bool.not(C.fits(52n, q)), Nat.is_eq(EF, 0n)) == True{} : Bool}, +hov: {Nat.is_lt(Nat.add(EF, SF.pick(Nat, C.fits(53n, q), 1n, 2n)), 2047n) == True{} : Bool}) -> {SF.pack(s, q, u) == bits(s, Nat.add(q, C.shift(52n, EF))) : F.F64}:
  pkg_c(one, h1, s, q, u, EF, hEF, hq, C.fits(53n, q), {==}, C.fits(52n, q), {==}, h0, hov)

def pko_c(+s: Bool, +q: Nat, +u: Nat, +EF: Nat, +hEF: {Nat.add(EF, 1926n) == u : Nat}, +f53: Bool, +h52: {C.fits(52n, q) == False{} : Bool}, +hov: {Nat.is_lt(Nat.add(EF, SF.pick(Nat, f53, 1n, 2n)), 2047n) == False{} : Bool}) -> {SF.pick(F.F64, f53, SF.pick(F.F64, C.fits(52n, q), SF.encode(s, 0n, q), SF.pack_e(s, Nat.sub(Nat.add(u, 1075n), SF.zb()), C.low(52n, q))), SF.pack_e(s, Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), 0n)) == SF.inf(s) : F.F64}:
  match f53:
    case True{}:
      +e1 = efv(u, EF, hEF)
      +hle = Equal.trans(Bool, Nat.is_le(2047n, Nat.sub(Nat.add(u, 1075n), SF.zb())), Nat.is_le(2047n, 1n+EF), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(2047n, z), Nat.sub(Nat.add(u, 1075n), SF.zb()), 1n+EF, e1), Equal.trans(Bool, Nat.is_le(2047n, 1n+EF), Bool.not(Nat.is_lt(1n+EF, 2047n)), True{}, FB.le_nlt(2047n, 1n+EF), Equal.cong(Bool, Bool, t => Bool.not(t), Nat.is_lt(1n+EF, 2047n), False{}, L.subst(Nat, z => {Nat.is_lt(z, 2047n) == False{} : Bool}, Nat.add(EF, 1n), 1n+EF, Equal.trans(Nat, Nat.add(EF, 1n), Nat.add(1n, EF), 1n+EF, NA.add_comm(EF, 1n), {==}), hov))))
      +p0 = Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.encode(s, 0n, q), SF.pack_e(s, Nat.sub(Nat.add(u, 1075n), SF.zb()), C.low(52n, q))), C.fits(52n, q), False{}, h52)
      Equal.trans(F.F64, SF.pick(F.F64, C.fits(52n, q), SF.encode(s, 0n, q), SF.pack_e(s, Nat.sub(Nat.add(u, 1075n), SF.zb()), C.low(52n, q))), SF.pack_e(s, Nat.sub(Nat.add(u, 1075n), SF.zb()), C.low(52n, q)), SF.inf(s), p0, Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.inf(s), SF.encode(s, Nat.sub(Nat.add(u, 1075n), SF.zb()), C.low(52n, q))), Nat.is_le(2047n, Nat.sub(Nat.add(u, 1075n), SF.zb())), True{}, hle))
    case False{}:
      +e1 = ef2v(u, EF, hEF)
      +hle = Equal.trans(Bool, Nat.is_le(2047n, Nat.sub(Nat.add(1n+u, 1075n), SF.zb())), Nat.is_le(2047n, 2n+EF), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(2047n, z), Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), 2n+EF, e1), Equal.trans(Bool, Nat.is_le(2047n, 2n+EF), Bool.not(Nat.is_lt(2n+EF, 2047n)), True{}, FB.le_nlt(2047n, 2n+EF), Equal.cong(Bool, Bool, t => Bool.not(t), Nat.is_lt(2n+EF, 2047n), False{}, L.subst(Nat, z => {Nat.is_lt(z, 2047n) == False{} : Bool}, Nat.add(EF, 2n), 2n+EF, Equal.trans(Nat, Nat.add(EF, 2n), Nat.add(2n, EF), 2n+EF, NA.add_comm(EF, 2n), {==}), hov))))
      Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.inf(s), SF.encode(s, Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), 0n)), Nat.is_le(2047n, Nat.sub(Nat.add(1n+u, 1075n), SF.zb())), True{}, hle)

def pko(+s: Bool, +q: Nat, +u: Nat, +EF: Nat, +hEF: {Nat.add(EF, 1926n) == u : Nat}, +h52: {C.fits(52n, q) == False{} : Bool}, +hov: {Nat.is_lt(Nat.add(EF, SF.pick(Nat, C.fits(53n, q), 1n, 2n)), 2047n) == False{} : Bool}) -> {SF.pack(s, q, u) == SF.inf(s) : F.F64}:
  pko_c(s, q, u, EF, hEF, C.fits(53n, q), h52, hov)

# ---- when the rounded significand reaches 2^53 ----

def hsp(+m: Nat) -> {C.high(10n, Nat.add(m, 512n)) == Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))) : Nat}:
  Equal.trans(Nat, C.high(10n, Nat.add(m, 512n)), C.high(10n, Nat.add(Nat.add(C.low(10n, m), C.shift(10n, C.high(10n, m))), 512n)), Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), Equal.cong(Nat, Nat, z => C.high(10n, Nat.add(z, 512n)), m, Nat.add(C.low(10n, m), C.shift(10n, C.high(10n, m))), WW.low_high(10n, m)), Equal.trans(Nat, C.high(10n, Nat.add(Nat.add(C.low(10n, m), C.shift(10n, C.high(10n, m))), 512n)), C.high(10n, Nat.add(Nat.add(C.low(10n, m), 512n), C.shift(10n, C.high(10n, m)))), Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), Equal.cong(Nat, Nat, z => C.high(10n, z), Nat.add(Nat.add(C.low(10n, m), C.shift(10n, C.high(10n, m))), 512n), Nat.add(Nat.add(C.low(10n, m), 512n), C.shift(10n, C.high(10n, m))), A.add_rot(C.low(10n, m), C.shift(10n, C.high(10n, m)), 512n)), Equal.trans(Nat, C.high(10n, Nat.add(Nat.add(C.low(10n, m), 512n), C.shift(10n, C.high(10n, m)))), Nat.add(C.high(10n, Nat.add(C.low(10n, m), 512n)), C.high(10n, m)), Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), WW.high_add_shift(10n, Nat.add(C.low(10n, m), 512n), C.high(10n, m)), NA.add_comm(C.high(10n, Nat.add(C.low(10n, m), 512n)), C.high(10n, m)))))

def mod_sh(+k: Nat, +x: Nat) -> {Nat.mod(C.shift(1n+k, x), 2n) == 0n : Nat}:
  WW.odd_limb(k, 0n, x)

def fsub_c(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +R0: Nat, +hR: {Nat.is_le(R0, C.shift(1n+k, one)) == True{} : Bool}, +f: Bool, +hf: {C.fits(1n+k, R0) == f : Bool}) -> {C.fits(1n+k, Nat.sub(R0, Nat.mod(R0, 2n))) == f : Bool}:
  match f:
    case True{}:
      SH.fits_lek(1n+k, Nat.sub(R0, Nat.mod(R0, 2n)), R0, UH.sub_le(R0, Nat.mod(R0, 2n)), hf)
    case False{}:
      +hlt = Equal.trans(Bool, Nat.is_lt(R0, C.shift(1n+k, one)), C.fits(1n+k, R0), False{}, lt_fit(1n+k, one, h1, R0), hf)
      +eR = N.le_antisym(R0, C.shift(1n+k, one), hR, N.not_lt_le(R0, C.shift(1n+k, one), hlt))
      +em = Equal.trans(Nat, Nat.mod(R0, 2n), Nat.mod(C.shift(1n+k, one), 2n), 0n, Equal.cong(Nat, Nat, z => Nat.mod(z, 2n), R0, C.shift(1n+k, one), eR), mod_sh(k, one))
      +es = Equal.trans(Nat, Nat.sub(R0, Nat.mod(R0, 2n)), Nat.sub(R0, 0n), R0, Equal.cong(Nat, Nat, z => Nat.sub(R0, z), Nat.mod(R0, 2n), 0n, em), N.sub_zero(R0))
      Equal.trans(Bool, C.fits(1n+k, Nat.sub(R0, Nat.mod(R0, 2n))), C.fits(1n+k, R0), False{}, Equal.cong(Nat, Bool, z => C.fits(1n+k, z), Nat.sub(R0, Nat.mod(R0, 2n)), R0, es), hf)

def fpk(+one: Nat, +h1: {one == 1n : Nat}, +R0: Nat, +hR: {Nat.is_le(R0, C.shift(53n, one)) == True{} : Bool}, +t: Bool) -> {C.fits(53n, SF.pick(Nat, t, Nat.sub(R0, Nat.mod(R0, 2n)), R0)) == C.fits(53n, R0) : Bool}:
  match t:
    case True{}:
      fsub_c(52n, one, h1, R0, hR, C.fits(53n, R0), {==})
    case False{}:
      {==}

def le1(+t: Nat, +h: {C.fits(1n, t) == True{} : Bool}) -> {Nat.is_le(t, 1n) == True{} : Bool}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+ +p:
      NC.absurd_tf({Nat.is_le(2n+p, 1n) == True{} : Bool}, h)

def R_le(+one: Nat, +h1: {one == 1n : Nat}, +m: Nat, +hm: {C.fits(63n, m) == True{} : Bool}) -> {Nat.is_le(Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), C.shift(53n, one)) == True{} : Bool}:
  +t = C.high(10n, Nat.add(C.low(10n, m), 512n))
  +ht = le1(t, SH.fits_high(10n, 1n, Nat.add(C.low(10n, m), 512n), fits_add1(10n, C.low(10n, m), 512n, WW.low_fits(10n, m), {==})))
  +hq = WW.lt_one(53n, one, h1, C.high(10n, m), SH.fits_high(10n, 53n, m, hm))
  N.le_trans(Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), Nat.add(C.high(10n, m), 1n), C.shift(53n, one), N.le_add_left(t, 1n, C.high(10n, m), ht), succ_le(C.high(10n, m), C.shift(53n, one), hq))

# the rounded significand overflows 53 bits exactly when m + 2^9 overflows 63
def p2(+one: Nat, +h1: {one == 1n : Nat}, +m: Nat, +hm: {C.fits(63n, m) == True{} : Bool}) -> {C.fits(53n, SF.rne(m, 10n)) == C.fits(63n, Nat.add(m, 512n)) : Bool}:
  +e1 = Equal.cong(Nat, Bool, z => C.fits(53n, z), SF.rne(m, 10n), SF.pick(Nat, Nat.is_eq(C.low(10n, m), 512n), Nat.sub(Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), Nat.mod(Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), 2n)), Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n)))), Equal.sym(Nat, SF.pick(Nat, Nat.is_eq(C.low(10n, m), 512n), Nat.sub(Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), Nat.mod(Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), 2n)), Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n)))), SF.rne(m, 10n), rp_c(C.high(10n, m), C.low(10n, m), WW.low_fits(10n, m), Nat.cmp(C.low(10n, m), 512n), {==})))
  +e2 = fpk(one, h1, Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), R_le(one, h1, m, hm), Nat.is_eq(C.low(10n, m), 512n))
  +e3 = Equal.cong(Nat, Bool, z => C.fits(53n, z), Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), C.high(10n, Nat.add(m, 512n)), Equal.sym(Nat, C.high(10n, Nat.add(m, 512n)), Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), hsp(m)))
  +e4 = Equal.sym(Bool, C.fits(63n, Nat.add(m, 512n)), C.fits(53n, C.high(10n, Nat.add(m, 512n))), fits_hc(10n, 53n, Nat.add(m, 512n)))
  Equal.trans(Bool, C.fits(53n, SF.rne(m, 10n)), C.fits(53n, SF.pick(Nat, Nat.is_eq(C.low(10n, m), 512n), Nat.sub(Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), Nat.mod(Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), 2n)), Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))))), C.fits(63n, Nat.add(m, 512n)), e1, Equal.trans(Bool, C.fits(53n, SF.pick(Nat, Nat.is_eq(C.low(10n, m), 512n), Nat.sub(Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), Nat.mod(Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), 2n)), Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))))), C.fits(53n, Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n)))), C.fits(63n, Nat.add(m, 512n)), e2, Equal.trans(Bool, C.fits(53n, Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n)))), C.fits(53n, C.high(10n, Nat.add(m, 512n))), C.fits(63n, Nat.add(m, 512n)), e3, e4)))

# SoftFloat's carry test: 2^63 <= sig + 2^9
def ovle(+one: Nat, +h1: {one == 1n : Nat}, +sig: WU.U64, +hS: {C.fits(63n, SW.value(sig)) == True{} : Bool}, +c: U32, +hc: {c == U32{WD.pw(32n, 31n)} : U32}) -> {X.le(WU.U64{0, c}, X.add(sig, WU.U64{512, 0})) == Bool.not(C.fits(63n, Nat.add(SW.value(sig), 512n))) : Bool}:
  a1 = WA.add_value(sig, WU.U64{512, 0})
  +ev1 = Equal.trans(Nat, SW.value(X.add(sig, WU.U64{512, 0})), C.low(64n, Nat.add(SW.value(sig), 512n)), Nat.add(SW.value(sig), 512n), a1, WW.low_fit(64n, Nat.add(SW.value(sig), 512n), fits_add1(63n, SW.value(sig), 512n, hS, {==})))
  +ec = Equal.trans(Nat, C.shift(32n, v(c)), C.shift(32n, C.shift(31n, one)), C.shift(63n, one), Equal.cong(Nat, Nat, z => C.shift(32n, z), v(c), C.shift(31n, one), FB.pwv(31n, {==}, one, h1, c, hc)), Equal.sym(Nat, C.shift(63n, one), C.shift(32n, C.shift(31n, one)), WW.shift_comp(32n, 31n, one)))
  l1 = WA.lt_value(X.add(sig, WU.U64{512, 0}), WU.U64{0, c})
  +e2 = Equal.trans(Bool, Nat.is_lt(SW.value(X.add(sig, WU.U64{512, 0})), C.shift(32n, v(c))), Nat.is_lt(Nat.add(SW.value(sig), 512n), C.shift(32n, v(c))), Nat.is_lt(Nat.add(SW.value(sig), 512n), C.shift(63n, one)), Equal.cong(Nat, Bool, z => Nat.is_lt(z, C.shift(32n, v(c))), SW.value(X.add(sig, WU.U64{512, 0})), Nat.add(SW.value(sig), 512n), ev1), Equal.cong(Nat, Bool, z => Nat.is_lt(Nat.add(SW.value(sig), 512n), z), C.shift(32n, v(c)), C.shift(63n, one), ec))
  +e3 = Equal.trans(Bool, X.lt(X.add(sig, WU.U64{512, 0}), WU.U64{0, c}), Nat.is_lt(Nat.add(SW.value(sig), 512n), C.shift(63n, one)), C.fits(63n, Nat.add(SW.value(sig), 512n)), Equal.trans(Bool, X.lt(X.add(sig, WU.U64{512, 0}), WU.U64{0, c}), Nat.is_lt(SW.value(X.add(sig, WU.U64{512, 0})), C.shift(32n, v(c))), Nat.is_lt(Nat.add(SW.value(sig), 512n), C.shift(63n, one)), l1, e2), lt_fit(63n, one, h1, Nat.add(SW.value(sig), 512n)))
  Equal.cong(Bool, Bool, t => Bool.not(t), X.lt(X.add(sig, WU.U64{512, 0}), WU.U64{0, c}), C.fits(63n, Nat.add(SW.value(sig), 512n)), e3)


# ---- small facts for roundPackToF64 ----

def ze0(+z: Bool) -> {F.zero_e(0n, z) == 0n : Nat}:
  match z:
    case True{}:
      {==}
    case False{}:
      {==}

def rpw(+w: WU.U64, +hS: {C.fits(63n, SW.value(w)) == True{} : Bool}) -> {SW.value(X.clear0(X.shr(X.add(w, WU.U64{512, 0}), 10n), U32.is_eq(U32.and(X.lo(w), 1023), 512))) == SF.rne(SW.value(w), 10n) : Nat}:
  match w:
    case WU.U64{+l, +h}:
      rpv(l, h, hS)

def max_r(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.max(a, b) == b : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+ +ap 0n:
      NC.absurd_tf({Nat.max(1n+ap, 0n) == 0n : Nat}, h)
    case 1n+ +ap 1n+ +bp:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.max(ap, bp), bp, max_r(ap, bp, h))

def max_l(+a: Nat, +b: Nat, +h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.max(a, b) == a : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+ +bp:
      NC.absurd_tf({Nat.max(0n, 1n+bp) == 0n : Nat}, h)
    case 1n+ +ap 0n:
      {==}
    case 1n+ +ap 1n+ +bp:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.max(ap, bp), ap, max_l(ap, bp, h))

def ge_or(+c: Nat, +n: Nat) -> {Bool.or(Nat.is_lt(c, n), Nat.is_eq(n, c)) == Nat.is_le(c, n) : Bool}:
  match c n:
    case 0n 0n:
      {==}
    case 0n 1n+ +np:
      {==}
    case 1n+ +cp 0n:
      {==}
    case 1n+ +cp 1n+ +np:
      ge_or(cp, np)

def le_succ_lt(+a: Nat, +b: Nat) -> {Nat.is_le(1n+a, b) == Nat.is_lt(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+ +bp:
      match bp:
        case 0n:
          {==}
        case 1n+ +bq:
          {==}
    case 1n+ +ap 0n:
      {==}
    case 1n+ +ap 1n+ +bp:
      le_succ_lt(ap, bp)

def and_f(+b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def or_f(+b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def or_t(+b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def not_t(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, LW.true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case False{}:
      {==}

def not_f(+b: Bool, +h: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, LW.true_ne_false(h))

def pick_lt(+c: Bool) -> {Nat.is_lt(SF.pick(Nat, c, 1n, 2n), 2047n) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# the overflow test of roundPackToF64 against the spec's exponent field
def ov_c(+EF: Nat, +f: Bool) -> {Bool.or(Nat.is_lt(2045n, EF), Bool.and(Nat.is_eq(EF, 2045n), Bool.not(f))) == Bool.not(Nat.is_lt(Nat.add(EF, SF.pick(Nat, f, 1n, 2n)), 2047n)) : Bool}:
  match f:
    case True{}:
      +l1 = Equal.trans(Bool, Bool.or(Nat.is_lt(2045n, EF), Bool.and(Nat.is_eq(EF, 2045n), False{})), Bool.or(Nat.is_lt(2045n, EF), False{}), Nat.is_lt(2045n, EF), Equal.cong(Bool, Bool, t => Bool.or(Nat.is_lt(2045n, EF), t), Bool.and(Nat.is_eq(EF, 2045n), False{}), False{}, and_f(Nat.is_eq(EF, 2045n))), or_f(Nat.is_lt(2045n, EF)))
      +r1 = Equal.trans(Bool, Bool.not(Nat.is_lt(Nat.add(EF, 1n), 2047n)), Bool.not(Nat.is_lt(EF, 2046n)), Nat.is_lt(2045n, EF), Equal.cong(Bool, Bool, t => Bool.not(t), Nat.is_lt(Nat.add(EF, 1n), 2047n), Nat.is_lt(EF, 2046n), WW.lt_cancel_r(EF, 2046n, 1n)), Equal.trans(Bool, Bool.not(Nat.is_lt(EF, 2046n)), Nat.is_le(2046n, EF), Nat.is_lt(2045n, EF), Equal.sym(Bool, Nat.is_le(2046n, EF), Bool.not(Nat.is_lt(EF, 2046n)), FB.le_nlt(2046n, EF)), le_succ_lt(2045n, EF)))
      Equal.trans(Bool, Bool.or(Nat.is_lt(2045n, EF), Bool.and(Nat.is_eq(EF, 2045n), False{})), Nat.is_lt(2045n, EF), Bool.not(Nat.is_lt(Nat.add(EF, 1n), 2047n)), l1, Equal.sym(Bool, Bool.not(Nat.is_lt(Nat.add(EF, 1n), 2047n)), Nat.is_lt(2045n, EF), r1))
    case False{}:
      +l1 = Equal.trans(Bool, Bool.or(Nat.is_lt(2045n, EF), Bool.and(Nat.is_eq(EF, 2045n), True{})), Bool.or(Nat.is_lt(2045n, EF), Nat.is_eq(EF, 2045n)), Nat.is_le(2045n, EF), Equal.cong(Bool, Bool, t => Bool.or(Nat.is_lt(2045n, EF), t), Bool.and(Nat.is_eq(EF, 2045n), True{}), Nat.is_eq(EF, 2045n), U.and_true(Nat.is_eq(EF, 2045n))), ge_or(2045n, EF))
      +r1 = Equal.trans(Bool, Bool.not(Nat.is_lt(Nat.add(EF, 2n), 2047n)), Bool.not(Nat.is_lt(EF, 2045n)), Nat.is_le(2045n, EF), Equal.cong(Bool, Bool, t => Bool.not(t), Nat.is_lt(Nat.add(EF, 2n), 2047n), Nat.is_lt(EF, 2045n), WW.lt_cancel_r(EF, 2045n, 2n)), Equal.sym(Bool, Nat.is_le(2045n, EF), Bool.not(Nat.is_lt(EF, 2045n)), FB.le_nlt(2045n, EF)))
      Equal.trans(Bool, Bool.or(Nat.is_lt(2045n, EF), Bool.and(Nat.is_eq(EF, 2045n), True{})), Nat.is_le(2045n, EF), Bool.not(Nat.is_lt(Nat.add(EF, 2n), 2047n)), l1, Equal.sym(Bool, Bool.not(Nat.is_lt(Nat.add(EF, 2n), 2047n)), Nat.is_le(2045n, EF), r1))

def eq_cancel_r(+a: Nat, +b: Nat, +c: Nat) -> {Nat.is_eq(Nat.add(a, c), Nat.add(b, c)) == Nat.is_eq(a, b) : Bool}:
  Equal.cong(Cmp, Bool, t => Cmp.is_eq(t), Nat.cmp(Nat.add(a, c), Nat.add(b, c)), Nat.cmp(a, b), NC.cmp_addr(a, b, c))

def sub_cancel_r(+a: Nat, +b: Nat, +c: Nat) -> {Nat.sub(Nat.add(a, c), Nat.add(b, c)) == Nat.sub(a, b) : Nat}:
  match c:
    case 0n:
      Equal.trans(Nat, Nat.sub(Nat.add(a, 0n), Nat.add(b, 0n)), Nat.sub(a, Nat.add(b, 0n)), Nat.sub(a, b), Equal.cong(Nat, Nat, z => Nat.sub(z, Nat.add(b, 0n)), Nat.add(a, 0n), a, N.add_zero(a)), Equal.cong(Nat, Nat, z => Nat.sub(a, z), Nat.add(b, 0n), b, N.add_zero(b)))
    case 1n+ +cp:
      Equal.trans(Nat, Nat.sub(Nat.add(a, 1n+cp), Nat.add(b, 1n+cp)), Nat.sub(1n+Nat.add(a, cp), Nat.add(b, 1n+cp)), Nat.sub(a, b), Equal.cong(Nat, Nat, z => Nat.sub(z, Nat.add(b, 1n+cp)), Nat.add(a, 1n+cp), 1n+Nat.add(a, cp), N.add_succ(a, cp)), Equal.trans(Nat, Nat.sub(1n+Nat.add(a, cp), Nat.add(b, 1n+cp)), Nat.sub(1n+Nat.add(a, cp), 1n+Nat.add(b, cp)), Nat.sub(a, b), Equal.cong(Nat, Nat, z => Nat.sub(1n+Nat.add(a, cp), z), Nat.add(b, 1n+cp), 1n+Nat.add(b, cp), N.add_succ(b, cp)), sub_cancel_r(a, b, cp)))

def sub_add_l(+a: Nat, +x: Nat) -> {Nat.sub(Nat.add(a, x), x) == a : Nat}:
  Equal.trans(Nat, Nat.sub(Nat.add(a, x), x), Nat.sub(Nat.add(x, a), x), a, Equal.cong(Nat, Nat, z => Nat.sub(z, x), Nat.add(a, x), Nat.add(x, a), NA.add_comm(a, x)), N.add_sub_cancel(x, a))

def half_le(+n: Nat) -> {Nat.is_le(C.half(n), n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+ +p:
      N.le_trans(1n+C.half(p), 1n+p, 2n+p, half_le(p), N.le_succ(1n+p))

# q < 2^53 + 1 fits 54 bits
def fit54(+one: Nat, +h1: {one == 1n : Nat}, +q: Nat, +hq: {Nat.is_le(q, C.shift(53n, one)) == True{} : Bool}) -> {C.fits(54n, q) == True{} : Bool}:
  +h0 = L.subst(Nat, o => {Nat.is_lt(o, Nat.double(o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})
  +h2 = WW.shift_lt(53n, one, Nat.double(one), h0)
  +h3 = L.subst(Nat, z => {Nat.is_lt(C.shift(53n, one), z) == True{} : Bool}, C.shift(53n, Nat.double(one)), C.shift(54n, one), WW.shift_dbl(53n, one), h2)
  Equal.trans(Bool, C.fits(54n, q), Nat.is_lt(q, C.shift(54n, one)), True{}, Equal.sym(Bool, Nat.is_lt(q, C.shift(54n, one)), C.fits(54n, q), lt_fit(54n, one, h1, q)), N.le_lt_trans(q, C.shift(53n, one), C.shift(54n, one), hq, h3))

# the high part of a normal q <= 2^53 is the spec's 1 or 2
def hpick_c(+one: Nat, +h1: {one == 1n : Nat}, +q: Nat, +hq: {Nat.is_le(q, C.shift(53n, one)) == True{} : Bool}, +h52: {C.fits(52n, q) == False{} : Bool}, +f: Bool, +hf: {C.fits(53n, q) == f : Bool}) -> {C.high(52n, q) == SF.pick(Nat, f, 1n, 2n) : Nat}:
  match f:
    case True{}:
      hi_one(C.high(52n, q), Equal.trans(Bool, Nat.is_eq(C.half(C.high(52n, q)), 0n), C.fits(53n, q), True{}, Equal.sym(Bool, C.fits(53n, q), Nat.is_eq(C.half(C.high(52n, q)), 0n), f53h(q)), hf), h52)
    case False{}:
      +eq = top_q(one, h1, q, hq, hf)
      +e1 = Equal.trans(Nat, C.high(52n, q), C.high(52n, C.shift(52n, Nat.double(one))), Nat.double(one), Equal.cong(Nat, Nat, z => C.high(52n, z), q, C.shift(52n, Nat.double(one)), eq), WW.high_u(52n, 0n, Nat.double(one), fz(52n)))
      Equal.trans(Nat, C.high(52n, q), Nat.double(one), 2n, e1, Equal.cong(Nat, Nat, z => Nat.double(z), one, 1n, h1))

def qsplit(+q: Nat, +EF: Nat) -> {Nat.add(C.low(52n, q), C.shift(52n, Nat.add(C.high(52n, q), EF))) == Nat.add(q, C.shift(52n, EF)) : Nat}:
  Equal.trans(Nat, Nat.add(C.low(52n, q), C.shift(52n, Nat.add(C.high(52n, q), EF))), Nat.add(C.low(52n, q), Nat.add(C.shift(52n, C.high(52n, q)), C.shift(52n, EF))), Nat.add(q, C.shift(52n, EF)), Equal.cong(Nat, Nat, z => Nat.add(C.low(52n, q), z), C.shift(52n, Nat.add(C.high(52n, q), EF)), Nat.add(C.shift(52n, C.high(52n, q)), C.shift(52n, EF)), WW.shift_add(52n, C.high(52n, q), EF)), Equal.trans(Nat, Nat.add(C.low(52n, q), Nat.add(C.shift(52n, C.high(52n, q)), C.shift(52n, EF))), Nat.add(Nat.add(C.low(52n, q), C.shift(52n, C.high(52n, q))), C.shift(52n, EF)), Nat.add(q, C.shift(52n, EF)), Equal.sym(Nat, Nat.add(Nat.add(C.low(52n, q), C.shift(52n, C.high(52n, q))), C.shift(52n, EF)), Nat.add(C.low(52n, q), Nat.add(C.shift(52n, C.high(52n, q)), C.shift(52n, EF))), NA.add_assoc(C.low(52n, q), C.shift(52n, C.high(52n, q)), C.shift(52n, EF))), Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(52n, EF)), Nat.add(C.low(52n, q), C.shift(52n, C.high(52n, q))), q, Equal.sym(Nat, q, Nat.add(C.low(52n, q), C.shift(52n, C.high(52n, q))), WW.low_high(52n, q)))))

# a normal q with its exponent field below 2047 fits the 63-bit pattern
def qfit(+one: Nat, +h1: {one == 1n : Nat}, +q: Nat, +EF: Nat, +hq: {Nat.is_le(q, C.shift(53n, one)) == True{} : Bool}, +h52: {C.fits(52n, q) == False{} : Bool}, +hov: {Nat.is_lt(Nat.add(EF, SF.pick(Nat, C.fits(53n, q), 1n, 2n)), 2047n) == True{} : Bool}) -> {C.fits(63n, Nat.add(q, C.shift(52n, EF))) == True{} : Bool}:
  +eH = hpick_c(one, h1, q, hq, h52, C.fits(53n, q), {==})
  +h2 = L.subst(Nat, z => {Nat.is_lt(Nat.add(EF, z), 2047n) == True{} : Bool}, SF.pick(Nat, C.fits(53n, q), 1n, 2n), C.high(52n, q), Equal.sym(Nat, C.high(52n, q), SF.pick(Nat, C.fits(53n, q), 1n, 2n), eH), hov)
  +h3 = L.subst(Nat, z => {Nat.is_lt(z, 2047n) == True{} : Bool}, Nat.add(EF, C.high(52n, q)), Nat.add(C.high(52n, q), EF), NA.add_comm(EF, C.high(52n, q)), h2)
  +f11 = WW.fits_of_lt(11n, Nat.add(C.high(52n, q), EF), N.lt_trans(Nat.add(C.high(52n, q), EF), 2047n, 2048n, h3, {==}))
  +f = WW.limbs_fit(52n, 11n, C.low(52n, q), Nat.add(C.high(52n, q), EF), WW.low_fits(52n, q), f11)
  L.subst(Nat, z => {C.fits(63n, z) == True{} : Bool}, Nat.add(C.low(52n, q), C.shift(52n, Nat.add(C.high(52n, q), EF))), Nat.add(q, C.shift(52n, EF)), qsplit(q, EF), f)

def ef11(+EF: Nat, +c: Nat, +hov: {Nat.is_lt(Nat.add(EF, c), 2047n) == True{} : Bool}) -> {C.fits(11n, EF) == True{} : Bool}:
  WW.fits_of_lt(11n, EF, N.le_lt_trans(EF, Nat.add(EF, c), 2048n, N.le_add_right(EF, c), N.lt_trans(Nat.add(EF, c), 2047n, 2048n, hov, {==})))

# ---- roundPackToF64's last step ----

def rpfE(+s: Bool, +E: Nat, +w: WU.U64, +hS: {C.fits(63n, SW.value(w)) == True{} : Bool}, +hE: {C.fits(11n, E) == True{} : Bool}, +hz: {C.fits(52n, SF.rne(SW.value(w), 10n)) == False{} : Bool}, +hq: {C.fits(63n, Nat.add(SF.rne(SW.value(w), 10n), C.shift(52n, E))) == True{} : Bool}) -> {F.rp_fin(s, E, w) == bits(s, Nat.add(SF.rne(SW.value(w), 10n), C.shift(52n, E))) : F.F64}:
  +r = X.clear0(X.shr(X.add(w, WU.U64{512, 0}), 10n), U32.is_eq(U32.and(X.lo(w), 1023), 512))
  +q = SF.rne(SW.value(w), 10n)
  +ev = rpw(w, hS)
  z0 = WA.is_zero_value(r)
  +hzr = Equal.trans(Bool, X.is_zero(r), Nat.is_eq(SW.value(r), 0n), False{}, z0, Equal.trans(Bool, Nat.is_eq(SW.value(r), 0n), Nat.is_eq(q, 0n), False{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), SW.value(r), q, ev), nz_of(52n, q, hz)))
  +e1 = Equal.cong(Bool, F.F64, t => F.pack(s, F.zero_e(E, t), r), X.is_zero(r), False{}, hzr)
  +hn = L.subst(Nat, z => {C.fits(63n, Nat.add(z, C.shift(52n, E))) == True{} : Bool}, q, SW.value(r), Equal.sym(Nat, SW.value(r), q, ev), hq)
  +e2 = pack_v(s, E, hE, r, hn)
  +e3 = Equal.cong(Nat, F.F64, z => bits(s, Nat.add(z, C.shift(52n, E))), SW.value(r), q, ev)
  Equal.trans(F.F64, F.pack(s, F.zero_e(E, X.is_zero(r)), r), F.pack(s, E, r), bits(s, Nat.add(q, C.shift(52n, E))), e1, Equal.trans(F.F64, F.pack(s, E, r), bits(s, Nat.add(SW.value(r), C.shift(52n, E))), bits(s, Nat.add(q, C.shift(52n, E))), e2, e3))

def rpf0(+s: Bool, +w: WU.U64, +hS: {C.fits(63n, SW.value(w)) == True{} : Bool}, +hq: {C.fits(63n, Nat.add(SF.rne(SW.value(w), 10n), C.shift(52n, 0n))) == True{} : Bool}) -> {F.rp_fin(s, 0n, w) == bits(s, Nat.add(SF.rne(SW.value(w), 10n), C.shift(52n, 0n))) : F.F64}:
  +r = X.clear0(X.shr(X.add(w, WU.U64{512, 0}), 10n), U32.is_eq(U32.and(X.lo(w), 1023), 512))
  +q = SF.rne(SW.value(w), 10n)
  +ev = rpw(w, hS)
  +e1 = Equal.cong(Nat, F.F64, t => F.pack(s, t, r), F.zero_e(0n, X.is_zero(r)), 0n, ze0(X.is_zero(r)))
  +hn = L.subst(Nat, z => {C.fits(63n, Nat.add(z, C.shift(52n, 0n))) == True{} : Bool}, q, SW.value(r), Equal.sym(Nat, SW.value(r), q, ev), hq)
  +e2 = pack_v(s, 0n, {==}, r, hn)
  +e3 = Equal.cong(Nat, F.F64, z => bits(s, Nat.add(z, C.shift(52n, 0n))), SW.value(r), q, ev)
  Equal.trans(F.F64, F.pack(s, F.zero_e(0n, X.is_zero(r)), r), F.pack(s, 0n, r), bits(s, Nat.add(q, C.shift(52n, 0n))), e1, Equal.trans(F.F64, F.pack(s, 0n, r), bits(s, Nat.add(SW.value(r), C.shift(52n, 0n))), bits(s, Nat.add(q, C.shift(52n, 0n))), e2, e3))


# ---- roundPackToF64 is the spec's round ----

def esub63(+x: Nat) -> {Nat.sub(Nat.add(x, 63n), 53n) == Nat.add(10n, x) : Nat}:
  Equal.trans(Nat, Nat.sub(Nat.add(x, 63n), 53n), Nat.sub(Nat.add(63n, x), 53n), Nat.add(10n, x), Equal.cong(Nat, Nat, z => Nat.sub(z, 53n), Nat.add(x, 63n), Nat.add(63n, x), NA.add_comm(x, 63n)), {==})

def sr(+s: Bool, +m: Nat, +x: Nat, +h62: {C.fits(62n, m) == False{} : Bool}, +h63: {C.fits(63n, m) == True{} : Bool}) -> {SF.round(s, m, x) == SF.round_u(s, m, x, Nat.max(Nat.add(10n, x), 1926n)) : F.F64}:
  +e1 = Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.zero(s), SF.round_u(s, m, x, Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)))), Nat.is_eq(m, 0n), False{}, nz_of(62n, m, h62))
  +e2 = Equal.cong(Nat, F.F64, z => SF.round_u(s, m, x, Nat.max(Nat.sub(Nat.add(x, z), 53n), Nat.sub(SF.zb(), 1074n))), M.bit_length(m), 63n, bl63(m, h62, h63))
  +e3 = Equal.cong(Nat, F.F64, z => SF.round_u(s, m, x, Nat.max(z, Nat.sub(SF.zb(), 1074n))), Nat.sub(Nat.add(x, 63n), 53n), Nat.add(10n, x), esub63(x))
  Equal.trans(F.F64, SF.round(s, m, x), SF.round_u(s, m, x, Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.round_u(s, m, x, Nat.max(Nat.add(10n, x), 1926n)), e1, Equal.trans(F.F64, SF.round_u(s, m, x, Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.round_u(s, m, x, Nat.max(Nat.sub(Nat.add(x, 63n), 53n), Nat.sub(SF.zb(), 1074n))), SF.round_u(s, m, x, Nat.max(Nat.add(10n, x), 1926n)), e2, e3))

def lt_sub_pos(+x: Nat, +n: Nat, +h: {Nat.is_lt(x, n) == True{} : Bool}) -> {Nat.is_le(1n, Nat.sub(n, x)) == True{} : Bool}:
  match x n:
    case 0n 0n:
      NC.absurd_tf({Nat.is_le(1n, 0n) == True{} : Bool}, h)
    case 0n 1n+ +np:
      N.zero_le(np)
    case 1n+ +xp 0n:
      NC.absurd_tf({Nat.is_le(1n, 0n) == True{} : Bool}, h)
    case 1n+ +xp 1n+ +np:
      lt_sub_pos(xp, np, h)

def sub_add_a(+a: Nat, +n: Nat, +x: Nat, +h: {Nat.is_le(x, n) == True{} : Bool}) -> {Nat.sub(Nat.add(a, n), x) == Nat.add(a, Nat.sub(n, x)) : Nat}:
  Equal.trans(Nat, Nat.sub(Nat.add(a, n), x), Nat.sub(Nat.add(n, a), x), Nat.add(a, Nat.sub(n, x)), Equal.cong(Nat, Nat, z => Nat.sub(z, x), Nat.add(a, n), Nat.add(n, a), NA.add_comm(a, n)), Equal.trans(Nat, Nat.sub(Nat.add(n, a), x), Nat.add(Nat.sub(n, x), a), Nat.add(a, Nat.sub(n, x)), sub_add_r(n, a, x, h), NA.add_comm(Nat.sub(n, x), a)))

def le_cancel_r(+a: Nat, +b: Nat, +c: Nat) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == Nat.is_le(a, b) : Bool}:
  Equal.cong(Cmp, Bool, t => Cmp.is_le(t), Nat.cmp(Nat.add(a, c), Nat.add(b, c)), Nat.cmp(a, b), NC.cmp_addr(a, b, c))

def jfit(+d: Nat, +m: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +h63: {C.fits(63n, m) == True{} : Bool}) -> {C.fits(63n, SW.jam(C.high(d, m), C.low(d, m))) == True{} : Bool}:
  +h = C.high(d, m)
  +t = Nat.max(C.bit(h), Nat.min(C.low(d, m), 1n))
  +hle = L.subst(Nat, z => {Nat.is_le(63n, z) == True{} : Bool}, Nat.add(62n, d), Nat.add(d, 62n), NA.add_comm(62n, d), hd)
  +fh = Equal.trans(Bool, C.fits(62n, h), C.fits(Nat.add(d, 62n), m), True{}, Equal.sym(Bool, C.fits(Nat.add(d, 62n), m), C.fits(62n, h), fits_hc(d, 62n, m)), SH.fits_mono(63n, Nat.add(d, 62n), m, hle, h63))
  +fhh = SH.fits_lek(62n, C.half(h), h, half_le(h), fh)
  +ft = small(t, max_le1(C.bit(h), C.low(d, m), WW.bit_le1(h)))
  +f = WW.limbs_fit(1n, 62n, t, C.half(h), ft, fhh)
  L.subst(Nat, z => {C.fits(63n, z) == True{} : Bool}, Nat.add(t, Nat.double(C.half(h))), SW.jam(h, C.low(d, m)), Equal.sym(Nat, SW.jam(h, C.low(d, m)), Nat.add(t, Nat.double(C.half(h))), jam_form(h, C.low(d, m))), f)

def rp_sub(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +e: Nat, +sig: WU.U64, +x: Nat, +hx: {Nat.add(x, 2180n) == e : Nat}, +h62: {C.fits(62n, SW.value(sig)) == False{} : Bool}, +h63: {C.fits(63n, SW.value(sig)) == True{} : Bool}, +hb: {Nat.is_lt(x, 1916n) == True{} : Bool}, +u: Nat, +hu: {Nat.max(Nat.add(10n, x), 1926n) == u : Nat}) -> {F.rp_neg(s, e, sig, True{}) == SF.round_u(s, SW.value(sig), x, u) : F.F64}:
  +hu1 = Equal.trans(Nat, u, Nat.max(Nat.add(10n, x), 1926n), 1926n, Equal.sym(Nat, Nat.max(Nat.add(10n, x), 1926n), u, hu), max_r(Nat.add(10n, x), 1926n, hb))
  +d = Nat.sub(F.off(), e)
  +ed = Equal.trans(Nat, d, Nat.sub(F.off(), Nat.add(x, 2180n)), Nat.sub(1916n, x), Equal.cong(Nat, Nat, z => Nat.sub(F.off(), z), e, Nat.add(x, 2180n), Equal.sym(Nat, Nat.add(x, 2180n), e, hx)), sub_cancel_r(1916n, x, 2180n))
  +hd1 = L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, Nat.sub(1916n, x), d, Equal.sym(Nat, d, Nat.sub(1916n, x), ed), lt_sub_pos(x, 1916n, hb))
  +ku = Equal.trans(Nat, Nat.sub(u, x), Nat.sub(1926n, x), Nat.add(10n, d), Equal.cong(Nat, Nat, z => Nat.sub(z, x), u, 1926n, hu1), Equal.trans(Nat, Nat.sub(1926n, x), Nat.add(10n, Nat.sub(1916n, x)), Nat.add(10n, d), sub_add_a(10n, 1916n, x, N.lt_le(x, 1916n, hb)), Equal.cong(Nat, Nat, z => Nat.add(10n, z), Nat.sub(1916n, x), d, Equal.sym(Nat, d, Nat.sub(1916n, x), ed))))
  +hle = L.subst(Nat, z => {Nat.is_le(x, z) == True{} : Bool}, 1926n, u, Equal.sym(Nat, u, 1926n, hu1), N.le_trans(x, 1916n, 1926n, N.lt_le(x, 1916n, hb), {==}))
  sj = SH.shr_jam_value(sig, d)
  sj2 = SH.shr_jam_value(sig, d)
  +est = sticky(8n, d, SW.value(sig))
  +eq = Equal.trans(Nat, SF.rne(SW.value(sig), Nat.add(10n, d)), SF.rne(SW.jam(C.high(d, SW.value(sig)), C.low(d, SW.value(sig))), 10n), SF.rne(SW.value(X.shr_jam(sig, d)), 10n), est, Equal.cong(Nat, Nat, z => SF.rne(z, 10n), SW.jam(C.high(d, SW.value(sig)), C.low(d, SW.value(sig))), SW.value(X.shr_jam(sig, d)), Equal.sym(Nat, SW.value(X.shr_jam(sig, d)), SW.jam(C.high(d, SW.value(sig)), C.low(d, SW.value(sig))), sj)))
  +hJ = L.subst(Nat, z => {C.fits(63n, z) == True{} : Bool}, SW.jam(C.high(d, SW.value(sig)), C.low(d, SW.value(sig))), SW.value(X.shr_jam(sig, d)), Equal.sym(Nat, SW.value(X.shr_jam(sig, d)), SW.jam(C.high(d, SW.value(sig)), C.low(d, SW.value(sig))), sj2), jfit(d, SW.value(sig), hd1, h63))
  +hqJ = rne_top(one, h1, SW.value(X.shr_jam(sig, d)), hJ)
  +hq = L.subst(Nat, z => {Nat.is_le(z, C.shift(53n, one)) == True{} : Bool}, SF.rne(SW.value(X.shr_jam(sig, d)), 10n), SF.rne(SW.value(sig), Nat.add(10n, d)), Equal.sym(Nat, SF.rne(SW.value(sig), Nat.add(10n, d)), SF.rne(SW.value(X.shr_jam(sig, d)), 10n), eq), hqJ)
  +h0 = or_t(Bool.not(C.fits(52n, SF.rne(SW.value(sig), Nat.add(10n, d)))))
  +hov = pick_lt(C.fits(53n, SF.rne(SW.value(sig), Nat.add(10n, d))))
  +s1 = Equal.cong(Bool, F.F64, t => SF.pack(s, SF.pick(Nat, t, SF.rne(SW.value(sig), Nat.sub(u, x)), C.shift(Nat.sub(x, u), SW.value(sig))), u), Nat.is_le(x, u), True{}, hle)
  +s2 = Equal.cong(Nat, F.F64, z => SF.pack(s, SF.rne(SW.value(sig), z), u), Nat.sub(u, x), Nat.add(10n, d), ku)
  +s3 = pkg(one, h1, s, SF.rne(SW.value(sig), Nat.add(10n, d)), u, 0n, Equal.sym(Nat, u, 1926n, hu1), hq, h0, hov)
  +sp = Equal.trans(F.F64, SF.round_u(s, SW.value(sig), x, u), SF.pack(s, SF.rne(SW.value(sig), Nat.sub(u, x)), u), bits(s, Nat.add(SF.rne(SW.value(sig), Nat.add(10n, d)), C.shift(52n, 0n))), s1, Equal.trans(F.F64, SF.pack(s, SF.rne(SW.value(sig), Nat.sub(u, x)), u), SF.pack(s, SF.rne(SW.value(sig), Nat.add(10n, d)), u), bits(s, Nat.add(SF.rne(SW.value(sig), Nat.add(10n, d)), C.shift(52n, 0n))), s2, s3))
  +f54 = SH.fits_mono(54n, 63n, SF.rne(SW.value(X.shr_jam(sig, d)), 10n), {==}, fit54(one, h1, SF.rne(SW.value(X.shr_jam(sig, d)), 10n), hqJ))
  +hq0 = L.subst(Nat, z => {C.fits(63n, z) == True{} : Bool}, SF.rne(SW.value(X.shr_jam(sig, d)), 10n), Nat.add(SF.rne(SW.value(X.shr_jam(sig, d)), 10n), 0n), Equal.sym(Nat, Nat.add(SF.rne(SW.value(X.shr_jam(sig, d)), 10n), 0n), SF.rne(SW.value(X.shr_jam(sig, d)), 10n), N.add_zero(SF.rne(SW.value(X.shr_jam(sig, d)), 10n))), f54)
  +i1 = rpf0(s, X.shr_jam(sig, d), hJ, hq0)
  +i2 = Equal.cong(Nat, F.F64, z => bits(s, Nat.add(z, C.shift(52n, 0n))), SF.rne(SW.value(X.shr_jam(sig, d)), 10n), SF.rne(SW.value(sig), Nat.add(10n, d)), Equal.sym(Nat, SF.rne(SW.value(sig), Nat.add(10n, d)), SF.rne(SW.value(X.shr_jam(sig, d)), 10n), eq))
  Equal.trans(F.F64, F.rp_fin(s, 0n, X.shr_jam(sig, d)), bits(s, Nat.add(SF.rne(SW.value(sig), Nat.add(10n, d)), C.shift(52n, 0n))), SF.round_u(s, SW.value(sig), x, u), Equal.trans(F.F64, F.rp_fin(s, 0n, X.shr_jam(sig, d)), bits(s, Nat.add(SF.rne(SW.value(X.shr_jam(sig, d)), 10n), C.shift(52n, 0n))), bits(s, Nat.add(SF.rne(SW.value(sig), Nat.add(10n, d)), C.shift(52n, 0n))), i1, i2), Equal.sym(F.F64, SF.round_u(s, SW.value(sig), x, u), bits(s, Nat.add(SF.rne(SW.value(sig), Nat.add(10n, d)), C.shift(52n, 0n))), sp))

def ov_eq(+one: Nat, +h1: {one == 1n : Nat}, +e: Nat, +sig: WU.U64, +x: Nat, +hx: {Nat.add(x, 2180n) == e : Nat}, +hge: {Nat.is_le(1916n, x) == True{} : Bool}, +h63: {C.fits(63n, SW.value(sig)) == True{} : Bool}) -> {Bool.or(Nat.is_lt(Nat.add(F.off(), 2045n), e), Bool.and(Nat.is_eq(e, Nat.add(F.off(), 2045n)), X.le(WU.U64{0, 2147483648}, X.add(sig, WU.U64{512, 0})))) == Bool.not(Nat.is_lt(Nat.add(Nat.sub(e, F.off()), SF.pick(Nat, C.fits(53n, SF.rne(SW.value(sig), 10n)), 1n, 2n)), 2047n)) : Bool}:
  +he = L.subst(Nat, z => {Nat.is_le(F.off(), z) == True{} : Bool}, Nat.add(x, 2180n), e, hx, Equal.trans(Bool, Nat.is_le(Nat.add(1916n, 2180n), Nat.add(x, 2180n)), Nat.is_le(1916n, x), True{}, le_cancel_r(1916n, x, 2180n), hge))
  +ee = Equal.trans(Nat, e, Nat.add(4096n, Nat.sub(e, F.off())), Nat.add(Nat.sub(e, F.off()), 4096n), Equal.sym(Nat, Nat.add(4096n, Nat.sub(e, F.off())), e, N.sub_add(e, 4096n, he)), NA.add_comm(4096n, Nat.sub(e, F.off())))
  +a1 = Equal.trans(Bool, Nat.is_lt(6141n, e), Nat.is_lt(6141n, Nat.add(Nat.sub(e, F.off()), 4096n)), Nat.is_lt(2045n, Nat.sub(e, F.off())), Equal.cong(Nat, Bool, z => Nat.is_lt(6141n, z), e, Nat.add(Nat.sub(e, F.off()), 4096n), ee), WW.lt_cancel_r(2045n, Nat.sub(e, F.off()), 4096n))
  +a2 = Equal.trans(Bool, Nat.is_eq(e, 6141n), Nat.is_eq(Nat.add(Nat.sub(e, F.off()), 4096n), 6141n), Nat.is_eq(Nat.sub(e, F.off()), 2045n), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 6141n), e, Nat.add(Nat.sub(e, F.off()), 4096n), ee), eq_cancel_r(Nat.sub(e, F.off()), 2045n, 4096n))
  +a3 = Equal.trans(Bool, X.le(WU.U64{0, 2147483648}, X.add(sig, WU.U64{512, 0})), Bool.not(C.fits(63n, Nat.add(SW.value(sig), 512n))), Bool.not(C.fits(53n, SF.rne(SW.value(sig), 10n))), ovle(one, h1, sig, h63, 2147483648, {==}), Equal.cong(Bool, Bool, t => Bool.not(t), C.fits(63n, Nat.add(SW.value(sig), 512n)), C.fits(53n, SF.rne(SW.value(sig), 10n)), Equal.sym(Bool, C.fits(53n, SF.rne(SW.value(sig), 10n)), C.fits(63n, Nat.add(SW.value(sig), 512n)), p2(one, h1, SW.value(sig), h63))))
  +LE = X.le(WU.U64{0, 2147483648}, X.add(sig, WU.U64{512, 0}))
  +c1 = Equal.cong(Bool, Bool, t => Bool.or(t, Bool.and(Nat.is_eq(e, 6141n), LE)), Nat.is_lt(6141n, e), Nat.is_lt(2045n, Nat.sub(e, F.off())), a1)
  +c2 = Equal.cong(Bool, Bool, t => Bool.or(Nat.is_lt(2045n, Nat.sub(e, F.off())), Bool.and(t, LE)), Nat.is_eq(e, 6141n), Nat.is_eq(Nat.sub(e, F.off()), 2045n), a2)
  +c3 = Equal.cong(Bool, Bool, t => Bool.or(Nat.is_lt(2045n, Nat.sub(e, F.off())), Bool.and(Nat.is_eq(Nat.sub(e, F.off()), 2045n), t)), LE, Bool.not(C.fits(53n, SF.rne(SW.value(sig), 10n))), a3)
  Equal.trans(Bool, Bool.or(Nat.is_lt(6141n, e), Bool.and(Nat.is_eq(e, 6141n), LE)), Bool.or(Nat.is_lt(2045n, Nat.sub(e, F.off())), Bool.and(Nat.is_eq(e, 6141n), LE)), Bool.not(Nat.is_lt(Nat.add(Nat.sub(e, F.off()), SF.pick(Nat, C.fits(53n, SF.rne(SW.value(sig), 10n)), 1n, 2n)), 2047n)), c1, Equal.trans(Bool, Bool.or(Nat.is_lt(2045n, Nat.sub(e, F.off())), Bool.and(Nat.is_eq(e, 6141n), LE)), Bool.or(Nat.is_lt(2045n, Nat.sub(e, F.off())), Bool.and(Nat.is_eq(Nat.sub(e, F.off()), 2045n), LE)), Bool.not(Nat.is_lt(Nat.add(Nat.sub(e, F.off()), SF.pick(Nat, C.fits(53n, SF.rne(SW.value(sig), 10n)), 1n, 2n)), 2047n)), c2, Equal.trans(Bool, Bool.or(Nat.is_lt(2045n, Nat.sub(e, F.off())), Bool.and(Nat.is_eq(Nat.sub(e, F.off()), 2045n), LE)), Bool.or(Nat.is_lt(2045n, Nat.sub(e, F.off())), Bool.and(Nat.is_eq(Nat.sub(e, F.off()), 2045n), Bool.not(C.fits(53n, SF.rne(SW.value(sig), 10n))))), Bool.not(Nat.is_lt(Nat.add(Nat.sub(e, F.off()), SF.pick(Nat, C.fits(53n, SF.rne(SW.value(sig), 10n)), 1n, 2n)), 2047n)), c3, ov_c(Nat.sub(e, F.off()), C.fits(53n, SF.rne(SW.value(sig), 10n))))))

def rp_nc(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +e: Nat, +sig: WU.U64, +x: Nat, +h62: {C.fits(62n, SW.value(sig)) == False{} : Bool}, +h63: {C.fits(63n, SW.value(sig)) == True{} : Bool}, +u: Nat, +hEF: {Nat.add(Nat.sub(e, F.off()), 1926n) == u : Nat}, +o: Bool, +ho: {Bool.not(Nat.is_lt(Nat.add(Nat.sub(e, F.off()), SF.pick(Nat, C.fits(53n, SF.rne(SW.value(sig), 10n)), 1n, 2n)), 2047n)) == o : Bool}) -> {F.rp_over(s, e, sig, o) == SF.pack(s, SF.rne(SW.value(sig), 10n), u) : F.F64}:
  match o:
    case True{}:
      +hovF = not_t(Nat.is_lt(Nat.add(Nat.sub(e, F.off()), SF.pick(Nat, C.fits(53n, SF.rne(SW.value(sig), 10n)), 1n, 2n)), 2047n), ho)
      Equal.trans(F.F64, F.inf(s), SF.inf(s), SF.pack(s, SF.rne(SW.value(sig), 10n), u), inf_v(s), Equal.sym(F.F64, SF.pack(s, SF.rne(SW.value(sig), 10n), u), SF.inf(s), pko(s, SF.rne(SW.value(sig), 10n), u, Nat.sub(e, F.off()), hEF, rne_norm(SW.value(sig), h62), hovF)))
    case False{}:
      +hovT = not_f(Nat.is_lt(Nat.add(Nat.sub(e, F.off()), SF.pick(Nat, C.fits(53n, SF.rne(SW.value(sig), 10n)), 1n, 2n)), 2047n), ho)
      +hz = rne_norm(SW.value(sig), h62)
      +hq = rne_top(one, h1, SW.value(sig), h63)
      +i1 = rpfE(s, Nat.sub(e, F.off()), sig, h63, ef11(Nat.sub(e, F.off()), SF.pick(Nat, C.fits(53n, SF.rne(SW.value(sig), 10n)), 1n, 2n), hovT), hz, qfit(one, h1, SF.rne(SW.value(sig), 10n), Nat.sub(e, F.off()), hq, hz, hovT))
      +h0 = Equal.cong(Bool, Bool, t => Bool.or(Bool.not(t), Nat.is_eq(Nat.sub(e, F.off()), 0n)), C.fits(52n, SF.rne(SW.value(sig), 10n)), False{}, hz)
      +sp = pkg(one, h1, s, SF.rne(SW.value(sig), 10n), u, Nat.sub(e, F.off()), hEF, hq, h0, hovT)
      Equal.trans(F.F64, F.rp_fin(s, Nat.sub(e, F.off()), sig), bits(s, Nat.add(SF.rne(SW.value(sig), 10n), C.shift(52n, Nat.sub(e, F.off())))), SF.pack(s, SF.rne(SW.value(sig), 10n), u), i1, Equal.sym(F.F64, SF.pack(s, SF.rne(SW.value(sig), 10n), u), bits(s, Nat.add(SF.rne(SW.value(sig), 10n), C.shift(52n, Nat.sub(e, F.off())))), sp))

def rp_norm(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +e: Nat, +sig: WU.U64, +x: Nat, +hx: {Nat.add(x, 2180n) == e : Nat}, +h62: {C.fits(62n, SW.value(sig)) == False{} : Bool}, +h63: {C.fits(63n, SW.value(sig)) == True{} : Bool}, +hb: {Nat.is_lt(x, 1916n) == False{} : Bool}, +u: Nat, +hu: {Nat.max(Nat.add(10n, x), 1926n) == u : Nat}) -> {F.rp_neg(s, e, sig, False{}) == SF.round_u(s, SW.value(sig), x, u) : F.F64}:
  +hge = N.not_lt_le(x, 1916n, hb)
  +hu1 = Equal.trans(Nat, u, Nat.max(Nat.add(10n, x), 1926n), Nat.add(10n, x), Equal.sym(Nat, Nat.max(Nat.add(10n, x), 1926n), u, hu), max_l(Nat.add(10n, x), 1926n, hge))
  +eEF = Equal.trans(Nat, Nat.sub(e, F.off()), Nat.sub(Nat.add(x, 2180n), F.off()), Nat.sub(x, 1916n), Equal.cong(Nat, Nat, z => Nat.sub(z, F.off()), e, Nat.add(x, 2180n), Equal.sym(Nat, Nat.add(x, 2180n), e, hx)), sub_cancel_r(x, 1916n, 2180n))
  +y = Nat.sub(x, 1916n)
  +ex = Equal.trans(Nat, Nat.add(y, 1926n), Nat.add(Nat.add(y, 1916n), 10n), u, Equal.sym(Nat, Nat.add(Nat.add(y, 1916n), 10n), Nat.add(y, 1926n), NA.add_assoc(y, 1916n, 10n)), Equal.trans(Nat, Nat.add(Nat.add(y, 1916n), 10n), Nat.add(x, 10n), u, Equal.cong(Nat, Nat, z => Nat.add(z, 10n), Nat.add(y, 1916n), x, Equal.trans(Nat, Nat.add(y, 1916n), Nat.add(1916n, y), x, NA.add_comm(y, 1916n), N.sub_add(x, 1916n, hge))), Equal.trans(Nat, Nat.add(x, 10n), Nat.add(10n, x), u, NA.add_comm(x, 10n), Equal.sym(Nat, u, Nat.add(10n, x), hu1))))
  +hEF = Equal.trans(Nat, Nat.add(Nat.sub(e, F.off()), 1926n), Nat.add(y, 1926n), u, Equal.cong(Nat, Nat, z => Nat.add(z, 1926n), Nat.sub(e, F.off()), y, eEF), ex)
  +hle = L.subst(Nat, z => {Nat.is_le(x, z) == True{} : Bool}, Nat.add(10n, x), u, Equal.sym(Nat, u, Nat.add(10n, x), hu1), L.subst(Nat, z => {Nat.is_le(x, z) == True{} : Bool}, Nat.add(x, 10n), Nat.add(10n, x), NA.add_comm(x, 10n), N.le_add_right(x, 10n)))
  +ku = Equal.trans(Nat, Nat.sub(u, x), Nat.sub(Nat.add(10n, x), x), 10n, Equal.cong(Nat, Nat, z => Nat.sub(z, x), u, Nat.add(10n, x), hu1), sub_add_l(10n, x))
  +s1 = Equal.cong(Bool, F.F64, t => SF.pack(s, SF.pick(Nat, t, SF.rne(SW.value(sig), Nat.sub(u, x)), C.shift(Nat.sub(x, u), SW.value(sig))), u), Nat.is_le(x, u), True{}, hle)
  +s2 = Equal.cong(Nat, F.F64, z => SF.pack(s, SF.rne(SW.value(sig), z), u), Nat.sub(u, x), 10n, ku)
  +sp = Equal.trans(F.F64, SF.round_u(s, SW.value(sig), x, u), SF.pack(s, SF.rne(SW.value(sig), Nat.sub(u, x)), u), SF.pack(s, SF.rne(SW.value(sig), 10n), u), s1, s2)
  +eo = ov_eq(one, h1, e, sig, x, hx, hge, h63)
  +i1 = Equal.cong(Bool, F.F64, t => F.rp_over(s, e, sig, t), Bool.or(Nat.is_lt(Nat.add(F.off(), 2045n), e), Bool.and(Nat.is_eq(e, Nat.add(F.off(), 2045n)), X.le(WU.U64{0, 2147483648}, X.add(sig, WU.U64{512, 0})))), Bool.not(Nat.is_lt(Nat.add(Nat.sub(e, F.off()), SF.pick(Nat, C.fits(53n, SF.rne(SW.value(sig), 10n)), 1n, 2n)), 2047n)), eo)
  +i2 = rp_nc(one, h1, s, e, sig, x, h62, h63, u, hEF, Bool.not(Nat.is_lt(Nat.add(Nat.sub(e, F.off()), SF.pick(Nat, C.fits(53n, SF.rne(SW.value(sig), 10n)), 1n, 2n)), 2047n)), {==})
  Equal.trans(F.F64, F.rp_over(s, e, sig, Bool.or(Nat.is_lt(Nat.add(F.off(), 2045n), e), Bool.and(Nat.is_eq(e, Nat.add(F.off(), 2045n)), X.le(WU.U64{0, 2147483648}, X.add(sig, WU.U64{512, 0}))))), SF.pack(s, SF.rne(SW.value(sig), 10n), u), SF.round_u(s, SW.value(sig), x, u), Equal.trans(F.F64, F.rp_over(s, e, sig, Bool.or(Nat.is_lt(Nat.add(F.off(), 2045n), e), Bool.and(Nat.is_eq(e, Nat.add(F.off(), 2045n)), X.le(WU.U64{0, 2147483648}, X.add(sig, WU.U64{512, 0}))))), F.rp_over(s, e, sig, Bool.not(Nat.is_lt(Nat.add(Nat.sub(e, F.off()), SF.pick(Nat, C.fits(53n, SF.rne(SW.value(sig), 10n)), 1n, 2n)), 2047n))), SF.pack(s, SF.rne(SW.value(sig), 10n), u), i1, i2), Equal.sym(F.F64, SF.round_u(s, SW.value(sig), x, u), SF.pack(s, SF.rne(SW.value(sig), 10n), u), sp))

def rp_c2(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +e: Nat, +sig: WU.U64, +x: Nat, +hx: {Nat.add(x, 2180n) == e : Nat}, +h62: {C.fits(62n, SW.value(sig)) == False{} : Bool}, +h63: {C.fits(63n, SW.value(sig)) == True{} : Bool}, +b: Bool, +hb: {Nat.is_lt(x, 1916n) == b : Bool}, +u: Nat, +hu: {Nat.max(Nat.add(10n, x), 1926n) == u : Nat}) -> {F.rp_neg(s, e, sig, b) == SF.round_u(s, SW.value(sig), x, u) : F.F64}:
  match b:
    case True{}:
      rp_sub(one, h1, s, e, sig, x, hx, h62, h63, hb, u, hu)
    case False{}:
      rp_norm(one, h1, s, e, sig, x, hx, h62, h63, hb, u, hu)

# SoftFloat's roundPackToF64(s, e, sig), sig with its top bit at 62 and e the
# biased exponent minus one plus OFF, is Flocq's round_NE of s * sig * 2^(e - 2180 - Z)
def round_pack(+s: Bool, +e: Nat, +sig: WU.U64, +x: Nat, +hx: {Nat.add(x, 2180n) == e : Nat}, +h62: {C.fits(62n, SW.value(sig)) == False{} : Bool}, +h63: {C.fits(63n, SW.value(sig)) == True{} : Bool}) -> {F.round_pack(s, e, sig) == SF.round(s, SW.value(sig), x) : F.F64}:
  +elt = Equal.trans(Bool, Nat.is_lt(e, F.off()), Nat.is_lt(Nat.add(x, 2180n), F.off()), Nat.is_lt(x, 1916n), Equal.cong(Nat, Bool, z => Nat.is_lt(z, F.off()), e, Nat.add(x, 2180n), Equal.sym(Nat, Nat.add(x, 2180n), e, hx)), WW.lt_cancel_r(x, 1916n, 2180n))
  +i1 = Equal.cong(Bool, F.F64, t => F.rp_neg(s, e, sig, t), Nat.is_lt(e, F.off()), Nat.is_lt(x, 1916n), elt)
  +i2 = rp_c2(1n, {==}, s, e, sig, x, hx, h62, h63, Nat.is_lt(x, 1916n), {==}, Nat.max(Nat.add(10n, x), 1926n), {==})
  +s0 = sr(s, SW.value(sig), x, h62, h63)
  Equal.trans(F.F64, F.rp_neg(s, e, sig, Nat.is_lt(e, F.off())), SF.round_u(s, SW.value(sig), x, Nat.max(Nat.add(10n, x), 1926n)), SF.round(s, SW.value(sig), x), Equal.trans(F.F64, F.rp_neg(s, e, sig, Nat.is_lt(e, F.off())), F.rp_neg(s, e, sig, Nat.is_lt(x, 1916n)), SF.round_u(s, SW.value(sig), x, Nat.max(Nat.add(10n, x), 1926n)), i1, i2), Equal.sym(F.F64, SF.round(s, SW.value(sig), x), SF.round_u(s, SW.value(sig), x, Nat.max(Nat.add(10n, x), 1926n)), s0))
