import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/spec/numeric.bend as S
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../lib/u32.bend as U
import ../../lib/u32div.bend as UD
import ../../lib/word.bend as WD
import ./width.bend as WW
import ./u32laws.bend as LW

# The bit-field clauses of spec/math/f64.bend: Neg, Abs, Copysign, IsNan,
# IsInf, IsFinite, IsZero and Signbit. A double is two U32 words; the high
# word H splits as H = F20 + 2^20 * (E + 2^11 * s) (fraction bits, exponent
# field, sign), which is the IEEE 754-2019 section 3.4 binary64 layout (the
# same decomposition as Flocq's Binary.split_bits / join_bits, Boldo and
# Melquiond, "Flocq: A Unified Library for Proving Floating-Point Algorithms
# in Coq", ARITH 2011). Masks and the sign bit are read on the bit words
# (U32 is a Word(32n)); no constant 2^k is ever expanded.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# ---- generic: words, masks and the top bit ----

def sb(+k: Nat, +x: Nat) -> {S.scale_binary(k, x) == C.shift(k, x) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.cong(Nat, Nat, t => Nat.double(t), S.scale_binary(p, x), C.shift(p, x), sb(p, x))

# the low k bits of a word
def andw(+n: Nat, +k: Nat, +w: Word(n)) -> {S.unsigned(n, Word.and(n, w, WD.mask(n, k))) == C.low(k, S.unsigned(n, w)) : Nat}:
  +a = S.unsigned(n, Word.and(n, w, WD.mask(n, k)))
  +hp = WD.hi_part(n, k, w)
  +e1 = WD.mask_split(n, k, w)
  +e2 = Equal.trans(Nat, S.unsigned(n, w), Nat.add(a, S.scale_binary(k, hp)), Nat.add(a, C.shift(k, hp)), e1, Equal.cong(Nat, Nat, z => Nat.add(a, z), S.scale_binary(k, hp), C.shift(k, hp), sb(k, hp)))
  +hl = WD.mask_lt(n, k, 1n, {==}, w)
  +hl2 = L.subst(Nat, z => {Nat.is_lt(a, z) == True{} : Bool}, S.scale_binary(k, 1n), C.pow2(k), Equal.sym(Nat, C.pow2(k), S.scale_binary(k, 1n), U.pow2_scale(k)), hl)
  Equal.sym(Nat, C.low(k, S.unsigned(n, w)), a, Equal.trans(Nat, C.low(k, S.unsigned(n, w)), C.low(k, Nat.add(a, C.shift(k, hp))), a, Equal.cong(Nat, Nat, z => C.low(k, z), S.unsigned(n, w), Nat.add(a, C.shift(k, hp)), e2), WW.low_uniq(k, a, hp, hl2)))

def andm0(+x: U32, +k: Nat) -> {v(U32.and(x, U32{WD.mask(32n, k)})) == C.low(k, v(x)) : Nat}:
  match x:
    case U32{+w}:
      +m = Word.and(32n, w, WD.mask(32n, k))
      Equal.trans(Nat, U32.to_nat(U32{m}), S.unsigned(32n, m), C.low(k, v(U32{w})), U.to_nat_word(m), Equal.trans(Nat, S.unsigned(32n, m), C.low(k, S.unsigned(32n, w)), C.low(k, v(U32{w})), andw(32n, k, w), Equal.cong(Nat, Nat, z => C.low(k, z), S.unsigned(32n, w), v(U32{w}), Equal.sym(Nat, v(U32{w}), S.unsigned(32n, w), U.to_nat_word(w)))))

# x and c for a mask constant c = 2^k - 1
def andm(+x: U32, +k: Nat, +c: U32, +hc: {c == U32{WD.mask(32n, k)} : U32}) -> {v(U32.and(x, c)) == C.low(k, v(x)) : Nat}:
  L.subst(U32, z => {v(U32.and(x, z)) == C.low(k, v(x)) : Nat}, U32{WD.mask(32n, k)}, c, Equal.sym(U32, c, U32{WD.mask(32n, k)}, hc), andm0(x, k))

# the value of a constant c = 2^k
def pwv(+k: Nat, +hk: {Nat.is_lt(k, 32n) == True{} : Bool}, +one: Nat, +h1: {one == 1n : Nat}, +c: U32, +hc: {c == U32{WD.pw(32n, k)} : U32}) -> {v(c) == C.shift(k, one) : Nat}:
  +e0 = Equal.trans(Nat, v(U32{WD.pw(32n, k)}), S.unsigned(32n, WD.pw(32n, k)), C.shift(k, one), U.to_nat_word(WD.pw(32n, k)), Equal.trans(Nat, S.unsigned(32n, WD.pw(32n, k)), S.scale_binary(k, one), C.shift(k, one), WD.pwv(32n, k, hk, one, h1, WD.pw(32n, k), {==}), sb(k, one)))
  L.subst(U32, z => {v(z) == C.shift(k, one) : Nat}, U32{WD.pw(32n, k)}, c, Equal.sym(U32, c, U32{WD.pw(32n, k)}, hc), e0)

# flipping the top bit
def xstep(+q: Nat, +b: Bool, +t: Word(1n+q), +ih: {S.unsigned(1n+q, Word.xor(1n+q, t, WD.pw(1n+q, q))) == Nat.add(C.low(q, S.unsigned(1n+q, t)), C.shift(q, Nat.sub(1n, C.high(q, S.unsigned(1n+q, t))))) : Nat}) -> {S.unsigned(2n+q, Word.xor(2n+q, WCon{b, t}, WD.pw(2n+q, 1n+q))) == Nat.add(C.low(1n+q, S.unsigned(2n+q, WCon{b, t})), C.shift(1n+q, Nat.sub(1n, C.high(1n+q, S.unsigned(2n+q, WCon{b, t}))))) : Nat}:
  match b:
    case True{}:
      +T = S.unsigned(1n+q, t)
      +X0 = S.unsigned(1n+q, Word.xor(1n+q, t, WD.pw(1n+q, q)))
      +lq = C.low(q, T)
      +sq = C.shift(q, Nat.sub(1n, C.high(q, T)))
      +U0 = Nat.add(1n, Nat.double(T))
      +e1 = Equal.cong(Nat, Nat, z => 1n+Nat.double(z), X0, Nat.add(lq, sq), ih)
      +e2 = Equal.cong(Nat, Nat, z => 1n+z, Nat.double(Nat.add(lq, sq)), Nat.add(Nat.double(lq), Nat.double(sq)), NA.double_add(lq, sq))
      +r1 = Equal.cong(Nat, Nat, z => Nat.add(Nat.add(z, Nat.double(C.low(q, C.half(U0)))), Nat.double(C.shift(q, Nat.sub(1n, C.high(q, C.half(U0)))))), C.bit(U0), 1n, WW.bit_dbl(1n, T))
      +r2 = Equal.cong(Nat, Nat, z => Nat.add(Nat.add(1n, Nat.double(C.low(q, z))), Nat.double(C.shift(q, Nat.sub(1n, C.high(q, z))))), C.half(U0), T, WW.half_dbl(1n, T))
      +r = Equal.trans(Nat, Nat.add(Nat.add(C.bit(U0), Nat.double(C.low(q, C.half(U0)))), Nat.double(C.shift(q, Nat.sub(1n, C.high(q, C.half(U0)))))), Nat.add(Nat.add(1n, Nat.double(C.low(q, C.half(U0)))), Nat.double(C.shift(q, Nat.sub(1n, C.high(q, C.half(U0)))))), Nat.add(Nat.add(1n, Nat.double(lq)), Nat.double(sq)), r1, r2)
      Equal.trans(Nat, 1n+Nat.double(X0), 1n+Nat.double(Nat.add(lq, sq)), Nat.add(Nat.add(C.bit(U0), Nat.double(C.low(q, C.half(U0)))), Nat.double(C.shift(q, Nat.sub(1n, C.high(q, C.half(U0)))))), e1, Equal.trans(Nat, 1n+Nat.double(Nat.add(lq, sq)), Nat.add(Nat.add(1n, Nat.double(lq)), Nat.double(sq)), Nat.add(Nat.add(C.bit(U0), Nat.double(C.low(q, C.half(U0)))), Nat.double(C.shift(q, Nat.sub(1n, C.high(q, C.half(U0)))))), e2, Equal.sym(Nat, Nat.add(Nat.add(C.bit(U0), Nat.double(C.low(q, C.half(U0)))), Nat.double(C.shift(q, Nat.sub(1n, C.high(q, C.half(U0)))))), Nat.add(Nat.add(1n, Nat.double(lq)), Nat.double(sq)), r)))
    case False{}:
      +T = S.unsigned(1n+q, t)
      +X0 = S.unsigned(1n+q, Word.xor(1n+q, t, WD.pw(1n+q, q)))
      +lq = C.low(q, T)
      +sq = C.shift(q, Nat.sub(1n, C.high(q, T)))
      +U0 = Nat.add(0n, Nat.double(T))
      +e1 = Equal.cong(Nat, Nat, z => Nat.double(z), X0, Nat.add(lq, sq), ih)
      +e2 = NA.double_add(lq, sq)
      +r1 = Equal.cong(Nat, Nat, z => Nat.add(Nat.add(z, Nat.double(C.low(q, C.half(U0)))), Nat.double(C.shift(q, Nat.sub(1n, C.high(q, C.half(U0)))))), C.bit(U0), 0n, WW.bit_dbl(0n, T))
      +r2 = Equal.cong(Nat, Nat, z => Nat.add(Nat.add(0n, Nat.double(C.low(q, z))), Nat.double(C.shift(q, Nat.sub(1n, C.high(q, z))))), C.half(U0), T, WW.half_dbl(0n, T))
      +r = Equal.trans(Nat, Nat.add(Nat.add(C.bit(U0), Nat.double(C.low(q, C.half(U0)))), Nat.double(C.shift(q, Nat.sub(1n, C.high(q, C.half(U0)))))), Nat.add(Nat.add(0n, Nat.double(C.low(q, C.half(U0)))), Nat.double(C.shift(q, Nat.sub(1n, C.high(q, C.half(U0)))))), Nat.add(Nat.double(lq), Nat.double(sq)), r1, r2)
      Equal.trans(Nat, Nat.double(X0), Nat.double(Nat.add(lq, sq)), Nat.add(Nat.add(C.bit(U0), Nat.double(C.low(q, C.half(U0)))), Nat.double(C.shift(q, Nat.sub(1n, C.high(q, C.half(U0)))))), e1, Equal.trans(Nat, Nat.double(Nat.add(lq, sq)), Nat.add(Nat.double(lq), Nat.double(sq)), Nat.add(Nat.add(C.bit(U0), Nat.double(C.low(q, C.half(U0)))), Nat.double(C.shift(q, Nat.sub(1n, C.high(q, C.half(U0)))))), e2, Equal.sym(Nat, Nat.add(Nat.add(C.bit(U0), Nat.double(C.low(q, C.half(U0)))), Nat.double(C.shift(q, Nat.sub(1n, C.high(q, C.half(U0)))))), Nat.add(Nat.double(lq), Nat.double(sq)), r)))

def xtop(+p: Nat, +w: Word(1n+p)) -> {S.unsigned(1n+p, Word.xor(1n+p, w, WD.pw(1n+p, p))) == Nat.add(C.low(p, S.unsigned(1n+p, w)), C.shift(p, Nat.sub(1n, C.high(p, S.unsigned(1n+p, w))))) : Nat}:
  match p:
    case 0n:
      match w:
        case WCon{+b, +t}:
          match b:
            case True{}:
              {==}
            case False{}:
              {==}
    case 1n+ +q:
      match w:
        case WCon{+b, +t}:
          xstep(q, b, t, xtop(q, t))

# keeping only the top bit
def astep(+q: Nat, +b: Bool, +t: Word(1n+q), +ih: {S.unsigned(1n+q, Word.and(1n+q, t, WD.pw(1n+q, q))) == C.shift(q, C.high(q, S.unsigned(1n+q, t))) : Nat}) -> {S.unsigned(2n+q, Word.and(2n+q, WCon{b, t}, WD.pw(2n+q, 1n+q))) == C.shift(1n+q, C.high(1n+q, S.unsigned(2n+q, WCon{b, t}))) : Nat}:
  match b:
    case True{}:
      +T = S.unsigned(1n+q, t)
      +A0 = S.unsigned(1n+q, Word.and(1n+q, t, WD.pw(1n+q, q)))
      +U0 = Nat.add(1n, Nat.double(T))
      Equal.trans(Nat, Nat.double(A0), Nat.double(C.shift(q, C.high(q, T))), Nat.double(C.shift(q, C.high(q, C.half(U0)))), Equal.cong(Nat, Nat, z => Nat.double(z), A0, C.shift(q, C.high(q, T)), ih), Equal.cong(Nat, Nat, z => Nat.double(C.shift(q, C.high(q, z))), T, C.half(U0), Equal.sym(Nat, C.half(U0), T, WW.half_dbl(1n, T))))
    case False{}:
      +T = S.unsigned(1n+q, t)
      +A0 = S.unsigned(1n+q, Word.and(1n+q, t, WD.pw(1n+q, q)))
      +U0 = Nat.add(0n, Nat.double(T))
      Equal.trans(Nat, Nat.double(A0), Nat.double(C.shift(q, C.high(q, T))), Nat.double(C.shift(q, C.high(q, C.half(U0)))), Equal.cong(Nat, Nat, z => Nat.double(z), A0, C.shift(q, C.high(q, T)), ih), Equal.cong(Nat, Nat, z => Nat.double(C.shift(q, C.high(q, z))), T, C.half(U0), Equal.sym(Nat, C.half(U0), T, WW.half_dbl(0n, T))))

def atop(+p: Nat, +w: Word(1n+p)) -> {S.unsigned(1n+p, Word.and(1n+p, w, WD.pw(1n+p, p))) == C.shift(p, C.high(p, S.unsigned(1n+p, w))) : Nat}:
  match p:
    case 0n:
      match w:
        case WCon{+b, +t}:
          match b:
            case True{}:
              {==}
            case False{}:
              {==}
    case 1n+ +q:
      match w:
        case WCon{+b, +t}:
          astep(q, b, t, atop(q, t))

# ---- Nat and Bool facts ----

def le_nlt(+a: Nat, +b: Nat) -> {Nat.is_le(a, b) == Bool.not(Nat.is_lt(b, a)) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+ +bp:
      {==}
    case 1n+ +ap 0n:
      {==}
    case 1n+ +ap 1n+ +bp:
      le_nlt(ap, bp)

# 2^k <= n exactly when n does not fit k bits
def le_fit(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +n: Nat) -> {Nat.is_le(C.shift(k, one), n) == Bool.not(C.fits(k, n)) : Bool}:
  +e2a = Equal.trans(Bool, Nat.is_lt(n, C.shift(k, 1n)), Nat.is_lt(n, C.pow2(k)), C.fits(k, n), Equal.cong(Nat, Bool, z => Nat.is_lt(n, z), C.shift(k, 1n), C.pow2(k), WW.shift_one(k)), Equal.sym(Bool, C.fits(k, n), Nat.is_lt(n, C.pow2(k)), WW.fits_lt(k, n)))
  +e2 = L.subst(Nat, o => {Nat.is_lt(n, C.shift(k, o)) == C.fits(k, n) : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), e2a)
  Equal.trans(Bool, Nat.is_le(C.shift(k, one), n), Bool.not(Nat.is_lt(n, C.shift(k, one))), Bool.not(C.fits(k, n)), le_nlt(C.shift(k, one), n), Equal.cong(Bool, Bool, z => Bool.not(z), Nat.is_lt(n, C.shift(k, one)), C.fits(k, n), e2))

# n div 2^k
def div_sh(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +n: Nat) -> {Nat.div(n, C.shift(k, one)) == C.high(k, n) : Nat}:
  +pp = Nat.sub(C.shift(k, one), 1n)
  +ep = Equal.trans(Nat, C.pow2(k), C.shift(k, 1n), C.shift(k, one), Equal.sym(Nat, C.shift(k, 1n), C.pow2(k), WW.shift_one(k)), Equal.cong(Nat, Nat, o => C.shift(k, o), 1n, one, Equal.sym(Nat, one, 1n, h1)))
  +hpos = L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, C.pow2(k), C.shift(k, one), ep, N.pow2_pos(k))
  +hs = N.sub_add(C.shift(k, one), 1n, hpos)
  +hp = Equal.trans(Nat, C.pow2(k), C.shift(k, one), 1n+pp, ep, Equal.sym(Nat, 1n+pp, C.shift(k, one), hs))
  L.subst(Nat, z => {Nat.div(n, z) == C.high(k, n) : Nat}, 1n+pp, C.shift(k, one), hs, Equal.sym(Nat, C.high(k, n), Nat.div(n, 1n+pp), WW.high_div(k, n, pp, hp)))

def z2(+a: Nat, +k: Nat, +b: Nat) -> {Nat.is_eq(Nat.add(a, C.shift(k, b)), 0n) == Bool.and(Nat.is_eq(a, 0n), Nat.is_eq(b, 0n)) : Bool}:
  match a:
    case 0n:
      WW.shift_eq0(k, b)
    case 1n+ +ap:
      {==}

def lt_ne(+a: Nat, +m: Nat, +h: {Nat.is_lt(a, 1n+m) == True{} : Bool}) -> {Nat.is_lt(a, m) == Bool.not(Nat.is_eq(a, m)) : Bool}:
  match a m:
    case 0n 0n:
      {==}
    case 0n 1n+ +mp:
      {==}
    case 1n+ +ap 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 0n) == Bool.not(Nat.is_eq(1n+ap, 0n)) : Bool}, N.lt_zero_absurd(ap, h))
    case 1n+ +ap 1n+ +mp:
      lt_ne(ap, mp, h)

def rot3(+a: Bool, +b: Bool, +c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(c, Bool.and(a, b)) : Bool}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# the low a + b bits: the low a, then the next b
def low_split(+a: Nat, +b: Nat, +n: Nat) -> {C.low(Nat.add(a, b), n) == Nat.add(C.low(a, n), C.shift(a, C.low(b, C.high(a, n)))) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+ +p:
      +l = C.low(p, C.half(n))
      +s = C.shift(p, C.low(b, C.high(p, C.half(n))))
      Equal.trans(Nat, Nat.add(C.bit(n), Nat.double(C.low(Nat.add(p, b), C.half(n)))), Nat.add(C.bit(n), Nat.double(Nat.add(l, s))), Nat.add(Nat.add(C.bit(n), Nat.double(l)), Nat.double(s)), Equal.cong(Nat, Nat, z => Nat.add(C.bit(n), Nat.double(z)), C.low(Nat.add(p, b), C.half(n)), Nat.add(l, s), low_split(p, b, C.half(n))), Equal.trans(Nat, Nat.add(C.bit(n), Nat.double(Nat.add(l, s))), Nat.add(C.bit(n), Nat.add(Nat.double(l), Nat.double(s))), Nat.add(Nat.add(C.bit(n), Nat.double(l)), Nat.double(s)), Equal.cong(Nat, Nat, z => Nat.add(C.bit(n), z), Nat.double(Nat.add(l, s)), Nat.add(Nat.double(l), Nat.double(s)), NA.double_add(l, s)), Equal.sym(Nat, Nat.add(Nat.add(C.bit(n), Nat.double(l)), Nat.double(s)), Nat.add(C.bit(n), Nat.add(Nat.double(l), Nat.double(s))), NA.add_assoc(C.bit(n), Nat.double(l), Nat.double(s)))))

# ---- the fields of the high word ----

# the exponent field
def ef_g(+one: Nat, +h1: {one == 1n : Nat}, +h: U32, +c20: U32, +hc20: {c20 == U32{WD.pw(32n, 20n)} : U32}, +m11: U32, +hm11: {m11 == U32{WD.mask(32n, 11n)} : U32}) -> {v(U32.and(U32.div(h, c20), m11)) == C.low(11n, C.high(20n, v(h))) : Nat}:
  +hz = L.subst(U32, z => {U32.is_zero(z) == False{} : Bool}, U32{WD.pw(32n, 20n)}, c20, Equal.sym(U32, c20, U32{WD.pw(32n, 20n)}, hc20), {==})
  +d = U32.div(h, c20)
  +e3 = Equal.trans(Nat, v(d), Nat.div(v(h), v(c20)), Nat.div(v(h), C.shift(20n, one)), UD.div_nat(h, c20, hz), Equal.cong(Nat, Nat, z => Nat.div(v(h), z), v(c20), C.shift(20n, one), pwv(20n, {==}, one, h1, c20, hc20)))
  +e4 = Equal.trans(Nat, v(d), Nat.div(v(h), C.shift(20n, one)), C.high(20n, v(h)), e3, div_sh(20n, one, h1, v(h)))
  Equal.trans(Nat, v(U32.and(d, m11)), C.low(11n, v(d)), C.low(11n, C.high(20n, v(h))), andm(d, 11n, m11, hm11), Equal.cong(Nat, Nat, z => C.low(11n, z), v(d), C.high(20n, v(h)), e4))

# the fraction is zero
def fz_g(+l: U32, +h: U32, +m20: U32, +hm20: {m20 == U32{WD.mask(32n, 20n)} : U32}) -> {X.is_zero(WU.U64{l, U32.and(h, m20)}) == Nat.is_eq(SF.frac(F.Bits{l, h}), 0n) : Bool}:
  +f = C.low(20n, v(h))
  +e1 = Equal.cong(Bool, Bool, z => Bool.and(z, U32.is_zero(U32.and(h, m20))), U32.is_zero(l), Nat.is_eq(v(l), 0n), LW.zero_nat(l))
  +e2 = Equal.trans(Bool, U32.is_zero(U32.and(h, m20)), Nat.is_eq(v(U32.and(h, m20)), 0n), Nat.is_eq(f, 0n), LW.zero_nat(U32.and(h, m20)), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), v(U32.and(h, m20)), f, andm(h, 20n, m20, hm20)))
  +e3 = Equal.cong(Bool, Bool, z => Bool.and(Nat.is_eq(v(l), 0n), z), U32.is_zero(U32.and(h, m20)), Nat.is_eq(f, 0n), e2)
  Equal.trans(Bool, Bool.and(U32.is_zero(l), U32.is_zero(U32.and(h, m20))), Bool.and(Nat.is_eq(v(l), 0n), U32.is_zero(U32.and(h, m20))), Nat.is_eq(Nat.add(v(l), C.shift(32n, f)), 0n), e1, Equal.trans(Bool, Bool.and(Nat.is_eq(v(l), 0n), U32.is_zero(U32.and(h, m20))), Bool.and(Nat.is_eq(v(l), 0n), Nat.is_eq(f, 0n)), Nat.is_eq(Nat.add(v(l), C.shift(32n, f)), 0n), e3, Equal.sym(Bool, Nat.is_eq(Nat.add(v(l), C.shift(32n, f)), 0n), Bool.and(Nat.is_eq(v(l), 0n), Nat.is_eq(f, 0n)), z2(v(l), 32n, f))))

# ---- the classification clauses ----

def signbit_g(+one: Nat, +h1: {one == 1n : Nat}, +l: U32, +h: U32, +c: U32, +hc: {c == U32{WD.pw(32n, 31n)} : U32}) -> {Cmp.is_le(U32.cmp(c, h)) == SF.sign(F.Bits{l, h}) : Bool}:
  +e1 = Equal.cong(Cmp, Bool, t => Cmp.is_le(t), U32.cmp(c, h), Nat.cmp(v(c), v(h)), U.u32_cmp(c, h))
  +e2 = Equal.cong(Nat, Bool, z => Nat.is_le(z, v(h)), v(c), C.shift(31n, one), pwv(31n, {==}, one, h1, c, hc))
  Equal.trans(Bool, Cmp.is_le(U32.cmp(c, h)), Nat.is_le(v(c), v(h)), Bool.not(C.fits(31n, v(h))), e1, Equal.trans(Bool, Nat.is_le(v(c), v(h)), Nat.is_le(C.shift(31n, one), v(h)), Bool.not(C.fits(31n, v(h))), e2, le_fit(31n, one, h1, v(h))))

def signbit_value(+x: F.F64) -> SF.Signbit.value(x):
  match x:
    case F.Bits{+l, +h}:
      signbit_g(1n, {==}, l, h, 2147483648, {==})

def isnan_g(+one: Nat, +h1: {one == 1n : Nat}, +l: U32, +h: U32, +c20: U32, +hc20: {c20 == U32{WD.pw(32n, 20n)} : U32}, +m11: U32, +hm11: {m11 == U32{WD.mask(32n, 11n)} : U32}, +m20: U32, +hm20: {m20 == U32{WD.mask(32n, 20n)} : U32}) -> {Bool.and(Nat.is_eq(v(U32.and(U32.div(h, c20), m11)), 2047n), Bool.not(X.is_zero(WU.U64{l, U32.and(h, m20)}))) == SF.is_nan(F.Bits{l, h}) : Bool}:
  +ei = v(U32.and(U32.div(h, c20), m11))
  +es = SF.efield(F.Bits{l, h})
  +zi = X.is_zero(WU.U64{l, U32.and(h, m20)})
  +zs = Nat.is_eq(SF.frac(F.Bits{l, h}), 0n)
  Equal.trans(Bool, Bool.and(Nat.is_eq(ei, 2047n), Bool.not(zi)), Bool.and(Nat.is_eq(es, 2047n), Bool.not(zi)), Bool.and(Nat.is_eq(es, 2047n), Bool.not(zs)), Equal.cong(Nat, Bool, z => Bool.and(Nat.is_eq(z, 2047n), Bool.not(zi)), ei, es, ef_g(one, h1, h, c20, hc20, m11, hm11)), Equal.cong(Bool, Bool, z => Bool.and(Nat.is_eq(es, 2047n), Bool.not(z)), zi, zs, fz_g(l, h, m20, hm20)))

def is_nan_value(+x: F.F64) -> SF.IsNan.value(x):
  match x:
    case F.Bits{+l, +h}:
      isnan_g(1n, {==}, l, h, 1048576, {==}, 2047, {==}, 1048575, {==})

def isinf_g(+one: Nat, +h1: {one == 1n : Nat}, +l: U32, +h: U32, +c20: U32, +hc20: {c20 == U32{WD.pw(32n, 20n)} : U32}, +m11: U32, +hm11: {m11 == U32{WD.mask(32n, 11n)} : U32}, +m20: U32, +hm20: {m20 == U32{WD.mask(32n, 20n)} : U32}) -> {Bool.and(Nat.is_eq(v(U32.and(U32.div(h, c20), m11)), 2047n), X.is_zero(WU.U64{l, U32.and(h, m20)})) == SF.is_inf(F.Bits{l, h}) : Bool}:
  +ei = v(U32.and(U32.div(h, c20), m11))
  +es = SF.efield(F.Bits{l, h})
  +zi = X.is_zero(WU.U64{l, U32.and(h, m20)})
  +zs = Nat.is_eq(SF.frac(F.Bits{l, h}), 0n)
  Equal.trans(Bool, Bool.and(Nat.is_eq(ei, 2047n), zi), Bool.and(Nat.is_eq(es, 2047n), zi), Bool.and(Nat.is_eq(es, 2047n), zs), Equal.cong(Nat, Bool, z => Bool.and(Nat.is_eq(z, 2047n), zi), ei, es, ef_g(one, h1, h, c20, hc20, m11, hm11)), Equal.cong(Bool, Bool, z => Bool.and(Nat.is_eq(es, 2047n), z), zi, zs, fz_g(l, h, m20, hm20)))

def is_inf_value(+x: F.F64) -> SF.IsInf.value(x):
  match x:
    case F.Bits{+l, +h}:
      isinf_g(1n, {==}, l, h, 1048576, {==}, 2047, {==}, 1048575, {==})

def isfin_g(+one: Nat, +h1: {one == 1n : Nat}, +l: U32, +h: U32, +c20: U32, +hc20: {c20 == U32{WD.pw(32n, 20n)} : U32}, +m11: U32, +hm11: {m11 == U32{WD.mask(32n, 11n)} : U32}) -> {Nat.is_lt(v(U32.and(U32.div(h, c20), m11)), 2047n) == Bool.not(Nat.is_eq(SF.efield(F.Bits{l, h}), 2047n)) : Bool}:
  +ei = v(U32.and(U32.div(h, c20), m11))
  +es = SF.efield(F.Bits{l, h})
  Equal.trans(Bool, Nat.is_lt(ei, 2047n), Nat.is_lt(es, 2047n), Bool.not(Nat.is_eq(es, 2047n)), Equal.cong(Nat, Bool, z => Nat.is_lt(z, 2047n), ei, es, ef_g(one, h1, h, c20, hc20, m11, hm11)), lt_ne(es, 2047n, WW.low_lt(11n, C.high(20n, v(h)))))

def is_finite_value(+x: F.F64) -> SF.IsFinite.value(x):
  match x:
    case F.Bits{+l, +h}:
      isfin_g(1n, {==}, l, h, 1048576, {==}, 2047, {==})

def iszero_g(+l: U32, +h: U32, +m31: U32, +hm31: {m31 == U32{WD.mask(32n, 31n)} : U32}) -> {X.is_zero(WU.U64{l, U32.and(h, m31)}) == SF.is_zero(F.Bits{l, h}) : Bool}:
  +H = v(h)
  +f = C.low(20n, H)
  +E = C.low(11n, C.high(20n, H))
  +e1 = Equal.cong(Bool, Bool, z => Bool.and(z, U32.is_zero(U32.and(h, m31))), U32.is_zero(l), Nat.is_eq(v(l), 0n), LW.zero_nat(l))
  +e2 = Equal.trans(Bool, U32.is_zero(U32.and(h, m31)), Nat.is_eq(v(U32.and(h, m31)), 0n), Nat.is_eq(C.low(31n, H), 0n), LW.zero_nat(U32.and(h, m31)), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), v(U32.and(h, m31)), C.low(31n, H), andm(h, 31n, m31, hm31)))
  +e3 = Equal.trans(Bool, Nat.is_eq(C.low(31n, H), 0n), Nat.is_eq(Nat.add(f, C.shift(20n, E)), 0n), Bool.and(Nat.is_eq(f, 0n), Nat.is_eq(E, 0n)), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), C.low(31n, H), Nat.add(f, C.shift(20n, E)), low_split(20n, 11n, H)), z2(f, 20n, E))
  +e4 = Equal.cong(Bool, Bool, z => Bool.and(Nat.is_eq(v(l), 0n), z), U32.is_zero(U32.and(h, m31)), Bool.and(Nat.is_eq(f, 0n), Nat.is_eq(E, 0n)), Equal.trans(Bool, U32.is_zero(U32.and(h, m31)), Nat.is_eq(C.low(31n, H), 0n), Bool.and(Nat.is_eq(f, 0n), Nat.is_eq(E, 0n)), e2, e3))
  +e5 = rot3(Nat.is_eq(v(l), 0n), Nat.is_eq(f, 0n), Nat.is_eq(E, 0n))
  +e6 = Equal.cong(Bool, Bool, z => Bool.and(Nat.is_eq(E, 0n), z), Bool.and(Nat.is_eq(v(l), 0n), Nat.is_eq(f, 0n)), Nat.is_eq(Nat.add(v(l), C.shift(32n, f)), 0n), Equal.sym(Bool, Nat.is_eq(Nat.add(v(l), C.shift(32n, f)), 0n), Bool.and(Nat.is_eq(v(l), 0n), Nat.is_eq(f, 0n)), z2(v(l), 32n, f)))
  Equal.trans(Bool, Bool.and(U32.is_zero(l), U32.is_zero(U32.and(h, m31))), Bool.and(Nat.is_eq(v(l), 0n), U32.is_zero(U32.and(h, m31))), Bool.and(Nat.is_eq(E, 0n), Nat.is_eq(Nat.add(v(l), C.shift(32n, f)), 0n)), e1, Equal.trans(Bool, Bool.and(Nat.is_eq(v(l), 0n), U32.is_zero(U32.and(h, m31))), Bool.and(Nat.is_eq(v(l), 0n), Bool.and(Nat.is_eq(f, 0n), Nat.is_eq(E, 0n))), Bool.and(Nat.is_eq(E, 0n), Nat.is_eq(Nat.add(v(l), C.shift(32n, f)), 0n)), e4, Equal.trans(Bool, Bool.and(Nat.is_eq(v(l), 0n), Bool.and(Nat.is_eq(f, 0n), Nat.is_eq(E, 0n))), Bool.and(Nat.is_eq(E, 0n), Bool.and(Nat.is_eq(v(l), 0n), Nat.is_eq(f, 0n))), Bool.and(Nat.is_eq(E, 0n), Nat.is_eq(Nat.add(v(l), C.shift(32n, f)), 0n)), e5, e6)))

def is_zero_value(+x: F.F64) -> SF.IsZero.value(x):
  match x:
    case F.Bits{+l, +h}:
      iszero_g(l, h, 2147483647, {==})

# ---- sign flips, masks and the sign bit ----

def xorv0(+h: U32) -> {v(U32.xor(h, U32{WD.pw(32n, 31n)})) == Nat.add(C.low(31n, v(h)), C.shift(31n, Nat.sub(1n, C.high(31n, v(h))))) : Nat}:
  match h:
    case U32{+w}:
      +m = Word.xor(32n, w, WD.pw(32n, 31n))
      +e0 = Equal.sym(Nat, v(U32{w}), S.unsigned(32n, w), U.to_nat_word(w))
      Equal.trans(Nat, U32.to_nat(U32{m}), S.unsigned(32n, m), Nat.add(C.low(31n, v(U32{w})), C.shift(31n, Nat.sub(1n, C.high(31n, v(U32{w}))))), U.to_nat_word(m), Equal.trans(Nat, S.unsigned(32n, m), Nat.add(C.low(31n, S.unsigned(32n, w)), C.shift(31n, Nat.sub(1n, C.high(31n, S.unsigned(32n, w))))), Nat.add(C.low(31n, v(U32{w})), C.shift(31n, Nat.sub(1n, C.high(31n, v(U32{w}))))), xtop(31n, w), Equal.cong(Nat, Nat, z => Nat.add(C.low(31n, z), C.shift(31n, Nat.sub(1n, C.high(31n, z)))), S.unsigned(32n, w), v(U32{w}), e0)))

def xorv(+h: U32, +c: U32, +hc: {c == U32{WD.pw(32n, 31n)} : U32}) -> {v(U32.xor(h, c)) == Nat.add(C.low(31n, v(h)), C.shift(31n, Nat.sub(1n, C.high(31n, v(h))))) : Nat}:
  L.subst(U32, z => {v(U32.xor(h, z)) == Nat.add(C.low(31n, v(h)), C.shift(31n, Nat.sub(1n, C.high(31n, v(h))))) : Nat}, U32{WD.pw(32n, 31n)}, c, Equal.sym(U32, c, U32{WD.pw(32n, 31n)}, hc), xorv0(h))

def andv0(+h: U32) -> {v(U32.and(h, U32{WD.pw(32n, 31n)})) == C.shift(31n, C.high(31n, v(h))) : Nat}:
  match h:
    case U32{+w}:
      +m = Word.and(32n, w, WD.pw(32n, 31n))
      +e0 = Equal.sym(Nat, v(U32{w}), S.unsigned(32n, w), U.to_nat_word(w))
      Equal.trans(Nat, U32.to_nat(U32{m}), S.unsigned(32n, m), C.shift(31n, C.high(31n, v(U32{w}))), U.to_nat_word(m), Equal.trans(Nat, S.unsigned(32n, m), C.shift(31n, C.high(31n, S.unsigned(32n, w))), C.shift(31n, C.high(31n, v(U32{w}))), atop(31n, w), Equal.cong(Nat, Nat, z => C.shift(31n, C.high(31n, z)), S.unsigned(32n, w), v(U32{w}), e0)))

def andv(+h: U32, +c: U32, +hc: {c == U32{WD.pw(32n, 31n)} : U32}) -> {v(U32.and(h, c)) == C.shift(31n, C.high(31n, v(h))) : Nat}:
  L.subst(U32, z => {v(U32.and(h, z)) == C.shift(31n, C.high(31n, v(h))) : Nat}, U32{WD.pw(32n, 31n)}, c, Equal.sym(U32, c, U32{WD.pw(32n, 31n)}, hc), andv0(h))

# an addition below 2^32 is exact
def addv(+one: Nat, +h1: {one == 1n : Nat}, +a: U32, +b: U32, +h: {Nat.is_lt(Nat.add(v(a), v(b)), C.shift(32n, one)) == True{} : Bool}) -> {v(U32.add(a, b)) == Nat.add(v(a), v(b)) : Nat}:
  match a b:
    case U32{+x} U32{+y}:
      +ex = U.to_nat_word(x)
      +ey = U.to_nat_word(y)
      +es = Equal.trans(Nat, Nat.add(v(U32{x}), v(U32{y})), Nat.add(S.unsigned(32n, x), v(U32{y})), Nat.add(S.unsigned(32n, x), S.unsigned(32n, y)), Equal.cong(Nat, Nat, z => Nat.add(z, v(U32{y})), v(U32{x}), S.unsigned(32n, x), ex), Equal.cong(Nat, Nat, z => Nat.add(S.unsigned(32n, x), z), v(U32{y}), S.unsigned(32n, y), ey))
      +h2 = L.subst(Nat, z => {Nat.is_lt(z, C.shift(32n, one)) == True{} : Bool}, Nat.add(v(U32{x}), v(U32{y})), Nat.add(S.unsigned(32n, x), S.unsigned(32n, y)), es, h)
      +h3 = L.subst(Nat, z => {Nat.is_lt(Nat.add(S.unsigned(32n, x), S.unsigned(32n, y)), z) == True{} : Bool}, C.shift(32n, one), S.scale_binary(32n, one), Equal.sym(Nat, S.scale_binary(32n, one), C.shift(32n, one), sb(32n, one)), h2)
      +m = Word.add(32n, x, y)
      Equal.trans(Nat, U32.to_nat(U32{m}), S.unsigned(32n, m), Nat.add(v(U32{x}), v(U32{y})), U.to_nat_word(m), Equal.trans(Nat, S.unsigned(32n, m), Nat.add(S.unsigned(32n, x), S.unsigned(32n, y)), Nat.add(v(U32{x}), v(U32{y})), WD.add_exact(32n, one, h1, x, y, h3), Equal.sym(Nat, Nat.add(v(U32{x}), v(U32{y})), Nat.add(S.unsigned(32n, x), S.unsigned(32n, y)), es)))

# the sign bit c of a 32-bit word is 0 or 1
def half0(+h: U32) -> {Nat.is_eq(C.half(C.high(31n, v(h))), 0n) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_eq(z, 0n) == True{} : Bool}, C.high(32n, v(h)), C.high(1n, C.high(31n, v(h))), WW.high_comp(1n, 31n, v(h)), LW.vb(h))

def bit_c(+c: Nat, +h2: {Nat.is_eq(C.half(c), 0n) == True{} : Bool}) -> {c == SF.b2n(Bool.not(Nat.is_eq(c, 0n))) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+ +q:
      Empty.absurd({2n+q == SF.b2n(Bool.not(Nat.is_eq(2n+q, 0n))) : Nat}, LW.true_ne_false(Equal.sym(Bool, False{}, True{}, h2)))

def nbit_c(+c: Nat, +h2: {Nat.is_eq(C.half(c), 0n) == True{} : Bool}) -> {Nat.sub(1n, c) == SF.b2n(Bool.not(Bool.not(Nat.is_eq(c, 0n)))) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+ +q:
      Empty.absurd({Nat.sub(1n, 2n+q) == SF.b2n(Bool.not(Bool.not(Nat.is_eq(2n+q, 0n)))) : Nat}, LW.true_ne_false(Equal.sym(Bool, False{}, True{}, h2)))

# f + 2^20 E + 2^31 t is f + 2^20 (E + 2^11 t)
def fold(+f: Nat, +E: Nat, +t: Nat) -> {Nat.add(Nat.add(f, C.shift(20n, E)), C.shift(31n, t)) == Nat.add(f, C.shift(20n, Nat.add(E, C.shift(11n, t)))) : Nat}:
  +e1 = NA.add_assoc(f, C.shift(20n, E), C.shift(31n, t))
  +e2 = Equal.cong(Nat, Nat, z => Nat.add(f, Nat.add(C.shift(20n, E), z)), C.shift(31n, t), C.shift(20n, C.shift(11n, t)), WW.shift_comp(20n, 11n, t))
  +e3 = Equal.cong(Nat, Nat, z => Nat.add(f, z), Nat.add(C.shift(20n, E), C.shift(20n, C.shift(11n, t))), C.shift(20n, Nat.add(E, C.shift(11n, t))), Equal.sym(Nat, C.shift(20n, Nat.add(E, C.shift(11n, t))), Nat.add(C.shift(20n, E), C.shift(20n, C.shift(11n, t))), WW.shift_add(20n, E, C.shift(11n, t))))
  Equal.trans(Nat, Nat.add(Nat.add(f, C.shift(20n, E)), C.shift(31n, t)), Nat.add(f, Nat.add(C.shift(20n, E), C.shift(31n, t))), Nat.add(f, C.shift(20n, Nat.add(E, C.shift(11n, t)))), e1, Equal.trans(Nat, Nat.add(f, Nat.add(C.shift(20n, E), C.shift(31n, t))), Nat.add(f, Nat.add(C.shift(20n, E), C.shift(20n, C.shift(11n, t)))), Nat.add(f, C.shift(20n, Nat.add(E, C.shift(11n, t)))), e2, e3))

# a pattern with the fraction and exponent of x and sign s is encode(s, ...)
def enc_g(+l: U32, +h: U32, +s: Bool, +y: U32, +hy: {v(y) == Nat.add(C.low(20n, v(h)), C.shift(20n, Nat.add(C.low(11n, C.high(20n, v(h))), C.shift(11n, SF.b2n(s))))) : Nat}) -> {F.Bits{l, y} == SF.encode(s, SF.efield(F.Bits{l, h}), SF.frac(F.Bits{l, h})) : F.F64}:
  +f = C.low(20n, v(h))
  +T = C.shift(20n, Nat.add(C.low(11n, C.high(20n, v(h))), C.shift(11n, SF.b2n(s))))
  +fr = Nat.add(v(l), C.shift(32n, f))
  +elo = Equal.trans(U32, U32.from_nat(C.low(32n, fr)), U32.from_nat(v(l)), l, Equal.cong(Nat, U32, z => U32.from_nat(z), C.low(32n, fr), v(l), WW.low_u(32n, v(l), f, LW.vb(l))), LW.rt(l))
  +ehi0 = Equal.trans(Nat, Nat.add(C.high(32n, fr), T), Nat.add(f, T), v(y), Equal.cong(Nat, Nat, z => Nat.add(z, T), C.high(32n, fr), f, WW.high_u(32n, v(l), f, LW.vb(l))), Equal.sym(Nat, v(y), Nat.add(f, T), hy))
  +ehi = Equal.trans(U32, U32.from_nat(Nat.add(C.high(32n, fr), T)), U32.from_nat(v(y)), y, Equal.cong(Nat, U32, z => U32.from_nat(z), Nat.add(C.high(32n, fr), T), v(y), ehi0), LW.rt(y))
  +e = Equal.trans(F.F64, F.Bits{U32.from_nat(C.low(32n, fr)), U32.from_nat(Nat.add(C.high(32n, fr), T))}, F.Bits{l, U32.from_nat(Nat.add(C.high(32n, fr), T))}, F.Bits{l, y}, Equal.cong(U32, F.F64, z => F.Bits{z, U32.from_nat(Nat.add(C.high(32n, fr), T))}, U32.from_nat(C.low(32n, fr)), l, elo), Equal.cong(U32, F.F64, z => F.Bits{l, z}, U32.from_nat(Nat.add(C.high(32n, fr), T)), y, ehi))
  Equal.sym(F.F64, F.Bits{U32.from_nat(C.low(32n, fr)), U32.from_nat(Nat.add(C.high(32n, fr), T))}, F.Bits{l, y}, e)

def neg_g(+l: U32, +h: U32, +c: U32, +hc: {c == U32{WD.pw(32n, 31n)} : U32}) -> {F.Bits{l, U32.xor(h, c)} == SF.neg(F.Bits{l, h}) : F.F64}:
  +H = v(h)
  +f = C.low(20n, H)
  +E = C.low(11n, C.high(20n, H))
  +t = Nat.sub(1n, C.high(31n, H))
  +tb = SF.b2n(Bool.not(SF.sign(F.Bits{l, h})))
  +e1 = Equal.trans(Nat, v(U32.xor(h, c)), Nat.add(C.low(31n, H), C.shift(31n, t)), Nat.add(Nat.add(f, C.shift(20n, E)), C.shift(31n, t)), xorv(h, c, hc), Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(31n, t)), C.low(31n, H), Nat.add(f, C.shift(20n, E)), low_split(20n, 11n, H)))
  +e2 = Equal.trans(Nat, v(U32.xor(h, c)), Nat.add(Nat.add(f, C.shift(20n, E)), C.shift(31n, t)), Nat.add(f, C.shift(20n, Nat.add(E, C.shift(11n, t)))), e1, fold(f, E, t))
  +e3 = Equal.cong(Nat, Nat, z => Nat.add(f, C.shift(20n, Nat.add(E, C.shift(11n, z)))), t, tb, nbit_c(C.high(31n, H), half0(h)))
  enc_g(l, h, Bool.not(SF.sign(F.Bits{l, h})), U32.xor(h, c), Equal.trans(Nat, v(U32.xor(h, c)), Nat.add(f, C.shift(20n, Nat.add(E, C.shift(11n, t)))), Nat.add(f, C.shift(20n, Nat.add(E, C.shift(11n, tb)))), e2, e3))

def neg_value(+x: F.F64) -> SF.Neg.value(x):
  match x:
    case F.Bits{+l, +h}:
      neg_g(l, h, 2147483648, {==})

def abs_g(+l: U32, +h: U32, +m31: U32, +hm31: {m31 == U32{WD.mask(32n, 31n)} : U32}) -> {F.Bits{l, U32.and(h, m31)} == SF.encode(False{}, SF.efield(F.Bits{l, h}), SF.frac(F.Bits{l, h})) : F.F64}:
  +H = v(h)
  +f = C.low(20n, H)
  +E = C.low(11n, C.high(20n, H))
  +e1 = Equal.trans(Nat, v(U32.and(h, m31)), C.low(31n, H), Nat.add(f, C.shift(20n, E)), andm(h, 31n, m31, hm31), low_split(20n, 11n, H))
  +e2 = Equal.cong(Nat, Nat, z => Nat.add(f, C.shift(20n, z)), E, Nat.add(E, C.shift(11n, SF.b2n(False{}))), Equal.sym(Nat, Nat.add(E, 0n), E, N.add_zero(E)))
  enc_g(l, h, False{}, U32.and(h, m31), Equal.trans(Nat, v(U32.and(h, m31)), Nat.add(f, C.shift(20n, E)), Nat.add(f, C.shift(20n, Nat.add(E, C.shift(11n, SF.b2n(False{}))))), e1, e2))

def abs_value(+x: F.F64) -> SF.Abs.value(x):
  match x:
    case F.Bits{+l, +h}:
      abs_g(l, h, 2147483647, {==})

def cs_g(+one: Nat, +h1: {one == 1n : Nat}, +l: U32, +h: U32, +l2: U32, +h2: U32, +m31: U32, +hm31: {m31 == U32{WD.mask(32n, 31n)} : U32}, +c: U32, +hc: {c == U32{WD.pw(32n, 31n)} : U32}) -> {F.Bits{l, U32.add(U32.and(h, m31), U32.and(h2, c))} == SF.encode(SF.sign(F.Bits{l2, h2}), SF.efield(F.Bits{l, h}), SF.frac(F.Bits{l, h})) : F.F64}:
  +H = v(h)
  +f = C.low(20n, H)
  +E = C.low(11n, C.high(20n, H))
  +c2 = C.high(31n, v(h2))
  +a = U32.and(h, m31)
  +b = U32.and(h2, c)
  +ea = andm(h, 31n, m31, hm31)
  +eb = andv(h2, c, hc)
  +esum = Equal.trans(Nat, Nat.add(v(a), v(b)), Nat.add(C.low(31n, H), v(b)), Nat.add(C.low(31n, H), C.shift(31n, c2)), Equal.cong(Nat, Nat, z => Nat.add(z, v(b)), v(a), C.low(31n, H), ea), Equal.cong(Nat, Nat, z => Nat.add(C.low(31n, H), z), v(b), C.shift(31n, c2), eb))
  +hfit = WW.limbs_fit(31n, 1n, C.low(31n, H), c2, WW.low_fits(31n, H), half0(h2))
  +hlt0 = WW.lt_one(32n, one, h1, Nat.add(C.low(31n, H), C.shift(31n, c2)), hfit)
  +hlt = L.subst(Nat, z => {Nat.is_lt(z, C.shift(32n, one)) == True{} : Bool}, Nat.add(C.low(31n, H), C.shift(31n, c2)), Nat.add(v(a), v(b)), Equal.sym(Nat, Nat.add(v(a), v(b)), Nat.add(C.low(31n, H), C.shift(31n, c2)), esum), hlt0)
  +e1 = Equal.trans(Nat, v(U32.add(a, b)), Nat.add(v(a), v(b)), Nat.add(C.low(31n, H), C.shift(31n, c2)), addv(one, h1, a, b, hlt), esum)
  +e2 = Equal.trans(Nat, v(U32.add(a, b)), Nat.add(C.low(31n, H), C.shift(31n, c2)), Nat.add(Nat.add(f, C.shift(20n, E)), C.shift(31n, c2)), e1, Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(31n, c2)), C.low(31n, H), Nat.add(f, C.shift(20n, E)), low_split(20n, 11n, H)))
  +e3 = Equal.trans(Nat, v(U32.add(a, b)), Nat.add(Nat.add(f, C.shift(20n, E)), C.shift(31n, c2)), Nat.add(f, C.shift(20n, Nat.add(E, C.shift(11n, c2)))), e2, fold(f, E, c2))
  +e4 = Equal.cong(Nat, Nat, z => Nat.add(f, C.shift(20n, Nat.add(E, C.shift(11n, z)))), c2, SF.b2n(SF.sign(F.Bits{l2, h2})), bit_c(c2, half0(h2)))
  enc_g(l, h, SF.sign(F.Bits{l2, h2}), U32.add(a, b), Equal.trans(Nat, v(U32.add(a, b)), Nat.add(f, C.shift(20n, Nat.add(E, C.shift(11n, c2)))), Nat.add(f, C.shift(20n, Nat.add(E, C.shift(11n, SF.b2n(SF.sign(F.Bits{l2, h2})))))), e3, e4))

def copysign_value(+x: F.F64, +y: F.F64) -> SF.Copysign.value(x, y):
  match x y:
    case F.Bits{+l, +h} F.Bits{+l2, +h2}:
      cs_g(1n, {==}, l, h, l2, h2, 2147483647, {==}, 2147483648, {==})
