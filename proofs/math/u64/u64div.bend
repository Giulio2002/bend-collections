import Base
import ../../../spec/math/u64.bend as SU
import ../../../src/math/u64.bend as U
import ../../lib/lemmas/src/wide.bend as W
import ../../lib/lemmas/spec/numeric.bend as S
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/u32alg.bend as A
import ../../lib/u32.bend as U3
import ../../lib/lemmas/proofs/division_quotient.bend as DQ
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/u32div.bend as UD
import ./u64.bend as P
import ../../lib/lemmas/types/model.bend as T
import ../../lib/lemmas/proofs/modular_addition.bend as MA
import ../../lib/lemmas/proofs/modular_negation.bend as MN
import ../../lib/lemmas/proofs/negation_magnitude.bend as NM
import ../../lib/lemmas/proofs/word_value.bend as WV

# div_small(a, d) is Nat division of the 64-bit value by d, 0 < d <= 2^20.
# The implementation's constants 2^20, 2^12, 2^8, 4095 and 255 are carried as
# variables tied to their words by equations, so their (large) values stay
# symbolic.

# ---- U32 views ----

def dm_e2(+a: U32, +b: U32, h: UD.dm_type(a, b)) -> {Nat.add(Nat.mul(UD.v(U32.div(a, b)), UD.v(b)), UD.v(U32.mod(a, b))) == UD.v(a) : Nat}:
  (e, l) = h
  e

def dm_l2(+a: U32, +b: U32, h: UD.dm_type(a, b)) -> {Nat.is_lt(UD.v(U32.mod(a, b)), UD.v(b)) == True{} : Bool}:
  (e, l) = h
  l

def dm_e(+a: U32, +b: U32, +hb: {U32.is_zero(b) == False{} : Bool}) -> {Nat.add(Nat.mul(UD.v(U32.div(a, b)), UD.v(b)), UD.v(U32.mod(a, b))) == UD.v(a) : Nat}:
  dm_e2(a, b, UD.div_mod(a, b, hb))

def dm_l(+a: U32, +b: U32, +hb: {U32.is_zero(b) == False{} : Bool}) -> {Nat.is_lt(UD.v(U32.mod(a, b)), UD.v(b)) == True{} : Bool}:
  dm_l2(a, b, UD.div_mod(a, b, hb))

def mul32(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +y: U32, +h: {Nat.is_lt(Nat.mul(UD.v(x), UD.v(y)), WD.sc(32n, one)) == True{} : Bool}) -> {UD.v(U32.mul(x, y)) == Nat.mul(UD.v(x), UD.v(y)) : Nat}:
  match x y:
    case U32{+a} U32{+b}:
      +cv = Equal.trans(Nat, Nat.mul(UD.v(U32{a}), UD.v(U32{b})), Nat.mul(WD.uw(32n, a), UD.v(U32{b})), Nat.mul(WD.uw(32n, a), WD.uw(32n, b)), Equal.cong(Nat, Nat, z => Nat.mul(z, UD.v(U32{b})), UD.v(U32{a}), WD.uw(32n, a), UD.vw(a)), Equal.cong(Nat, Nat, z => Nat.mul(WD.uw(32n, a), z), UD.v(U32{b}), WD.uw(32n, b), UD.vw(b)))
      +hw = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(32n, one)) == True{} : Bool}, Nat.mul(UD.v(U32{a}), UD.v(U32{b})), Nat.mul(WD.uw(32n, a), WD.uw(32n, b)), cv, h)
      Equal.trans(Nat, UD.v(U32{Word.mul(32n, a, b)}), WD.uw(32n, Word.mul(32n, a, b)), Nat.mul(UD.v(U32{a}), UD.v(U32{b})), UD.vw(Word.mul(32n, a, b)), Equal.trans(Nat, WD.uw(32n, Word.mul(32n, a, b)), Nat.mul(WD.uw(32n, a), WD.uw(32n, b)), Nat.mul(UD.v(U32{a}), UD.v(U32{b})), WD.mul_exact(32n, one, h1, a, b, hw), Equal.sym(Nat, Nat.mul(UD.v(U32{a}), UD.v(U32{b})), Nat.mul(WD.uw(32n, a), WD.uw(32n, b)), cv)))

def add32(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +y: U32, +h: {Nat.is_lt(Nat.add(UD.v(x), UD.v(y)), WD.sc(32n, one)) == True{} : Bool}) -> {UD.v(U32.add(x, y)) == Nat.add(UD.v(x), UD.v(y)) : Nat}:
  match x y:
    case U32{+a} U32{+b}:
      +cv = Equal.trans(Nat, Nat.add(UD.v(U32{a}), UD.v(U32{b})), Nat.add(WD.uw(32n, a), UD.v(U32{b})), Nat.add(WD.uw(32n, a), WD.uw(32n, b)), Equal.cong(Nat, Nat, z => Nat.add(z, UD.v(U32{b})), UD.v(U32{a}), WD.uw(32n, a), UD.vw(a)), Equal.cong(Nat, Nat, z => Nat.add(WD.uw(32n, a), z), UD.v(U32{b}), WD.uw(32n, b), UD.vw(b)))
      +hw = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(32n, one)) == True{} : Bool}, Nat.add(UD.v(U32{a}), UD.v(U32{b})), Nat.add(WD.uw(32n, a), WD.uw(32n, b)), cv, h)
      Equal.trans(Nat, UD.v(U32{Word.add(32n, a, b)}), WD.uw(32n, Word.add(32n, a, b)), Nat.add(UD.v(U32{a}), UD.v(U32{b})), UD.vw(Word.add(32n, a, b)), Equal.trans(Nat, WD.uw(32n, Word.add(32n, a, b)), Nat.add(WD.uw(32n, a), WD.uw(32n, b)), Nat.add(UD.v(U32{a}), UD.v(U32{b})), WD.add_exact(32n, one, h1, a, b, hw), Equal.sym(Nat, Nat.add(UD.v(U32{a}), UD.v(U32{b})), Nat.add(WD.uw(32n, a), WD.uw(32n, b)), cv)))

def hp32(+k: Nat, x: U32) -> Nat:
  match x:
    case U32{w}:
      WD.hi_part(32n, k, w)

def and32w(+k: Nat, +x: U32) -> {UD.v(x) == Nat.add(UD.v(U32.and(x, U32{WD.mask(32n, k)})), WD.sc(k, hp32(k, x))) : Nat}:
  match x:
    case U32{+w}:
      %Equal.sym(Nat, UD.v(U32{w}), WD.uw(32n, w), UD.vw(w)) : {_ == Nat.add(UD.v(U32{Word.and(32n, w, WD.mask(32n, k))}), WD.sc(k, WD.hi_part(32n, k, w))) : Nat}
      %Equal.sym(Nat, UD.v(U32{Word.and(32n, w, WD.mask(32n, k))}), WD.uw(32n, Word.and(32n, w, WD.mask(32n, k))), UD.vw(Word.and(32n, w, WD.mask(32n, k)))) : {WD.uw(32n, w) == Nat.add(_, WD.sc(k, WD.hi_part(32n, k, w))) : Nat}
      WD.mask_split(32n, k, w)

def and32(+k: Nat, +x: U32, +m: U32, +hm: {m == U32{WD.mask(32n, k)} : U32}) -> {UD.v(x) == Nat.add(UD.v(U32.and(x, m)), WD.sc(k, hp32(k, x))) : Nat}:
  L.subst(U32, z => {UD.v(x) == Nat.add(UD.v(U32.and(x, z)), WD.sc(k, hp32(k, x))) : Nat}, U32{WD.mask(32n, k)}, m, Equal.sym(U32, m, U32{WD.mask(32n, k)}, hm), and32w(k, x))

def and32_ltw(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: U32) -> {Nat.is_lt(UD.v(U32.and(x, U32{WD.mask(32n, k)})), WD.sc(k, one)) == True{} : Bool}:
  match x:
    case U32{+w}:
      %Equal.sym(Nat, UD.v(U32{Word.and(32n, w, WD.mask(32n, k))}), WD.uw(32n, Word.and(32n, w, WD.mask(32n, k))), UD.vw(Word.and(32n, w, WD.mask(32n, k)))) : {Nat.is_lt(_, WD.sc(k, one)) == True{} : Bool}
      WD.mask_lt(32n, k, one, h1, w)

def and32_lt(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: U32, +m: U32, +hm: {m == U32{WD.mask(32n, k)} : U32}) -> {Nat.is_lt(UD.v(U32.and(x, m)), WD.sc(k, one)) == True{} : Bool}:
  L.subst(U32, z => {Nat.is_lt(UD.v(U32.and(x, z)), WD.sc(k, one)) == True{} : Bool}, U32{WD.mask(32n, k)}, m, Equal.sym(U32, m, U32{WD.mask(32n, k)}, hm), and32_ltw(k, one, h1, x))

def pow32(+k: Nat, +hk: {Nat.is_lt(k, 32n) == True{} : Bool}, +one: Nat, +h1: {one == 1n : Nat}, +c: U32, +hc: {c == U32{WD.pw(32n, k)} : U32}) -> {UD.v(c) == WD.sc(k, one) : Nat}:
  +e = Equal.trans(Nat, UD.v(U32{WD.pw(32n, k)}), WD.uw(32n, WD.pw(32n, k)), WD.sc(k, one), UD.vw(WD.pw(32n, k)), WD.pwv(32n, k, hk, one, h1, WD.pw(32n, k), {==}))
  L.subst(U32, z => {UD.v(z) == WD.sc(k, one) : Nat}, U32{WD.pw(32n, k)}, c, Equal.sym(U32, c, U32{WD.pw(32n, k)}, hc), e)

def le32(+a: U32, +b: U32, +h: {U32.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(UD.v(a), UD.v(b)) == True{} : Bool}:
  L.subst(Cmp, c => {Cmp.is_le(c) == True{} : Bool}, U32.cmp(a, b), Nat.cmp(UD.v(a), UD.v(b)), U3.u32_cmp(a, b), h)

# ---- the generalised implementation ----

def g_fin(+lo: U32, +hi: U32, +d: U32, +t1: U32, +t2: U32, +t3: U32, +c20: U32, +c8: U32) -> U.U64:
  U.U64{U32.add(U32.add(U32.mul(U32.div(t1, d), c20), U32.mul(U32.div(t2, d), c8)), U32.div(t3, d)), U32.div(hi, d)}

def g_t3(+lo: U32, +hi: U32, +d: U32, +t1: U32, +t2: U32, +c20: U32, +c8: U32, +m8: U32) -> U.U64:
  g_fin(lo, hi, d, t1, t2, U32.add(U32.mul(U32.mod(t2, d), c8), U32.and(lo, m8)), c20, c8)

def g_t2(+lo: U32, +hi: U32, +d: U32, +t1: U32, +c20: U32, +c12: U32, +c8: U32, +m12: U32, +m8: U32) -> U.U64:
  g_t3(lo, hi, d, t1, U32.add(U32.mul(U32.mod(t1, d), c12), U32.and(U32.div(lo, c8), m12)), c20, c8, m8)

def gdiv(a: U.U64, +d: U32, +c20: U32, +c12: U32, +c8: U32, +m12: U32, +m8: U32) -> U.U64:
  U.U64{+lo, +hi} = a
  g_t2(lo, hi, d, U32.add(U32.mul(U32.mod(hi, d), c12), U32.div(lo, c20)), c20, c12, c8, m12, m8)

def impl(+a: U.U64, +d: U32) -> {U.div_small(a, d) == gdiv(a, d, 1048576, 4096, 256, 4095, 255) : U.U64}:
  match a:
    case U.U64{lo, hi}:
      {==}

# ---- algebra ----

# 2^8 (2^12 (2^12 h + a) + b) + c == ((2^20 a + 2^8 b) + c) + 2^32 h
def expand(+h: Nat, +a: Nat, +b: Nat, +c: Nat) -> {Nat.add(WD.sc(8n, Nat.add(WD.sc(12n, Nat.add(WD.sc(12n, h), a)), b)), c) == Nat.add(Nat.add(Nat.add(WD.sc(20n, a), WD.sc(8n, b)), c), WD.sc(32n, h)) : Nat}:
  +rhs = Nat.add(Nat.add(Nat.add(WD.sc(20n, a), WD.sc(8n, b)), c), WD.sc(32n, h))
  +x = WD.sc(32n, h)
  +y = WD.sc(20n, a)
  +z = WD.sc(8n, b)
  %A.sc_add(12n, WD.sc(12n, h), a) : {Nat.add(WD.sc(8n, Nat.add(_, b)), c) == rhs : Nat}
  %A.sc_add(8n, Nat.add(WD.sc(12n, WD.sc(12n, h)), WD.sc(12n, a)), b) : {Nat.add(_, c) == rhs : Nat}
  %A.sc_add(8n, WD.sc(12n, WD.sc(12n, h)), WD.sc(12n, a)) : {Nat.add(Nat.add(_, z), c) == rhs : Nat}
  Equal.trans(Nat, Nat.add(Nat.add(Nat.add(x, y), z), c), Nat.add(Nat.add(x, Nat.add(y, z)), c), rhs,
    Equal.cong(Nat, Nat, w => Nat.add(w, c), Nat.add(Nat.add(x, y), z), Nat.add(x, Nat.add(y, z)), N.add_assoc(x, y, z)),
    Equal.trans(Nat, Nat.add(Nat.add(x, Nat.add(y, z)), c), Nat.add(x, Nat.add(Nat.add(y, z), c)), rhs, N.add_assoc(x, Nat.add(y, z), c), N.add_comm(x, Nat.add(Nat.add(y, z), c))))

# a value equation rewritten into a bound
def lt_eq(+a: Nat, +b: Nat, +k: Nat, +e: {a == b : Nat}, +h: {Nat.is_lt(a, k) == True{} : Bool}) -> {Nat.is_lt(b, k) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(z, k) == True{} : Bool}, a, b, e, h)

# a scaled product c*k with v(k) == 2^j, as 2^j c
def mul_pow(+one: Nat, +h1: {one == 1n : Nat}, +j: Nat, +c: Nat, +kv: Nat, +hk: {kv == WD.sc(j, one) : Nat}) -> {Nat.mul(c, kv) == WD.sc(j, c) : Nat}:
  Equal.trans(Nat, Nat.mul(c, kv), Nat.mul(c, WD.sc(j, one)), WD.sc(j, c), Equal.cong(Nat, Nat, z => Nat.mul(c, z), kv, WD.sc(j, one), hk), AR.mul_sc1(j, one, h1, c))

# v(x * k) == 2^j v(x) when v(k) == 2^j and 2^j v(x) < 2^32
def mulp32(+one: Nat, +h1: {one == 1n : Nat}, +j: Nat, +x: U32, +k: U32, +hk: {UD.v(k) == WD.sc(j, one) : Nat}, +hb: {Nat.is_lt(WD.sc(j, UD.v(x)), WD.sc(32n, one)) == True{} : Bool}) -> {UD.v(U32.mul(x, k)) == WD.sc(j, UD.v(x)) : Nat}:
  +em = mul_pow(one, h1, j, UD.v(x), UD.v(k), hk)
  Equal.trans(Nat, UD.v(U32.mul(x, k)), Nat.mul(UD.v(x), UD.v(k)), WD.sc(j, UD.v(x)), mul32(one, h1, x, k, lt_eq(WD.sc(j, UD.v(x)), Nat.mul(UD.v(x), UD.v(k)), WD.sc(32n, one), Equal.sym(Nat, Nat.mul(UD.v(x), UD.v(k)), WD.sc(j, UD.v(x)), em), hb)), em)

# v(x + y) == a + b when v(x) == a, v(y) == b and a + b < 2^32
def addv32(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +y: U32, +a: Nat, +b: Nat, +ha: {UD.v(x) == a : Nat}, +hb: {UD.v(y) == b : Nat}, +h: {Nat.is_lt(Nat.add(a, b), WD.sc(32n, one)) == True{} : Bool}) -> {UD.v(U32.add(x, y)) == Nat.add(a, b) : Nat}:
  +e = Equal.trans(Nat, Nat.add(UD.v(x), UD.v(y)), Nat.add(a, UD.v(y)), Nat.add(a, b), Equal.cong(Nat, Nat, z => Nat.add(z, UD.v(y)), UD.v(x), a, ha), Equal.cong(Nat, Nat, z => Nat.add(a, z), UD.v(y), b, hb))
  Equal.trans(Nat, UD.v(U32.add(x, y)), Nat.add(UD.v(x), UD.v(y)), Nat.add(a, b), add32(one, h1, x, y, lt_eq(Nat.add(a, b), Nat.add(UD.v(x), UD.v(y)), WD.sc(32n, one), Equal.sym(Nat, Nat.add(UD.v(x), UD.v(y)), Nat.add(a, b), e), h)), e)

# ---- the low limb in 12/12/8-bit digits ----

def lo_eq(+one: Nat, +h1: {one == 1n : Nat}, +lo: U32, +c20: U32, +c8: U32, +m12: U32, +m8: U32, +h20: {UD.v(c20) == WD.sc(20n, one) : Nat}, +h8: {UD.v(c8) == WD.sc(8n, one) : Nat}, +hm12: {m12 == U32{WD.mask(32n, 12n)} : U32}, +hm8: {m8 == U32{WD.mask(32n, 8n)} : U32}, +nz20: {U32.is_zero(c20) == False{} : Bool}, +nz8: {U32.is_zero(c8) == False{} : Bool}) -> {UD.v(lo) == Nat.add(Nat.add(WD.sc(20n, UD.v(U32.div(lo, c20))), WD.sc(8n, UD.v(U32.and(U32.div(lo, c8), m12)))), UD.v(U32.and(lo, m8))) : Nat}:
  +ln = UD.v(lo)
  +l1 = UD.v(U32.div(lo, c20))
  +r1 = UD.v(U32.mod(lo, c20))
  +w8 = UD.v(U32.div(lo, c8))
  +r8 = UD.v(U32.mod(lo, c8))
  +l2 = UD.v(U32.and(U32.div(lo, c8), m12))
  +l3 = UD.v(U32.and(lo, m8))
  +y2 = hp32(12n, U32.div(lo, c8))
  +y3 = hp32(8n, lo)
  +e20 = Equal.trans(Nat, Nat.add(WD.sc(20n, l1), r1), Nat.add(Nat.mul(l1, UD.v(c20)), r1), ln, Equal.cong(Nat, Nat, z => Nat.add(z, r1), WD.sc(20n, l1), Nat.mul(l1, UD.v(c20)), Equal.sym(Nat, Nat.mul(l1, UD.v(c20)), WD.sc(20n, l1), mul_pow(one, h1, 20n, l1, UD.v(c20), h20))), dm_e(lo, c20, nz20))
  +l20 = L.subst(Nat, z => {Nat.is_lt(r1, z) == True{} : Bool}, UD.v(c20), WD.sc(20n, one), h20, dm_l(lo, c20, nz20))
  +e8 = Equal.trans(Nat, Nat.add(WD.sc(8n, w8), r8), Nat.add(Nat.mul(w8, UD.v(c8)), r8), ln, Equal.cong(Nat, Nat, z => Nat.add(z, r8), WD.sc(8n, w8), Nat.mul(w8, UD.v(c8)), Equal.sym(Nat, Nat.mul(w8, UD.v(c8)), WD.sc(8n, w8), mul_pow(one, h1, 8n, w8, UD.v(c8), h8))), dm_e(lo, c8, nz8))
  +l8 = L.subst(Nat, z => {Nat.is_lt(r8, z) == True{} : Bool}, UD.v(c8), WD.sc(8n, one), h8, dm_l(lo, c8, nz8))
  +s3 = and32(8n, lo, m8, hm8)
  +b3 = and32_lt(8n, one, h1, lo, m8, hm8)
  +er8 = WD.uniq(8n, one, h1, r8, l3, w8, y3, Equal.trans(Nat, Nat.add(r8, WD.sc(8n, w8)), Nat.add(WD.sc(8n, w8), r8), Nat.add(l3, WD.sc(8n, y3)), N.add_comm(r8, WD.sc(8n, w8)), Equal.trans(Nat, Nat.add(WD.sc(8n, w8), r8), ln, Nat.add(l3, WD.sc(8n, y3)), e8, s3)), l8, b3)
  +s2 = and32(12n, U32.div(lo, c8), m12, hm12)
  +b2 = and32_lt(12n, one, h1, U32.div(lo, c8), m12, hm12)
  # ln == (2^8 l2 + 2^20 y2) + l3
  +elw = Equal.trans(Nat, ln, Nat.add(WD.sc(8n, w8), l3), Nat.add(Nat.add(WD.sc(8n, l2), WD.sc(20n, y2)), l3),
    Equal.trans(Nat, ln, Nat.add(WD.sc(8n, w8), r8), Nat.add(WD.sc(8n, w8), l3), Equal.sym(Nat, Nat.add(WD.sc(8n, w8), r8), ln, e8), Equal.cong(Nat, Nat, z => Nat.add(WD.sc(8n, w8), z), r8, l3, er8)),
    Equal.cong(Nat, Nat, z => Nat.add(z, l3), WD.sc(8n, w8), Nat.add(WD.sc(8n, l2), WD.sc(20n, y2)),
      Equal.trans(Nat, WD.sc(8n, w8), WD.sc(8n, Nat.add(l2, WD.sc(12n, y2))), Nat.add(WD.sc(8n, l2), WD.sc(20n, y2)), Equal.cong(Nat, Nat, z => WD.sc(8n, z), w8, Nat.add(l2, WD.sc(12n, y2)), s2), Equal.sym(Nat, Nat.add(WD.sc(8n, l2), WD.sc(8n, WD.sc(12n, y2))), WD.sc(8n, Nat.add(l2, WD.sc(12n, y2))), A.sc_add(8n, l2, WD.sc(12n, y2))))))
  +hb2 = AR.digit_lt(8n, one, h1, l3, l2, WD.sc(12n, one), b3, b2)
  +er1 = WD.uniq(20n, one, h1, r1, Nat.add(WD.sc(8n, l2), l3), l1, y2,
    Equal.trans(Nat, Nat.add(r1, WD.sc(20n, l1)), ln, Nat.add(Nat.add(WD.sc(8n, l2), l3), WD.sc(20n, y2)),
      Equal.trans(Nat, Nat.add(r1, WD.sc(20n, l1)), Nat.add(WD.sc(20n, l1), r1), ln, N.add_comm(r1, WD.sc(20n, l1)), e20),
      Equal.trans(Nat, ln, Nat.add(Nat.add(WD.sc(8n, l2), WD.sc(20n, y2)), l3), Nat.add(Nat.add(WD.sc(8n, l2), l3), WD.sc(20n, y2)), elw, A.add_rot(WD.sc(8n, l2), WD.sc(20n, y2), l3))),
    l20, hb2)
  Equal.trans(Nat, ln, Nat.add(WD.sc(20n, l1), Nat.add(WD.sc(8n, l2), l3)), Nat.add(Nat.add(WD.sc(20n, l1), WD.sc(8n, l2)), l3),
    Equal.trans(Nat, ln, Nat.add(WD.sc(20n, l1), r1), Nat.add(WD.sc(20n, l1), Nat.add(WD.sc(8n, l2), l3)), Equal.sym(Nat, Nat.add(WD.sc(20n, l1), r1), ln, e20), Equal.cong(Nat, Nat, z => Nat.add(WD.sc(20n, l1), z), r1, Nat.add(WD.sc(8n, l2), l3), er1)),
    Equal.sym(Nat, Nat.add(Nat.add(WD.sc(20n, l1), WD.sc(8n, l2)), l3), Nat.add(WD.sc(20n, l1), Nat.add(WD.sc(8n, l2), l3)), N.add_assoc(WD.sc(20n, l1), WD.sc(8n, l2), l3)))

# the top digit of the low limb is below 2^12
def lo_l1(+one: Nat, +h1: {one == 1n : Nat}, +lo: U32, +c20: U32, +h20: {UD.v(c20) == WD.sc(20n, one) : Nat}, +nz20: {U32.is_zero(c20) == False{} : Bool}) -> {Nat.is_lt(UD.v(U32.div(lo, c20)), WD.sc(12n, one)) == True{} : Bool}:
  +l1 = UD.v(U32.div(lo, c20))
  +r1 = UD.v(U32.mod(lo, c20))
  +e20 = Equal.trans(Nat, Nat.add(WD.sc(20n, l1), r1), Nat.add(Nat.mul(l1, UD.v(c20)), r1), UD.v(lo), Equal.cong(Nat, Nat, z => Nat.add(z, r1), WD.sc(20n, l1), Nat.mul(l1, UD.v(c20)), Equal.sym(Nat, Nat.mul(l1, UD.v(c20)), WD.sc(20n, l1), mul_pow(one, h1, 20n, l1, UD.v(c20), h20))), dm_e(lo, c20, nz20))
  +le = L.subst(Nat, z => {Nat.is_le(WD.sc(20n, l1), z) == True{} : Bool}, Nat.add(WD.sc(20n, l1), r1), UD.v(lo), e20, N.le_add_right(WD.sc(20n, l1), r1))
  AR.sc_lt_cancel(20n, l1, WD.sc(12n, one), N.le_lt_trans(WD.sc(20n, l1), UD.v(lo), WD.sc(32n, one), le, UD.vb(one, h1, lo)))

# one digit of the long division: t = x * 2^j + y with x < d, y < 2^j
def tval(+one: Nat, +h1: {one == 1n : Nat}, +j: Nat, +x: U32, +k: U32, +y: U32, +dn: Nat, +hk: {UD.v(k) == WD.sc(j, one) : Nat}, +hy: {Nat.is_lt(UD.v(y), WD.sc(j, one)) == True{} : Bool}, +hx: {Nat.is_lt(UD.v(x), dn) == True{} : Bool}, +hjk: {Nat.is_le(WD.sc(j, dn), WD.sc(32n, one)) == True{} : Bool}) -> {UD.v(U32.add(U32.mul(x, k), y)) == Nat.add(WD.sc(j, UD.v(x)), UD.v(y)) : Nat}:
  +hm = N.lt_le_trans(WD.sc(j, UD.v(x)), WD.sc(j, dn), WD.sc(32n, one), AR.sc_lt(j, UD.v(x), dn, hx), hjk)
  +ha = N.lt_le_trans(Nat.add(WD.sc(j, UD.v(x)), UD.v(y)), WD.sc(j, dn), WD.sc(32n, one), AR.digit_lt(j, one, h1, UD.v(y), UD.v(x), dn, hy, hx), hjk)
  addv32(one, h1, U32.mul(x, k), y, WD.sc(j, UD.v(x)), UD.v(y), mulp32(one, h1, j, x, k, hk, hm), {==}, ha)

# ---- the value of the generalised division ----

def gval(+one: Nat, +h1: {one == 1n : Nat}, +lo: U32, +hi: U32, +d: U32, +c20: U32, +c12: U32, +c8: U32, +m12: U32, +m8: U32, +hd0: {U32.is_zero(d) == False{} : Bool}, +hle: {U32.is_le(d, c20) == True{} : Bool}, +p20: {c20 == U32{WD.pw(32n, 20n)} : U32}, +p12: {c12 == U32{WD.pw(32n, 12n)} : U32}, +p8: {c8 == U32{WD.pw(32n, 8n)} : U32}, +hm12: {m12 == U32{WD.mask(32n, 12n)} : U32}, +hm8: {m8 == U32{WD.mask(32n, 8n)} : U32}, +nz20: {U32.is_zero(c20) == False{} : Bool}, +nz8: {U32.is_zero(c8) == False{} : Bool}) -> {P.val(gdiv(U.U64{lo, hi}, d, c20, c12, c8, m12, m8)) == Nat.div(P.val(U.U64{lo, hi}), UD.v(d)) : Nat}:
  +kk = WD.sc(32n, one)
  +mm = WD.sc(20n, one)
  +pp = WD.sc(12n, one)
  +h20 = pow32(20n, {==}, one, h1, c20, p20)
  +h12 = pow32(12n, {==}, one, h1, c12, p12)
  +h8 = pow32(8n, {==}, one, h1, c8, p8)
  +dn = UD.v(d)
  +hdm = L.subst(Nat, z => {Nat.is_le(dn, z) == True{} : Bool}, UD.v(c20), mm, h20, le32(d, c20, hle))
  +hk12 = AR.sc_le(12n, dn, mm, hdm)
  +hk8 = N.le_trans(WD.sc(8n, dn), WD.sc(8n, mm), WD.sc(8n, WD.sc(4n, mm)), AR.sc_le(8n, dn, mm, hdm), AR.sc_le(8n, mm, WD.sc(4n, mm), AR.le_sc(4n, mm)))
  # the high limb
  +qh = UD.v(U32.div(hi, d))
  +rh = UD.v(U32.mod(hi, d))
  +eh = dm_e(hi, d, hd0)
  +lh = dm_l(hi, d, hd0)
  # the low limb's digits
  +l1u = U32.div(lo, c20)
  +l2u = U32.and(U32.div(lo, c8), m12)
  +l3u = U32.and(lo, m8)
  +l1 = UD.v(l1u)
  +l2 = UD.v(l2u)
  +l3 = UD.v(l3u)
  +hl1 = lo_l1(one, h1, lo, c20, h20, nz20)
  +hl2 = and32_lt(12n, one, h1, U32.div(lo, c8), m12, hm12)
  +hl3 = and32_lt(8n, one, h1, lo, m8, hm8)
  +hlw = lo_eq(one, h1, lo, c20, c8, m12, m8, h20, h8, hm12, hm8, nz20, nz8)
  # t1
  +t1 = U32.add(U32.mul(U32.mod(hi, d), c12), l1u)
  +vt1 = tval(one, h1, 12n, U32.mod(hi, d), c12, l1u, dn, h12, hl1, lh, hk12)
  +q1 = UD.v(U32.div(t1, d))
  +r1 = UD.v(U32.mod(t1, d))
  +lr1 = dm_l(t1, d, hd0)
  +f1 = Equal.trans(Nat, Nat.add(WD.sc(12n, rh), l1), UD.v(t1), Nat.add(Nat.mul(q1, dn), r1), Equal.sym(Nat, UD.v(t1), Nat.add(WD.sc(12n, rh), l1), vt1), Equal.sym(Nat, Nat.add(Nat.mul(q1, dn), r1), UD.v(t1), dm_e(t1, d, hd0)))
  +hq1 = AR.quot_lt(12n, one, h1, q1, dn, r1, lt_eq(Nat.add(WD.sc(12n, rh), l1), Nat.add(Nat.mul(q1, dn), r1), WD.sc(12n, dn), f1, AR.digit_lt(12n, one, h1, l1, rh, dn, hl1, lh)))
  # t2
  +t2 = U32.add(U32.mul(U32.mod(t1, d), c12), l2u)
  +vt2 = tval(one, h1, 12n, U32.mod(t1, d), c12, l2u, dn, h12, hl2, lr1, hk12)
  +q2 = UD.v(U32.div(t2, d))
  +r2 = UD.v(U32.mod(t2, d))
  +lr2 = dm_l(t2, d, hd0)
  +f2 = Equal.trans(Nat, Nat.add(WD.sc(12n, r1), l2), UD.v(t2), Nat.add(Nat.mul(q2, dn), r2), Equal.sym(Nat, UD.v(t2), Nat.add(WD.sc(12n, r1), l2), vt2), Equal.sym(Nat, Nat.add(Nat.mul(q2, dn), r2), UD.v(t2), dm_e(t2, d, hd0)))
  +hq2 = AR.quot_lt(12n, one, h1, q2, dn, r2, lt_eq(Nat.add(WD.sc(12n, r1), l2), Nat.add(Nat.mul(q2, dn), r2), WD.sc(12n, dn), f2, AR.digit_lt(12n, one, h1, l2, r1, dn, hl2, lr1)))
  # t3
  +t3 = U32.add(U32.mul(U32.mod(t2, d), c8), l3u)
  +vt3 = tval(one, h1, 8n, U32.mod(t2, d), c8, l3u, dn, h8, hl3, lr2, hk8)
  +q3 = UD.v(U32.div(t3, d))
  +r3 = UD.v(U32.mod(t3, d))
  +lr3 = dm_l(t3, d, hd0)
  +f3 = Equal.trans(Nat, Nat.add(WD.sc(8n, r2), l3), UD.v(t3), Nat.add(Nat.mul(q3, dn), r3), Equal.sym(Nat, UD.v(t3), Nat.add(WD.sc(8n, r2), l3), vt3), Equal.sym(Nat, Nat.add(Nat.mul(q3, dn), r3), UD.v(t3), dm_e(t3, d, hd0)))
  +hq3 = AR.quot_lt(8n, one, h1, q3, dn, r3, lt_eq(Nat.add(WD.sc(8n, r2), l3), Nat.add(Nat.mul(q3, dn), r3), WD.sc(8n, dn), f3, AR.digit_lt(8n, one, h1, l3, r2, dn, hl3, lr2)))
  # the quotient's low limb
  +a1 = U32.mul(U32.div(t1, d), c20)
  +a2 = U32.mul(U32.div(t2, d), c8)
  +a12 = U32.add(a1, a2)
  +lo2 = U32.add(a12, U32.div(t3, d))
  +hi2 = U32.div(hi, d)
  +va1 = mulp32(one, h1, 20n, U32.div(t1, d), c20, h20, AR.sc_lt(20n, q1, pp, hq1))
  +hq2m = AR.sc_lt(8n, q2, pp, hq2)
  +va2 = mulp32(one, h1, 8n, U32.div(t2, d), c8, h8, N.lt_le_trans(WD.sc(8n, q2), mm, kk, hq2m, AR.le_sc(12n, mm)))
  +va12 = addv32(one, h1, a1, a2, WD.sc(20n, q1), WD.sc(8n, q2), va1, va2, AR.digit_lt(20n, one, h1, WD.sc(8n, q2), q1, pp, hq2m, hq1))
  +hx = AR.digit_lt(8n, one, h1, q3, q2, pp, hq3, hq2)
  +hb = AR.digit_lt(20n, one, h1, Nat.add(WD.sc(8n, q2), q3), q1, pp, hx, hq1)
  +hb2 = lt_eq(Nat.add(WD.sc(20n, q1), Nat.add(WD.sc(8n, q2), q3)), Nat.add(Nat.add(WD.sc(20n, q1), WD.sc(8n, q2)), q3), kk, Equal.sym(Nat, Nat.add(Nat.add(WD.sc(20n, q1), WD.sc(8n, q2)), q3), Nat.add(WD.sc(20n, q1), Nat.add(WD.sc(8n, q2), q3)), N.add_assoc(WD.sc(20n, q1), WD.sc(8n, q2), q3)), hb)
  +vlo2 = addv32(one, h1, a12, U32.div(t3, d), Nat.add(WD.sc(20n, q1), WD.sc(8n, q2)), q3, va12, {==}, hb2)
  # the division identity, three digits at a time
  +x1 = AR.step(12n, qh, rh, dn, l1, q1, r1, UD.v(hi), Equal.sym(Nat, Nat.add(Nat.mul(qh, dn), rh), UD.v(hi), eh), f1)
  +x2 = AR.step(12n, Nat.add(WD.sc(12n, qh), q1), r1, dn, l2, q2, r2, Nat.add(WD.sc(12n, UD.v(hi)), l1), x1, f2)
  +x3 = AR.step(8n, Nat.add(WD.sc(12n, Nat.add(WD.sc(12n, qh), q1)), q2), r2, dn, l3, q3, r3, Nat.add(WD.sc(12n, Nat.add(WD.sc(12n, UD.v(hi)), l1)), l2), x2, f3)
  +ea = expand(UD.v(hi), l1, l2, l3)
  +eq = expand(qh, q1, q2, q3)
  +qx = Nat.add(WD.sc(8n, Nat.add(WD.sc(12n, Nat.add(WD.sc(12n, qh), q1)), q2)), q3)
  +qv = Nat.add(UD.v(lo2), WD.sc(32n, qh))
  +eqv = Equal.trans(Nat, qx, Nat.add(Nat.add(Nat.add(WD.sc(20n, q1), WD.sc(8n, q2)), q3), WD.sc(32n, qh)), qv, eq, Equal.cong(Nat, Nat, z => Nat.add(z, WD.sc(32n, qh)), Nat.add(Nat.add(WD.sc(20n, q1), WD.sc(8n, q2)), q3), UD.v(lo2), Equal.sym(Nat, UD.v(lo2), Nat.add(Nat.add(WD.sc(20n, q1), WD.sc(8n, q2)), q3), vlo2)))
  +lhs3 = Nat.add(WD.sc(8n, Nat.add(WD.sc(12n, Nat.add(WD.sc(12n, UD.v(hi)), l1)), l2)), l3)
  +ca = Equal.trans(Nat, P.val(U.U64{lo, hi}), Nat.add(UD.v(lo), WD.sc(32n, UD.v(hi))), lhs3, P.val_pack(lo, hi),
    Equal.trans(Nat, Nat.add(UD.v(lo), WD.sc(32n, UD.v(hi))), Nat.add(Nat.add(Nat.add(WD.sc(20n, l1), WD.sc(8n, l2)), l3), WD.sc(32n, UD.v(hi))), lhs3, Equal.cong(Nat, Nat, z => Nat.add(z, WD.sc(32n, UD.v(hi))), UD.v(lo), Nat.add(Nat.add(WD.sc(20n, l1), WD.sc(8n, l2)), l3), hlw), Equal.sym(Nat, lhs3, Nat.add(Nat.add(Nat.add(WD.sc(20n, l1), WD.sc(8n, l2)), l3), WD.sc(32n, UD.v(hi))), ea)))
  +c = Equal.trans(Nat, P.val(U.U64{lo, hi}), lhs3, Nat.add(Nat.mul(qv, dn), r3), ca, Equal.trans(Nat, lhs3, Nat.add(Nat.mul(qx, dn), r3), Nat.add(Nat.mul(qv, dn), r3), x3, Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(z, dn), r3), qx, qv, eqv)))
  Equal.trans(Nat, P.val(gdiv(U.U64{lo, hi}, d, c20, c12, c8, m12, m8)), qv, Nat.div(P.val(U.U64{lo, hi}), dn), P.val_pack(lo2, hi2),
    Equal.sym(Nat, Nat.div(P.val(U.U64{lo, hi}), dn), qv, Equal.trans(Nat, Nat.div(P.val(U.U64{lo, hi}), dn), Nat.div(Nat.add(Nat.mul(qv, dn), r3), dn), qv, Equal.cong(Nat, Nat, z => Nat.div(z, dn), P.val(U.U64{lo, hi}), Nat.add(Nat.mul(qv, dn), r3), c), DQ.identify(qv, dn, r3, lr3))))

# THEOREM: div_small is Nat division of the 64-bit value, for 0 < d <= 2^20.
def div_value(+a: U.U64, +d: U32, +hd0: {U32.is_zero(d) == False{} : Bool}, +hle: {U32.is_le(d, 1048576) == True{} : Bool}) -> {P.val(U.div_small(a, d)) == Nat.div(P.val(a), UD.v(d)) : Nat}:
  match a:
    case U.U64{+lo, +hi}:
      gval(1n, {==}, lo, hi, d, 1048576, 4096, 256, 4095, 255, hd0, hle, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# ---- signed division ----

def from_u(+n: Nat, +w: Word(n)) -> {S.from_nat(n, S.unsigned(n, w)) == w : Word(n)}:
  %Equal.trans(Nat, Nat.add(S.unsigned(n, w), S.scale_binary(n, 0n)), Nat.add(S.unsigned(n, w), 0n), S.unsigned(n, w), Equal.cong(Nat, Nat, z => Nat.add(S.unsigned(n, w), z), S.scale_binary(n, 0n), 0n, A.sc_zero(n)), N.add_zero(S.unsigned(n, w))) : {S.from_nat(n, _) == w : Word(n)}
  MA.reconstruct(n, w, 0n)

# THEOREM: div_small is the specification's unsigned 64-bit quotient.
def div_bits(+a: U.U64, +d: U32, +hd0: {U32.is_zero(d) == False{} : Bool}, +hle: {U32.is_le(d, 1048576) == True{} : Bool}) -> {P.bits(U.div_small(a, d)) == S.unsigned_quotient(64n, P.bits(a), d) : Word(64n)}:
  Equal.trans(Word(64n), P.bits(U.div_small(a, d)), S.from_nat(64n, P.val(U.div_small(a, d))), S.unsigned_quotient(64n, P.bits(a), d),
    Equal.sym(Word(64n), S.from_nat(64n, P.val(U.div_small(a, d))), P.bits(U.div_small(a, d)), from_u(64n, P.bits(U.div_small(a, d)))),
    Equal.trans(Word(64n), S.from_nat(64n, P.val(U.div_small(a, d))), S.from_nat(64n, Nat.div(P.val(a), UD.v(d))), S.unsigned_quotient(64n, P.bits(a), d),
      Equal.cong(Nat, Word(64n), z => S.from_nat(64n, z), P.val(U.div_small(a, d)), Nat.div(P.val(a), UD.v(d)), div_value(a, d, hd0, hle)),
      Equal.sym(Word(64n), S.unsigned_quotient(64n, P.bits(a), d), S.from_nat(64n, Nat.div(P.val(a), UD.v(d))), DQ.specification_equation(64n, P.bits(a), d))))

# negate, divide the magnitude, negate back: the specification's quotient of
# a negative word, at every width
def neg_quot(+n: Nat, +w: Word(n), +d: U32, +hnz: {W.is_zero(n, w) == False{} : Bool}) -> {Word.inc(n, Word.not(n, S.unsigned_quotient(n, Word.inc(n, Word.not(n, w)), d))) == S.negative_quotient(n, w, d) : Word(n)}:
  match n w:
    case 0n WNil{}:
      {==}
    case 1n+p WCon{+bit, +tail}:
      +m = {1n+p : Nat}
      +ww = {WCon{bit, tail} : Word(1n+p)}
      +x = Word.inc(m, Word.not(m, ww))
      +dn = U32.to_nat(d)
      +sc = S.scale_binary(m, 1n)
      +q = Nat.div(S.unsigned(m, x), dn)
      +hx = NM.magnitude(m, ww, hnz)
      +hq = N.le_lt_trans(q, S.unsigned(m, x), sc, AR.div_le(S.unsigned(m, x), dn), WD.lt1(m, 1n, {==}, S.unsigned(m, x), WD.wb(m, 1n, {==}, x)))
      +hqv = WV.from_nat_value(m, q, L.subst(Nat, z => {Nat.is_lt(q, z) == True{} : Bool}, sc, Nat.pow(2n, m), NM.scale_power(m), hq))
      +e1 = Equal.cong(Word(m), Word(m), z => Word.inc(m, Word.not(m, z)), S.unsigned_quotient(m, x, d), S.from_nat(m, q), DQ.specification_equation(m, x, d))
      +e2 = MN.negation_refines(m, S.from_nat(m, q))
      +e3 = Equal.cong(Nat, Word(m), z => S.from_nat(m, Nat.sub(sc, z)), S.unsigned(m, S.from_nat(m, q)), q, hqv)
      +e4 = Equal.cong(Nat, Word(m), z => S.from_nat(m, Nat.sub(sc, Nat.div(z, dn))), S.unsigned(m, x), Nat.sub(sc, S.unsigned(m, ww)), hx)
      +e5 = Equal.cong(Nat, Word(m), z => S.from_nat(m, Nat.sub(z, Nat.div(Nat.sub(z, S.unsigned(m, ww)), dn))), sc, Nat.pow(2n, m), NM.scale_power(m))
      Equal.trans(Word(m), Word.inc(m, Word.not(m, S.unsigned_quotient(m, x, d))), Word.inc(m, Word.not(m, S.from_nat(m, q))), S.negative_quotient(m, ww, d), e1,
        Equal.trans(Word(m), Word.inc(m, Word.not(m, S.from_nat(m, q))), S.from_nat(m, Nat.sub(sc, S.unsigned(m, S.from_nat(m, q)))), S.negative_quotient(m, ww, d), e2,
          Equal.trans(Word(m), S.from_nat(m, Nat.sub(sc, S.unsigned(m, S.from_nat(m, q)))), S.from_nat(m, Nat.sub(sc, q)), S.negative_quotient(m, ww, d), e3,
            Equal.trans(Word(m), S.from_nat(m, Nat.sub(sc, q)), S.from_nat(m, Nat.sub(sc, Nat.div(Nat.sub(sc, S.unsigned(m, ww)), dn))), S.negative_quotient(m, ww, d), e4, e5))))

def is_zero_eq(+n: Nat, +w: Word(n), +h: {W.is_zero(n, w) == True{} : Bool}) -> {w == Word.zero(n) : Word(n)}:
  match n w:
    case 0n WNil{}:
      {==}
    case 1n+p WCon{True{}, t}:
      Empty.absurd({WCon{True{}, t} == Word.zero(1n+p) : Word(1n+p)}, L.false_true(h))
    case 1n+p WCon{False{}, t}:
      Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, t, Word.zero(p), is_zero_eq(p, t, h))

def nz_g(+w: Word(64n), +z: Bool, +hz: {W.is_zero(64n, w) == z : Bool}, +hn: {S.negative(w) == True{} : Bool}) -> {W.is_zero(64n, w) == False{} : Bool}:
  match z:
    case False{}:
      hz
    case True{}:
      Empty.absurd({W.is_zero(64n, w) == False{} : Bool}, L.false_true(L.subst(Word(64n), x => {S.negative(x) == True{} : Bool}, w, Word.zero(64n), is_zero_eq(64n, w, hz), hn)))

# a negative word is nonzero
def nz_neg(+w: Word(64n), +hn: {S.negative(w) == True{} : Bool}) -> {W.is_zero(64n, w) == False{} : Bool}:
  nz_g(w, W.is_zero(64n, w), {==}, hn)

def qs(w: Word(64n), neg: Bool, +d: U32) -> Word(64n):
  SU.signed_quotient(w, neg, d)

def signed_g(+lo: U32, +hi: U32, +d: U32, +hd0: {U32.is_zero(d) == False{} : Bool}, +hle: {U32.is_le(d, 1048576) == True{} : Bool}, +g: Bool, +hg: {S.negative(W.pack(lo, hi)) == g : Bool}) -> {P.bits(U.div_sign(U.U64{lo, hi}, d, g)) == qs(W.pack(lo, hi), g, d) : Word(64n)}:
  match g:
    case False{}:
      div_bits(U.U64{lo, hi}, d, hd0, hle)
    case True{}:
      +a = {U.U64{lo, hi} : U.U64}
      +r = U.div_small(U.neg(a), d)
      Equal.trans(Word(64n), P.bits(U.neg(r)), Word.inc(64n, Word.not(64n, P.bits(r))), S.negative_quotient(64n, W.pack(lo, hi), d), P.neg(r),
        Equal.trans(Word(64n), Word.inc(64n, Word.not(64n, P.bits(r))), Word.inc(64n, Word.not(64n, S.unsigned_quotient(64n, P.bits(U.neg(a)), d))), S.negative_quotient(64n, W.pack(lo, hi), d),
          Equal.cong(Word(64n), Word(64n), z => Word.inc(64n, Word.not(64n, z)), P.bits(r), S.unsigned_quotient(64n, P.bits(U.neg(a)), d), div_bits(U.neg(a), d, hd0, hle)),
          Equal.trans(Word(64n), Word.inc(64n, Word.not(64n, S.unsigned_quotient(64n, P.bits(U.neg(a)), d))), Word.inc(64n, Word.not(64n, S.unsigned_quotient(64n, Word.inc(64n, Word.not(64n, W.pack(lo, hi))), d))), S.negative_quotient(64n, W.pack(lo, hi), d),
            Equal.cong(Word(64n), Word(64n), z => Word.inc(64n, Word.not(64n, S.unsigned_quotient(64n, z, d))), P.bits(U.neg(a)), Word.inc(64n, Word.not(64n, W.pack(lo, hi))), P.neg(a)),
            neg_quot(64n, W.pack(lo, hi), d, nz_neg(W.pack(lo, hi), hg)))))

# THEOREM: div_small_signed is the specification's signed quotient
# (truncating toward zero), for 0 < d <= 2^20.
def div_signed(+a: U.U64, +d: U32, +hd0: {U32.is_zero(d) == False{} : Bool}, +hle: {U32.is_le(d, 1048576) == True{} : Bool}) -> {P.bits(U.div_small_signed(a, d)) == qs(P.bits(a), S.negative(P.bits(a)), d) : Word(64n)}:
  match a:
    case U.U64{+lo, +hi}:
      %Equal.sym(Bool, S.negative(W.pack(lo, hi)), U32.is_ge(hi, 2147483648), P.negative_pack(lo, hi)) : {P.bits(U.div_small_signed(U.U64{lo, hi}, d)) == qs(W.pack(lo, hi), _, d) : Word(64n)}
      signed_g(lo, hi, d, hd0, hle, U32.is_ge(hi, 2147483648), P.negative_pack(lo, hi))

def qs_spec(+w: Word(64n), +neg: Bool) -> {qs(w, neg, 1000000) == S.quotient_signed(w, neg) : Word(64n)}:
  match neg:
    case False{}:
      {==}
    case True{}:
      {==}

# THEOREM: dividing by 10^6 is the specification's nanoseconds-to-milliseconds.
def milliseconds(+a: U.U64) -> {T.I64{P.bits(U.div_small_signed(a, 1000000))} == S.milliseconds(T.I64{P.bits(a)}) : T.Int64}:
  Equal.cong(Word(64n), T.Int64, z => T.I64{z}, P.bits(U.div_small_signed(a, 1000000)), S.quotient_signed(P.bits(a), S.negative(P.bits(a))), Equal.trans(Word(64n), P.bits(U.div_small_signed(a, 1000000)), qs(P.bits(a), S.negative(P.bits(a)), 1000000), S.quotient_signed(P.bits(a), S.negative(P.bits(a))), div_signed(a, 1000000, {==}, {==}), qs_spec(P.bits(a), S.negative(P.bits(a)))))
