import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/u32.bend as U
import ../../lib/u32div.bend as UD
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/u32alg.bend as A
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../natural/arith.bend as NR
import ../u64/u64div.bend as PD
import ./w64mul.bend as WM
import ./u32.bend as U32P
import ./shrn.bend as SR

# Mod32.value and Div32 of spec/math/w64.bend: 64 / 32 long division, the
# high word by U32 division and the low word by two 16-bit digits (Knuth
# TAOCP 4.3.1, short division; every partial dividend r 2^16 + g stays below
# 2^48, the runtime's Nat bound; the digit decomposition follows the proved
# split of proofs/math/u64/u64div.bend, and the invariant "remainder of the
# prefix" is WhyMP's mpn_divrem_1 loop invariant, Rieu-Helft et al., VSTTE
# 2017). The digit constant 2^16 is a U32 word kept symbolic.

def v(+x: U32) -> Nat:
  UD.v(x)

# ---- the low word in two 16-bit digits ----

def lo_dig(+one: Nat, +h1: {one == 1n : Nat}, +lo: U32, +c16: U32, +m16: U32, +h16: {UD.v(c16) == WD.sc(16n, one) : Nat}, +hm16: {m16 == U32{WD.mask(32n, 16n)} : U32}, +nz16: {U32.is_zero(c16) == False{} : Bool}) -> {UD.v(lo) == Nat.add(WD.sc(16n, UD.v(U32.div(lo, c16))), UD.v(U32.and(lo, m16))) : Nat}:
  +ln = UD.v(lo)
  +l1 = UD.v(U32.div(lo, c16))
  +r1 = UD.v(U32.mod(lo, c16))
  +l2 = UD.v(U32.and(lo, m16))
  +y = PD.hp32(16n, lo)
  +e16 = Equal.trans(Nat, Nat.add(WD.sc(16n, l1), r1), Nat.add(Nat.mul(l1, UD.v(c16)), r1), ln, Equal.cong(Nat, Nat, z => Nat.add(z, r1), WD.sc(16n, l1), Nat.mul(l1, UD.v(c16)), Equal.sym(Nat, Nat.mul(l1, UD.v(c16)), WD.sc(16n, l1), PD.mul_pow(one, h1, 16n, l1, UD.v(c16), h16))), PD.dm_e(lo, c16, nz16))
  +l16 = L.subst(Nat, z => {Nat.is_lt(r1, z) == True{} : Bool}, UD.v(c16), WD.sc(16n, one), h16, PD.dm_l(lo, c16, nz16))
  +s2 = PD.and32(16n, lo, m16, hm16)
  +b2 = PD.and32_lt(16n, one, h1, lo, m16, hm16)
  +er = WD.uniq(16n, one, h1, r1, l2, l1, y, Equal.trans(Nat, Nat.add(r1, WD.sc(16n, l1)), Nat.add(WD.sc(16n, l1), r1), Nat.add(l2, WD.sc(16n, y)), N.add_comm(r1, WD.sc(16n, l1)), Equal.trans(Nat, Nat.add(WD.sc(16n, l1), r1), ln, Nat.add(l2, WD.sc(16n, y)), e16, s2)), l16, b2)
  Equal.trans(Nat, ln, Nat.add(WD.sc(16n, l1), r1), Nat.add(WD.sc(16n, l1), l2), Equal.sym(Nat, Nat.add(WD.sc(16n, l1), r1), ln, e16), Equal.cong(Nat, Nat, z => Nat.add(WD.sc(16n, l1), z), r1, l2, er))

# ---- the Nat base ----

def k256(+one: Nat, +h1: {one == 1n : Nat}) -> {256n == WD.sc(8n, one) : Nat}:
  L.subst(Nat, o => {256n == WD.sc(8n, o) : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})

# 2^16 is the literal 65536n. The checker computes every closed Nat in a type
# to its unary normal form, so a closed 256n * 256n (or any closed term worth
# 2^16) overflows its stack; only literals and open terms are safe. So 2^16 is
# reached from 8192n in seven closed steps of Nat.add(8192n, _), each cheap,
# joined by oct over variables, which keeps every intermediate term open.

# c == (a + a) + x when a + x == b and a + b == c
def add_twice(+a: Nat, +x: Nat, +b: Nat, +c: Nat, +hb: {Nat.add(a, x) == b : Nat}, +hc: {Nat.add(a, b) == c : Nat}) -> {c == Nat.add(Nat.add(a, a), x) : Nat}:
  %hc : {_ == Nat.add(Nat.add(a, a), x) : Nat}
  %hb : {Nat.add(a, _) == Nat.add(Nat.add(a, a), x) : Nat}
  Equal.sym(Nat, Nat.add(Nat.add(a, a), x), Nat.add(a, Nat.add(a, x)), NA.add_assoc(a, a, x))

# eight steps of a: L_i == i * a, so L8 == 2^3 * a
def oct(+one: Nat, +e: Nat, +l1: Nat, +l2: Nat, +l3: Nat, +l4: Nat, +l5: Nat, +l6: Nat, +l7: Nat, +l8: Nat, +h1: {l1 == WD.sc(e, one) : Nat}, +h2: {Nat.add(l1, l1) == l2 : Nat}, +h3: {Nat.add(l1, l2) == l3 : Nat}, +h4: {Nat.add(l1, l3) == l4 : Nat}, +h5: {Nat.add(l1, l4) == l5 : Nat}, +h6: {Nat.add(l1, l5) == l6 : Nat}, +h7: {Nat.add(l1, l6) == l7 : Nat}, +h8: {Nat.add(l1, l7) == l8 : Nat}) -> {l8 == WD.sc(3n, WD.sc(e, one)) : Nat}:
  +q4 = L.subst(Nat, z => {l4 == Nat.add(z, l2) : Nat}, Nat.add(l1, l1), l2, h2, add_twice(l1, l2, l3, l4, h3, h4))
  +q6 = L.subst(Nat, z => {l6 == Nat.add(z, l4) : Nat}, Nat.add(l1, l1), l2, h2, add_twice(l1, l4, l5, l6, h5, h6))
  +q8a = L.subst(Nat, z => {l8 == Nat.add(z, l6) : Nat}, Nat.add(l1, l1), l2, h2, add_twice(l1, l6, l7, l8, h7, h8))
  +q8b = L.subst(Nat, z => {l8 == Nat.add(l2, z) : Nat}, l6, Nat.add(l2, l4), q6, q8a)
  +q8c = Equal.trans(Nat, l8, Nat.add(l2, Nat.add(l2, l4)), Nat.add(Nat.add(l2, l2), l4), q8b, Equal.sym(Nat, Nat.add(Nat.add(l2, l2), l4), Nat.add(l2, Nat.add(l2, l4)), NA.add_assoc(l2, l2, l4)))
  +q8 = L.subst(Nat, z => {l8 == Nat.add(z, l4) : Nat}, Nat.add(l2, l2), l4, Equal.sym(Nat, l4, Nat.add(l2, l2), q4), q8c)
  +d2 = Equal.trans(Nat, l2, Nat.add(l1, l1), Nat.double(l1), Equal.sym(Nat, Nat.add(l1, l1), l2, h2), Equal.sym(Nat, Nat.double(l1), Nat.add(l1, l1), NA.double_self(l1)))
  +d4 = Equal.trans(Nat, l4, Nat.add(l2, l2), Nat.double(l2), q4, Equal.sym(Nat, Nat.double(l2), Nat.add(l2, l2), NA.double_self(l2)))
  +d8 = Equal.trans(Nat, l8, Nat.add(l4, l4), Nat.double(l4), q8, Equal.sym(Nat, Nat.double(l4), Nat.add(l4, l4), NA.double_self(l4)))
  +r1 = L.subst(Nat, z => {l8 == Nat.double(z) : Nat}, l4, Nat.double(l2), d4, d8)
  +r2 = L.subst(Nat, z => {l8 == Nat.double(Nat.double(z)) : Nat}, l2, Nat.double(l1), d2, r1)
  L.subst(Nat, z => {l8 == Nat.double(Nat.double(Nat.double(z))) : Nat}, l1, WD.sc(e, one), h1, r2)

def k8192(+one: Nat, +h1: {one == 1n : Nat}) -> {8192n == WD.sc(13n, one) : Nat}:
  L.subst(Nat, o => {8192n == WD.sc(13n, o) : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})

def k65536(+one: Nat, +h1: {one == 1n : Nat}) -> {65536n == WD.sc(16n, one) : Nat}:
  +o = oct(one, 13n, 8192n, 16384n, 24576n, 32768n, 40960n, 49152n, 57344n, 65536n, k8192(one, h1), {==}, {==}, {==}, {==}, {==}, {==}, {==})
  Equal.trans(Nat, 65536n, WD.sc(3n, WD.sc(13n, one)), WD.sc(16n, one), o, WM.sc_sc(3n, 13n, one))

# ---- one short-division step keeps the remainder of the prefix ----

def mstep(+dp: Nat, +x: Nat, +b: Nat, +g: Nat) -> {Nat.mod(Nat.add(Nat.mul(Nat.mod(x, 1n+dp), b), g), 1n+dp) == Nat.mod(Nat.add(Nat.mul(x, b), g), 1n+dp) : Nat}:
  +y = Nat.mul(Nat.mod(x, 1n+dp), b)
  Equal.trans(Nat, Nat.mod(Nat.add(y, g), 1n+dp), Nat.mod(Nat.add(Nat.mod(y, 1n+dp), g), 1n+dp), Nat.mod(Nat.add(Nat.mul(x, b), g), 1n+dp), Equal.sym(Nat, Nat.mod(Nat.add(Nat.mod(y, 1n+dp), g), 1n+dp), Nat.mod(Nat.add(y, g), 1n+dp), NR.mod_add_l(dp, y, g)),
    Equal.trans(Nat, Nat.mod(Nat.add(Nat.mod(y, 1n+dp), g), 1n+dp), Nat.mod(Nat.add(Nat.mod(Nat.mul(x, b), 1n+dp), g), 1n+dp), Nat.mod(Nat.add(Nat.mul(x, b), g), 1n+dp), Equal.cong(Nat, Nat, t => Nat.mod(Nat.add(t, g), 1n+dp), Nat.mod(y, 1n+dp), Nat.mod(Nat.mul(x, b), 1n+dp), NR.mod_mul_l(dp, x, b)), NR.mod_add_l(dp, Nat.mul(x, b), g)))

# ---- the digits rebuild the 64-bit value ----

def x2_eq(+one: Nat, +h1: {one == 1n : Nat}, +h: Nat, +g1: Nat, +g2: Nat) -> {Nat.add(Nat.mul(Nat.add(Nat.mul(h, 65536n), g1), 65536n), g2) == Nat.add(Nat.add(WD.sc(16n, g1), g2), WD.sc(32n, h)) : Nat}:
  +h16 = WD.sc(16n, h)
  +a1 = Nat.add(Nat.mul(h, 65536n), g1)
  +e1 = WM.cong_l(Nat.mul(h, 65536n), h16, g1, PD.mul_pow(one, h1, 16n, h, 65536n, k65536(one, h1)))
  +e2 = Equal.trans(Nat, Nat.mul(a1, 65536n), Nat.mul(Nat.add(h16, g1), 65536n), WD.sc(16n, Nat.add(h16, g1)), Equal.cong(Nat, Nat, t => Nat.mul(t, 65536n), a1, Nat.add(h16, g1), e1), PD.mul_pow(one, h1, 16n, Nat.add(h16, g1), 65536n, k65536(one, h1)))
  +e3 = Equal.trans(Nat, WD.sc(16n, Nat.add(h16, g1)), Nat.add(WD.sc(16n, h16), WD.sc(16n, g1)), Nat.add(WD.sc(32n, h), WD.sc(16n, g1)), WM.sc_add2(16n, h16, g1), WM.cong_l(WD.sc(16n, h16), WD.sc(32n, h), WD.sc(16n, g1), WM.sc_sc(16n, 16n, h)))
  +pp = WD.sc(32n, h)
  +aa = WD.sc(16n, g1)
  +e4 = WM.cong_l(Nat.mul(a1, 65536n), Nat.add(pp, aa), g2, Equal.trans(Nat, Nat.mul(a1, 65536n), WD.sc(16n, Nat.add(h16, g1)), Nat.add(pp, aa), e2, e3))
  Equal.trans(Nat, Nat.add(Nat.mul(a1, 65536n), g2), Nat.add(Nat.add(pp, aa), g2), Nat.add(Nat.add(aa, g2), pp), e4, Equal.trans(Nat, Nat.add(Nat.add(pp, aa), g2), Nat.add(pp, Nat.add(aa, g2)), Nat.add(Nat.add(aa, g2), pp), NA.add_assoc(pp, aa, g2), NA.add_comm(pp, Nat.add(aa, g2))))

# ---- mod32 with its word constants symbolic ----

def d1g(+lo: U32, +c16: U32) -> Nat:
  U32.to_nat(U32.div(lo, c16))

def d2g(+lo: U32, +m16: U32) -> Nat:
  U32.to_nat(U32.and(lo, m16))

def mod32g(+a: WU.U64, +d: U32, +c16: U32, +m16: U32) -> U32:
  U32.from_nat(X.mod_step(X.mod_step(U32.to_nat(U32.mod(X.hi(a), d)), 65536n, d1g(X.lo(a), c16), U32.to_nat(d)), 65536n, d2g(X.lo(a), m16), U32.to_nat(d)))

# the high digit is a shift, U32.shrn(lo, 16), the word U32.div(lo, 2^16)
def dig1_eq(+lo: U32) -> {X.dig1(lo) == d1g(lo, 65536) : Nat}:
  Equal.cong(U32, Nat, z => U32.to_nat(z), U32.shrn(lo, 16n), U32.div(lo, 65536), SR.shr16(lo))

def impl_mod(+a: WU.U64, +d: U32) -> {X.mod32(a, d) == mod32g(a, d, 65536, 65535) : U32}:
  %Equal.sym(Nat, X.dig1(X.lo(a)), d1g(X.lo(a), 65536), dig1_eq(X.lo(a))) : {U32.from_nat(X.mod_step(X.mod_step(U32.to_nat(U32.mod(X.hi(a), d)), 65536n, _, U32.to_nat(d)), 65536n, X.dig2(X.lo(a)), U32.to_nat(d))) == mod32g(a, d, 65536, 65535) : U32}
  {==}

def mod_inner(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk: {k == 32n : Nat}, +lo: U32, +hi: U32, +d: U32, +hd: {U32.is_zero(d) == False{} : Bool}, +c16: U32, +p16: {c16 == U32{WD.pw(32n, 16n)} : U32}, +m16: U32, +pm16: {m16 == U32{WD.mask(32n, 16n)} : U32}, +nd: Nat, +hnd: {v(d) == nd : Nat}) -> {v(mod32g(WU.U64{lo, hi}, d, c16, m16)) == Nat.mod(SW.value(WU.U64{lo, hi}), v(d)) : Nat}:
  match nd:
    case 0n:
      Empty.absurd({v(mod32g(WU.U64{lo, hi}, d, c16, m16)) == Nat.mod(SW.value(WU.U64{lo, hi}), v(d)) : Nat}, U32P.true_ne_false(Equal.trans(Bool, True{}, U32.is_zero(d), False{}, Equal.sym(Bool, U32.is_zero(d), True{}, L.subst(U32, z => {U32.is_zero(z) == True{} : Bool}, 0, d, Equal.sym(U32, d, 0, U.injective(d, 0, hnd)), {==})), hd)))
    case 1n+ +dp:
      +hh = v(hi)
      +g1 = d1g(lo, c16)
      +g2 = d2g(lo, m16)
      +h16 = PD.pow32(16n, {==}, one, h1, c16, p16)
      +nz16 = L.subst(U32, z => {U32.is_zero(z) == False{} : Bool}, U32{WD.pw(32n, 16n)}, c16, Equal.sym(U32, c16, U32{WD.pw(32n, 16n)}, p16), {==})
      +e0 = Equal.trans(Nat, v(U32.mod(hi, d)), Nat.mod(hh, v(d)), Nat.mod(hh, 1n+dp), UD.mod_nat(hi, d, hd), Equal.cong(Nat, Nat, t => Nat.mod(hh, t), v(d), 1n+dp, hnd))
      +x1 = Nat.add(Nat.mul(hh, 65536n), g1)
      +x2 = Nat.add(Nat.mul(x1, 65536n), g2)
      +m0 = v(U32.mod(hi, d))
      +m1 = Nat.mod(Nat.add(Nat.mul(m0, 65536n), g1), 1n+dp)
      +rr = Nat.mod(Nat.add(Nat.mul(m1, 65536n), g2), 1n+dp)
      +e1 = Equal.trans(Nat, m1, Nat.mod(Nat.add(Nat.mul(Nat.mod(hh, 1n+dp), 65536n), g1), 1n+dp), Nat.mod(x1, 1n+dp), Equal.cong(Nat, Nat, t => Nat.mod(Nat.add(Nat.mul(t, 65536n), g1), 1n+dp), m0, Nat.mod(hh, 1n+dp), e0), mstep(dp, hh, 65536n, g1))
      +e2 = Equal.trans(Nat, rr, Nat.mod(Nat.add(Nat.mul(Nat.mod(x1, 1n+dp), 65536n), g2), 1n+dp), Nat.mod(x2, 1n+dp), Equal.cong(Nat, Nat, t => Nat.mod(Nat.add(Nat.mul(t, 65536n), g2), 1n+dp), m1, Nat.mod(x1, 1n+dp), e1), mstep(dp, x1, 65536n, g2))
      +elo = lo_dig(one, h1, lo, c16, m16, h16, pm16, nz16)
      +ex2 = Equal.trans(Nat, x2, Nat.add(Nat.add(WD.sc(16n, g1), g2), WD.sc(32n, hh)), SW.value(WU.U64{lo, hi}), x2_eq(one, h1, hh, g1, g2), Equal.trans(Nat, Nat.add(Nat.add(WD.sc(16n, g1), g2), WD.sc(32n, hh)), Nat.add(v(lo), WD.sc(32n, hh)), SW.value(WU.U64{lo, hi}), WM.cong_l(Nat.add(WD.sc(16n, g1), g2), v(lo), WD.sc(32n, hh), Equal.sym(Nat, v(lo), Nat.add(WD.sc(16n, g1), g2), elo)), WM.cong_r(v(lo), WD.sc(32n, hh), C.shift(32n, hh), Equal.sym(Nat, C.shift(32n, hh), WD.sc(32n, hh), WM.shift_sc(32n, hh)))))
      +eres = Equal.trans(Nat, rr, Nat.mod(x2, 1n+dp), Nat.mod(SW.value(WU.U64{lo, hi}), 1n+dp), e2, Equal.cong(Nat, Nat, t => Nat.mod(t, 1n+dp), x2, SW.value(WU.U64{lo, hi}), ex2))
      +blt = N.lt_le_trans(rr, 1n+dp, C.pow2(k), NR.dm_lt(dp, Nat.add(Nat.mul(m1, 65536n), g2)), N.lt_le(1n+dp, C.pow2(k), L.subst(Nat, z => {Nat.is_lt(z, C.pow2(k)) == True{} : Bool}, v(d), 1n+dp, hnd, U32P.val_lt(1n, {==}, k, hk, d))))
      +efit = U.to_nat_from_nat(rr, k, U32P.le_k(k, hk), blt)
      %Equal.sym(Nat, v(d), 1n+dp, hnd) : {v(U32.from_nat(X.mod_step(X.mod_step(v(U32.mod(hi, d)), 65536n, g1, _), 65536n, g2, _))) == Nat.mod(SW.value(WU.U64{lo, hi}), _) : Nat}
      Equal.trans(Nat, v(U32.from_nat(rr)), rr, Nat.mod(SW.value(WU.U64{lo, hi}), 1n+dp), efit, eres)

# Mod32.value: a 64-bit value mod a nonzero U32
def mod32_value(+a: WU.U64, +d: U32, +hd: {U32.is_zero(d) == False{} : Bool}) -> SW.Mod32.value(a, d, hd):
  match a:
    case WU.U64{+lo, +hi}:
      %Equal.sym(U32, X.mod32(WU.U64{lo, hi}, d), mod32g(WU.U64{lo, hi}, d, 65536, 65535), impl_mod(WU.U64{lo, hi}, d)) : {U32.to_nat(_) == Nat.mod(SW.value(WU.U64{lo, hi}), U32.to_nat(d)) : Nat}
      mod_inner(1n, {==}, 32n, {==}, lo, hi, d, hd, 65536, {==}, 65535, {==}, v(d), {==})

# Div32.rem: div32's remainder is mod32's term
def div32_rem(+a: WU.U64, +d: U32, +hd: {U32.is_zero(d) == False{} : Bool}) -> SW.Div32.rem(a, d, hd):
  mod32_value(a, d, hd)

# ==== Div32.quot ====

# one digit of long division: (A D + r) b + g == (A b + q2) D + r2 when r b + g == q2 D + r2
def dstep(+A: Nat, +D: Nat, +r: Nat, +b: Nat, +g: Nat, +q2: Nat, +r2: Nat, +e: {Nat.add(Nat.mul(r, b), g) == Nat.add(Nat.mul(q2, D), r2) : Nat}) -> {Nat.add(Nat.mul(Nat.add(Nat.mul(A, D), r), b), g) == Nat.add(Nat.mul(Nat.add(Nat.mul(A, b), q2), D), r2) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(Nat.mul(A, D), r), b), g), Nat.add(Nat.add(Nat.mul(Nat.mul(A, D), b), Nat.mul(r, b)), g), Nat.add(Nat.mul(Nat.add(Nat.mul(A, b), q2), D), r2), Equal.cong(Nat, Nat, z => Nat.add(z, g), Nat.mul(Nat.add(Nat.mul(A, D), r), b), Nat.add(Nat.mul(Nat.mul(A, D), b), Nat.mul(r, b)), NA.mul_add_right(Nat.mul(A, D), r, b)), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(Nat.mul(A, D), b), Nat.mul(r, b)), g), Nat.add(Nat.mul(Nat.mul(A, D), b), Nat.add(Nat.mul(r, b), g)), Nat.add(Nat.mul(Nat.add(Nat.mul(A, b), q2), D), r2), NA.add_assoc(Nat.mul(Nat.mul(A, D), b), Nat.mul(r, b), g), Equal.trans(Nat, Nat.add(Nat.mul(Nat.mul(A, D), b), Nat.add(Nat.mul(r, b), g)), Nat.add(Nat.mul(Nat.mul(A, D), b), Nat.add(Nat.mul(q2, D), r2)), Nat.add(Nat.mul(Nat.add(Nat.mul(A, b), q2), D), r2), Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(Nat.mul(A, D), b), z), Nat.add(Nat.mul(r, b), g), Nat.add(Nat.mul(q2, D), r2), e), Equal.trans(Nat, Nat.add(Nat.mul(Nat.mul(A, D), b), Nat.add(Nat.mul(q2, D), r2)), Nat.add(Nat.add(Nat.mul(Nat.mul(A, D), b), Nat.mul(q2, D)), r2), Nat.add(Nat.mul(Nat.add(Nat.mul(A, b), q2), D), r2), Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(Nat.mul(A, D), b), Nat.mul(q2, D)), r2), Nat.add(Nat.mul(Nat.mul(A, D), b), Nat.add(Nat.mul(q2, D), r2)), NA.add_assoc(Nat.mul(Nat.mul(A, D), b), Nat.mul(q2, D), r2)), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(Nat.mul(A, D), b), Nat.mul(q2, D)), r2), Nat.add(Nat.add(Nat.mul(Nat.mul(A, b), D), Nat.mul(q2, D)), r2), Nat.add(Nat.mul(Nat.add(Nat.mul(A, b), q2), D), r2), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(z, Nat.mul(q2, D)), r2), Nat.mul(Nat.mul(A, D), b), Nat.mul(Nat.mul(A, b), D), Equal.trans(Nat, Nat.mul(Nat.mul(A, D), b), Nat.mul(A, Nat.mul(D, b)), Nat.mul(Nat.mul(A, b), D), NA.mul_assoc(A, D, b), Equal.trans(Nat, Nat.mul(A, Nat.mul(D, b)), Nat.mul(A, Nat.mul(b, D)), Nat.mul(Nat.mul(A, b), D), Equal.cong(Nat, Nat, z => Nat.mul(A, z), Nat.mul(D, b), Nat.mul(b, D), NA.mul_comm(D, b)), Equal.sym(Nat, Nat.mul(Nat.mul(A, b), D), Nat.mul(A, Nat.mul(b, D)), NA.mul_assoc(A, b, D))))), Equal.cong(Nat, Nat, z => Nat.add(z, r2), Nat.add(Nat.mul(Nat.mul(A, b), D), Nat.mul(q2, D)), Nat.mul(Nat.add(Nat.mul(A, b), q2), D), Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(A, b), q2), D), Nat.add(Nat.mul(Nat.mul(A, b), D), Nat.mul(q2, D)), NA.mul_add_right(Nat.mul(A, b), q2, D))))))))

def lt_cancel_mul_c(+a: Nat, +b: Nat, +d: Nat, +h: {Nat.is_lt(Nat.mul(a, d), Nat.mul(b, d)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_lt(a, b) == c : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match c:
    case True{}:
      hc
    case False{}:
      Empty.absurd({Nat.is_lt(a, b) == True{} : Bool}, U32P.true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(Nat.mul(a, d), Nat.mul(b, d)), False{}, Equal.sym(Bool, Nat.is_lt(Nat.mul(a, d), Nat.mul(b, d)), True{}, h), N.le_not_lt(Nat.mul(a, d), Nat.mul(b, d), AR.mul_le(b, a, d, N.not_lt_le(a, b, hc))))))

def lt_cancel_mul(+a: Nat, +b: Nat, +d: Nat, +h: {Nat.is_lt(Nat.mul(a, d), Nat.mul(b, d)) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  lt_cancel_mul_c(a, b, d, h, Nat.is_lt(a, b), {==})

def div32q_g(+lo: U32, +hi: U32, +d: U32, +c16: U32, +m16: U32) -> WU.U64:
  WU.U64{U32.from_nat(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), U32.to_nat(d)), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), U32.to_nat(d)), 65536n, d2g(lo, m16)), U32.to_nat(d)))), U32.div(hi, d)}

def impl_q(+lo: U32, +hi: U32, +d: U32) -> {X.fst_q(X.div32(WU.U64{lo, hi}, d)) == div32q_g(lo, hi, d, 65536, 65535) : WU.U64}:
  %Equal.sym(Nat, X.dig1(lo), d1g(lo, 65536), dig1_eq(lo)) : {X.fst_q(X.div32_t1(U32.div(hi, d), lo, X.dig_t(U32.to_nat(U32.mod(hi, d)), 65536n, _), U32.to_nat(d))) == div32q_g(lo, hi, d, 65536, 65535) : WU.U64}
  {==}

def quot_core(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk: {k == 32n : Nat}, +lo: U32, +hi: U32, +d: U32, +hd: {U32.is_zero(d) == False{} : Bool}, +c16: U32, +p16: {c16 == U32{WD.pw(32n, 16n)} : U32}, +m16: U32, +pm16: {m16 == U32{WD.mask(32n, 16n)} : U32}, +dp: Nat, +hnd: {v(d) == 1n+dp : Nat}) -> {Nat.add(U32.to_nat(U32.from_nat(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)))), C.shift(32n, v(U32.div(hi, d)))) == Nat.div(SW.value(WU.U64{lo, hi}), 1n+dp) : Nat}:
  +h16 = PD.pow32(16n, {==}, one, h1, c16, p16)
  +nz16 = L.subst(U32, z => {U32.is_zero(z) == False{} : Bool}, U32{WD.pw(32n, 16n)}, c16, Equal.sym(U32, c16, U32{WD.pw(32n, 16n)}, p16), {==})
  +e1 = NR.dm_eq(dp, X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)))
  +e2 = NR.dm_eq(dp, X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)))
  +s = Equal.trans(Nat, Nat.add(Nat.mul(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 65536n), d2g(lo, m16)), Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 1n+dp), Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp)), 65536n), d2g(lo, m16)), Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), 1n+dp), Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), Equal.cong(Nat, Nat, t => Nat.add(Nat.mul(t, 65536n), d2g(lo, m16)), X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 1n+dp), Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp)), e1), dstep(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 1n+dp, Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp), Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp), e2))
  +elo = lo_dig(one, h1, lo, c16, m16, h16, pm16, nz16)
  +eY = Equal.trans(Nat, Nat.add(Nat.mul(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 65536n), d2g(lo, m16)), Nat.add(Nat.add(WD.sc(16n, d1g(lo, c16)), d2g(lo, m16)), WD.sc(32n, v(U32.mod(hi, d)))), Nat.add(v(lo), WD.sc(32n, v(U32.mod(hi, d)))), x2_eq(one, h1, v(U32.mod(hi, d)), d1g(lo, c16), d2g(lo, m16)), WM.cong_l(Nat.add(WD.sc(16n, d1g(lo, c16)), d2g(lo, m16)), v(lo), WD.sc(32n, v(U32.mod(hi, d))), Equal.sym(Nat, v(lo), Nat.add(WD.sc(16n, d1g(lo, c16)), d2g(lo, m16)), elo)))
  +ehh = Equal.trans(Nat, Nat.add(Nat.mul(v(U32.div(hi, d)), 1n+dp), v(U32.mod(hi, d))), Nat.add(Nat.mul(v(U32.div(hi, d)), v(d)), v(U32.mod(hi, d))), v(hi), Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(v(U32.div(hi, d)), z), v(U32.mod(hi, d))), 1n+dp, v(d), Equal.sym(Nat, v(d), 1n+dp, hnd)), PD.dm_e(hi, d, hd))
  +v1 = WM.cong_r(v(lo), C.shift(32n, v(hi)), WD.sc(32n, v(hi)), WM.shift_sc(32n, v(hi)))
  +v2 = WM.cong_r(v(lo), WD.sc(32n, v(hi)), WD.sc(32n, Nat.add(Nat.mul(v(U32.div(hi, d)), 1n+dp), v(U32.mod(hi, d)))), Equal.cong(Nat, Nat, z => WD.sc(32n, z), v(hi), Nat.add(Nat.mul(v(U32.div(hi, d)), 1n+dp), v(U32.mod(hi, d))), Equal.sym(Nat, Nat.add(Nat.mul(v(U32.div(hi, d)), 1n+dp), v(U32.mod(hi, d))), v(hi), ehh)))
  +v3 = WM.cong_r(v(lo), WD.sc(32n, Nat.add(Nat.mul(v(U32.div(hi, d)), 1n+dp), v(U32.mod(hi, d)))), Nat.add(WD.sc(32n, Nat.mul(v(U32.div(hi, d)), 1n+dp)), WD.sc(32n, v(U32.mod(hi, d)))), WM.sc_add2(32n, Nat.mul(v(U32.div(hi, d)), 1n+dp), v(U32.mod(hi, d))))
  +a0 = v(lo)
  +aB = WD.sc(32n, Nat.mul(v(U32.div(hi, d)), 1n+dp))
  +aM = WD.sc(32n, v(U32.mod(hi, d)))
  +v4 = Equal.trans(Nat, Nat.add(a0, Nat.add(aB, aM)), Nat.add(a0, Nat.add(aM, aB)), Nat.add(Nat.add(a0, aM), aB), WM.cong_r(a0, Nat.add(aB, aM), Nat.add(aM, aB), NA.add_comm(aB, aM)), Equal.sym(Nat, Nat.add(Nat.add(a0, aM), aB), Nat.add(a0, Nat.add(aM, aB)), NA.add_assoc(a0, aM, aB)))
  +v5 = WM.cong_l(Nat.add(a0, aM), Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), 1n+dp), Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), aB, Equal.trans(Nat, Nat.add(a0, aM), Nat.add(Nat.mul(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 65536n), d2g(lo, m16)), Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), 1n+dp), Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), Equal.sym(Nat, Nat.add(Nat.mul(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 65536n), d2g(lo, m16)), Nat.add(a0, aM), eY), s))
  +bQ = Nat.mul(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), 1n+dp)
  +bS = Nat.mul(WD.sc(32n, v(U32.div(hi, d))), 1n+dp)
  +v6 = Equal.trans(Nat, Nat.add(Nat.add(bQ, Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), aB), Nat.add(Nat.add(bQ, Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), bS), Nat.add(Nat.add(bQ, bS), Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), WM.cong_r(Nat.add(bQ, Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), aB, bS, Equal.sym(Nat, bS, aB, WM.mul_sc_l(32n, v(U32.div(hi, d)), 1n+dp))), Equal.trans(Nat, Nat.add(Nat.add(bQ, Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), bS), Nat.add(bQ, Nat.add(Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp), bS)), Nat.add(Nat.add(bQ, bS), Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), NA.add_assoc(bQ, Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp), bS), Equal.trans(Nat, Nat.add(bQ, Nat.add(Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp), bS)), Nat.add(bQ, Nat.add(bS, Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp))), Nat.add(Nat.add(bQ, bS), Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), WM.cong_r(bQ, Nat.add(Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp), bS), Nat.add(bS, Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), NA.add_comm(Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp), bS)), Equal.sym(Nat, Nat.add(Nat.add(bQ, bS), Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), Nat.add(bQ, Nat.add(bS, Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp))), NA.add_assoc(bQ, bS, Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp))))))
  +v7 = WM.cong_l(Nat.add(bQ, bS), Nat.mul(Nat.add(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), WD.sc(32n, v(U32.div(hi, d)))), 1n+dp), Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp), Equal.sym(Nat, Nat.mul(Nat.add(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), WD.sc(32n, v(U32.div(hi, d)))), 1n+dp), Nat.add(bQ, bS), NA.mul_add_right(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), WD.sc(32n, v(U32.div(hi, d))), 1n+dp)))
  +ev = Equal.trans(Nat, SW.value(WU.U64{lo, hi}), Nat.add(a0, WD.sc(32n, v(hi))), Nat.add(Nat.mul(Nat.add(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), WD.sc(32n, v(U32.div(hi, d)))), 1n+dp), Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), v1, Equal.trans(Nat, Nat.add(a0, WD.sc(32n, v(hi))), Nat.add(a0, WD.sc(32n, Nat.add(Nat.mul(v(U32.div(hi, d)), 1n+dp), v(U32.mod(hi, d))))), Nat.add(Nat.mul(Nat.add(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), WD.sc(32n, v(U32.div(hi, d)))), 1n+dp), Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), v2, Equal.trans(Nat, Nat.add(a0, WD.sc(32n, Nat.add(Nat.mul(v(U32.div(hi, d)), 1n+dp), v(U32.mod(hi, d))))), Nat.add(a0, Nat.add(aB, aM)), Nat.add(Nat.mul(Nat.add(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), WD.sc(32n, v(U32.div(hi, d)))), 1n+dp), Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), v3, Equal.trans(Nat, Nat.add(a0, Nat.add(aB, aM)), Nat.add(Nat.add(a0, aM), aB), Nat.add(Nat.mul(Nat.add(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), WD.sc(32n, v(U32.div(hi, d)))), 1n+dp), Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), v4, Equal.trans(Nat, Nat.add(Nat.add(a0, aM), aB), Nat.add(Nat.add(bQ, Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), aB), Nat.add(Nat.mul(Nat.add(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), WD.sc(32n, v(U32.div(hi, d)))), 1n+dp), Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), v5, Equal.trans(Nat, Nat.add(Nat.add(bQ, Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), aB), Nat.add(Nat.add(bQ, bS), Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), Nat.add(Nat.mul(Nat.add(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), WD.sc(32n, v(U32.div(hi, d)))), 1n+dp), Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), v6, v7))))))
  +ediv = Equal.trans(Nat, Nat.div(SW.value(WU.U64{lo, hi}), 1n+dp), Nat.div(Nat.add(Nat.mul(Nat.add(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), WD.sc(32n, v(U32.div(hi, d)))), 1n+dp), Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), 1n+dp), Nat.add(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), WD.sc(32n, v(U32.div(hi, d)))), Equal.cong(Nat, Nat, t => Nat.div(t, 1n+dp), SW.value(WU.U64{lo, hi}), Nat.add(Nat.mul(Nat.add(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), WD.sc(32n, v(U32.div(hi, d)))), 1n+dp), Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), ev), NR.div_of(Nat.add(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), WD.sc(32n, v(U32.div(hi, d)))), dp, Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp), NR.dm_lt(dp, X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)))))
  +hml = N.lt_succ_le_succ(v(U32.mod(hi, d)), v(d), PD.dm_l(hi, d, hd))
  +hml1 = L.subst(Nat, o => {Nat.is_le(Nat.add(o, v(U32.mod(hi, d))), v(d)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), hml)
  +hY2 = N.lt_le_trans(Nat.add(v(lo), WD.sc(32n, v(U32.mod(hi, d)))), Nat.add(WD.sc(32n, one), WD.sc(32n, v(U32.mod(hi, d)))), WD.sc(32n, v(d)), N.lt_add_r2(v(lo), WD.sc(32n, one), WD.sc(32n, v(U32.mod(hi, d))), UD.vb(one, h1, lo)), L.subst(Nat, z => {Nat.is_le(z, WD.sc(32n, v(d))) == True{} : Bool}, WD.sc(32n, Nat.add(one, v(U32.mod(hi, d)))), Nat.add(WD.sc(32n, one), WD.sc(32n, v(U32.mod(hi, d)))), WM.sc_add2(32n, one, v(U32.mod(hi, d))), AR.sc_le(32n, Nat.add(one, v(U32.mod(hi, d))), v(d), hml1)))
  +hY = L.subst(Nat, z => {Nat.is_lt(Nat.add(Nat.mul(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 65536n), d2g(lo, m16)), WD.sc(32n, z)) == True{} : Bool}, v(d), 1n+dp, hnd, L.subst(Nat, z => {Nat.is_lt(z, WD.sc(32n, v(d))) == True{} : Bool}, Nat.add(v(lo), WD.sc(32n, v(U32.mod(hi, d)))), Nat.add(Nat.mul(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 65536n), d2g(lo, m16)), Equal.sym(Nat, Nat.add(Nat.mul(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 65536n), d2g(lo, m16)), Nat.add(v(lo), WD.sc(32n, v(U32.mod(hi, d)))), eY), hY2))
  +hQY = L.subst(Nat, z => {Nat.is_le(Nat.mul(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), 1n+dp), z) == True{} : Bool}, Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), 1n+dp), Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), Nat.add(Nat.mul(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 65536n), d2g(lo, m16)), Equal.sym(Nat, Nat.add(Nat.mul(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 65536n), d2g(lo, m16)), Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), 1n+dp), Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), s), N.le_add_right(Nat.mul(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), 1n+dp), Nat.mod(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)))
  +hQ0 = L.subst(Nat, z => {Nat.is_lt(Nat.mul(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), 1n+dp), z) == True{} : Bool}, WD.sc(32n, 1n+dp), Nat.mul(WD.sc(32n, one), 1n+dp), Equal.trans(Nat, WD.sc(32n, 1n+dp), Nat.mul(1n+dp, WD.sc(32n, one)), Nat.mul(WD.sc(32n, one), 1n+dp), Equal.sym(Nat, Nat.mul(1n+dp, WD.sc(32n, one)), WD.sc(32n, 1n+dp), WM.mul_sc1(32n, one, h1, 1n+dp)), NA.mul_comm(1n+dp, WD.sc(32n, one))), N.le_lt_trans(Nat.mul(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), 1n+dp), Nat.add(Nat.mul(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 65536n), d2g(lo, m16)), WD.sc(32n, 1n+dp), hQY, hY))
  +hQ = lt_cancel_mul(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), WD.sc(32n, one), 1n+dp, hQ0)
  +hQ1 = L.subst(Nat, o => {Nat.is_lt(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), WD.sc(32n, o)) == True{} : Bool}, one, 1n, h1, hQ)
  +hQ2 = L.subst(Nat, z => {Nat.is_lt(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), WD.sc(z, 1n)) == True{} : Bool}, 32n, k, Equal.sym(Nat, k, 32n, hk), hQ1)
  +blt = L.subst(Nat, z => {Nat.is_lt(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), z) == True{} : Bool}, WD.sc(k, 1n), C.pow2(k), Equal.sym(Nat, C.pow2(k), WD.sc(k, 1n), U.pow2_scale(k)), hQ2)
  +efit = U.to_nat_from_nat(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), k, U32P.le_k(k, hk), blt)
  Equal.trans(Nat, Nat.add(U32.to_nat(U32.from_nat(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)))), C.shift(32n, v(U32.div(hi, d)))), Nat.add(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), WD.sc(32n, v(U32.div(hi, d)))), Nat.div(SW.value(WU.U64{lo, hi}), 1n+dp), Equal.trans(Nat, Nat.add(U32.to_nat(U32.from_nat(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)))), C.shift(32n, v(U32.div(hi, d)))), Nat.add(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), C.shift(32n, v(U32.div(hi, d)))), Nat.add(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), WD.sc(32n, v(U32.div(hi, d)))), WM.cong_l(U32.to_nat(U32.from_nat(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)))), Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), C.shift(32n, v(U32.div(hi, d))), efit), WM.cong_r(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), C.shift(32n, v(U32.div(hi, d))), WD.sc(32n, v(U32.div(hi, d))), WM.shift_sc(32n, v(U32.div(hi, d))))), Equal.sym(Nat, Nat.div(SW.value(WU.U64{lo, hi}), 1n+dp), Nat.add(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), 1n+dp), 65536n, d2g(lo, m16)), 1n+dp)), WD.sc(32n, v(U32.div(hi, d)))), ediv))

def quot_inner(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk: {k == 32n : Nat}, +lo: U32, +hi: U32, +d: U32, +hd: {U32.is_zero(d) == False{} : Bool}, +c16: U32, +p16: {c16 == U32{WD.pw(32n, 16n)} : U32}, +m16: U32, +pm16: {m16 == U32{WD.mask(32n, 16n)} : U32}, +nd: Nat, +hnd: {v(d) == nd : Nat}) -> {Nat.add(U32.to_nat(U32.from_nat(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), v(d)), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), v(d)), 65536n, d2g(lo, m16)), v(d))))), C.shift(32n, v(U32.div(hi, d)))) == Nat.div(SW.value(WU.U64{lo, hi}), v(d)) : Nat}:
  match nd:
    case 0n:
      Empty.absurd({Nat.add(U32.to_nat(U32.from_nat(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), v(d)), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), v(d)), 65536n, d2g(lo, m16)), v(d))))), C.shift(32n, v(U32.div(hi, d)))) == Nat.div(SW.value(WU.U64{lo, hi}), v(d)) : Nat}, U32P.true_ne_false(Equal.trans(Bool, True{}, U32.is_zero(d), False{}, Equal.sym(Bool, U32.is_zero(d), True{}, L.subst(U32, z => {U32.is_zero(z) == True{} : Bool}, 0, d, Equal.sym(U32, d, 0, U.injective(d, 0, hnd)), {==})), hd)))
    case 1n+ +dp:
      L.subst(Nat, z => {Nat.add(U32.to_nat(U32.from_nat(Nat.add(Nat.mul(Nat.div(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), z), 65536n), Nat.div(X.dig_t(Nat.mod(X.dig_t(v(U32.mod(hi, d)), 65536n, d1g(lo, c16)), z), 65536n, d2g(lo, m16)), z)))), C.shift(32n, v(U32.div(hi, d)))) == Nat.div(SW.value(WU.U64{lo, hi}), z) : Nat}, 1n+dp, v(d), Equal.sym(Nat, v(d), 1n+dp, hnd), quot_core(one, h1, k, hk, lo, hi, d, hd, c16, p16, m16, pm16, dp, hnd))

# Div32.quot: a 64-bit value divided by a nonzero U32
def div32_quot(+a: WU.U64, +d: U32, +hd: {U32.is_zero(d) == False{} : Bool}) -> SW.Div32.quot(a, d, hd):
  match a:
    case WU.U64{+lo, +hi}:
      %Equal.sym(WU.U64, X.fst_q(X.div32(WU.U64{lo, hi}, d)), div32q_g(lo, hi, d, 65536, 65535), impl_q(lo, hi, d)) : {SW.value(_) == Nat.div(SW.value(WU.U64{lo, hi}), U32.to_nat(d)) : Nat}
      quot_inner(1n, {==}, 32n, {==}, lo, hi, d, hd, 65536, {==}, 65535, {==}, v(d), {==})
