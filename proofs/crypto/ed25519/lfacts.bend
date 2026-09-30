import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../spec/crypto/curve25519/x25519.bend as SX
import ../../../spec/crypto/ed25519.bend as SE
import ../../../src/crypto/curve25519/limbs.bend as LS
import ../../../src/crypto/ed25519/scalar.bend as ESC
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../curve25519/num.bend as M
import ../curve25519/limbs.bend as LM
import ../curve25519/consts.bend as K
import ../curve25519/xlem.bend as LD
import ../fe/nl.bend as NL
import ../fe/pw.bend as PW
import ../fe/pass.bend as PS
import ../fe/bytes.bend as BY
import ../fe/conv.bend as CV
import ./adc.bend as AD
import ./scalar3.bend as S3

# The group order L = SE.ell(one) of spec/crypto/ed25519.bend: its shape
# 2^252 <= L <= 2^252 + 2^125 by certified digit additions (the constants'
# values stay open in the symbolic one), and the 17-bit limbs of
# src/crypto/ed25519/scalar.bend (l15): value L, limbs below 2^17.

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

# ---- constant digit strings ----

# L - 2^252 in 32 bytes
def cl32() -> List<&2, U32>:
  [237, 211, 245, 92, 26, 99, 18, 88, 214, 156, 247, 162, 222, 249, 222, 20,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

# 2^125 - (L - 2^252)
def dd32() -> List<&2, U32>:
  [19, 44, 10, 163, 229, 156, 237, 167, 41, 99, 8, 93, 33, 6, 33, 11,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def b252() -> List<&2, U32>:
  K.rep(31n, 0, [16])

def b125() -> List<&2, U32>:
  K.rep(15n, 0, Con{32, K.rep(16n, 0, Nil{})})

def adc_l() -> {AD.adc_ok(cl32(), b252(), ESC.ell(), 0n, 0n) == True{} : Bool}:
  {==}

def adc_c() -> {AD.adc_ok(cl32(), dd32(), b125(), 0n, 0n) == True{} : Bool}:
  {==}

# 2^(8 n) x
def m8(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+m:
      Nat.add(8n, m8(m))

def shn_sc(+n: Nat, +x: Nat) -> {LM.shn(n, x) == WD.sc(m8(n), x) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      tr(C.shift(8n, LM.shn(m, x)), WD.sc(8n, WD.sc(m8(m), x)), WD.sc(Nat.add(8n, m8(m)), x), M.cong_sc(8n, LM.shn(m, x), WD.sc(m8(m), x), shn_sc(m, x)), M.sc_sc(8n, m8(m), x))

def sh32_zero(+one: Nat, +xs: List<&2, U32>, +h: {LM.okb(32n, xs, 255n) == True{} : Bool}) -> {LM.sh(xs, Nat.mul(one, 0n)) == 0n : Nat}:
  tr(LM.sh(xs, Nat.mul(one, 0n)), LM.shn(32n, Nat.mul(one, 0n)), 0n, LM.sh_okb(32n, xs, 255n, Nat.mul(one, 0n), h), tr(LM.shn(32n, Nat.mul(one, 0n)), LM.shn(32n, 0n), 0n, Equal.cong(Nat, Nat, t => LM.shn(32n, t), Nat.mul(one, 0n), 0n, NA.mul_zero(one)), {==}))

# the certified sum without carries: valo(x) + valo(y) == valo(z)
def adc_sum(+one: Nat, +xs: List<&2, U32>, +ys: List<&2, U32>, +zs: List<&2, U32>, +h: {AD.adc_ok(xs, ys, zs, 0n, 0n) == True{} : Bool}, +hx: {LM.okb(32n, xs, 255n) == True{} : Bool}) -> {Nat.add(K.valo(one, xs), K.valo(one, ys)) == K.valo(one, zs) : Nat}:
  +X = K.valo(one, xs)
  +Y = K.valo(one, ys)
  +Z = K.valo(one, zs)
  +e = AD.adc_val(one, xs, ys, zs, 0n, 0n, h)
  tr(Nat.add(X, Y), Nat.add(Nat.add(X, Y), Nat.mul(one, 0n)), Z, tr(Nat.add(X, Y), Nat.add(Nat.add(X, Y), 0n), Nat.add(Nat.add(X, Y), Nat.mul(one, 0n)), sy(Nat.add(Nat.add(X, Y), 0n), Nat.add(X, Y), N.add_zero(Nat.add(X, Y))), M.cong_r(Nat.add(X, Y), 0n, Nat.mul(one, 0n), sy(Nat.mul(one, 0n), 0n, NA.mul_zero(one)))), tr(Nat.add(Nat.add(X, Y), Nat.mul(one, 0n)), Nat.add(Z, LM.sh(xs, Nat.mul(one, 0n))), Z, e, tr(Nat.add(Z, LM.sh(xs, Nat.mul(one, 0n))), Nat.add(Z, 0n), Z, M.cong_r(Z, LM.sh(xs, Nat.mul(one, 0n)), 0n, sh32_zero(one, xs, hx)), N.add_zero(Z))))

# valo(one, [k]) == one k
def valo1(+one: Nat, +k: U32) -> {K.valo(one, [k]) == Nat.mul(one, U32.to_nat(k)) : Nat}:
  N.add_zero(Nat.mul(one, U32.to_nat(k)))

def valo_b252(+one: Nat) -> {K.valo(one, b252()) == WD.sc(252n, one) : Nat}:
  +e1 = K.run0(one, 31n, [16])
  +e2 = Equal.cong(Nat, Nat, t => LM.shn(31n, t), K.valo(one, [16]), WD.sc(4n, one), tr(K.valo(one, [16]), Nat.mul(one, 16n), WD.sc(4n, one), valo1(one, 16), AR.mul_sc(4n, one)))
  tr(K.valo(one, b252()), LM.shn(31n, K.valo(one, [16])), WD.sc(252n, one), e1, tr(LM.shn(31n, K.valo(one, [16])), LM.shn(31n, WD.sc(4n, one)), WD.sc(252n, one), e2, tr(LM.shn(31n, WD.sc(4n, one)), WD.sc(248n, WD.sc(4n, one)), WD.sc(252n, one), shn_sc(31n, WD.sc(4n, one)), M.sc_sc(248n, 4n, one))))

def valo_b125(+one: Nat) -> {K.valo(one, b125()) == WD.sc(125n, one) : Nat}:
  +t = {Con{32, K.rep(16n, 0, Nil{})} : List<&2, U32>}
  +e0 = tr(K.valo(one, K.rep(16n, 0, Nil{})), LM.shn(16n, 0n), 0n, K.run0(one, 16n, Nil{}), {==})
  +et = tr(K.valo(one, t), Nat.add(Nat.mul(one, 32n), C.shift(8n, 0n)), WD.sc(5n, one), M.cong_r(Nat.mul(one, 32n), C.shift(8n, K.valo(one, K.rep(16n, 0, Nil{}))), C.shift(8n, 0n), M.cong_sc(8n, K.valo(one, K.rep(16n, 0, Nil{})), 0n, e0)), tr(Nat.add(Nat.mul(one, 32n), C.shift(8n, 0n)), Nat.mul(one, 32n), WD.sc(5n, one), N.add_zero(Nat.mul(one, 32n)), AR.mul_sc(5n, one)))
  tr(K.valo(one, b125()), LM.shn(15n, K.valo(one, t)), WD.sc(125n, one), K.run0(one, 15n, t), tr(LM.shn(15n, K.valo(one, t)), LM.shn(15n, WD.sc(5n, one)), WD.sc(125n, one), Equal.cong(Nat, Nat, z => LM.shn(15n, z), K.valo(one, t), WD.sc(5n, one), et), tr(LM.shn(15n, WD.sc(5n, one)), WD.sc(120n, WD.sc(5n, one)), WD.sc(125n, one), shn_sc(15n, WD.sc(5n, one)), M.sc_sc(120n, 5n, one))))

# L == c + 2^252 with c <= 2^125
def ell_split(+one: Nat) -> {Nat.add(K.valo(one, cl32()), WD.sc(252n, one)) == SE.ell(one) : Nat}:
  tr(Nat.add(K.valo(one, cl32()), WD.sc(252n, one)), Nat.add(K.valo(one, cl32()), K.valo(one, b252())), SE.ell(one), M.cong_r(K.valo(one, cl32()), WD.sc(252n, one), K.valo(one, b252()), sy(K.valo(one, b252()), WD.sc(252n, one), valo_b252(one))), tr(Nat.add(K.valo(one, cl32()), K.valo(one, b252())), K.valo(one, ESC.ell()), SE.ell(one), adc_sum(one, cl32(), b252(), ESC.ell(), adc_l(), {==}), S3.ell_valo(one)))

def c_le(+one: Nat) -> {Nat.is_le(K.valo(one, cl32()), WD.sc(125n, one)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(K.valo(one, cl32()), z) == True{} : Bool}, Nat.add(K.valo(one, cl32()), K.valo(one, dd32())), WD.sc(125n, one), tr(Nat.add(K.valo(one, cl32()), K.valo(one, dd32())), K.valo(one, b125()), WD.sc(125n, one), adc_sum(one, cl32(), dd32(), b125(), adc_c(), {==}), valo_b125(one)), N.le_add_right(K.valo(one, cl32()), K.valo(one, dd32())))

# 2^252 <= L
def ell_lo(+one: Nat) -> {Nat.is_le(WD.sc(252n, one), SE.ell(one)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(WD.sc(252n, one), z) == True{} : Bool}, Nat.add(K.valo(one, cl32()), WD.sc(252n, one)), SE.ell(one), ell_split(one), NL.le_add_l(K.valo(one, cl32()), WD.sc(252n, one)))

# L <= 2^252 + 2^125
def ell_hi(+one: Nat) -> {Nat.is_le(SE.ell(one), Nat.add(WD.sc(252n, one), WD.sc(125n, one))) == True{} : Bool}:
  +a = M.le_add_r(K.valo(one, cl32()), WD.sc(125n, one), WD.sc(252n, one), c_le(one))
  +b = L.subst(Nat, z => {Nat.is_le(z, Nat.add(WD.sc(125n, one), WD.sc(252n, one))) == True{} : Bool}, Nat.add(K.valo(one, cl32()), WD.sc(252n, one)), SE.ell(one), ell_split(one), a)
  L.subst(Nat, z => {Nat.is_le(SE.ell(one), z) == True{} : Bool}, Nat.add(WD.sc(125n, one), WD.sc(252n, one)), Nat.add(WD.sc(252n, one), WD.sc(125n, one)), NA.add_comm(WD.sc(125n, one), WD.sc(252n, one)), b)

# L < 2^253
def ell_lt253(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_lt(SE.ell(one), WD.sc(253n, one)) == True{} : Bool}:
  +a = N.lt_add_left(WD.sc(125n, one), WD.sc(252n, one), WD.sc(252n, one), PW.lt_sc(126n, 125n, one, h1))
  N.le_lt_trans(SE.ell(one), Nat.add(WD.sc(252n, one), WD.sc(125n, one)), WD.sc(253n, one), ell_hi(one), L.subst(Nat, z => {Nat.is_lt(Nat.add(WD.sc(252n, one), WD.sc(125n, one)), z) == True{} : Bool}, Nat.add(WD.sc(252n, one), WD.sc(252n, one)), WD.sc(253n, one), PW.dbl(252n, one), a))

# ---- the limbs of L ----

def lbits_eq(+xs: List<&2, U32>) -> {ESC.lbits(xs) == LS.take(255n, LS.bits_all(8n, LS.nat_of(ESC.ell()))) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def tb_len() -> {PS.ln(LS.take(255n, LS.bits_all(8n, LS.nat_of(ESC.ell())))) == 255n : Nat}:
  {==}

def ell_tight() -> {FS.bytes_ok(32n, ESC.ell()) == True{} : Bool}:
  {==}

def mask_ell() -> {SX.mask_last(ESC.ell()) == ESC.ell() : List<&2, U32>}:
  {==}

# value(take(255, B8)) == L
def bits_ell(+one: Nat, +h1: {one == 1n : Nat}) -> {BY.bv(LS.take(255n, LS.bits_all(8n, LS.nat_of(ESC.ell())))) == SE.ell(one) : Nat}:
  +V = FS.value(ESC.ell())
  +e1 = CV.take_mod(one, h1, 255n, LS.bits_all(8n, LS.nat_of(ESC.ell())), BY.bits_all_lt(8n, LS.nat_of(ESC.ell())))
  +hn = L.subst(Nat, o => {FV.below(LS.nat_of(ESC.ell()), WD.sc(8n, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), CV.nat_below(32n, ESC.ell(), ell_tight()))
  +e2 = tr(BY.bv(LS.bits_all(8n, LS.nat_of(ESC.ell()))), BY.lvw(8n, LS.nat_of(ESC.ell())), V, BY.bits_all_val(one, h1, 8n, LS.nat_of(ESC.ell()), hn), BY.lvw8(ESC.ell()))
  +em = tr(FS.value(SX.mask_last(ESC.ell())), Nat.mod(V, WD.sc(LD.m7(31n), one)), Nat.mod(V, WD.sc(255n, one)), LD.mask_mod(one, h1, 31n, ESC.ell(), ell_tight()), Equal.cong(Nat, Nat, z => Nat.mod(V, WD.sc(z, one)), LD.m7(31n), 255n, {==}))
  +e3 = tr(Nat.mod(V, WD.sc(255n, one)), FS.value(SX.mask_last(ESC.ell())), V, sy(FS.value(SX.mask_last(ESC.ell())), Nat.mod(V, WD.sc(255n, one)), em), Equal.cong(List<&2, U32>, Nat, z => FS.value(z), SX.mask_last(ESC.ell()), ESC.ell(), mask_ell()))
  +e4 = tr(V, K.valo(one, ESC.ell()), SE.ell(one), sy(K.valo(one, ESC.ell()), V, K.valo_value(one, h1, ESC.ell())), S3.ell_valo(one))
  tr(BY.bv(LS.take(255n, LS.bits_all(8n, LS.nat_of(ESC.ell())))), Nat.mod(BY.bv(LS.bits_all(8n, LS.nat_of(ESC.ell()))), WD.sc(255n, one)), SE.ell(one), e1, tr(Nat.mod(BY.bv(LS.bits_all(8n, LS.nat_of(ESC.ell()))), WD.sc(255n, one)), Nat.mod(V, WD.sc(255n, one)), SE.ell(one), Equal.cong(Nat, Nat, z => Nat.mod(z, WD.sc(255n, one)), BY.bv(LS.bits_all(8n, LS.nat_of(ESC.ell()))), V, e2), tr(Nat.mod(V, WD.sc(255n, one)), V, SE.ell(one), e3, e4)))

def l15_val(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>) -> {FV.lv(ESC.l15(xs)) == SE.ell(one) : Nat}:
  +T = LS.take(255n, LS.bits_all(8n, LS.nat_of(ESC.ell())))
  +bl = ESC.lbits(xs)
  +hfit = BY.fits_len(17n, 15n, bl, L.subst(List<&2, Nat>, z => {Nat.is_le(PS.ln(z), 255n) == True{} : Bool}, T, bl, Equal.sym(List<&2, Nat>, bl, T, lbits_eq(xs)), L.subst(Nat, z => {Nat.is_le(z, 255n) == True{} : Bool}, 255n, PS.ln(T), sy(PS.ln(T), 255n, tb_len()), {==})))
  +e1 = sy(BY.lvw(17n, ESC.l15(xs)), FV.lv(ESC.l15(xs)), BY.lvw17(ESC.l15(xs)))
  +e2 = BY.group_val(17n, 15n, bl, hfit)
  +e3 = Equal.cong(List<&2, Nat>, Nat, z => BY.bv(z), bl, T, lbits_eq(xs))
  tr(FV.lv(ESC.l15(xs)), BY.lvw(17n, ESC.l15(xs)), SE.ell(one), e1, tr(BY.lvw(17n, ESC.l15(xs)), BY.bv(bl), SE.ell(one), e2, tr(BY.bv(bl), BY.bv(T), SE.ell(one), e3, bits_ell(one, h1))))

def l15_below(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +xs: List<&2, U32>) -> {FV.below(ESC.l15(xs), R) == True{} : Bool}:
  +T = LS.take(255n, LS.bits_all(8n, LS.nat_of(ESC.ell())))
  +bl = ESC.lbits(xs)
  +h2 = L.subst(List<&2, Nat>, z => {FV.below(z, 2n) == True{} : Bool}, T, bl, Equal.sym(List<&2, Nat>, bl, T, lbits_eq(xs)), NL.take_below(255n, LS.bits_all(8n, LS.nat_of(ESC.ell())), 2n, BY.bits_all_lt(8n, LS.nat_of(ESC.ell()))))
  L.subst(Nat, z => {FV.below(ESC.l15(xs), z) == True{} : Bool}, WD.sc(17n, one), R, sy(R, WD.sc(17n, one), hR), CV.group_below(one, h1, 17n, 15n, bl, h2))

def l15_len(+xs: List<&2, U32>) -> {PS.ln(ESC.l15(xs)) == 15n : Nat}:
  CV.group_len(17n, 15n, ESC.lbits(xs))
