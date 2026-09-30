import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/ed25519.bend as SE
import ../../../src/crypto/curve25519/field.bend as F
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../../src/crypto/ed25519/scalar.bend as ESC
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/u32alg.bend as A
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../curve25519/num.bend as M
import ../curve25519/limbs.bend as LM
import ../curve25519/consts.bend as K
import ../curve25519/cong.bend as G
import ./adc.bend as AD
import ./scalar.bend as SC

# The group order L of spec/crypto/ed25519.bend: L + (2^256 - L) == 2^256
# and 2 L <= 2^256 by certified digit additions, and lt_l of
# src/crypto/ed25519/scalar.bend (reduce and mul_add: horner.bend).

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# 2^256 - 2 L
def dlist() -> List<&2, U32>:
  [38, 88, 20, 70, 203, 57, 219, 79, 83, 198, 16, 186, 66, 12, 66, 214,
   255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 223]

def zeros() -> List<&2, U32>:
  K.rep(32n, 0, Nil{})

def adc1() -> {AD.adc_ok(ESC.ell(), dlist(), ESC.comp_l(), 0n, 0n) == True{} : Bool}:
  {==}

def adc2() -> {AD.adc_ok(ESC.comp_l(), ESC.ell(), zeros(), 0n, 1n) == True{} : Bool}:
  {==}

def ell_valo(+one: Nat) -> {K.valo(one, ESC.ell()) == SE.ell(one) : Nat}:
  AD.valo_u(one, ESC.ell())

def mmL(+one: Nat) -> Nat:
  Nat.sub(SE.ell(one), 1n)

def ell_ge(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_le(2n, SE.ell(one)) == True{} : Bool}:
  +e = Equal.sym(Nat, K.valo(one, ESC.ell()), SE.ell(one), ell_valo(one))
  +a = L.subst(Nat, o => {Nat.is_le(2n, Nat.mul(o, v(237))) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})
  +b = N.le_trans(2n, Nat.mul(one, v(237)), K.valo(one, ESC.ell()), a, N.le_add_right(Nat.mul(one, v(237)), C.shift(8n, K.valo(one, K.rep(0n, 0, [211, 245, 92, 26, 99, 18, 88, 214, 156, 247, 162, 222, 249, 222, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16])))))
  L.subst(Nat, z => {Nat.is_le(2n, z) == True{} : Bool}, K.valo(one, ESC.ell()), SE.ell(one), Equal.sym(Nat, SE.ell(one), K.valo(one, ESC.ell()), e), b)

def ell_eq(+one: Nat, +h1: {one == 1n : Nat}) -> {1n+mmL(one) == SE.ell(one) : Nat}:
  N.sub_add(SE.ell(one), 1n, N.le_trans(1n, 2n, SE.ell(one), {==}, ell_ge(one, h1)))

def one_lt(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_lt(1n, 1n+mmL(one)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(1n, z) == True{} : Bool}, SE.ell(one), 1n+mmL(one), Equal.sym(Nat, 1n+mmL(one), SE.ell(one), ell_eq(one, h1)), N.succ_le_lt(1n, SE.ell(one), ell_ge(one, h1)))

def cp_okb() -> {LM.okb(32n, ESC.comp_l(), 255n) == True{} : Bool}:
  {==}

def zero_vg(+one: Nat, +h1: {one == 1n : Nat}) -> {K.valo(one, zeros()) == 0n : Nat}:
  Equal.trans(Nat, K.valo(one, zeros()), LM.shn(32n, K.valo(one, Nil{})), 0n, K.run0(one, 32n, Nil{}), {==})

# (2^256 - L) + L == 2^256
def hvL(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.add(K.valo(one, ESC.comp_l()), 1n+mmL(one)) == SC.T(one) : Nat}:
  +cp = ESC.comp_l()
  +C1 = K.valo(one, cp)
  +L1 = K.valo(one, ESC.ell())
  +e = AD.adc_val(one, cp, ESC.ell(), zeros(), 0n, 1n, adc2())
  +e1 = Equal.trans(Nat, Nat.add(K.valo(one, zeros()), LM.sh(cp, Nat.mul(one, 1n))), Nat.add(0n, LM.shn(32n, Nat.mul(one, 1n))), SC.T(one), M.cong_add(K.valo(one, zeros()), 0n, LM.sh(cp, Nat.mul(one, 1n)), LM.shn(32n, Nat.mul(one, 1n)), zero_vg(one, h1), LM.sh_okb(32n, cp, 255n, Nat.mul(one, 1n), cp_okb())), Equal.cong(Nat, Nat, z => LM.shn(32n, z), Nat.mul(one, 1n), one, NA.mul_one(one)))
  +e2 = Equal.trans(Nat, Nat.add(Nat.add(C1, L1), Nat.mul(one, 0n)), Nat.add(Nat.add(C1, L1), 0n), Nat.add(C1, L1), M.cong_r(Nat.add(C1, L1), Nat.mul(one, 0n), 0n, NA.mul_zero(one)), N.add_zero(Nat.add(C1, L1)))
  +e3 = M.cong_r(C1, 1n+mmL(one), L1, Equal.trans(Nat, 1n+mmL(one), SE.ell(one), L1, ell_eq(one, h1), Equal.sym(Nat, L1, SE.ell(one), ell_valo(one))))
  Equal.trans(Nat, Nat.add(C1, 1n+mmL(one)), Nat.add(C1, L1), SC.T(one), e3, Equal.trans(Nat, Nat.add(C1, L1), Nat.add(Nat.add(C1, L1), Nat.mul(one, 0n)), SC.T(one), Equal.sym(Nat, Nat.add(Nat.add(C1, L1), Nat.mul(one, 0n)), Nat.add(C1, L1), e2), Equal.trans(Nat, Nat.add(Nat.add(C1, L1), Nat.mul(one, 0n)), Nat.add(K.valo(one, zeros()), LM.sh(cp, Nat.mul(one, 1n))), SC.T(one), e, e1)))

# 2 L <= 2^256
def h2L(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_le(Nat.add(1n+mmL(one), 1n+mmL(one)), SC.T(one)) == True{} : Bool}:
  +l = K.valo(one, ESC.ell())
  +d = K.valo(one, dlist())
  +c = K.valo(one, ESC.comp_l())
  +m = {1n+mmL(one) : Nat}
  +e = AD.adc_val(one, ESC.ell(), dlist(), ESC.comp_l(), 0n, 0n, adc1())
  +s0 = Equal.trans(Nat, LM.sh(ESC.ell(), Nat.mul(one, 0n)), LM.shn(32n, Nat.mul(one, 0n)), 0n, LM.sh_okb(32n, ESC.ell(), 255n, Nat.mul(one, 0n), {==}), Equal.cong(Nat, Nat, z => LM.shn(32n, z), Nat.mul(one, 0n), 0n, NA.mul_zero(one)))
  +e1 = Equal.trans(Nat, Nat.add(l, d), Nat.add(Nat.add(l, d), Nat.mul(one, 0n)), c, Equal.trans(Nat, Nat.add(l, d), Nat.add(Nat.add(l, d), 0n), Nat.add(Nat.add(l, d), Nat.mul(one, 0n)), Equal.sym(Nat, Nat.add(Nat.add(l, d), 0n), Nat.add(l, d), N.add_zero(Nat.add(l, d))), M.cong_r(Nat.add(l, d), 0n, Nat.mul(one, 0n), Equal.sym(Nat, Nat.mul(one, 0n), 0n, NA.mul_zero(one)))), Equal.trans(Nat, Nat.add(Nat.add(l, d), Nat.mul(one, 0n)), Nat.add(c, LM.sh(ESC.ell(), Nat.mul(one, 0n))), c, e, Equal.trans(Nat, Nat.add(c, LM.sh(ESC.ell(), Nat.mul(one, 0n))), Nat.add(c, 0n), c, M.cong_r(c, LM.sh(ESC.ell(), Nat.mul(one, 0n)), 0n, s0), N.add_zero(c))))
  +lm = Equal.trans(Nat, l, SE.ell(one), m, ell_valo(one), Equal.sym(Nat, m, SE.ell(one), ell_eq(one, h1)))
  +e2 = Equal.trans(Nat, Nat.add(Nat.add(m, m), d), Nat.add(m, Nat.add(l, d)), SC.T(one), Equal.trans(Nat, Nat.add(Nat.add(m, m), d), Nat.add(m, Nat.add(m, d)), Nat.add(m, Nat.add(l, d)), NA.add_assoc(m, m, d), M.cong_r(m, Nat.add(m, d), Nat.add(l, d), M.cong_l(m, l, d, Equal.sym(Nat, l, m, lm)))), Equal.trans(Nat, Nat.add(m, Nat.add(l, d)), Nat.add(m, c), SC.T(one), M.cong_r(m, Nat.add(l, d), c, e1), Equal.trans(Nat, Nat.add(m, c), Nat.add(c, m), SC.T(one), NA.add_comm(m, c), hvL(one, h1))))
  L.subst(Nat, z => {Nat.is_le(Nat.add(m, m), z) == True{} : Bool}, Nat.add(Nat.add(m, m), d), SC.T(one), e2, N.le_add_right(Nat.add(m, m), d))

# ---- x < L, for M = 1 + mmL ----

def lt_l_m(+one: Nat, +h1: {one == 1n : Nat}, +x: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}) -> {ESC.lt_l(x) == Nat.is_lt(FS.value(x), 1n+mmL(one)) : Bool}:
  SC.lt_by(one, h1, mmL(one), x, ESC.comp_l(), hx, cp_okb(), hvL(one, h1), Nat.is_lt(v(LM.cc(F.carry(F.addl(x, ESC.comp_l()), 0))), one), {==})
