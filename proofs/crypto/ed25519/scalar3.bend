import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/ed25519.bend as SE
import ../../../src/crypto/curve25519/field.bend as F
import ../../../src/crypto/ed25519/scalar.bend as ESC
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../curve25519/num.bend as M
import ../curve25519/limbs.bend as LM
import ./bytefield.bend as LO

# The group order L of spec/crypto/ed25519.bend: L + (2^256 - L) == 2^256
# by a certified digit addition, and lt_l of
# src/crypto/ed25519/scalar.bend (reduce and mul_add: horner.bend).

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def zeros() -> List<&2, U32>:
  LO.rep(32n, 0, Nil{})

def adc2() -> {LO.adc_ok(ESC.comp_l(), ESC.ell(), zeros(), 0n, 1n) == True{} : Bool}:
  {==}

def ell_valo(+one: Nat) -> {LO.valo(one, ESC.ell()) == SE.ell(one) : Nat}:
  LO.valo_u(one, ESC.ell())

def mmL(+one: Nat) -> Nat:
  Nat.sub(SE.ell(one), 1n)

def ell_ge(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_le(2n, SE.ell(one)) == True{} : Bool}:
  +e = Equal.sym(Nat, LO.valo(one, ESC.ell()), SE.ell(one), ell_valo(one))
  +a = L.subst(Nat, o => {Nat.is_le(2n, Nat.mul(o, v(237))) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})
  +b = N.le_trans(2n, Nat.mul(one, v(237)), LO.valo(one, ESC.ell()), a, N.le_add_right(Nat.mul(one, v(237)), C.shift(8n, LO.valo(one, LO.rep(0n, 0, [211, 245, 92, 26, 99, 18, 88, 214, 156, 247, 162, 222, 249, 222, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16])))))
  L.subst(Nat, z => {Nat.is_le(2n, z) == True{} : Bool}, LO.valo(one, ESC.ell()), SE.ell(one), Equal.sym(Nat, SE.ell(one), LO.valo(one, ESC.ell()), e), b)

def ell_eq(+one: Nat, +h1: {one == 1n : Nat}) -> {1n+mmL(one) == SE.ell(one) : Nat}:
  N.sub_add(SE.ell(one), 1n, N.le_trans(1n, 2n, SE.ell(one), {==}, ell_ge(one, h1)))

def cp_okb() -> {LM.okb(32n, ESC.comp_l(), 255n) == True{} : Bool}:
  {==}

def zero_vg(+one: Nat, +h1: {one == 1n : Nat}) -> {LO.valo(one, zeros()) == 0n : Nat}:
  Equal.trans(Nat, LO.valo(one, zeros()), LM.shn(32n, LO.valo(one, Nil{})), 0n, LO.run0(one, 32n, Nil{}), {==})

# (2^256 - L) + L == 2^256
def hvL(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.add(LO.valo(one, ESC.comp_l()), 1n+mmL(one)) == LO.T(one) : Nat}:
  +cp = ESC.comp_l()
  +C1 = LO.valo(one, cp)
  +L1 = LO.valo(one, ESC.ell())
  +e = LO.adc_val(one, cp, ESC.ell(), zeros(), 0n, 1n, adc2())
  +e1 = Equal.trans(Nat, Nat.add(LO.valo(one, zeros()), LM.sh(cp, Nat.mul(one, 1n))), Nat.add(0n, LM.shn(32n, Nat.mul(one, 1n))), LO.T(one), M.cong_add(LO.valo(one, zeros()), 0n, LM.sh(cp, Nat.mul(one, 1n)), LM.shn(32n, Nat.mul(one, 1n)), zero_vg(one, h1), LM.sh_okb(32n, cp, 255n, Nat.mul(one, 1n), cp_okb())), Equal.cong(Nat, Nat, z => LM.shn(32n, z), Nat.mul(one, 1n), one, NA.mul_one(one)))
  +e2 = Equal.trans(Nat, Nat.add(Nat.add(C1, L1), Nat.mul(one, 0n)), Nat.add(Nat.add(C1, L1), 0n), Nat.add(C1, L1), M.cong_r(Nat.add(C1, L1), Nat.mul(one, 0n), 0n, NA.mul_zero(one)), N.add_zero(Nat.add(C1, L1)))
  +e3 = M.cong_r(C1, 1n+mmL(one), L1, Equal.trans(Nat, 1n+mmL(one), SE.ell(one), L1, ell_eq(one, h1), Equal.sym(Nat, L1, SE.ell(one), ell_valo(one))))
  Equal.trans(Nat, Nat.add(C1, 1n+mmL(one)), Nat.add(C1, L1), LO.T(one), e3, Equal.trans(Nat, Nat.add(C1, L1), Nat.add(Nat.add(C1, L1), Nat.mul(one, 0n)), LO.T(one), Equal.sym(Nat, Nat.add(Nat.add(C1, L1), Nat.mul(one, 0n)), Nat.add(C1, L1), e2), Equal.trans(Nat, Nat.add(Nat.add(C1, L1), Nat.mul(one, 0n)), Nat.add(LO.valo(one, zeros()), LM.sh(cp, Nat.mul(one, 1n))), LO.T(one), e, e1)))

# ---- x < L, for M = 1 + mmL ----

def lt_l_m(+one: Nat, +h1: {one == 1n : Nat}, +x: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}) -> {ESC.lt_l(x) == Nat.is_lt(FS.value(x), 1n+mmL(one)) : Bool}:
  LO.lt_by(one, h1, mmL(one), x, ESC.comp_l(), hx, cp_okb(), hvL(one, h1), Nat.is_lt(v(LM.cc(F.carry(F.addl(x, ESC.comp_l()), 0))), one), {==})
