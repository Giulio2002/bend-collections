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
import ./scalar2.bend as S2

# The group order L of spec/crypto/ed25519.bend and the scalar clauses:
# L + (2^256 - L) == 2^256 and 2 L <= 2^256 by certified digit additions,
# then reduce, mul_add and lt_l of src/crypto/ed25519/scalar.bend.

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

# ---- the clauses, for M = 1 + mmL ----

def reduce_m(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +hb: {LM.lea(bs, 255n) == True{} : Bool}) -> {FS.value(ESC.reduce(bs)) == Nat.mod(FS.value(bs), 1n+mmL(one)) : Nat}:
  +mm = mmL(one)
  +n = X.bitlen(bs)
  +V = FS.value(bs)
  %Equal.sym(List<&2, U32>, ESC.mac(n, bs, F.one(), F.zero()), S2.macg(n, bs, F.one(), F.zero(), ESC.comp_l()), S2.mac_eq(n, bs, F.one(), F.zero())) : {FS.value(_) == Nat.mod(V, 1n+mm) : Nat}
  +e = S2.mac_val(one, h1, mm, h2L(one, h1), ESC.comp_l(), cp_okb(), hvL(one, h1), n, bs, F.one(), F.zero(), hb, {==}, one_lt(one, h1), {==}, {==})
  +e2 = Equal.trans(Nat, Nat.add(WD.sc(n, 0n), Nat.mul(C.low(n, V), 1n)), Nat.add(0n, Nat.mul(C.low(n, V), 1n)), V, M.cong_l(WD.sc(n, 0n), 0n, Nat.mul(C.low(n, V), 1n), A.sc_zero(n)), Equal.trans(Nat, Nat.mul(C.low(n, V), 1n), C.low(n, V), V, NA.mul_one(C.low(n, V)), S2.low_all(bs, hb)))
  Equal.trans(Nat, FS.value(S2.macg(n, bs, F.one(), F.zero(), ESC.comp_l())), Nat.mod(Nat.add(WD.sc(n, 0n), Nat.mul(C.low(n, V), 1n)), 1n+mm), Nat.mod(V, 1n+mm), e, M.cong_mod(1n+mm, Nat.add(WD.sc(n, 0n), Nat.mul(C.low(n, V), 1n)), V, e2))

def mul_add_m(+one: Nat, +h1: {one == 1n : Nat}, +k: List<&2, U32>, +s: List<&2, U32>, +r: List<&2, U32>, +hk: {LM.lea(k, 255n) == True{} : Bool}, +hs: {LM.okb(32n, s, 255n) == True{} : Bool}, +hr: {LM.okb(32n, r, 255n) == True{} : Bool}, +ls: {Nat.is_lt(FS.value(s), 1n+mmL(one)) == True{} : Bool}, +lr: {Nat.is_lt(FS.value(r), 1n+mmL(one)) == True{} : Bool}) -> {FS.value(ESC.mul_add(k, s, r)) == Nat.mod(Nat.add(FS.value(r), Nat.mul(FS.value(k), FS.value(s))), 1n+mmL(one)) : Nat}:
  +mm = mmL(one)
  +P = {1n+mm : Nat}
  +n = X.bitlen(k)
  +K2 = FS.value(k)
  +S = FS.value(s)
  +R = FS.value(r)
  +cp = ESC.comp_l()
  +hv = hvL(one, h1)
  +h2 = h2L(one, h1)
  +mg = S2.macg(n, k, s, F.zero(), cp)
  +om = S2.mac_okb(one, h1, mm, cp, cp_okb(), hv, n, k, s, F.zero(), hk, hs, {==})
  +lm = S2.mac_below(one, h1, mm, h2, cp, cp_okb(), hv, n, k, s, F.zero(), hk, hs, ls, {==}, {==})
  +em = S2.mac_val(one, h1, mm, h2, cp, cp_okb(), hv, n, k, s, F.zero(), hk, hs, ls, {==}, {==})
  +em2 = Equal.trans(Nat, FS.value(mg), Nat.mod(Nat.add(WD.sc(n, 0n), Nat.mul(C.low(n, K2), S)), P), Nat.mod(Nat.mul(K2, S), P), em, M.cong_mod(P, Nat.add(WD.sc(n, 0n), Nat.mul(C.low(n, K2), S)), Nat.mul(K2, S), Equal.trans(Nat, Nat.add(WD.sc(n, 0n), Nat.mul(C.low(n, K2), S)), Nat.add(0n, Nat.mul(C.low(n, K2), S)), Nat.mul(K2, S), M.cong_l(WD.sc(n, 0n), 0n, Nat.mul(C.low(n, K2), S), A.sc_zero(n)), Equal.cong(Nat, Nat, z => Nat.mul(z, S), C.low(n, K2), K2, S2.low_all(k, hk)))))
  %Equal.sym(List<&2, U32>, ESC.mac(n, k, s, F.zero()), mg, S2.mac_eq(n, k, s, F.zero())) : {FS.value(ESC.addm(_, r)) == Nat.mod(Nat.add(R, Nat.mul(K2, S)), P) : Nat}
  +ea = SC.addg_val(one, h1, mm, h2, cp, cp_okb(), hv, mg, r, om, hr, lm, lr)
  +eb = Equal.trans(Nat, Nat.mod(Nat.add(FS.value(mg), R), P), Nat.mod(Nat.add(Nat.mod(Nat.mul(K2, S), P), R), P), Nat.mod(Nat.add(R, Nat.mul(K2, S)), P), M.cong_mod(P, Nat.add(FS.value(mg), R), Nat.add(Nat.mod(Nat.mul(K2, S), P), R), M.cong_l(FS.value(mg), Nat.mod(Nat.mul(K2, S), P), R, em2)), Equal.trans(Nat, Nat.mod(Nat.add(Nat.mod(Nat.mul(K2, S), P), R), P), Nat.mod(Nat.add(Nat.mul(K2, S), R), P), Nat.mod(Nat.add(R, Nat.mul(K2, S)), P), NR.mod_add_l(mm, Nat.mul(K2, S), R), M.cong_mod(P, Nat.add(Nat.mul(K2, S), R), Nat.add(R, Nat.mul(K2, S)), NA.add_comm(Nat.mul(K2, S), R))))
  Equal.trans(Nat, FS.value(SC.addg(mg, r, cp)), Nat.mod(Nat.add(FS.value(mg), R), P), Nat.mod(Nat.add(R, Nat.mul(K2, S)), P), ea, eb)

def mul_add_lt(+one: Nat, +h1: {one == 1n : Nat}, +k: List<&2, U32>, +s: List<&2, U32>, +r: List<&2, U32>, +hk: {LM.lea(k, 255n) == True{} : Bool}, +hs: {LM.okb(32n, s, 255n) == True{} : Bool}, +hr: {LM.okb(32n, r, 255n) == True{} : Bool}, +ls: {Nat.is_lt(FS.value(s), 1n+mmL(one)) == True{} : Bool}, +lr: {Nat.is_lt(FS.value(r), 1n+mmL(one)) == True{} : Bool}) -> {LM.okb(32n, ESC.mul_add(k, s, r), 255n) == True{} : Bool}:
  +mm = mmL(one)
  +cp = ESC.comp_l()
  +n = X.bitlen(k)
  +mg = S2.macg(n, k, s, F.zero(), cp)
  %Equal.sym(List<&2, U32>, ESC.mac(n, k, s, F.zero()), mg, S2.mac_eq(n, k, s, F.zero())) : {LM.okb(32n, ESC.addm(_, r), 255n) == True{} : Bool}
  SC.addg_okb(one, h1, mm, cp, cp_okb(), hvL(one, h1), mg, r, S2.mac_okb(one, h1, mm, cp, cp_okb(), hvL(one, h1), n, k, s, F.zero(), hk, hs, {==}), hr)

def reduce_okb(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +hb: {LM.lea(bs, 255n) == True{} : Bool}) -> {LM.okb(32n, ESC.reduce(bs), 255n) == True{} : Bool}:
  %Equal.sym(List<&2, U32>, ESC.mac(X.bitlen(bs), bs, F.one(), F.zero()), S2.macg(X.bitlen(bs), bs, F.one(), F.zero(), ESC.comp_l()), S2.mac_eq(X.bitlen(bs), bs, F.one(), F.zero())) : {LM.okb(32n, _, 255n) == True{} : Bool}
  S2.mac_okb(one, h1, mmL(one), ESC.comp_l(), cp_okb(), hvL(one, h1), X.bitlen(bs), bs, F.one(), F.zero(), hb, {==}, {==})

def lt_l_m(+one: Nat, +h1: {one == 1n : Nat}, +x: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}) -> {ESC.lt_l(x) == Nat.is_lt(FS.value(x), 1n+mmL(one)) : Bool}:
  SC.lt_by(one, h1, mmL(one), x, ESC.comp_l(), hx, cp_okb(), hvL(one, h1), Nat.is_lt(v(LM.cc(F.carry(F.addl(x, ESC.comp_l()), 0))), one), {==})
