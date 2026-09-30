import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../spec/crypto/ed25519.bend as SE
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/curve25519/limbs.bend as LS
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../../src/crypto/ed25519/scalar.bend as ESC
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../curve25519/num.bend as M
import ../curve25519/limbs.bend as LM
import ../curve25519/cong.bend as G
import ../fe/nl.bend as NL
import ../fe/pw.bend as PW
import ../fe/carry.bend as CA
import ../fe/pass.bend as PS
import ../fe/canon.bend as CN
import ../fe/bytes.bend as BY
import ../fe/conv.bend as CV
import ../fe/cst.bend as CS
import ./scalar3.bend as S3
import ./lfacts.bend as LF
import ./horner.bend as HO
import ./bytes.bend as EB

# reduce and mul_add of src/crypto/ed25519/scalar.bend: the values mod L
# (M = 1 + mmL, S3.ell_eq), 32 tight bytes out.

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

def Mo(+one: Nat) -> Nat:
  1n+S3.mmL(one)

# ---- the facts about L the Horner lemmas take, for M = 1 + mmL ----

def to_m(+one: Nat, +h1: {one == 1n : Nat}, -Q: Nat -> Type, pf: Q(SE.ell(one))) -> Q(1n+S3.mmL(one)):
  L.subst(Nat, Q, SE.ell(one), 1n+S3.mmL(one), Equal.sym(Nat, 1n+S3.mmL(one), SE.ell(one), S3.ell_eq(one, h1)), pf)

def hLv(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>) -> {FV.lv(ESC.l15(xs)) == 1n+S3.mmL(one) : Nat}:
  to_m(one, h1, z => {FV.lv(ESC.l15(xs)) == z : Nat}, LF.l15_val(one, h1, xs))

def hL253(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_lt(1n+S3.mmL(one), WD.sc(253n, one)) == True{} : Bool}:
  to_m(one, h1, z => {Nat.is_lt(z, WD.sc(253n, one)) == True{} : Bool}, LF.ell_lt253(one, h1))

def hlo(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_le(WD.sc(252n, one), 1n+S3.mmL(one)) == True{} : Bool}:
  to_m(one, h1, z => {Nat.is_le(WD.sc(252n, one), z) == True{} : Bool}, LF.ell_lo(one))

def hhi(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_le(1n+S3.mmL(one), Nat.add(WD.sc(252n, one), WD.sc(125n, one))) == True{} : Bool}:
  to_m(one, h1, z => {Nat.is_le(z, Nat.add(WD.sc(252n, one), WD.sc(125n, one))) == True{} : Bool}, LF.ell_hi(one))

# Horner's rule over limbs below R: canonical, the value mod M
def hr_all(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +xs0: List<&2, U32>, +xs: List<&2, Nat>, +hxs: {FV.below(xs, R) == True{} : Bool}) -> {Bool.and(Bool.and(FV.below(ESC.hr(R, ESC.l15(xs0), xs), R), Nat.is_lt(FV.lv(ESC.hr(R, ESC.l15(xs0), xs)), 1n+S3.mmL(one))), Nat.is_eq(FV.lv(ESC.hr(R, ESC.l15(xs0), xs)), Nat.mod(FV.lv(xs), 1n+S3.mmL(one)))) == True{} : Bool}:
  HO.hr_ok(one, h1, R, hR, S3.mmL(one), ESC.l15(xs0), hLv(one, h1, xs0), LF.l15_below(one, h1, R, hR, xs0), LF.l15_len(xs0), hL253(one, h1), hlo(one, h1), hhi(one, h1), xs, hxs)

# the bytes out: value and tightness of the Horner result
def out_facts(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +xs0: List<&2, U32>, +xs: List<&2, Nat>, +hxs: {FV.below(xs, R) == True{} : Bool}) -> {Bool.and(Nat.is_eq(FS.value(LS.to_bytes_l(ESC.hr(R, ESC.l15(xs0), xs))), Nat.mod(FV.lv(xs), 1n+S3.mmL(one))), Nat.is_lt(FS.value(LS.to_bytes_l(ESC.hr(R, ESC.l15(xs0), xs))), 1n+S3.mmL(one))) == True{} : Bool}:
  +P = Mo(one)
  +Z = ESC.hr(R, ESC.l15(xs0), xs)
  +F = hr_all(one, h1, R, hR, xs0, xs, hxs)
  +hb = L.and_left(FV.below(Z, R), Nat.is_lt(FV.lv(Z), P), L.and_left(Bool.and(FV.below(Z, R), Nat.is_lt(FV.lv(Z), P)), Nat.is_eq(FV.lv(Z), Nat.mod(FV.lv(xs), P)), F))
  +hl = L.and_right(FV.below(Z, R), Nat.is_lt(FV.lv(Z), P), L.and_left(Bool.and(FV.below(Z, R), Nat.is_lt(FV.lv(Z), P)), Nat.is_eq(FV.lv(Z), Nat.mod(FV.lv(xs), P)), F))
  +he = N.eq_from_is_eq(FV.lv(Z), Nat.mod(FV.lv(xs), P), L.and_right(Bool.and(FV.below(Z, R), Nat.is_lt(FV.lv(Z), P)), Nat.is_eq(FV.lv(Z), Nat.mod(FV.lv(xs), P)), F))
  +hz17 = L.subst(Nat, z => {FV.below(Z, z) == True{} : Bool}, R, WD.sc(17n, one), hR, hb)
  +ev = CV.tb_value(one, h1, Z, hz17, HO.hr_len(R, ESC.l15(xs0), xs, LF.l15_len(xs0)))
  +V = FS.value(LS.to_bytes_l(Z))
  L.and_intro(Nat.is_eq(V, Nat.mod(FV.lv(xs), P)), Nat.is_lt(V, P), L.subst(Nat, z => {Nat.is_eq(V, z) == True{} : Bool}, V, Nat.mod(FV.lv(xs), P), tr(V, FV.lv(Z), Nat.mod(FV.lv(xs), P), ev, he), N.is_eq_refl(V)), L.subst(Nat, z => {Nat.is_lt(z, P) == True{} : Bool}, FV.lv(Z), V, sy(V, FV.lv(Z), ev), hl))

# ---- the limbs of a byte string ----

def lea_below(+bs: List<&2, U32>, +h: {LM.lea(bs, 255n) == True{} : Bool}) -> {FV.below(LS.nat_of(bs), 256n) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      NL.below_con(U32.to_nat(x), LS.nat_of(xt), 256n, N.le_lt_succ(U32.to_nat(x), 255n, LM.lea_head(x, xt, 255n, h)), lea_below(xt, LM.lea_tail(x, xt, 255n, h)))

def bitlen_ln(+bs: List<&2, U32>) -> {X.bitlen(bs) == Nat.mul(PS.ln(LS.nat_of(bs)), 8n) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      M.cong_r(8n, X.bitlen(xt), Nat.mul(PS.ln(LS.nat_of(xt)), 8n), bitlen_ln(xt))

# y <= 17 ((y + 16) div 17)
def ceil17(+y: Nat) -> {Nat.is_le(y, Nat.mul(Nat.div(Nat.add(y, 16n), 17n), 17n)) == True{} : Bool}:
  +s = Nat.add(y, 16n)
  +q = Nat.div(s, 17n)
  +r = Nat.mod(s, 17n)
  +e = NR.dm_eq(16n, s)
  +hr = N.lt_succ_le(r, 16n, NR.dm_lt(16n, s))
  +l1 = L.subst(Nat, z => {Nat.is_le(z, Nat.add(Nat.mul(q, 17n), 16n)) == True{} : Bool}, Nat.add(Nat.mul(q, 17n), r), s, sy(s, Nat.add(Nat.mul(q, 17n), r), e), N.le_add_left(r, 16n, Nat.mul(q, 17n), hr))
  +l2 = L.subst(Nat, z => {Nat.is_le(z, Nat.add(16n, Nat.mul(q, 17n))) == True{} : Bool}, s, Nat.add(16n, y), NA.add_comm(y, 16n), L.subst(Nat, z => {Nat.is_le(s, z) == True{} : Bool}, Nat.add(Nat.mul(q, 17n), 16n), Nat.add(16n, Nat.mul(q, 17n)), NA.add_comm(Nat.mul(q, 17n), 16n), l1))
  Equal.trans(Bool, Nat.is_le(y, Nat.mul(q, 17n)), Nat.is_le(Nat.add(16n, y), Nat.add(16n, Nat.mul(q, 17n))), True{}, Equal.sym(Bool, Nat.is_le(Nat.add(16n, y), Nat.add(16n, Nat.mul(q, 17n))), Nat.is_le(y, Nat.mul(q, 17n)), NR.le_add_cancel(16n, y, Nat.mul(q, 17n))), l2)

def limbs_val(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +h: {LM.lea(bs, 255n) == True{} : Bool}) -> {FV.lv(ESC.limbs17(bs)) == FS.value(bs) : Nat}:
  +B = LS.bits_all(8n, LS.nat_of(bs))
  +cnt = Nat.div(Nat.add(X.bitlen(bs), 16n), 17n)
  +hlB = tr(PS.ln(B), Nat.mul(PS.ln(LS.nat_of(bs)), 8n), X.bitlen(bs), CV.bits_all_len(8n, LS.nat_of(bs)), sy(X.bitlen(bs), Nat.mul(PS.ln(LS.nat_of(bs)), 8n), bitlen_ln(bs)))
  +hfit = BY.fits_len(17n, cnt, B, L.subst(Nat, z => {Nat.is_le(z, Nat.mul(cnt, 17n)) == True{} : Bool}, X.bitlen(bs), PS.ln(B), sy(PS.ln(B), X.bitlen(bs), hlB), ceil17(X.bitlen(bs))))
  +hn = L.subst(Nat, o => {FV.below(LS.nat_of(bs), WD.sc(8n, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), lea_below(bs, h))
  tr(FV.lv(ESC.limbs17(bs)), BY.lvw(17n, ESC.limbs17(bs)), FS.value(bs), sy(BY.lvw(17n, ESC.limbs17(bs)), FV.lv(ESC.limbs17(bs)), BY.lvw17(ESC.limbs17(bs))), tr(BY.lvw(17n, ESC.limbs17(bs)), BY.bv(B), FS.value(bs), BY.group_val(17n, cnt, B, hfit), tr(BY.bv(B), BY.lvw(8n, LS.nat_of(bs)), FS.value(bs), BY.bits_all_val(one, h1, 8n, LS.nat_of(bs), hn), BY.lvw8(bs))))

def limbs_below(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +bs: List<&2, U32>) -> {FV.below(ESC.limbs17(bs), R) == True{} : Bool}:
  L.subst(Nat, z => {FV.below(ESC.limbs17(bs), z) == True{} : Bool}, WD.sc(17n, one), R, sy(R, WD.sc(17n, one), hR), CV.group_below(one, h1, 17n, Nat.div(Nat.add(X.bitlen(bs), 16n), 17n), LS.bits_all(8n, LS.nat_of(bs)), BY.bits_all_lt(8n, LS.nat_of(bs))))

# ---- reduce ----

def red_facts(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +h: {LM.lea(bs, 255n) == True{} : Bool}) -> {Bool.and(Nat.is_eq(FS.value(ESC.reduce(bs)), Nat.mod(FS.value(bs), 1n+S3.mmL(one))), Nat.is_lt(FS.value(ESC.reduce(bs)), 1n+S3.mmL(one))) == True{} : Bool}:
  +R = FE.radix(X.one_of(bs))
  +hR = CS.radix_of_eq(one, h1, bs)
  +P = Mo(one)
  +O = out_facts(one, h1, R, hR, bs, ESC.limbs17(bs), limbs_below(one, h1, R, hR, bs))
  +V = FS.value(ESC.reduce(bs))
  L.subst(Nat, z => {Bool.and(Nat.is_eq(V, Nat.mod(z, P)), Nat.is_lt(V, P)) == True{} : Bool}, FV.lv(ESC.limbs17(bs)), FS.value(bs), limbs_val(one, h1, bs, h), O)

def reduce_m(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +h: {LM.lea(bs, 255n) == True{} : Bool}) -> {FS.value(ESC.reduce(bs)) == Nat.mod(FS.value(bs), 1n+S3.mmL(one)) : Nat}:
  +P = Mo(one)
  +V = FS.value(ESC.reduce(bs))
  N.eq_from_is_eq(V, Nat.mod(FS.value(bs), P), L.and_left(Nat.is_eq(V, Nat.mod(FS.value(bs), P)), Nat.is_lt(V, P), red_facts(one, h1, bs, h)))

def reduce_lt(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +h: {LM.lea(bs, 255n) == True{} : Bool}) -> {Nat.is_lt(FS.value(ESC.reduce(bs)), 1n+S3.mmL(one)) == True{} : Bool}:
  +P = Mo(one)
  +V = FS.value(ESC.reduce(bs))
  L.and_right(Nat.is_eq(V, Nat.mod(FS.value(bs), P)), Nat.is_lt(V, P), red_facts(one, h1, bs, h))

def reduce_okb(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>) -> {LM.okb(32n, ESC.reduce(bs), 255n) == True{} : Bool}:
  LM.bytes_okb(32n, ESC.reduce(bs), CV.tb_tight(one, h1, ESC.hr(FE.radix(X.one_of(bs)), ESC.l15(bs), ESC.limbs17(bs))))

# ---- mul_add ----

def cb_len(+xs: List<&2, Nat>, +p: Nat) -> {NL.cb(xs, p) == Nat.mul(PS.ln(xs), p) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      M.cong_r(p, NL.cb(xt, p), Nat.mul(PS.ln(xt), p), cb_len(xt, p))

# a value below M is its own value mod 2^255
def small255(+one: Nat, +h1: {one == 1n : Nat}, +v: Nat, +h: {Nat.is_lt(v, 1n+S3.mmL(one)) == True{} : Bool}) -> {Nat.mod(v, WD.sc(255n, one)) == v : Nat}:
  +b = Nat.sub(WD.sc(255n, one), 1n)
  +hb = PW.pos_succ(one, h1, 255n)
  +hv = N.lt_le_trans(v, 1n+S3.mmL(one), WD.sc(255n, one), h, N.lt_le(1n+S3.mmL(one), WD.sc(255n, one), N.lt_le_trans(1n+S3.mmL(one), WD.sc(253n, one), WD.sc(255n, one), hL253(one, h1), PW.le_sc(2n, 253n, one))))
  L.subst(Nat, z => {Nat.mod(v, z) == v : Nat}, 1n+b, WD.sc(255n, one), hb, NR.mod_of(0n, b, v, L.subst(Nat, z => {Nat.is_lt(v, z) == True{} : Bool}, WD.sc(255n, one), 1n+b, sy(1n+b, WD.sc(255n, one), hb), hv)))

def kl16(+k: List<&2, U32>, +hk: {LM.okb(32n, k, 255n) == True{} : Bool}) -> {ESC.limbs17(k) == LS.group(17n, 16n, LS.bits_all(8n, LS.nat_of(k))) : List<&2, Nat>}:
  Equal.cong(Nat, List<&2, Nat>, z => LS.group(17n, Nat.div(Nat.add(z, 16n), 17n), LS.bits_all(8n, LS.nat_of(k))), X.bitlen(k), EB.e8(32n), EB.bitlen_okb(32n, k, 255n, hk))

def alen(+k: List<&2, U32>, +s: List<&2, U32>, +r: List<&2, U32>) -> {PS.ln(LS.addl(LS.conv(LS.group(17n, 16n, LS.bits_all(8n, LS.nat_of(k))), LS.of_bytes_l(s)), LS.of_bytes_l(r))) == 30n : Nat}:
  {==}

def ma_facts(+one: Nat, +h1: {one == 1n : Nat}, +k: List<&2, U32>, +s: List<&2, U32>, +r: List<&2, U32>, +hk: {LM.okb(32n, k, 255n) == True{} : Bool}, +hs: {LM.okb(32n, s, 255n) == True{} : Bool}, +hr: {LM.okb(32n, r, 255n) == True{} : Bool}, +ls: {Nat.is_lt(FS.value(s), 1n+S3.mmL(one)) == True{} : Bool}, +lr: {Nat.is_lt(FS.value(r), 1n+S3.mmL(one)) == True{} : Bool}) -> {Bool.and(Nat.is_eq(FS.value(ESC.mul_add(k, s, r)), Nat.mod(Nat.add(FS.value(r), Nat.mul(FS.value(k), FS.value(s))), 1n+S3.mmL(one))), Nat.is_lt(FS.value(ESC.mul_add(k, s, r)), 1n+S3.mmL(one))) == True{} : Bool}:
  +P = Mo(one)
  +R = FE.radix(X.one_of(k))
  +hR = CS.radix_of_eq(one, h1, k)
  +s17 = WD.sc(17n, one)
  +KL = ESC.limbs17(k)
  +SL = LS.of_bytes_l(s)
  +RL = LS.of_bytes_l(r)
  +Kv = FS.value(k)
  +Sv = FS.value(s)
  +Rv = FS.value(r)
  +A = LS.addl(LS.conv(KL, SL), RL)
  +pr = LS.carry(R, A, 0n)
  +cl = LS.cr_limbs(pr)
  +cc = LS.cr_out(pr)
  +XS = LS.app(cl, [cc])
  +vK = limbs_val(one, h1, k, LM.okb_lea(32n, k, 255n, hk))
  +vS = tr(FV.lv(SL), Nat.mod(Sv, WD.sc(255n, one)), Sv, CV.ob_value(one, h1, s, LM.okb_bytes(32n, s, hs)), small255(one, h1, Sv, ls))
  +vR = tr(FV.lv(RL), Nat.mod(Rv, WD.sc(255n, one)), Rv, CV.ob_value(one, h1, r, LM.okb_bytes(32n, r, hr)), small255(one, h1, Rv, lr))
  +vA = tr(FV.lv(A), Nat.add(FV.lv(LS.conv(KL, SL)), FV.lv(RL)), Nat.add(Nat.mul(Kv, Sv), Rv), NL.lv_addl(LS.conv(KL, SL), RL), M.cong_add(FV.lv(LS.conv(KL, SL)), Nat.mul(Kv, Sv), FV.lv(RL), Rv, tr(FV.lv(LS.conv(KL, SL)), Nat.mul(FV.lv(KL), FV.lv(SL)), Nat.mul(Kv, Sv), NL.lv_conv(KL, SL), M.cong_mul(FV.lv(KL), Kv, FV.lv(SL), Sv, vK, vS)), vR))
  +lA = tr(PS.ln(A), PS.ln(LS.addl(LS.conv(LS.group(17n, 16n, LS.bits_all(8n, LS.nat_of(k))), SL), RL)), 30n, Equal.cong(List<&2, Nat>, Nat, z => PS.ln(LS.addl(LS.conv(z, SL), RL)), KL, LS.group(17n, 16n, LS.bits_all(8n, LS.nat_of(k))), kl16(k, hk)), alen(k, s, r))
  +lK = tr(PS.ln(KL), PS.ln(LS.group(17n, 16n, LS.bits_all(8n, LS.nat_of(k)))), 16n, Equal.cong(List<&2, Nat>, Nat, z => PS.ln(z), KL, LS.group(17n, 16n, LS.bits_all(8n, LS.nat_of(k))), kl16(k, hk)), CV.group_len(17n, 16n, LS.bits_all(8n, LS.nat_of(k))))
  +cv = CA.carry_val(one, h1, R, hR, A, 0n)
  +S30 = NL.sh(30n, one)
  +esh = HO.shl_mul(one, h1, A, 30n, lA, cc)
  +ecl = tr(Nat.add(FV.lv(cl), Nat.mul(cc, S30)), Nat.add(FV.lv(cl), CA.shl(A, cc)), Nat.add(Nat.mul(Kv, Sv), Rv), M.cong_r(FV.lv(cl), Nat.mul(cc, S30), CA.shl(A, cc), sy(CA.shl(A, cc), Nat.mul(cc, S30), esh)), tr(Nat.add(FV.lv(cl), CA.shl(A, cc)), Nat.add(FV.lv(A), 0n), Nat.add(Nat.mul(Kv, Sv), Rv), cv, tr(Nat.add(FV.lv(A), 0n), FV.lv(A), Nat.add(Nat.mul(Kv, Sv), Rv), N.add_zero(FV.lv(A)), vA)))
  +lcl = tr(PS.ln(cl), PS.ln(A), 30n, CN.carry_len(R, A, 0n), lA)
  +vX = tr(FV.lv(XS), Nat.add(FV.lv(cl), NL.sh(PS.ln(cl), FV.lv([cc]))), Nat.add(Nat.mul(Kv, Sv), Rv), HO.lv_app(cl, [cc]), tr(Nat.add(FV.lv(cl), NL.sh(PS.ln(cl), FV.lv([cc]))), Nat.add(FV.lv(cl), Nat.mul(cc, S30)), Nat.add(Nat.mul(Kv, Sv), Rv), M.cong_r(FV.lv(cl), NL.sh(PS.ln(cl), FV.lv([cc])), Nat.mul(cc, S30), tr(NL.sh(PS.ln(cl), FV.lv([cc])), NL.sh(30n, cc), Nat.mul(cc, S30), tr(NL.sh(PS.ln(cl), FV.lv([cc])), NL.sh(30n, FV.lv([cc])), NL.sh(30n, cc), Equal.cong(Nat, Nat, z => NL.sh(z, FV.lv([cc])), PS.ln(cl), 30n, lcl), Equal.cong(Nat, Nat, z => NL.sh(30n, z), FV.lv([cc]), cc, HO.lv1(cc))), HO.sh_mul(one, h1, 30n, cc))), ecl))
  +hK17 = L.subst(Nat, z => {FV.below(KL, z) == True{} : Bool}, R, s17, hR, limbs_below(one, h1, R, hR, k))
  +hconv = NL.conv_below(KL, SL, s17, s17, hK17, CV.ob_below(one, h1, s))
  +e38 = tr(NL.cb(KL, Nat.mul(s17, s17)), Nat.mul(16n, Nat.mul(s17, s17)), WD.sc(38n, one), tr(NL.cb(KL, Nat.mul(s17, s17)), Nat.mul(PS.ln(KL), Nat.mul(s17, s17)), Nat.mul(16n, Nat.mul(s17, s17)), cb_len(KL, Nat.mul(s17, s17)), Equal.cong(Nat, Nat, z => Nat.mul(z, Nat.mul(s17, s17)), PS.ln(KL), 16n, lK)), tr(Nat.mul(16n, Nat.mul(s17, s17)), Nat.mul(Nat.mul(s17, s17), 16n), WD.sc(38n, one), NA.mul_comm(16n, Nat.mul(s17, s17)), tr(Nat.mul(Nat.mul(s17, s17), 16n), WD.sc(4n, Nat.mul(s17, s17)), WD.sc(38n, one), PS.mulp(4n, Nat.mul(s17, s17)), tr(WD.sc(4n, Nat.mul(s17, s17)), WD.sc(4n, WD.sc(34n, one)), WD.sc(38n, one), M.cong_sc(4n, Nat.mul(s17, s17), WD.sc(34n, one), PW.scsc(17n, 17n, one, h1)), M.sc_sc(4n, 34n, one)))))
  +hconv38 = L.subst(Nat, z => {FV.below(LS.conv(KL, SL), z) == True{} : Bool}, NL.cb(KL, Nat.mul(s17, s17)), WD.sc(38n, one), e38, hconv)
  +hA = NL.below_mono(A, Nat.add(WD.sc(38n, one), s17), WD.sc(39n, one), PW.add_le_dbl(WD.sc(38n, one), s17, 38n, one, N.le_refl(WD.sc(38n, one)), PW.le_sc(21n, 17n, one)), NL.addl_below(LS.conv(KL, SL), RL, WD.sc(38n, one), s17, hconv38, CV.ob_below(one, h1, r)))
  +hAE = PS.at_r(one, R, hR, z => {Nat.is_le(Nat.add(WD.sc(39n, one), WD.sc(23n, one)), Nat.mul(z, WD.sc(23n, one))) == True{} : Bool}, L.subst(Nat, z => {Nat.is_le(Nat.add(WD.sc(39n, one), WD.sc(23n, one)), z) == True{} : Bool}, WD.sc(40n, one), Nat.mul(s17, WD.sc(23n, one)), sy(Nat.mul(s17, WD.sc(23n, one)), WD.sc(40n, one), PW.scsc(17n, 23n, one, h1)), PW.add_le_dbl(WD.sc(39n, one), WD.sc(23n, one), 39n, one, N.le_refl(WD.sc(39n, one)), PW.le_sc(16n, 23n, one))))
  +hcb = CA.carry_below(one, h1, R, hR, A, 0n, WD.sc(39n, one), WD.sc(23n, one), hA, PW.sc_pos(23n, one, h1), hAE)
  +hcl = L.and_left(FV.below(cl, R), Nat.is_lt(cc, WD.sc(23n, one)), hcb)
  +hKv = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(272n, one)) == True{} : Bool}, FV.lv(KL), Kv, vK, L.subst(Nat, z => {Nat.is_lt(FV.lv(KL), z) == True{} : Bool}, NL.sh(PS.ln(KL), one), WD.sc(272n, one), tr(NL.sh(PS.ln(KL), one), NL.sh(16n, one), WD.sc(272n, one), Equal.cong(Nat, Nat, z => NL.sh(z, one), PS.ln(KL), 16n, lK), NL.sh_sc(16n, one)), CN.lv_lt(one, h1, R, hR, KL, limbs_below(one, h1, R, hR, k))))
  +hS253 = N.lt_trans(Sv, P, WD.sc(253n, one), ls, hL253(one, h1))
  +hR253 = N.lt_trans(Rv, P, WD.sc(253n, one), lr, hL253(one, h1))
  +hKS = L.subst(Nat, z => {Nat.is_lt(Nat.mul(Kv, Sv), z) == True{} : Bool}, Nat.mul(WD.sc(272n, one), WD.sc(253n, one)), WD.sc(525n, one), PW.scsc(272n, 253n, one, h1), NL.lt_mul2(Kv, Sv, WD.sc(272n, one), WD.sc(253n, one), hKv, hS253))
  +hsum = N.lt_le_trans(Nat.add(Nat.mul(Kv, Sv), Rv), Nat.add(WD.sc(525n, one), WD.sc(253n, one)), WD.sc(526n, one), NL.lt_add2(Nat.mul(Kv, Sv), Rv, WD.sc(525n, one), WD.sc(253n, one), hKS, hR253), PW.add_le_dbl(WD.sc(525n, one), WD.sc(253n, one), 525n, one, N.le_refl(WD.sc(525n, one)), PW.le_sc(272n, 253n, one)))
  +e526 = tr(WD.sc(526n, one), Nat.mul(WD.sc(16n, one), WD.sc(510n, one)), Nat.mul(WD.sc(16n, one), S30), sy(Nat.mul(WD.sc(16n, one), WD.sc(510n, one)), WD.sc(526n, one), PW.scsc(16n, 510n, one, h1)), Equal.cong(Nat, Nat, z => Nat.mul(WD.sc(16n, one), z), WD.sc(510n, one), S30, sy(S30, WD.sc(510n, one), NL.sh_sc(30n, one))))
  +hcc16 = CN.mul_lt_cancel(cc, WD.sc(16n, one), S30, N.le_lt_trans(Nat.mul(cc, S30), Nat.add(Nat.mul(Kv, Sv), Rv), Nat.mul(WD.sc(16n, one), S30), L.subst(Nat, z => {Nat.is_le(Nat.mul(cc, S30), z) == True{} : Bool}, Nat.add(FV.lv(cl), Nat.mul(cc, S30)), Nat.add(Nat.mul(Kv, Sv), Rv), ecl, NL.le_add_l(FV.lv(cl), Nat.mul(cc, S30))), L.subst(Nat, z => {Nat.is_lt(Nat.add(Nat.mul(Kv, Sv), Rv), z) == True{} : Bool}, WD.sc(526n, one), Nat.mul(WD.sc(16n, one), S30), e526, hsum)))
  +hccR = N.lt_trans(cc, WD.sc(16n, one), R, hcc16, HO.r_lt_16(one, h1, R, hR))
  +hXS = BY.app_below(cl, [cc], R, hcl, NL.below_con(cc, Nil{}, R, hccR, {==}))
  +O = out_facts(one, h1, R, hR, k, XS, hXS)
  +V = FS.value(ESC.mul_add(k, s, r))
  +O2 = L.subst(Nat, z => {Bool.and(Nat.is_eq(V, Nat.mod(z, P)), Nat.is_lt(V, P)) == True{} : Bool}, FV.lv(XS), Nat.add(Nat.mul(Kv, Sv), Rv), vX, O)
  L.subst(Nat, z => {Bool.and(Nat.is_eq(V, Nat.mod(z, P)), Nat.is_lt(V, P)) == True{} : Bool}, Nat.add(Nat.mul(Kv, Sv), Rv), Nat.add(Rv, Nat.mul(Kv, Sv)), NA.add_comm(Nat.mul(Kv, Sv), Rv), O2)

def mul_add_m(+one: Nat, +h1: {one == 1n : Nat}, +k: List<&2, U32>, +s: List<&2, U32>, +r: List<&2, U32>, +hk: {LM.okb(32n, k, 255n) == True{} : Bool}, +hs: {LM.okb(32n, s, 255n) == True{} : Bool}, +hr: {LM.okb(32n, r, 255n) == True{} : Bool}, +ls: {Nat.is_lt(FS.value(s), 1n+S3.mmL(one)) == True{} : Bool}, +lr: {Nat.is_lt(FS.value(r), 1n+S3.mmL(one)) == True{} : Bool}) -> {FS.value(ESC.mul_add(k, s, r)) == Nat.mod(Nat.add(FS.value(r), Nat.mul(FS.value(k), FS.value(s))), 1n+S3.mmL(one)) : Nat}:
  +P = Mo(one)
  +V = FS.value(ESC.mul_add(k, s, r))
  +X0 = Nat.mod(Nat.add(FS.value(r), Nat.mul(FS.value(k), FS.value(s))), P)
  N.eq_from_is_eq(V, X0, L.and_left(Nat.is_eq(V, X0), Nat.is_lt(V, P), ma_facts(one, h1, k, s, r, hk, hs, hr, ls, lr)))

def mul_add_lt(+one: Nat, +h1: {one == 1n : Nat}, +k: List<&2, U32>, +s: List<&2, U32>, +r: List<&2, U32>) -> {LM.okb(32n, ESC.mul_add(k, s, r), 255n) == True{} : Bool}:
  +R = FE.radix(X.one_of(k))
  +pr = LS.carry(R, LS.addl(LS.conv(ESC.limbs17(k), LS.of_bytes_l(s)), LS.of_bytes_l(r)), 0n)
  LM.bytes_okb(32n, ESC.mul_add(k, s, r), CV.tb_tight(one, h1, ESC.hr(R, ESC.l15(k), LS.app(LS.cr_limbs(pr), [LS.cr_out(pr)]))))
