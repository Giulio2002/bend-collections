import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/x25519.bend as SX
import ../../../spec/crypto/ed25519.bend as SE
import ../../../spec/crypto/sha512.bend as SHA
import ../../../src/crypto/hash.bend as H
import ../../../src/crypto/curve25519/field.bend as F
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../../src/crypto/ed25519/point.bend as PT
import ../../../src/crypto/ed25519/scalar.bend as ESC
import ../../../src/crypto/ed25519/ed25519.bend as E
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../curve25519/limbs.bend as LM
import ../curve25519/cong.bend as G
import ../curve25519/xbits.bend as XB
import ../fe/rel.bend as RE
import ./scalar3.bend as S3
import ./sclause.bend as SL
import ./prel.bend as PR
import ./bytes.bend as BY
import ./tcommon.bend as TC
import ./tscal.bend as TH

# Signing (RFC 8032 5.1.6) with the parts of the expanded key against
# spec/crypto/ed25519.bend.

def ma_eq(+one: Nat, +h1: {one == 1n : Nat}, +k: List<&2, U32>, +r: List<&2, U32>, +sk: List<&2, U32>, +hk: {LM.okb(32n, k, 255n) == True{} : Bool}, +hr: {LM.okb(32n, r, 255n) == True{} : Bool}, +lr: {Nat.is_lt(FS.value(r), 1n+S3.mmL(one)) == True{} : Bool}, +hsk: {LM.okb(32n, sk, 255n) == True{} : Bool}, +Rs: Nat, +Ks: Nat, +Ss: Nat, +eR: {FS.value(r) == Rs : Nat}, +eK: {FS.value(k) == Ks : Nat}, +eS: {FS.value(sk) == Ss : Nat}) -> {ESC.mul_add(k, ESC.reduce(sk), r) == SX.le_bytes(C.shift(5n, one), Nat.mod(Nat.add(Rs, Nat.mul(Ks, Ss)), SE.ell(one))) : List<&2, U32>}:
  +mm = S3.mmL(one)
  +M = {1n+S3.mmL(one) : Nat}
  +el = SE.ell(one)
  +s = ESC.reduce(sk)
  +hl = LM.okb_lea(32n, sk, 255n, hsk)
  +os = SL.reduce_okb(one, h1, sk)
  +ls = SL.reduce_lt(one, h1, sk, hl)
  +MA = ESC.mul_add(k, s, r)
  +Vr = FS.value(r)
  +Vk = FS.value(k)
  +Vs = FS.value(sk)
  +T0 = FS.value(MA)
  +T1 = Nat.mod(Nat.add(Vr, Nat.mul(Vk, FS.value(s))), M)
  +T2 = Nat.mod(Nat.add(Vr, Nat.mul(Vk, Nat.mod(Vs, M))), M)
  +T3 = Nat.mod(Nat.add(Vr, Nat.mul(Vk, Vs)), M)
  +T4 = Nat.mod(Nat.add(Rs, Nat.mul(Vk, Vs)), M)
  +T5 = Nat.mod(Nat.add(Rs, Nat.mul(Ks, Vs)), M)
  +T6 = Nat.mod(Nat.add(Rs, Nat.mul(Ks, Ss)), M)
  +T7 = Nat.mod(Nat.add(Rs, Nat.mul(Ks, Ss)), el)
  +e0 = SL.mul_add_m(one, h1, k, s, r, hk, os, hr, ls, lr)
  +e1 = Equal.cong(Nat, Nat, z => Nat.mod(Nat.add(Vr, Nat.mul(Vk, z)), M), FS.value(s), Nat.mod(Vs, M), SL.reduce_m(one, h1, sk, hl))
  +e2 = G.c_add(mm, Vr, Vr, Nat.mul(Vk, Nat.mod(Vs, M)), Nat.mul(Vk, Vs), G.c_refl(mm, Vr), G.c_mul(mm, Vk, Vk, Nat.mod(Vs, M), Vs, G.c_refl(mm, Vk), G.c_mod(mm, Vs)))
  +e3 = Equal.cong(Nat, Nat, z => Nat.mod(Nat.add(z, Nat.mul(Vk, Vs)), M), Vr, Rs, eR)
  +e4 = Equal.cong(Nat, Nat, z => Nat.mod(Nat.add(Rs, Nat.mul(z, Vs)), M), Vk, Ks, eK)
  +e5 = Equal.cong(Nat, Nat, z => Nat.mod(Nat.add(Rs, Nat.mul(Ks, z)), M), Vs, Ss, eS)
  +e6 = Equal.cong(Nat, Nat, z => Nat.mod(Nat.add(Rs, Nat.mul(Ks, Ss)), z), M, el, S3.ell_eq(one, h1))
  +ev = Equal.trans(Nat, T0, T1, T7, e0, Equal.trans(Nat, T1, T2, T7, e1, Equal.trans(Nat, T2, T3, T7, e2, Equal.trans(Nat, T3, T4, T7, e3, Equal.trans(Nat, T4, T5, T7, e4, Equal.trans(Nat, T5, T6, T7, e5, e6))))))
  +eb = Equal.sym(List<&2, U32>, SX.le_bytes(32n, T0), MA, XB.bytes_le(32n, MA, SL.mul_add_lt(one, h1, k, s, r)))
  +e8 = Equal.trans(List<&2, U32>, MA, SX.le_bytes(32n, T0), SX.le_bytes(32n, T7), eb, Equal.cong(Nat, List<&2, U32>, z => SX.le_bytes(32n, z), T0, T7, ev))
  L.subst(Nat, z => {MA == SX.le_bytes(z, T7) : List<&2, U32>}, 32n, C.shift(5n, one), Equal.cong(Nat, Nat, z => C.shift(5n, z), 1n, one, Equal.sym(Nat, one, 1n, h1)), e8)

# ---- key generation ----

def rb_eq(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd2: RE.Rel(one, pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +B: PT.Pt, +SB: SE.EPt, +hB: PR.Rp(one, pp, B, SB), +r: List<&2, U32>, +okr: {LM.okb(32n, r, 255n) == True{} : Bool}, +Rs: Nat, +eR: {FS.value(r) == Rs : Nat}) -> {PT.encode(PT.cs_r(cs), PT.mul(cs, r, B)) == SE.encode(one, 1n+pp, SE.mul(one, 1n+pp, D, Rs, SB)) : List<&2, U32>}:
  +P = {1n+pp : Nat}
  +R = PT.cs_r(cs)
  Equal.trans(List<&2, U32>, PT.encode(R, PT.mul(cs, r, B)), SE.encode(one, P, SE.mul(one, P, D, FS.value(r), SB)), SE.encode(one, P, SE.mul(one, P, D, Rs, SB)), TC.enc_rel(one, h1, pp, hP, R, hR, PT.mul(cs, r, B), SE.mul(one, P, D, FS.value(r), SB), TC.mul_rel(one, h1, pp, hP, cs, hR, D, rd2, r, okr, B, SB, hB)), Equal.cong(Nat, List<&2, U32>, z => SE.encode(one, P, SE.mul(one, P, D, z, SB)), FS.value(r), Rs, eR))

# R || S

def sig_eq(+one: Nat, +h1: {one == 1n : Nat}, +RB: List<&2, U32>, +SRB: List<&2, U32>, +eRB: {RB == SRB : List<&2, U32>}, +k: List<&2, U32>, +okk: {LM.okb(32n, k, 255n) == True{} : Bool}, +Ks: Nat, +eK: {FS.value(k) == Ks : Nat}, +r: List<&2, U32>, +okr: {LM.okb(32n, r, 255n) == True{} : Bool}, +lr: {Nat.is_lt(FS.value(r), 1n+S3.mmL(one)) == True{} : Bool}, +Rs: Nat, +eR: {FS.value(r) == Rs : Nat}, +sk: List<&2, U32>, +hsk: {LM.okb(32n, sk, 255n) == True{} : Bool}, +Ss: Nat, +eS: {FS.value(sk) == Ss : Nat}) -> {E.cat(RB, ESC.mul_add(k, ESC.reduce(sk), r)) == SE.cat(SRB, SX.le_bytes(C.shift(5n, one), Nat.mod(Nat.add(Rs, Nat.mul(Ks, Ss)), SE.ell(one)))) : List<&2, U32>}:
  +MA = ESC.mul_add(k, ESC.reduce(sk), r)
  +SMB = SX.le_bytes(C.shift(5n, one), Nat.mod(Nat.add(Rs, Nat.mul(Ks, Ss)), SE.ell(one)))
  +eMA = ma_eq(one, h1, k, r, sk, okk, okr, lr, hsk, Rs, Ks, Ss, eR, eK, eS)
  Equal.trans(List<&2, U32>, E.cat(RB, MA), SE.cat(RB, MA), SE.cat(SRB, SMB), BY.cat_eq(RB, MA), Equal.trans(List<&2, U32>, SE.cat(RB, MA), SE.cat(SRB, MA), SE.cat(SRB, SMB), Equal.cong(List<&2, U32>, List<&2, U32>, z => SE.cat(z, MA), RB, SRB, eRB), Equal.cong(List<&2, U32>, List<&2, U32>, z => SE.cat(SRB, z), MA, SMB, eMA)))

def prefix_eq(+h: List<&2, U32>, +msg: List<&2, U32>) -> {E.cat(F.drop(32n, h), msg) == SE.cat(SE.rest(32n, h), msg) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, E.cat(F.drop(32n, h), msg), SE.cat(F.drop(32n, h), msg), SE.cat(SE.rest(32n, h), msg), BY.cat_eq(F.drop(32n, h), msg), Equal.cong(List<&2, U32>, List<&2, U32>, z => SE.cat(z, msg), F.drop(32n, h), SE.rest(32n, h), BY.drop_eq(32n, h)))

# the signature from the parts of the expanded key

def sign_body_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd2: RE.Rel(one, pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +B: PT.Pt, +hB: PR.Rp(one, pp, B, SE.base(1n+pp, D)), +h: List<&2, U32>, +hh: {LM.okb(64n, h, 255n) == True{} : Bool}, +msg: List<&2, U32>) -> {E.sign_parts(cs, B, ESC.reduce(E.secret(h)), E.prefix(h), E.public_of(cs, B, h), msg) == SE.sign_body(one, 1n+pp, D, h, msg) : List<&2, U32>}:
  +P = {1n+pp : Nat}
  +el = SE.ell(one)
  +SB = SE.base(P, D)
  +A = E.public_of(cs, B, h)
  +SA = SE.public_of(one, P, D, h)
  +RH = E.cat(F.drop(32n, h), msg)
  +SRH = SE.cat(SE.rest(32n, h), msg)
  +r = ESC.reduce(H.sha512(RH))
  +Rs = Nat.mod(FS.value(SHA.sha512_bytes(SRH)), el)
  +eR = TH.rh_eq(one, h1, RH, SRH, prefix_eq(h, msg))
  +okr = SL.reduce_okb(one, h1, H.sha512(RH))
  +RB = PT.encode(PT.cs_r(cs), PT.mul(cs, r, B))
  +SRB = SE.encode(one, P, SE.mul(one, P, D, Rs, SB))
  +eRB = rb_eq(one, h1, pp, hP, cs, hR, D, rd2, B, SB, hB, r, okr, Rs, eR)
  +k = E.hram(RB, A, msg)
  +Ks = SE.hram(one, SRB, SA, msg)
  +eK = TH.hk_val(one, h1, RB, SRB, eRB, A, SA, TC.public_rel(one, h1, pp, hP, cs, hR, D, rd2, B, hB, h, hh), msg)
  +sk = X.clamp(F.take(32n, h))
  +hsk = XB.clamp_okb(F.take(32n, h), BY.take_okb(32n, 32n, h, 255n, hh))
  sig_eq(one, h1, RB, SRB, eRB, k, TH.hk_okb(one, h1, RB, A, msg), Ks, eK, r, okr, SL.reduce_lt(one, h1, H.sha512(RH), BY.sha_lea(RH)), Rs, eR, sk, hsk, SE.secret(h), TC.secret_eq(h))

def sign_guard(+one: Nat, +p: Nat, +d: Nat, +h: List<&2, U32>, +msg: List<&2, U32>, +x: List<&2, U32>, +e: {x == SE.sign_body(one, p, d, h, msg) : List<&2, U32>}) -> {x == SE.sign_with(one, p, d, h, msg) : List<&2, U32>}:
  match d:
    case 0n:
      e
    case 1n+ +q:
      e

def sign_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd2: RE.Rel(one, pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +B: PT.Pt, +hB: PR.Rp(one, pp, B, SE.base(1n+pp, D)), +h: List<&2, U32>, +hh: {LM.okb(64n, h, 255n) == True{} : Bool}, +msg: List<&2, U32>) -> {E.sign_parts(cs, B, ESC.reduce(E.secret(h)), E.prefix(h), E.public_of(cs, B, h), msg) == SE.sign_with(one, 1n+pp, D, h, msg) : List<&2, U32>}:
  sign_guard(one, 1n+pp, D, h, msg, E.sign_parts(cs, B, ESC.reduce(E.secret(h)), E.prefix(h), E.public_of(cs, B, h), msg), sign_body_rel(one, h1, pp, hP, cs, hR, D, rd2, B, hB, h, hh, msg))

# ---- verification ----
