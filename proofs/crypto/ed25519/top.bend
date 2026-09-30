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
import ../curve25519/rel.bend as RL
import ../curve25519/xbits.bend as XB
import ./scalar.bend as SC
import ./scalar3.bend as S3
import ./prel.bend as PR
import ./pcodec.bend as PC
import ./pdec.bend as PD
import ./bytes.bend as BY

# Key generation, signing and verification of src/crypto/ed25519/ed25519.bend
# against spec/crypto/ed25519.bend, for p = 1 + pp (hP) and the curve
# constants computed from an input xs (PT.consts(xs), related to the spec's d
# and sqrt(-1) by pcodec.bend).

def bits_eq(+one: Nat, +h1: {one == 1n : Nat}, +k: List<&2, U32>, +hk: {LM.okb(32n, k, 255n) == True{} : Bool}) -> {X.bitlen(k) == C.shift(8n, one) : Nat}:
  Equal.trans(Nat, X.bitlen(k), 256n, C.shift(8n, one), BY.bitlen_256(k, hk), Equal.cong(Nat, Nat, z => C.shift(8n, z), 1n, one, Equal.sym(Nat, one, 1n, h1)))

# [k] p, k 32 bytes: the implementation runs over bitlen(k) = 256 bits, the
# spec over 2^8 one
def mul_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +D: Nat, +rd2: RL.R(pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +k: List<&2, U32>, +hk: {LM.okb(32n, k, 255n) == True{} : Bool}, +p: PT.Pt, +sp: SE.EPt, +hp: PR.Rp(pp, p, sp)) -> PR.Rp(pp, PT.mul(cs, k, p), SE.mul(one, 1n+pp, D, FS.value(k), sp)):
  %Equal.sym(Nat, X.bitlen(k), C.shift(8n, one), bits_eq(one, h1, k, hk)) : PR.Rp(pp, PT.smul(_, cs, k, p, PT.identity()), SE.mul(one, 1n+pp, D, FS.value(k), sp))
  PR.smul_rel(one, h1, pp, hP, C.shift(8n, one), cs, D, rd2, k, LM.okb_lea(32n, k, 255n, hk), p, sp, hp, PT.identity(), SE.identity(), PD.identity_rel(pp))

# encode, the spec's byte count 2^5 one
def enc_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +p: PT.Pt, +sp: SE.EPt, +hp: PR.Rp(pp, p, sp)) -> {PT.encode(p) == SE.encode(one, 1n+pp, sp) : List<&2, U32>}:
  L.subst(Nat, z => {PT.encode(p) == SE.encode_n(z, 1n+pp, sp) : List<&2, U32>}, 32n, C.shift(5n, one), Equal.cong(Nat, Nat, z => C.shift(5n, z), 1n, one, Equal.sym(Nat, one, 1n, h1)), PC.encode_rel(one, h1, pp, hP, p, sp, hp))

# ---- scalars from digests ----

def rh_val(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>) -> {FS.value(ESC.reduce(H.sha512(bs))) == Nat.mod(FS.value(SHA.sha512_bytes(bs)), SE.ell(one)) : Nat}:
  +M = {1n+S3.mmL(one) : Nat}
  +hb = H.sha512(bs)
  +sb = SHA.sha512_bytes(bs)
  +e1 = S3.reduce_m(one, h1, hb, BY.sha_lea(bs))
  +e2 = Equal.cong(List<&2, U32>, Nat, z => Nat.mod(FS.value(z), M), hb, sb, BY.sha_eq(bs))
  +e3 = Equal.cong(Nat, Nat, z => Nat.mod(FS.value(sb), z), M, SE.ell(one), S3.ell_eq(one, h1))
  Equal.trans(Nat, FS.value(ESC.reduce(hb)), Nat.mod(FS.value(hb), M), Nat.mod(FS.value(sb), SE.ell(one)), e1, Equal.trans(Nat, Nat.mod(FS.value(hb), M), Nat.mod(FS.value(sb), M), Nat.mod(FS.value(sb), SE.ell(one)), e2, e3))

def rh_eq(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +sbs: List<&2, U32>, +e: {bs == sbs : List<&2, U32>}) -> {FS.value(ESC.reduce(H.sha512(bs))) == Nat.mod(FS.value(SHA.sha512_bytes(sbs)), SE.ell(one)) : Nat}:
  Equal.trans(Nat, FS.value(ESC.reduce(H.sha512(bs))), Nat.mod(FS.value(SHA.sha512_bytes(bs)), SE.ell(one)), Nat.mod(FS.value(SHA.sha512_bytes(sbs)), SE.ell(one)), rh_val(one, h1, bs), Equal.cong(List<&2, U32>, Nat, z => Nat.mod(FS.value(SHA.sha512_bytes(z)), SE.ell(one)), bs, sbs, e))

def hram_s(+one: Nat, +rb: List<&2, U32>, +a: List<&2, U32>, +msg: List<&2, U32>) -> {SE.hram(one, rb, a, msg) == Nat.mod(FS.value(SHA.sha512_bytes(SE.cat(rb, SE.cat(a, msg)))), SE.ell(one)) : Nat}:
  match rb:
    case Nil{}:
      {==}
    case Con{x, xt}:
      {==}

def hram_i(+rb: List<&2, U32>, +a: List<&2, U32>, +msg: List<&2, U32>) -> {E.hram(rb, a, msg) == ESC.reduce(H.sha512(E.cat(rb, E.cat(a, msg)))) : List<&2, U32>}:
  match rb:
    case Nil{}:
      {==}
    case Con{x, xt}:
      {==}

def red_lt(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +hb: {LM.lea(bs, 255n) == True{} : Bool}) -> {Nat.is_lt(FS.value(ESC.reduce(bs)), 1n+S3.mmL(one)) == True{} : Bool}:
  +M = {1n+S3.mmL(one) : Nat}
  L.subst(Nat, z => {Nat.is_lt(z, M) == True{} : Bool}, Nat.mod(FS.value(bs), M), FS.value(ESC.reduce(bs)), Equal.sym(Nat, FS.value(ESC.reduce(bs)), Nat.mod(FS.value(bs), M), S3.reduce_m(one, h1, bs, hb)), SC.lt_mod(S3.mmL(one), FS.value(bs)))

def secret_eq(+h: List<&2, U32>) -> {FS.value(X.clamp(F.take(32n, h))) == SE.secret(h) : Nat}:
  +t = F.take(32n, h)
  +st = SE.first(32n, h)
  Equal.cong(List<&2, U32>, Nat, z => FS.value(z), X.clamp(t), SX.clamp(st), Equal.trans(List<&2, U32>, X.clamp(t), SX.clamp(t), SX.clamp(st), XB.clamp_eq(t), Equal.cong(List<&2, U32>, List<&2, U32>, z => SX.clamp(z), t, st, BY.take_eq(32n, h))))

def cat2_eq(+x: List<&2, U32>, +sx: List<&2, U32>, +y: List<&2, U32>, +sy: List<&2, U32>, +m: List<&2, U32>, +ex: {x == sx : List<&2, U32>}, +ey: {y == sy : List<&2, U32>}) -> {E.cat(x, E.cat(y, m)) == SE.cat(sx, SE.cat(sy, m)) : List<&2, U32>}:
  +e1 = BY.cat_eq(x, E.cat(y, m))
  +e2 = Equal.cong(List<&2, U32>, List<&2, U32>, z => SE.cat(x, z), E.cat(y, m), SE.cat(y, m), BY.cat_eq(y, m))
  +e3 = Equal.cong(List<&2, U32>, List<&2, U32>, z => SE.cat(z, SE.cat(y, m)), x, sx, ex)
  +e4 = Equal.cong(List<&2, U32>, List<&2, U32>, z => SE.cat(sx, SE.cat(z, m)), y, sy, ey)
  Equal.trans(List<&2, U32>, E.cat(x, E.cat(y, m)), SE.cat(x, E.cat(y, m)), SE.cat(sx, SE.cat(sy, m)), e1, Equal.trans(List<&2, U32>, SE.cat(x, E.cat(y, m)), SE.cat(x, SE.cat(y, m)), SE.cat(sx, SE.cat(sy, m)), e2, Equal.trans(List<&2, U32>, SE.cat(x, SE.cat(y, m)), SE.cat(sx, SE.cat(y, m)), SE.cat(sx, SE.cat(sy, m)), e3, e4)))

def hk_okb(+one: Nat, +h1: {one == 1n : Nat}, +rb: List<&2, U32>, +a: List<&2, U32>, +msg: List<&2, U32>) -> {LM.okb(32n, E.hram(rb, a, msg), 255n) == True{} : Bool}:
  +kh = H.sha512(E.cat(rb, E.cat(a, msg)))
  L.subst(List<&2, U32>, z => {LM.okb(32n, z, 255n) == True{} : Bool}, ESC.reduce(kh), E.hram(rb, a, msg), Equal.sym(List<&2, U32>, E.hram(rb, a, msg), ESC.reduce(kh), hram_i(rb, a, msg)), S3.reduce_okb(one, h1, kh, BY.sha_lea(E.cat(rb, E.cat(a, msg)))))

def hk_val(+one: Nat, +h1: {one == 1n : Nat}, +rb: List<&2, U32>, +srb: List<&2, U32>, +erb: {rb == srb : List<&2, U32>}, +a: List<&2, U32>, +sa: List<&2, U32>, +ea: {a == sa : List<&2, U32>}, +msg: List<&2, U32>) -> {FS.value(E.hram(rb, a, msg)) == SE.hram(one, srb, sa, msg) : Nat}:
  +KH = E.cat(rb, E.cat(a, msg))
  +SKH = SE.cat(srb, SE.cat(sa, msg))
  +M = Nat.mod(FS.value(SHA.sha512_bytes(SKH)), SE.ell(one))
  +e1 = Equal.cong(List<&2, U32>, Nat, z => FS.value(z), E.hram(rb, a, msg), ESC.reduce(H.sha512(KH)), hram_i(rb, a, msg))
  +e2 = rh_eq(one, h1, KH, SKH, cat2_eq(rb, srb, a, sa, msg, erb, ea))
  Equal.trans(Nat, FS.value(E.hram(rb, a, msg)), FS.value(ESC.reduce(H.sha512(KH))), SE.hram(one, srb, sa, msg), e1, Equal.trans(Nat, FS.value(ESC.reduce(H.sha512(KH))), M, SE.hram(one, srb, sa, msg), e2, Equal.sym(Nat, SE.hram(one, srb, sa, msg), M, hram_s(one, srb, sa, msg))))

# S = (r + k s) mod L, as 32 bytes: s reduced first (the implementation's
# reduce(secret)), the same residue
def ma_eq(+one: Nat, +h1: {one == 1n : Nat}, +k: List<&2, U32>, +r: List<&2, U32>, +sk: List<&2, U32>, +hk: {LM.okb(32n, k, 255n) == True{} : Bool}, +hr: {LM.okb(32n, r, 255n) == True{} : Bool}, +lr: {Nat.is_lt(FS.value(r), 1n+S3.mmL(one)) == True{} : Bool}, +hsk: {LM.okb(32n, sk, 255n) == True{} : Bool}, +Rs: Nat, +Ks: Nat, +Ss: Nat, +eR: {FS.value(r) == Rs : Nat}, +eK: {FS.value(k) == Ks : Nat}, +eS: {FS.value(sk) == Ss : Nat}) -> {ESC.mul_add(k, ESC.reduce(sk), r) == SX.le_bytes(C.shift(5n, one), Nat.mod(Nat.add(Rs, Nat.mul(Ks, Ss)), SE.ell(one))) : List<&2, U32>}:
  +mm = S3.mmL(one)
  +M = {1n+S3.mmL(one) : Nat}
  +el = SE.ell(one)
  +s = ESC.reduce(sk)
  +hl = LM.okb_lea(32n, sk, 255n, hsk)
  +lk = LM.okb_lea(32n, k, 255n, hk)
  +os = S3.reduce_okb(one, h1, sk, hl)
  +ls = red_lt(one, h1, sk, hl)
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
  +e0 = S3.mul_add_m(one, h1, k, s, r, lk, os, hr, ls, lr)
  +e1 = Equal.cong(Nat, Nat, z => Nat.mod(Nat.add(Vr, Nat.mul(Vk, z)), M), FS.value(s), Nat.mod(Vs, M), S3.reduce_m(one, h1, sk, hl))
  +e2 = G.c_add(mm, Vr, Vr, Nat.mul(Vk, Nat.mod(Vs, M)), Nat.mul(Vk, Vs), G.c_refl(mm, Vr), G.c_mul(mm, Vk, Vk, Nat.mod(Vs, M), Vs, G.c_refl(mm, Vk), G.c_mod(mm, Vs)))
  +e3 = Equal.cong(Nat, Nat, z => Nat.mod(Nat.add(z, Nat.mul(Vk, Vs)), M), Vr, Rs, eR)
  +e4 = Equal.cong(Nat, Nat, z => Nat.mod(Nat.add(Rs, Nat.mul(z, Vs)), M), Vk, Ks, eK)
  +e5 = Equal.cong(Nat, Nat, z => Nat.mod(Nat.add(Rs, Nat.mul(Ks, z)), M), Vs, Ss, eS)
  +e6 = Equal.cong(Nat, Nat, z => Nat.mod(Nat.add(Rs, Nat.mul(Ks, Ss)), z), M, el, S3.ell_eq(one, h1))
  +ev = Equal.trans(Nat, T0, T1, T7, e0, Equal.trans(Nat, T1, T2, T7, e1, Equal.trans(Nat, T2, T3, T7, e2, Equal.trans(Nat, T3, T4, T7, e3, Equal.trans(Nat, T4, T5, T7, e4, Equal.trans(Nat, T5, T6, T7, e5, e6))))))
  +eb = Equal.sym(List<&2, U32>, SX.le_bytes(32n, T0), MA, XB.bytes_le(32n, MA, S3.mul_add_lt(one, h1, k, s, r, lk, os, hr, ls, lr)))
  +e8 = Equal.trans(List<&2, U32>, MA, SX.le_bytes(32n, T0), SX.le_bytes(32n, T7), eb, Equal.cong(Nat, List<&2, U32>, z => SX.le_bytes(32n, z), T0, T7, ev))
  L.subst(Nat, z => {MA == SX.le_bytes(z, T7) : List<&2, U32>}, 32n, C.shift(5n, one), Equal.cong(Nat, Nat, z => C.shift(5n, z), 1n, one, Equal.sym(Nat, one, 1n, h1)), e8)

# ---- key generation ----

def public_body_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +xs: List<&2, U32>, +D: Nat, +rd: RL.R(pp, PT.cs_d(PT.consts(xs)), D), +rd2: RL.R(pp, PT.cs_d2(PT.consts(xs)), FS.fadd(1n+pp, D, D)), +h: List<&2, U32>, +hh: {LM.okb(64n, h, 255n) == True{} : Bool}) -> {E.public_of(PT.consts(xs), xs, h) == SE.public_body(one, 1n+pp, D, h) : List<&2, U32>}:
  +P = {1n+pp : Nat}
  +cs = PT.consts(xs)
  +sk = X.clamp(F.take(32n, h))
  +hs = XB.clamp_okb(F.take(32n, h), BY.take_okb(32n, 32n, h, 255n, hh))
  +B = PT.base(cs, xs)
  +SB = SE.base(P, D)
  +hB = PD.base_rel(one, h1, pp, hP, cs, D, rd, PC.r_sqm1(one, h1, pp, hP, xs), xs)
  +rm = mul_rel(one, h1, pp, hP, cs, D, rd2, sk, hs, B, SB, hB)
  +e1 = enc_rel(one, h1, pp, hP, PT.mul(cs, sk, B), SE.mul(one, P, D, FS.value(sk), SB), rm)
  Equal.trans(List<&2, U32>, PT.encode(PT.mul(cs, sk, B)), SE.encode(one, P, SE.mul(one, P, D, FS.value(sk), SB)), SE.encode(one, P, SE.mul(one, P, D, SE.secret(h), SB)), e1, Equal.cong(Nat, List<&2, U32>, z => SE.encode(one, P, SE.mul(one, P, D, z, SB)), FS.value(sk), SE.secret(h), secret_eq(h)))

def pub_guard(+one: Nat, +p: Nat, +d: Nat, +h: List<&2, U32>, +x: List<&2, U32>, +e: {x == SE.public_body(one, p, d, h) : List<&2, U32>}) -> {x == SE.public_of(one, p, d, h) : List<&2, U32>}:
  match d:
    case 0n:
      e
    case 1n+ +q:
      e

def public_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +xs: List<&2, U32>, +D: Nat, +rd: RL.R(pp, PT.cs_d(PT.consts(xs)), D), +rd2: RL.R(pp, PT.cs_d2(PT.consts(xs)), FS.fadd(1n+pp, D, D)), +h: List<&2, U32>, +hh: {LM.okb(64n, h, 255n) == True{} : Bool}) -> {E.public_of(PT.consts(xs), xs, h) == SE.public_of(one, 1n+pp, D, h) : List<&2, U32>}:
  pub_guard(one, 1n+pp, D, h, E.public_of(PT.consts(xs), xs, h), public_body_rel(one, h1, pp, hP, xs, D, rd, rd2, h, hh))

def rb_eq(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +D: Nat, +rd2: RL.R(pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +B: PT.Pt, +SB: SE.EPt, +hB: PR.Rp(pp, B, SB), +r: List<&2, U32>, +okr: {LM.okb(32n, r, 255n) == True{} : Bool}, +Rs: Nat, +eR: {FS.value(r) == Rs : Nat}) -> {PT.encode(PT.mul(cs, r, B)) == SE.encode(one, 1n+pp, SE.mul(one, 1n+pp, D, Rs, SB)) : List<&2, U32>}:
  +P = {1n+pp : Nat}
  Equal.trans(List<&2, U32>, PT.encode(PT.mul(cs, r, B)), SE.encode(one, P, SE.mul(one, P, D, FS.value(r), SB)), SE.encode(one, P, SE.mul(one, P, D, Rs, SB)), enc_rel(one, h1, pp, hP, PT.mul(cs, r, B), SE.mul(one, P, D, FS.value(r), SB), mul_rel(one, h1, pp, hP, cs, D, rd2, r, okr, B, SB, hB)), Equal.cong(Nat, List<&2, U32>, z => SE.encode(one, P, SE.mul(one, P, D, z, SB)), FS.value(r), Rs, eR))

# R || S
def sig_eq(+one: Nat, +h1: {one == 1n : Nat}, +RB: List<&2, U32>, +SRB: List<&2, U32>, +eRB: {RB == SRB : List<&2, U32>}, +k: List<&2, U32>, +okk: {LM.okb(32n, k, 255n) == True{} : Bool}, +Ks: Nat, +eK: {FS.value(k) == Ks : Nat}, +r: List<&2, U32>, +okr: {LM.okb(32n, r, 255n) == True{} : Bool}, +lr: {Nat.is_lt(FS.value(r), 1n+S3.mmL(one)) == True{} : Bool}, +Rs: Nat, +eR: {FS.value(r) == Rs : Nat}, +sk: List<&2, U32>, +hsk: {LM.okb(32n, sk, 255n) == True{} : Bool}, +Ss: Nat, +eS: {FS.value(sk) == Ss : Nat}) -> {E.cat(RB, ESC.mul_add(k, ESC.reduce(sk), r)) == SE.cat(SRB, SX.le_bytes(C.shift(5n, one), Nat.mod(Nat.add(Rs, Nat.mul(Ks, Ss)), SE.ell(one)))) : List<&2, U32>}:
  +MA = ESC.mul_add(k, ESC.reduce(sk), r)
  +SMB = SX.le_bytes(C.shift(5n, one), Nat.mod(Nat.add(Rs, Nat.mul(Ks, Ss)), SE.ell(one)))
  +eMA = ma_eq(one, h1, k, r, sk, okk, okr, lr, hsk, Rs, Ks, Ss, eR, eK, eS)
  Equal.trans(List<&2, U32>, E.cat(RB, MA), SE.cat(RB, MA), SE.cat(SRB, SMB), BY.cat_eq(RB, MA), Equal.trans(List<&2, U32>, SE.cat(RB, MA), SE.cat(SRB, MA), SE.cat(SRB, SMB), Equal.cong(List<&2, U32>, List<&2, U32>, z => SE.cat(z, MA), RB, SRB, eRB), Equal.cong(List<&2, U32>, List<&2, U32>, z => SE.cat(SRB, z), MA, SMB, eMA)))

def prefix_eq(+h: List<&2, U32>, +msg: List<&2, U32>) -> {E.cat(F.drop(32n, h), msg) == SE.cat(SE.rest(32n, h), msg) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, E.cat(F.drop(32n, h), msg), SE.cat(F.drop(32n, h), msg), SE.cat(SE.rest(32n, h), msg), BY.cat_eq(F.drop(32n, h), msg), Equal.cong(List<&2, U32>, List<&2, U32>, z => SE.cat(z, msg), F.drop(32n, h), SE.rest(32n, h), BY.drop_eq(32n, h)))

def sign_body_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +xs: List<&2, U32>, +D: Nat, +rd: RL.R(pp, PT.cs_d(PT.consts(xs)), D), +rd2: RL.R(pp, PT.cs_d2(PT.consts(xs)), FS.fadd(1n+pp, D, D)), +h: List<&2, U32>, +hh: {LM.okb(64n, h, 255n) == True{} : Bool}, +msg: List<&2, U32>) -> {E.sign_with(PT.consts(xs), xs, h, msg) == SE.sign_body(one, 1n+pp, D, h, msg) : List<&2, U32>}:
  +P = {1n+pp : Nat}
  +el = SE.ell(one)
  +cs = PT.consts(xs)
  +B = PT.base(cs, xs)
  +SB = SE.base(P, D)
  +hB = PD.base_rel(one, h1, pp, hP, cs, D, rd, PC.r_sqm1(one, h1, pp, hP, xs), xs)
  +A = E.public_of(cs, xs, h)
  +SA = SE.public_of(one, P, D, h)
  +RH = E.cat(F.drop(32n, h), msg)
  +SRH = SE.cat(SE.rest(32n, h), msg)
  +r = ESC.reduce(H.sha512(RH))
  +Rs = Nat.mod(FS.value(SHA.sha512_bytes(SRH)), el)
  +eR = rh_eq(one, h1, RH, SRH, prefix_eq(h, msg))
  +okr = S3.reduce_okb(one, h1, H.sha512(RH), BY.sha_lea(RH))
  +RB = PT.encode(PT.mul(cs, r, B))
  +SRB = SE.encode(one, P, SE.mul(one, P, D, Rs, SB))
  +eRB = rb_eq(one, h1, pp, hP, cs, D, rd2, B, SB, hB, r, okr, Rs, eR)
  +k = E.hram(RB, A, msg)
  +Ks = SE.hram(one, SRB, SA, msg)
  +eK = hk_val(one, h1, RB, SRB, eRB, A, SA, public_rel(one, h1, pp, hP, xs, D, rd, rd2, h, hh), msg)
  +sk = X.clamp(F.take(32n, h))
  +hsk = XB.clamp_okb(F.take(32n, h), BY.take_okb(32n, 32n, h, 255n, hh))
  sig_eq(one, h1, RB, SRB, eRB, k, hk_okb(one, h1, RB, A, msg), Ks, eK, r, okr, red_lt(one, h1, H.sha512(RH), BY.sha_lea(RH)), Rs, eR, sk, hsk, SE.secret(h), secret_eq(h))

def sign_guard(+one: Nat, +p: Nat, +d: Nat, +h: List<&2, U32>, +msg: List<&2, U32>, +x: List<&2, U32>, +e: {x == SE.sign_body(one, p, d, h, msg) : List<&2, U32>}) -> {x == SE.sign_with(one, p, d, h, msg) : List<&2, U32>}:
  match d:
    case 0n:
      e
    case 1n+ +q:
      e

def sign_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +xs: List<&2, U32>, +D: Nat, +rd: RL.R(pp, PT.cs_d(PT.consts(xs)), D), +rd2: RL.R(pp, PT.cs_d2(PT.consts(xs)), FS.fadd(1n+pp, D, D)), +h: List<&2, U32>, +hh: {LM.okb(64n, h, 255n) == True{} : Bool}, +msg: List<&2, U32>) -> {E.sign_with(PT.consts(xs), xs, h, msg) == SE.sign_with(one, 1n+pp, D, h, msg) : List<&2, U32>}:
  sign_guard(one, 1n+pp, D, h, msg, E.sign_with(PT.consts(xs), xs, h, msg), sign_body_rel(one, h1, pp, hP, xs, D, rd, rd2, h, hh, msg))

# ---- verification ----

def check_some(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +pk: List<&2, U32>, +msg: List<&2, U32>, +rb: List<&2, U32>, +sb: List<&2, U32>, +hsb: {LM.okb(32n, sb, 255n) == True{} : Bool}, +r: PT.Pt, +sr: SE.EPt, +hr: PR.Rp(pp, r, sr), +a: PT.Pt, +sa: SE.EPt, +ha: PR.Rp(pp, a, sa)) -> {E.check(PT.consts(pk), sb, rb, pk, msg, Some{r}, Some{a}) == SE.check(one, 1n+pp, SE.dconst(one, 1n+pp), FS.value(sb), rb, pk, msg, Some{sr}, Some{sa}) : Bool}:
  +P = {1n+pp : Nat}
  +D = SE.dconst(one, P)
  +cs = PT.consts(pk)
  +B = PT.base(cs, pk)
  +SB = SE.base(P, D)
  +hB = PD.base_rel(one, h1, pp, hP, cs, D, PC.r_d(one, h1, pp, hP, pk), PC.r_sqm1(one, h1, pp, hP, pk), pk)
  +rd2 = PC.r_d2(one, h1, pp, hP, pk)
  +k = E.hram(rb, pk, msg)
  +Ks = SE.hram(one, rb, pk, msg)
  +eK = hk_val(one, h1, rb, rb, {==}, pk, pk, {==}, msg)
  +okk = hk_okb(one, h1, rb, pk, msg)
  +ka = PT.mul(cs, k, a)
  +ska = SE.mul(one, P, D, FS.value(k), sa)
  +m1 = mul_rel(one, h1, pp, hP, cs, D, rd2, sb, hsb, B, SB, hB)
  +m2 = mul_rel(one, h1, pp, hP, cs, D, rd2, k, okk, a, sa, ha)
  +ad = PR.add_rel(one, h1, pp, hP, cs, D, rd2, r, ka, sr, ska, hr, m2)
  +lhs = SE.mul(one, P, D, FS.value(sb), SB)
  +eq = PC.equal_rel(one, h1, pp, hP, PT.mul(cs, sb, B), PT.add(cs, r, ka), lhs, SE.add(P, D, sr, ska), m1, ad)
  Equal.trans(Bool, PT.equal(PT.mul(cs, sb, B), PT.add(cs, r, ka)), SE.equal(P, lhs, SE.add(P, D, sr, ska)), SE.equal(P, lhs, SE.add(P, D, sr, SE.mul(one, P, D, Ks, sa))), eq, Equal.cong(Nat, Bool, z => SE.equal(P, lhs, SE.add(P, D, sr, SE.mul(one, P, D, z, sa))), FS.value(k), Ks, eK))

def check_a(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +pk: List<&2, U32>, +msg: List<&2, U32>, +rb: List<&2, U32>, +sb: List<&2, U32>, +hsb: {LM.okb(32n, sb, 255n) == True{} : Bool}, +r: PT.Pt, +sr: SE.EPt, +hr: PR.Rp(pp, r, sr), +aa: Maybe<&2, PT.Pt>, +saa: Maybe<&2, SE.EPt>, +haa: PC.MR(pp, aa, saa)) -> {E.check(PT.consts(pk), sb, rb, pk, msg, Some{r}, aa) == SE.check(one, 1n+pp, SE.dconst(one, 1n+pp), FS.value(sb), rb, pk, msg, Some{sr}, saa) : Bool}:
  match aa saa:
    case None{} None{}:
      {==}
    case Some{+a} Some{+sa}:
      check_some(one, h1, pp, hP, pk, msg, rb, sb, hsb, r, sr, hr, a, sa, haa)
    case None{} Some{+sa}:
      Empty.absurd({E.check(PT.consts(pk), sb, rb, pk, msg, Some{r}, None{}) == SE.check(one, 1n+pp, SE.dconst(one, 1n+pp), FS.value(sb), rb, pk, msg, Some{sr}, Some{sa}) : Bool}, L.true_false(haa))
    case Some{+a} None{}:
      Empty.absurd({E.check(PT.consts(pk), sb, rb, pk, msg, Some{r}, Some{a}) == SE.check(one, 1n+pp, SE.dconst(one, 1n+pp), FS.value(sb), rb, pk, msg, Some{sr}, None{}) : Bool}, L.true_false(haa))

def check_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +pk: List<&2, U32>, +msg: List<&2, U32>, +rb: List<&2, U32>, +sb: List<&2, U32>, +hsb: {LM.okb(32n, sb, 255n) == True{} : Bool}, +ra: Maybe<&2, PT.Pt>, +sra: Maybe<&2, SE.EPt>, +hra: PC.MR(pp, ra, sra), +aa: Maybe<&2, PT.Pt>, +saa: Maybe<&2, SE.EPt>, +haa: PC.MR(pp, aa, saa)) -> {E.check(PT.consts(pk), sb, rb, pk, msg, ra, aa) == SE.check(one, 1n+pp, SE.dconst(one, 1n+pp), FS.value(sb), rb, pk, msg, sra, saa) : Bool}:
  match ra sra:
    case None{} None{}:
      {==}
    case Some{+r} Some{+sr}:
      check_a(one, h1, pp, hP, pk, msg, rb, sb, hsb, r, sr, hra, aa, saa, haa)
    case None{} Some{+sr}:
      Empty.absurd({E.check(PT.consts(pk), sb, rb, pk, msg, None{}, aa) == SE.check(one, 1n+pp, SE.dconst(one, 1n+pp), FS.value(sb), rb, pk, msg, Some{sr}, saa) : Bool}, L.true_false(hra))
    case Some{+r} None{}:
      Empty.absurd({E.check(PT.consts(pk), sb, rb, pk, msg, Some{r}, aa) == SE.check(one, 1n+pp, SE.dconst(one, 1n+pp), FS.value(sb), rb, pk, msg, None{}, saa) : Bool}, L.true_false(hra))

def verify_with_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +pk: List<&2, U32>, +hpk: {LM.okb(32n, pk, 255n) == True{} : Bool}, +msg: List<&2, U32>, +rb: List<&2, U32>, +hrb: {LM.okb(32n, rb, 255n) == True{} : Bool}, +sb: List<&2, U32>, +hsb: {LM.okb(32n, sb, 255n) == True{} : Bool}, +s_ok: Bool) -> {E.verify_with(PT.consts(pk), pk, msg, rb, sb, s_ok) == SE.verify_with(one, 1n+pp, SE.dconst(one, 1n+pp), pk, msg, rb, FS.value(sb), s_ok) : Bool}:
  match s_ok:
    case True{}:
      +P = {1n+pp : Nat}
      +D = SE.dconst(one, P)
      +cs = PT.consts(pk)
      +rd = PC.r_d(one, h1, pp, hP, pk)
      +rs = PC.r_sqm1(one, h1, pp, hP, pk)
      check_rel(one, h1, pp, hP, pk, msg, rb, sb, hsb, PT.decode(cs, rb), SE.decode(P, D, rb), PD.decode_rel(one, h1, pp, hP, cs, D, rd, rs, rb, hrb), PT.decode(cs, pk), SE.decode(P, D, pk), PD.decode_rel(one, h1, pp, hP, cs, D, rd, rs, pk, hpk))
    case False{}:
      {==}
