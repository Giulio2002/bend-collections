import Base
import ../../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../../math/typed/width.bend as WW
import ../../../lib/logic.bend as Lg
import ../../../lib/nat.bend as N
import ../../../math/natural/arith.bend as NR
import ../../../../spec/lib/common.bend as C
import ../../../../spec/crypto/secp256k1/field.bend as FS
import ../../../../spec/crypto/secp256k1/curve.bend as CS
import ../../../../spec/crypto/secp256k1/group.bend as GS
import ../../../../spec/crypto/secp256k1/ecdsa.bend as ES
import ../../../math/number/nt_prime.bend as PM
import ./certb.bend as CB
import ./gfp.bend as GF
import ./glawp.bend as GP
import ./sym.bend as S
import ./sqrt.bend as SQ
import ./ecdg.bend as EG
import ./ecdv.bend as EV
import ./ecdw.bend as EW
import ./ecdp.bend as EP
import ./ecdb.bend as EB

# ECDSA on the specification (spec/crypto/secp256k1/ecdsa.bend): every
# signature that ES.sign returns verifies under the signer's public key
# (either encoding, strict or not) and ES.recover returns the signer's
# uncompressed key. The facts about p, n and G are hypotheses (hp, hc, hq,
# hg, hng: see ecdp.bend).

def rO(+one: Nat, +kp: CS.SPoint) -> Nat:
  Nat.mod(CS.aff_x(CS.to_affine(P1, kp)), N1)

def sO(+one: Nat, +e: Nat, +d: Nat, +k: Nat, +kp: CS.SPoint) -> Nat:
  FS.mmul(N1, FS.minv(N1, k), FS.madd(N1, e, FS.mmul(N1, rO(one, kp), d)))

def xO(+one: Nat, +kp: CS.SPoint) -> Nat:
  CS.aff_x(CS.to_affine(P1, kp))

def yO(+one: Nat, +kp: CS.SPoint) -> Nat:
  CS.aff_y(CS.to_affine(P1, kp))

def vO(+one: Nat, +kp: CS.SPoint, +hi: Bool) -> U32:
  U32.from_nat(EW.idn(Nat.is_lt(xO(one, kp), N1), hi, Nat.mod(yO(one, kp), 2n)))

# the signature of the nonce point kp = [k] G with s replaced (hi) or not
def sigO(+one: Nat, +e: Nat, +d: Nat, +k: Nat, +kp: CS.SPoint, +hi: Bool) -> LU:
  EB.sg(rO(one, kp), ES.low(hi, N1, sO(one, e, d, k, kp)), vO(one, kp, hi))

# sig verifies under the key of d (encoding c) and recovers to it
def Good(+one: Nat, +c: Bool, +d: Nat, +h: LU, +strict: Bool, +sig: LU) -> Data:
  S.Both<{ES.verify(one, ES.pk_of(one, c, QP), h, CS.first(64n, sig), strict) == True{} : Bool}, {ES.recover(one, h, sig) == Some{CS.encode_uncompressed(P1, QP)} : MLU}>

def GoodA(+one: Nat, +c: Bool, +d: Nat, +h: LU, +strict: Bool, att: ES.Attempt) -> Data:
  match att:
    case ES.Retry{}:
      Unit
    case ES.Sig{+sig}:
      Good(one, c, d, h, strict, sig)

def GoodM(+one: Nat, +c: Bool, +d: Nat, +h: LU, +strict: Bool, m: MLU) -> Data:
  match m:
    case None{}:
      Unit
    case Some{+sig}:
      Good(one, c, d, h, strict, sig)

# ---- small facts on the specification's p and n ----

def fit_n(+one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +hx: {Nat.is_lt(x, N1) == True{} : Bool}) -> {C.fits(256n, x) == True{} : Bool}:
  WW.fits_one(256n, one, h1, x, N.lt_le_trans(x, N1, C.shift(256n, one), hx, SQ.sub_le(C.shift(256n, one), FS.cn(one))))

def lt_mod_n(+one: Nat, +h1: {one == 1n : Nat}, +v: Nat) -> {Nat.is_lt(Nat.mod(v, N1), N1) == True{} : Bool}:
  Lg.subst(Nat, n => {Nat.is_lt(Nat.mod(v, n), n) == True{} : Bool}, 1n+EP.nmo(one), N1, ESYM(Nat, N1, 1n+EP.nmo(one), CB.n_suc(one, h1)), NR.dm_lt(EP.nmo(one), v))

def lt_mod_p(+one: Nat, +h1: {one == 1n : Nat}, +v: Nat) -> {Nat.is_lt(Nat.mod(v, P1), P1) == True{} : Bool}:
  Lg.subst(Nat, p => {Nat.is_lt(Nat.mod(v, p), p) == True{} : Bool}, 1n+GF.pm(one), P1, ESYM(Nat, P1, 1n+GF.pm(one), CB.p_suc(one, h1)), NR.dm_lt(GF.pm(one), v))

def ax_lt(+one: Nat, +h1: {one == 1n : Nat}, kp: CS.SPoint) -> {Nat.is_lt(xO(one, kp), P1) == True{} : Bool}:
  match kp:
    case CS.SPoint{+x, +y, +z}:
      lt_mod_p(one, h1, Nat.mul(x, FS.minv(P1, z)))

def pk_is(+one: Nat, c: Bool, +q: CS.SPoint) -> {ES.pk_of(one, c, q) == EW.pkb(P1, c, q) : LU}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def sok_0(+one: Nat, +x: Nat, +h: SOK(x)) -> {Nat.is_eq(x, 0n) == False{} : Bool}:
  Lg.not_true(Nat.is_eq(x, 0n), Lg.and_left(Bool.not(Nat.is_eq(x, 0n)), Nat.is_lt(x, ES.n(one)), h))

def sok_l(+one: Nat, +x: Nat, +h: SOK(x)) -> {Nat.is_lt(x, N1) == True{} : Bool}:
  Lg.and_right(Bool.not(Nat.is_eq(x, 0n)), Nat.is_lt(x, ES.n(one)), h)

def sok_i(+one: Nat, +x: Nat, +h0: {Nat.is_eq(x, 0n) == False{} : Bool}, +hl: {Nat.is_lt(x, N1) == True{} : Bool}) -> SOK(x):
  Lg.and_intro(Bool.not(Nat.is_eq(x, 0n)), Nat.is_lt(x, ES.n(one)), Lg.not_false(Nat.is_eq(x, 0n), h0), hl)

def or_t(a: Bool, +b: Bool, +hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

# ---- one signature ----

def sgood(HD1, +c: Bool, +d: Nat, +h: LU, +strict: Bool, +k: Nat, +kp: CS.SPoint, +hi: Bool, +sk: SOK(k), +sd: SOK(d), +hlen: {CS.length_is(32n, h) == True{} : Bool}, +vkp: V1(kp), +hkp: E1(kp, SM1(k, G1)), +r0: {Nat.is_eq(rO(one, kp), 0n) == False{} : Bool}, +s0: {Nat.is_eq(sO(one, HS, d, k, kp), 0n) == False{} : Bool}, +hhi: {Nat.is_lt(N1, Nat.double(sO(one, HS, d, k, kp))) == hi : Bool}) -> Good(one, c, d, h, strict, sigO(one, HS, d, k, kp, hi)):
  +r = rO(one, kp)
  +s = sO(one, HS, d, k, kp)
  +sl = ES.low(hi, N1, s)
  +v = vO(one, kp, hi)
  +k0 = sok_0(one, k, sk)
  +kl = sok_l(one, k, sk)
  +d0 = sok_0(one, d, sd)
  +dl = sok_l(one, d, sd)
  +vqp = GP.scalar_pmul_closed(one, h1, hp, hc, d, G1, hg)
  +hqp = GP.scalar_pmul(one, h1, hp, hc, d, G1, hg, fit_n(one, h1, d, dl))
  +slt = lt_mod_n(one, h1, Nat.mul(FS.minv(N1, k), FS.madd(N1, HS, FS.mmul(N1, r, d))))
  +lk = EP.lok(HA1, hi, s, slt, s0)
  +rlt = lt_mod_n(one, h1, xO(one, kp))
  +sr = sok_i(one, r, r0, rlt)
  +fr = fit_n(one, h1, r, rlt)
  +fs = fit_n(one, h1, sl, Lg.and_right(Bool.not(Nat.is_eq(sl, 0n)), Nat.is_lt(sl, N1), lk))
  +q = EG.nrm(P1, QP)
  +srs = Lg.and_intro(ES.scalar_ok(one, r), ES.scalar_ok(one, sl), sr, lk)
  +hok = Lg.and_intro(Bool.and(ES.scalar_ok(one, r), ES.scalar_ok(one, sl)), Bool.or(Bool.not(strict), Bool.not(Nat.is_lt(ES.n(one), Nat.double(sl)))), srs, or_t(Bool.not(strict), Bool.not(Nat.is_lt(ES.n(one), Nat.double(sl))), EP.lows(HA1, hi, s, slt, s0, hhi)))
  +hv = EP.v2(HA1, kp, QP, k, d, HS, hi, k0, kl, d0, dl, vkp, hkp, vqp, hqp, s0)
  +hdec = Lg.subst(LU, z => {CS.decode(ES.p(one), z) == Some{q} : MSP}, EW.pkb(P1, c, QP), ES.pk_of(one, c, QP), ESYM(LU, ES.pk_of(one, c, QP), EW.pkb(P1, c, QP), pk_is(one, c, QP)), EP.dpk(HA1, c, QP, d, d0, dl, vqp, hqp))
  +ver64 = EB.ver_a(one, ES.pk_of(one, c, QP), h, EB.s64(r, sl), strict, q, Lg.and_intro(CS.length_is(32n, h), CS.length_is(64n, EB.s64(r, sl)), hlen, EB.b_len64(r, sl)), hdec, EB.ver_q(one, q, h, EB.s64(r, sl), strict, r, sl, EB.b_r(r, sl, fr), EB.b_s(r, sl, fs), hok, hv))
  +ver = Lg.subst(LU, z => {ES.verify(one, ES.pk_of(one, c, QP), h, z, strict) == True{} : Bool}, EB.s64(r, sl), CS.first(64n, EB.sg(r, sl, v)), ESYM(LU, CS.first(64n, EB.sg(r, sl, v)), EB.s64(r, sl), EB.b_first64(r, sl, v)), ver64)
  +b = Nat.is_lt(xO(one, kp), N1)
  +qq = Nat.mod(yO(one, kp), 2n)
  +hq2 = NR.dm_lt(1n, yO(one, kp))
  +id = EW.idn(b, hi, qq)
  +pr = EV.prh(P1, hi, kp)
  +qr = EB.qrO(one, HS, r, sl, pr)
  +vpr = EP.pv2(HA1, kp, k, hi, k0, kl, vkp, hkp)
  +u1 = FS.mmul(N1, FS.mneg(N1, HS), FS.minv(N1, r))
  +u2 = FS.mmul(N1, sl, FS.minv(N1, r))
  +vqr = GP.group_closed(one, h1, hp, hc, PM1(u1, G1), PM1(u2, pr), GP.scalar_pmul_closed(one, h1, hp, hc, u1, G1, hg), GP.scalar_pmul_closed(one, h1, hp, hc, u2, pr, vpr))
  +hqr = EP.q2(HA1, kp, k, d, HS, hi, k0, kl, dl, vkp, hkp, r0)
  +enc = CS.encode_uncompressed(P1, QP)
  +hrr = EB.rec_e(one, HS, r, sl, pr, enc, EP.i2(HA1, qr, d, d0, dl, vqr, hqr), EP.e2(HA1, qr, QP, d, d0, dl, vqr, hqr, vqp, hqp))
  +hxl = ax_lt(one, h1, kp)
  +hxp = Lg.subst(Nat, z => {Nat.add(r, Nat.mul(z, ES.n(one))) == xO(one, kp) : Nat}, EW.jb(b), Nat.div(id, 2n), ESYM(Nat, Nat.div(id, 2n), EW.jb(b), EW.id_d(b, hi, qq, hq2)), EP.xrec(HA1, xO(one, kp), N.lt_trans(xO(one, kp), P1, Nat.double(N1), hxl, EP.p2n(one, h1)), b, {==}))
  +hdc = Lg.subst(Nat, z => {CS.decompress(ES.p(one), xO(one, kp), z) == Some{pr} : MSP}, ES.flip(hi, qq), Nat.mod(id, 2n), ESYM(Nat, Nat.mod(id, 2n), ES.flip(hi, qq), EW.id_m(b, hi, qq, hq2)), EP.dc2(HA1, kp, k, hi, k0, kl, vkp, hkp))
  +hx = EB.rec_d(one, HS, r, sl, id, xO(one, kp), pr, Some{enc}, hxp, hxl, hdc, hrr)
  +hokr = Lg.and_intro(Bool.and(ES.scalar_ok(one, r), ES.scalar_ok(one, sl)), Nat.is_lt(id, 4n), srs, EW.id_l(b, hi, qq, hq2))
  +hid = ETR(Nat, U32.to_nat(CS.head(CS.after(64n, EB.sg(r, sl, v)))), U32.to_nat(v), id, Equal.cong(U32, Nat, z => U32.to_nat(z), CS.head(CS.after(64n, EB.sg(r, sl, v))), v, EB.b_v(r, sl, v)), EW.id_u(b, hi, qq, hq2))
  +rec = EB.rec_a(one, h, EB.sg(r, sl, v), r, sl, id, Some{enc}, Lg.and_intro(CS.length_is(32n, h), CS.length_is(65n, EB.sg(r, sl, v)), hlen, EB.b_len65(r, sl, v)), EB.b_r2(r, sl, v, fr), EB.b_s2(r, sl, v, fs), hid, EB.rec_c(one, HS, r, sl, id, Some{enc}, hokr, hx))
  S.Both{ver, rec}

# ---- an attempt, the loop, sign ----

def fin_c(HD1, +c: Bool, +d: Nat, +h: LU, +strict: Bool, +k: Nat, +kp: CS.SPoint, +sk: SOK(k), +sd: SOK(d), +hlen: {CS.length_is(32n, h) == True{} : Bool}, +vkp: V1(kp), +hkp: E1(kp, SM1(k, G1)), bad: Bool, +hbad: {Bool.or(Nat.is_eq(rO(one, kp), 0n), Nat.is_eq(sO(one, HS, d, k, kp), 0n)) == bad : Bool}) -> GoodA(one, c, d, h, strict, ES.finish_if(bad, sigO(one, HS, d, k, kp, Nat.is_lt(N1, Nat.double(sO(one, HS, d, k, kp)))))):
  match bad:
    case True{}:
      Unit{}
    case False{}:
      sgood(HA1, c, d, h, strict, k, kp, Nat.is_lt(N1, Nat.double(sO(one, HS, d, k, kp))), sk, sd, hlen, vkp, hkp, EB.or_f_l(Nat.is_eq(rO(one, kp), 0n), Nat.is_eq(sO(one, HS, d, k, kp), 0n), hbad), EB.or_f_r(Nat.is_eq(rO(one, kp), 0n), Nat.is_eq(sO(one, HS, d, k, kp), 0n), hbad), {==})

def fin_good(HD1, +c: Bool, +d: Nat, +h: LU, +strict: Bool, +k: Nat, kp: CS.SPoint, +sk: SOK(k), +sd: SOK(d), +hlen: {CS.length_is(32n, h) == True{} : Bool}, +vkp: V1(kp), +hkp: E1(kp, SM1(k, G1))) -> GoodA(one, c, d, h, strict, ES.finish(one, HS, d, k, CS.to_affine(ES.p(one), kp))):
  match kp:
    case CS.SPoint{+kx, +ky, +kz}:
      fin_c(HA1, c, d, h, strict, k, CS.SPoint{kx, ky, kz}, sk, sd, hlen, vkp, hkp, Bool.or(Nat.is_eq(rO(one, CS.SPoint{kx, ky, kz}), 0n), Nat.is_eq(sO(one, HS, d, k, CS.SPoint{kx, ky, kz}), 0n)), {==})

def att_c(HD1, +c: Bool, +d: Nat, +h: LU, +strict: Bool, +k: Nat, +sd: SOK(d), +hlen: {CS.length_is(32n, h) == True{} : Bool}, ok: Bool, +hok: {ES.scalar_ok(one, k) == ok : Bool}) -> GoodA(one, c, d, h, strict, ES.attempt_ok(one, HS, d, k, ok)):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      fin_good(HA1, c, d, h, strict, k, PM1(k, G1), hok, sd, hlen, GP.scalar_pmul_closed(one, h1, hp, hc, k, G1, hg), GP.scalar_pmul(one, h1, hp, hc, k, G1, hg, fit_n(one, h1, k, sok_l(one, k, hok))))

def att_good(HD1, +c: Bool, +d: Nat, +h: LU, +strict: Bool, +v: LU, +sd: SOK(d), +hlen: {CS.length_is(32n, h) == True{} : Bool}) -> GoodA(one, c, d, h, strict, ES.attempt(one, HS, d, v)):
  att_c(HA1, c, d, h, strict, CS.os2ip(v), sd, hlen, ES.scalar_ok(one, CS.os2ip(v)), {==})

def loop_good(fuel: Nat, HD1, +c: Bool, +d: Nat, +h: LU, +strict: Bool, +kk: LU, +v: LU, att: ES.Attempt, +sd: SOK(d), +hlen: {CS.length_is(32n, h) == True{} : Bool}, +ga: GoodA(one, c, d, h, strict, att)) -> GoodM(one, c, d, h, strict, ES.sign_loop(fuel, one, HS, d, kk, v, att)):
  match fuel att:
    case 0n ES.Retry{}:
      Unit{}
    case 0n ES.Sig{sig}:
      ga
    case 1n+ +f ES.Retry{}:
      loop_good(f, HA1, c, d, h, strict, ES.hmac(kk, ES.cat(v, [0])), ES.hmac(ES.hmac(kk, ES.cat(v, [0])), ES.hmac(ES.hmac(kk, ES.cat(v, [0])), v)), ES.attempt(one, HS, d, ES.hmac(ES.hmac(kk, ES.cat(v, [0])), ES.hmac(ES.hmac(kk, ES.cat(v, [0])), v))), sd, hlen, att_good(HA1, c, d, h, strict, ES.hmac(ES.hmac(kk, ES.cat(v, [0])), ES.hmac(ES.hmac(kk, ES.cat(v, [0])), v)), sd, hlen))
    case 1n+f ES.Sig{sig}:
      ga

def drbg_good(HD1, +c: Bool, +d: Nat, +h: LU, +strict: Bool, g: ES.Drbg, +sd: SOK(d), +hlen: {CS.length_is(32n, h) == True{} : Bool}) -> GoodM(one, c, d, h, strict, ES.sign_drbg(one, HS, d, g)):
  match g:
    case ES.Drbg{+k, +v}:
      loop_good(16n, HA1, c, d, h, strict, k, ES.hmac(k, v), ES.attempt(one, HS, d, ES.hmac(k, v)), sd, hlen, att_good(HA1, c, d, h, strict, ES.hmac(k, v), sd, hlen))

def sign_g(HD1, +k0: LU, +v0: LU, +c: Bool, +d: Nat, +h: LU, +strict: Bool, +b1: Bool, +b2: Bool, ok: Bool, +hok: {Bool.and(b1, Bool.and(b2, ES.scalar_ok(one, d))) == ok : Bool}, +hb1: {b1 == CS.length_is(32n, h) : Bool}) -> GoodM(one, c, d, h, strict, ES.sign_d(one, k0, v0, h, d, ok)):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      drbg_good(HA1, c, d, h, strict, ES.drbg_init(k0, v0, ES.cat(ES.i2osp32(d), ES.i2osp32(HS))), Lg.and_right(b2, ES.scalar_ok(one, d), Lg.and_right(b1, Bool.and(b2, ES.scalar_ok(one, d)), hok)), ETR(Bool, CS.length_is(32n, h), b1, True{}, ESYM(Bool, b1, CS.length_is(32n, h), hb1), Lg.and_left(b1, Bool.and(b2, ES.scalar_ok(one, d)), hok)))

# every signature ES.sign returns is good for the key of OS2IP(sk)
def sign_good(HD1, +c: Bool, +sk: LU, +h: LU, +strict: Bool) -> GoodM(one, c, CS.os2ip(sk), h, strict, ES.sign(one, sk, h)):
  sign_g(HA1, ES.fill(32n, 0), ES.fill(32n, 1), c, CS.os2ip(sk), h, strict, CS.length_is(32n, h), CS.length_is(32n, sk), Bool.and(CS.length_is(32n, h), Bool.and(CS.length_is(32n, sk), ES.scalar_ok(one, CS.os2ip(sk)))), {==}, {==})

def good_of(HD1, +c: Bool, +sk: LU, +h: LU, +strict: Bool, +sig: LU, +hs: {ES.sign(one, sk, h) == Some{sig} : MLU}) -> Good(one, c, CS.os2ip(sk), h, strict, sig):
  Lg.subst(MLU, m => GoodM(one, c, CS.os2ip(sk), h, strict, m), ES.sign(one, sk, h), Some{sig}, hs, sign_good(HA1, c, sk, h, strict))

def fst(-A: Data, -B: Data, p: S.Both<A, B>) -> A:
  match p:
    case S.Both{a, b}:
      a

def snd(-A: Data, -B: Data, p: S.Both<A, B>) -> B:
  match p:
    case S.Both{a, b}:
      b

# sign, then verify with the signer's public key
def sign_verify(HD1, +sk: LU, +h: LU, +c: Bool, +strict: Bool, +sig: LU, +pk: LU, +hs: {ES.sign(one, sk, h) == Some{sig} : MLU}, +hpk: {ES.public_key(one, sk, c) == Some{pk} : MLU}) -> {ES.verify(one, pk, h, CS.first(64n, sig), strict) == True{} : Bool}:
  Lg.subst(LU, z => {ES.verify(one, z, h, CS.first(64n, sig), strict) == True{} : Bool}, ES.pk_of(one, c, CS.pmul(ES.p(one), CS.os2ip(sk), CS.g(one))), pk, EB.pk_eq(one, sk, c, pk, hpk),
    fst({ES.verify(one, ES.pk_of(one, c, CS.pmul(P1, CS.os2ip(sk), G1)), h, CS.first(64n, sig), strict) == True{} : Bool}, {ES.recover(one, h, sig) == Some{CS.encode_uncompressed(P1, CS.pmul(P1, CS.os2ip(sk), G1))} : MLU}, good_of(HA1, c, sk, h, strict, sig, hs)))

def pub_u(+one: Nat, +d: Nat, ok: Bool, +hok: {ok == True{} : Bool}) -> {ES.public_d(one, False{}, d, ok) == Some{CS.encode_uncompressed(P1, CS.pmul(P1, d, G1))} : MLU}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({ES.public_d(one, False{}, d, False{}) == Some{CS.encode_uncompressed(P1, CS.pmul(P1, d, G1))} : MLU}, Lg.false_true(hok))

# sign, then recover: the signer's uncompressed public key
def sign_recover(HD1, +sk: LU, +h: LU, +sig: LU, +hs: {ES.sign(one, sk, h) == Some{sig} : MLU}) -> {ES.recover(one, h, sig) == ES.public_key(one, sk, False{}) : MLU}:
  ETR(MLU, ES.recover(one, h, sig), Some{CS.encode_uncompressed(P1, CS.pmul(P1, CS.os2ip(sk), G1))}, ES.public_key(one, sk, False{}),
    snd({ES.verify(one, ES.pk_of(one, False{}, CS.pmul(P1, CS.os2ip(sk), G1)), h, CS.first(64n, sig), False{}) == True{} : Bool}, {ES.recover(one, h, sig) == Some{CS.encode_uncompressed(P1, CS.pmul(P1, CS.os2ip(sk), G1))} : MLU}, good_of(HA1, False{}, sk, h, False{}, sig, hs)),
    ESYM(MLU, ES.public_key(one, sk, False{}), Some{CS.encode_uncompressed(P1, CS.pmul(P1, CS.os2ip(sk), G1))}, pub_u(one, CS.os2ip(sk), Bool.and(CS.length_is(32n, sk), ES.scalar_ok(one, CS.os2ip(sk))), Lg.and_right(CS.length_is(32n, h), Bool.and(CS.length_is(32n, sk), ES.scalar_ok(one, CS.os2ip(sk))), EB.sign_ok(one, sk, h, sig, hs)))))
