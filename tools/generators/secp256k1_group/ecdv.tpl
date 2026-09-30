import Base
import ../../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../../math/typed/width.bend as WW
import ../semiring.bend as SR
import ../../../lib/logic.bend as Lg
import ../../../lib/nat.bend as N
import ../../../math/natural/arith.bend as NR
import ../../../../spec/lib/common.bend as C
import ../../../../spec/crypto/secp256k1/field.bend as FS
import ../../../../spec/crypto/secp256k1/curve.bend as CS
import ../../../../spec/crypto/secp256k1/group.bend as GS
import ../../../../spec/crypto/secp256k1/ecdsa.bend as ES
import ../../../math/number/nt_prime.bend as PM
import ./fld.bend as F
import ./glaw1.bend as G1
import ./glaw2.bend as G2
import ./glaw4.bend as G4
import ./glaw5.bend as G5
import ./aff1.bend as A1
import ./enc.bend as EC
import ./encv.bend as EV
import ./sqrt.bend as SQ
import ./ecdn.bend as EN
import ./ecdg.bend as EG

# The two checks of ECDSA on abstract points (modulus 1 + mp, order
# n = 1 + nm, generator g as in ecdg.bend): K equiv [k] g is the nonce
# point and Q equiv [d] g the public key; r = x(K) mod n,
# s = k^-1 (e + r d) mod n, and s' is s or n - s (ES.low).
#   vfy: the verification sum [e / s'] g + [r / s'] Q is not infinity and
#        its affine x mod n is r;
#   rcv_*: the recovery sum [-e / r] g + [s' / r] R', with R' the
#        normalized K or its negative, is not infinity and encodes as Q;
#   dcp: decompressing x(K) with the parity of y(K), flipped with s',
#        gives R'.

def scal(+mp: Nat, +rr: CS.SPoint, +g: CS.SPoint, +a: Nat, +b: Nat, +h: {a == b : Nat}, +he: E(rr, SM(a, g))) -> E(rr, SM(b, g)):
  %h : {GS.equiv(1n+mp, rr, GS.smul(1n+mp, _, g)) == True{} : Bool}
  he

def qnrm(FPD, NQD, GD, +qp: CS.SPoint, +d: Nat, +nzd: NZN(d), +vqp: V(qp), +hqp: E(qp, SM(d, g))) -> E(EG.nrm(1n+mp, qp), SM(d, g)):
  TR(EG.nrm(1n+mp, qp), qp, SM(d, g), vqp, SY(qp, EG.nrm(1n+mp, qp), EG.w_nrm_e(mp, hp, qp, EG.knz(FPA, NQA, GA, qp, d, nzd, vqp, hqp))), hqp)

def qnrm_v(FPD, NQD, GD, +qp: CS.SPoint, +d: Nat, +nzd: NZN(d), +vqp: V(qp), +hqp: E(qp, SM(d, g))) -> V(EG.nrm(1n+mp, qp)):
  EG.w_nrm_v(mp, hp, qp, vqp, EG.knz(FPA, NQA, GA, qp, d, nzd, vqp, hqp))

# the verification check
def vfy(FPD, NQD, GD, OD, +kp: CS.SPoint, +qp: CS.SPoint, +k: Nat, +d: Nat, +e: Nat, hi: Bool, +nzk: NZN(k), +hk: LTN(k), +nzd: NZN(d), +vkp: V(kp), +hkp: E(kp, SM(k, g)), +vqp: V(qp), +hqp: E(qp, SM(d, g)), +nzs: NZN(SSF(RV))) -> {Bool.and(Bool.not(CS.is_inf(RRH(ES.low(hi, 1n+nm, SSF(RV))))), Nat.is_eq(DN(CS.aff_x(TA(RRH(ES.low(hi, 1n+nm, SSF(RV)))))), RV)) == True{} : Bool}:
  match hi:
    case False{}:
      +nq = EG.nrm(1n+mp, qp)
      +vnq = qnrm_v(FPA, NQA, GA, qp, d, nzd, vqp, hqp)
      +hnq = qnrm(FPA, NQA, GA, qp, d, nzd, vqp, hqp)
      +w = IN(SSF(RV))
      +u1 = MN(e, w)
      +u2 = MN(RV, w)
      EG.rr_pos(FPA, NQA, GA, PA(PM(u1, g), PM(u2, nq)), kp, k, nzk, vkp, hkp, G1.v_add(FPA, PM(u1, g), PM(u2, nq), G4.pmul_valid(FPA, u1, g, vg), G4.pmul_valid(FPA, u2, nq, vnq)),
        scal(mp, PA(PM(u1, g), PM(u2, nq)), g, AN(u1, MN(u2, d)), k, EN.kk_pos(NQA, e, RV, d, k, nzk, hk, nzs),
          EG.lin2(FPA, NQA, GA, OA, u1, u2, nq, d, NR.dm_lt(nm, Nat.mul(e, w)), NR.dm_lt(nm, Nat.mul(RV, w)), vnq, hnq)))
    case True{}:
      +nq = EG.nrm(1n+mp, qp)
      +vnq = qnrm_v(FPA, NQA, GA, qp, d, nzd, vqp, hqp)
      +hnq = qnrm(FPA, NQA, GA, qp, d, nzd, vqp, hqp)
      +w = IN(NN(SSF(RV)))
      +u1 = MN(e, w)
      +u2 = MN(RV, w)
      EG.rr_neg(FPA, NQA, GA, PA(PM(u1, g), PM(u2, nq)), kp, k, nzk, vkp, hkp, G1.v_add(FPA, PM(u1, g), PM(u2, nq), G4.pmul_valid(FPA, u1, g, vg), G4.pmul_valid(FPA, u2, nq, vnq)),
        scal(mp, PA(PM(u1, g), PM(u2, nq)), g, AN(u1, MN(u2, d)), NN(k), EN.kk_neg(NQA, e, RV, d, k, nzk, hk, nzs),
          EG.lin2(FPA, NQA, GA, OA, u1, u2, nq, d, NR.dm_lt(nm, Nat.mul(e, w)), NR.dm_lt(nm, Nat.mul(RV, w)), vnq, hnq)))

# ---- recovery ----

# the normalized K, or its negative when s was replaced by n - s
def prh(+p: Nat, hi: Bool, +a: CS.SPoint) -> CS.SPoint:
  match hi:
    case False{}:
      EG.nrm(p, a)
    case True{}:
      GS.neg(p, EG.nrm(p, a))

# the recovery sum is [d] g
def rcv_q(FPD, NQD, GD, OD, +kp: CS.SPoint, +k: Nat, +d: Nat, +e: Nat, hi: Bool, +nzk: NZN(k), +hd: LTN(d), +vkp: V(kp), +hkp: E(kp, SM(k, g)), +nzr: NZN(RV)) -> E(QRH(ES.low(hi, 1n+nm, SSF(RV)), prh(1n+mp, hi, kp)), SM(d, g)):
  match hi:
    case False{}:
      +nk = EG.knz(FPA, NQA, GA, kp, k, nzk, vkp, hkp)
      +nr = EG.nrm(1n+mp, kp)
      +vnr = EG.w_nrm_v(mp, hp, kp, vkp, nk)
      +hnr = TR(nr, kp, SM(k, g), vkp, SY(kp, nr, EG.w_nrm_e(mp, hp, kp, nk)), hkp)
      +ri = IN(RV)
      +u1 = MN(NN(e), ri)
      +u2 = MN(SSF(RV), ri)
      scal(mp, PA(PM(u1, g), PM(u2, nr)), g, AN(u1, MN(u2, k)), d, EN.rec_pos(NQA, e, RV, d, k, nzk, nzr, hd),
        EG.lin2(FPA, NQA, GA, OA, u1, u2, nr, k, NR.dm_lt(nm, Nat.mul(NN(e), ri)), NR.dm_lt(nm, Nat.mul(SSF(RV), ri)), vnr, hnr))
    case True{}:
      +nk = EG.knz(FPA, NQA, GA, kp, k, nzk, vkp, hkp)
      +nr = EG.nrm(1n+mp, kp)
      +vnr = EG.w_nrm_v(mp, hp, kp, vkp, nk)
      +hnr = TR(nr, kp, SM(k, g), vkp, SY(kp, nr, EG.w_nrm_e(mp, hp, kp, nk)), hkp)
      +ri = IN(RV)
      +u1 = MN(NN(e), ri)
      +u2 = MN(NN(SSF(RV)), ri)
      +vsk = G4.v_smul(FPA, k, g, vg)
      scal(mp, PA(PM(u1, g), PM(u2, NG(nr))), g, AN(u1, MN(u2, NN(k))), d, EN.rec_neg(NQA, e, RV, d, k, nzk, nzr, hd),
        EG.lin2(FPA, NQA, GA, OA, u1, u2, NG(nr), NN(k), NR.dm_lt(nm, Nat.mul(NN(e), ri)), NR.dm_lt(nm, Nat.mul(NN(SSF(RV)), ri)), G2.v_neg(mp, nr, vnr),
          TR(NG(nr), NG(SM(k, g)), SM(NN(k), g), G2.v_neg(mp, SM(k, g), vsk), G5.e_neg(mp, nr, SM(k, g), hnr), SY(SM(NN(k), g), NG(SM(k, g)), EG.negk(FPA, NQA, GA, k)))))

def prh_v(FPD, NQD, GD, +kp: CS.SPoint, +k: Nat, hi: Bool, +nzk: NZN(k), +vkp: V(kp), +hkp: E(kp, SM(k, g))) -> V(prh(1n+mp, hi, kp)):
  match hi:
    case False{}:
      EG.w_nrm_v(mp, hp, kp, vkp, EG.knz(FPA, NQA, GA, kp, k, nzk, vkp, hkp))
    case True{}:
      G2.v_neg(mp, EG.nrm(1n+mp, kp), EG.w_nrm_v(mp, hp, kp, vkp, EG.knz(FPA, NQA, GA, kp, k, nzk, vkp, hkp)))

# a point equiv [d] g (d != 0 mod n) is not infinity ...
def rcv_i(FPD, NQD, GD, +qr: CS.SPoint, +d: Nat, +nzd: NZN(d), +vqr: V(qr), +hqr: E(qr, SM(d, g))) -> {CS.is_inf(qr) == False{} : Bool}:
  EG.w_inf(mp, qr, EG.knz(FPA, NQA, GA, qr, d, nzd, vqr, hqr))

# ... and encodes as any other
def rcv_e(FPD, NQD, GD, +qr: CS.SPoint, +qp: CS.SPoint, +d: Nat, +nzd: NZN(d), +vqr: V(qr), +hqr: E(qr, SM(d, g)), +vqp: V(qp), +hqp: E(qp, SM(d, g))) -> {CS.encode_uncompressed(1n+mp, qr) == CS.encode_uncompressed(1n+mp, qp) : List<&2, U32>}:
  Equal.cong(CS.SAffine, List<&2, U32>, t => CS.enc_u(t), TA(qr), TA(qp), EG.w_ta(mp, hp, qr, qp, vqr, vqp, EG.knz(FPA, NQA, GA, qr, d, nzd, vqr, hqr), EG.knz(FPA, NQA, GA, qp, d, nzd, vqp, hqp), TR(qr, SM(d, g), qp, G4.v_smul(FPA, d, g, vg), hqr, SY(qp, SM(d, g), hqp))))

# ---- decompression of x(K) ----

def two_cases(a: Nat, b: Nat, +ha: {Nat.is_lt(a, 2n) == True{} : Bool}, +hb: {Nat.is_lt(b, 2n) == True{} : Bool}, +hne: {Nat.is_eq(a, b) == False{} : Bool}) -> {a == Nat.sub(1n, b) : Nat}:
  match a b:
    case 0n 0n:
      Empty.absurd({0n == Nat.sub(1n, 0n) : Nat}, Lg.true_false(hne))
    case 0n 1n:
      {==}
    case 0n 2n+ +q:
      Empty.absurd({0n == Nat.sub(1n, 2n+q) : Nat}, N.lt_zero_absurd(q, hb))
    case 1n 0n:
      {==}
    case 1n 1n:
      Empty.absurd({1n == Nat.sub(1n, 1n) : Nat}, Lg.true_false(hne))
    case 1n 2n+ +q:
      Empty.absurd({1n == Nat.sub(1n, 2n+q) : Nat}, N.lt_zero_absurd(q, hb))
    case 2n+ +p b2:
      Empty.absurd({2n+p == Nat.sub(1n, b2) : Nat}, N.lt_zero_absurd(p, ha))

def par_ne_c(+a: Nat, +b: Nat, +hs: {Nat.mod(Nat.add(a, b), 2n) == 1n : Nat}, c: Bool, +hc: {Nat.is_eq(Nat.mod(a, 2n), Nat.mod(b, 2n)) == c : Bool}) -> {Nat.is_eq(Nat.mod(a, 2n), Nat.mod(b, 2n)) == False{} : Bool}:
  match c:
    case False{}:
      hc
    case True{}:
      Empty.absurd({Nat.is_eq(Nat.mod(a, 2n), Nat.mod(b, 2n)) == False{} : Bool}, SQ.par_ne(a, b, N.eq_from_is_eq(Nat.mod(a, 2n), Nat.mod(b, 2n), hc), hs))

def par_sum(+mp: Nat, +hodd: {Nat.mod(1n+mp, 2n) == 1n : Nat}, +yp: Nat, +hy: {Nat.is_lt(1n+yp, 1n+mp) == True{} : Bool}) -> {Nat.mod(Nat.add(FS.mneg(1n+mp, 1n+yp), 1n+yp), 2n) == 1n : Nat}:
  %ESYM(Nat, FS.mneg(1n+mp, 1n+yp), Nat.sub(mp, yp), SQ.neg_pos(mp, yp, hy)) : {Nat.mod(Nat.add(_, 1n+yp), 2n) == 1n : Nat}
  %ESYM(Nat, Nat.add(Nat.sub(mp, yp), 1n+yp), 1n+mp, SQ.neg_sum(mp, yp, hy)) : {Nat.mod(_, 2n) == 1n : Nat}
  hodd

# p odd, 0 < y < p: p - y has the other parity
def par_flip(+mp: Nat, +hodd: {Nat.mod(1n+mp, 2n) == 1n : Nat}, y: Nat, +hy: {Nat.is_lt(y, 1n+mp) == True{} : Bool}, +nzy: {Nat.is_eq(y, 0n) == False{} : Bool}) -> {Nat.mod(FS.mneg(1n+mp, y), 2n) == Nat.sub(1n, Nat.mod(y, 2n)) : Nat}:
  match y:
    case 0n:
      Empty.absurd({Nat.mod(FS.mneg(1n+mp, 0n), 2n) == Nat.sub(1n, Nat.mod(0n, 2n)) : Nat}, Lg.true_false(nzy))
    case 1n+ +yp:
      two_cases(Nat.mod(FS.mneg(1n+mp, 1n+yp), 2n), Nat.mod(1n+yp, 2n), NR.dm_lt(1n, FS.mneg(1n+mp, 1n+yp)), NR.dm_lt(1n, 1n+yp),
        par_ne_c(FS.mneg(1n+mp, 1n+yp), 1n+yp, par_sum(mp, hodd, yp, hy), Nat.is_eq(Nat.mod(FS.mneg(1n+mp, 1n+yp), 2n), Nat.mod(1n+yp, 2n)), {==}))

def dcp(+one: Nat, +h1: {one == 1n : Nat}, FPD, ED, kp: CS.SPoint, hi: Bool, +vkp: V(kp), +nk: NZP(EG.pz(kp))) -> {CS.decompress(1n+mp, CS.aff_x(TA(kp)), ES.flip(hi, Nat.mod(CS.aff_y(TA(kp)), 2n))) == Some{prh(1n+mp, hi, kp)} : Maybe<&2, CS.SPoint>}:
  match kp hi:
    case CS.SPoint{+kx, +ky, +kz} False{}:
      EC.decomp(one, h1, mp, hp, EA, MP(kx, IP(kz)), MP(ky, IP(kz)), NR.dm_lt(mp, Nat.mul(ky, IP(kz))), EC.aff_on(mp, hp, kx, ky, kz, vkp, nk))
    case CS.SPoint{+kx, +ky, +kz} True{}:
      +x = MP(kx, IP(kz))
      +y = MP(ky, IP(kz))
      +hy = NR.dm_lt(mp, Nat.mul(ky, IP(kz)))
      +on = EC.aff_on(mp, hp, kx, ky, kz, vkp, nk)
      +nzy = EN.nz_ne0(mp, y, G1.v_nz(mp, x, y, 1n, A1.nrm_v(mp, hp, kx, ky, kz, G1.v_onc(mp, kx, ky, kz, vkp), G1.v_nz(mp, kx, ky, kz, vkp), nk)))
      %par_flip(mp, hodd, y, hy, nzy) : {CS.decompress(1n+mp, x, _) == Some{CS.SPoint{x, FS.mneg(1n+mp, y), 1n}} : Maybe<&2, CS.SPoint>}
      EC.decomp(one, h1, mp, hp, EA, x, FS.mneg(1n+mp, y), NR.dm_lt(mp, Nat.sub(Nat.add(0n, 1n+mp), Nat.mod(y, 1n+mp))), EV.neg_on(mp, x, y, on))
