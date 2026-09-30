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
import ./enc.bend as EC
import ./sqrt.bend as SQ
import ./ecda.bend as AR
import ./ecdn.bend as EN
import ./ecdg.bend as EG
import ./ecdv.bend as EV

# The lemmas of ecdv.bend with their hypotheses on scalars written as the
# specification has them (k != 0 as a number, k < n), and the facts on the
# scalars r, s' and the recovery id that the specification's checks need.
# Every statement mentions the moduli only as 1 + mp and 1 + nm, so that it
# can be moved to FS.prime(one) and FS.order(one) (ecdp.bend).

def v2(FPD, NQD, GD, OD, +kp: CS.SPoint, +qp: CS.SPoint, +k: Nat, +d: Nat, +e: Nat, +hi: Bool, KH, DH, +vkp: V(kp), +hkp: E(kp, SM(k, g)), +vqp: V(qp), +hqp: E(qp, SM(d, g)), +s0: {Nat.is_eq(SSF(RV), 0n) == False{} : Bool}) -> {Bool.and(Bool.not(CS.is_inf(RRH(ES.low(hi, 1n+nm, SSF(RV))))), Nat.is_eq(DN(CS.aff_x(TA(RRH(ES.low(hi, 1n+nm, SSF(RV)))))), RV)) == True{} : Bool}:
  EV.vfy(FPA, NQA, GA, OA, kp, qp, k, d, e, hi, EN.nz_of(nm, k, kl, k0), kl, EN.nz_of(nm, d, dl, d0), vkp, hkp, vqp, hqp, EN.nz_of(nm, SSF(RV), NR.dm_lt(nm, Nat.mul(IN(k), AN(e, MN(RV, d)))), s0))

def q2(FPD, NQD, GD, OD, +kp: CS.SPoint, +k: Nat, +d: Nat, +e: Nat, +hi: Bool, KH, +dl: LTN(d), +vkp: V(kp), +hkp: E(kp, SM(k, g)), +r0: {Nat.is_eq(RV, 0n) == False{} : Bool}) -> E(QRH(ES.low(hi, 1n+nm, SSF(RV)), EV.prh(1n+mp, hi, kp)), SM(d, g)):
  EV.rcv_q(FPA, NQA, GA, OA, kp, k, d, e, hi, EN.nz_of(nm, k, kl, k0), dl, vkp, hkp, EN.nz_of(nm, RV, NR.dm_lt(nm, CS.aff_x(TA(kp))), r0))

def pv2(FPD, NQD, GD, +kp: CS.SPoint, +k: Nat, +hi: Bool, KH, +vkp: V(kp), +hkp: E(kp, SM(k, g))) -> V(EV.prh(1n+mp, hi, kp)):
  EV.prh_v(FPA, NQA, GA, kp, k, hi, EN.nz_of(nm, k, kl, k0), vkp, hkp)

def i2(FPD, NQD, GD, +qr: CS.SPoint, +d: Nat, DH, +vqr: V(qr), +hqr: E(qr, SM(d, g))) -> {CS.is_inf(qr) == False{} : Bool}:
  EV.rcv_i(FPA, NQA, GA, qr, d, EN.nz_of(nm, d, dl, d0), vqr, hqr)

def e2(FPD, NQD, GD, +qr: CS.SPoint, +qp: CS.SPoint, +d: Nat, DH, +vqr: V(qr), +hqr: E(qr, SM(d, g)), +vqp: V(qp), +hqp: E(qp, SM(d, g))) -> {CS.encode_uncompressed(1n+mp, qr) == CS.encode_uncompressed(1n+mp, qp) : List<&2, U32>}:
  EV.rcv_e(FPA, NQA, GA, qr, qp, d, EN.nz_of(nm, d, dl, d0), vqr, hqr, vqp, hqp)

def dc2(+one: Nat, +h1: {one == 1n : Nat}, FPD, NQD, GD, ED, +kp: CS.SPoint, +k: Nat, +hi: Bool, KH, +vkp: V(kp), +hkp: E(kp, SM(k, g))) -> {CS.decompress(1n+mp, CS.aff_x(TA(kp)), ES.flip(hi, Nat.mod(CS.aff_y(TA(kp)), 2n))) == Some{EV.prh(1n+mp, hi, kp)} : Maybe<&2, CS.SPoint>}:
  EV.dcp(one, h1, FPA, EA, kp, hi, vkp, EG.knz(FPA, NQA, GA, kp, k, EN.nz_of(nm, k, kl, k0), vkp, hkp))

# the key bytes (ES.pk_of, with the modulus as a parameter)
def pkb(+p: Nat, c: Bool, +q: CS.SPoint) -> List<&2, U32>:
  match c:
    case True{}:
      CS.encode_compressed(p, q)
    case False{}:
      CS.encode_uncompressed(p, q)

def dpk_r(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hp: PM.Prime(1n+mp), ED, c: Bool, qp: CS.SPoint, +vqp: V(qp), +nq: NZP(EG.pz(qp))) -> {CS.decode(1n+mp, pkb(1n+mp, c, qp)) == Some{EG.nrm(1n+mp, qp)} : Maybe<&2, CS.SPoint>}:
  match c qp:
    case True{} CS.SPoint{+x, +y, +z}:
      EC.rt_c(one, h1, mp, hp, EA, x, y, z, vqp, nq)
    case False{} CS.SPoint{+x, +y, +z}:
      EC.rt_u(one, h1, mp, hp, EA, x, y, z, vqp, nq)

# decoding the key of Q gives Q normalized
def dpk(+one: Nat, +h1: {one == 1n : Nat}, FPD, NQD, GD, ED, +c: Bool, +qp: CS.SPoint, +d: Nat, DH, +vqp: V(qp), +hqp: E(qp, SM(d, g))) -> {CS.decode(1n+mp, pkb(1n+mp, c, qp)) == Some{EG.nrm(1n+mp, qp)} : Maybe<&2, CS.SPoint>}:
  dpk_r(one, h1, mp, hp, EA, c, qp, vqp, EG.knz(FPA, NQA, GA, qp, d, EN.nz_of(nm, d, dl, d0), vqp, hqp))

# ---- s' = ES.low(hi, n, s) ----

# 1 <= s' < n
def lok(+nm: Nat, hi: Bool, +s: Nat, +sl: LTN(s), +s0: {Nat.is_eq(s, 0n) == False{} : Bool}) -> {Bool.and(Bool.not(Nat.is_eq(ES.low(hi, 1n+nm, s), 0n)), Nat.is_lt(ES.low(hi, 1n+nm, s), 1n+nm)) == True{} : Bool}:
  match hi:
    case False{}:
      Lg.and_intro(Bool.not(Nat.is_eq(s, 0n)), Nat.is_lt(s, 1n+nm), Lg.not_false(Nat.is_eq(s, 0n), s0), sl)
    case True{}:
      Lg.and_intro(Bool.not(Nat.is_eq(NN(s), 0n)), Nat.is_lt(NN(s), 1n+nm), Lg.not_false(Nat.is_eq(NN(s), 0n), EN.nz_ne0(nm, NN(s), EN.neg_nz(nm, s, EN.nz_of(nm, s, sl, s0)))), NR.dm_lt(nm, Nat.sub(Nat.add(0n, 1n+nm), Nat.mod(s, 1n+nm))))

def lows_t(+nm: Nat, s: Nat, +sl: LTN(s), +s0: {Nat.is_eq(s, 0n) == False{} : Bool}, +hh: {Nat.is_lt(1n+nm, Nat.double(s)) == True{} : Bool}) -> {Nat.is_lt(1n+nm, Nat.double(NN(s))) == False{} : Bool}:
  match s:
    case 0n:
      Empty.absurd({Nat.is_lt(1n+nm, Nat.double(NN(0n))) == False{} : Bool}, Lg.true_false(s0))
    case 1n+ +sp:
      %ESYM(Nat, FS.mneg(1n+nm, 1n+sp), Nat.sub(nm, sp), SQ.neg_pos(nm, sp, sl)) : {Nat.is_lt(1n+nm, Nat.double(_)) == False{} : Bool}
      %SQ.neg_sum(nm, sp, sl) : {Nat.is_lt(_, Nat.double(Nat.sub(nm, sp))) == False{} : Bool}
      AR.low_half(1n+sp, Nat.sub(nm, sp), Lg.subst(Nat, z => {Nat.is_lt(z, Nat.double(1n+sp)) == True{} : Bool}, 1n+nm, Nat.add(Nat.sub(nm, sp), 1n+sp), ESYM(Nat, Nat.add(Nat.sub(nm, sp), 1n+sp), 1n+nm, SQ.neg_sum(nm, sp, sl)), hh))

# s' is low: not n < 2 s'
def lows(+nm: Nat, hi: Bool, +s: Nat, +sl: LTN(s), +s0: {Nat.is_eq(s, 0n) == False{} : Bool}, +hhi: {Nat.is_lt(1n+nm, Nat.double(s)) == hi : Bool}) -> {Bool.not(Nat.is_lt(1n+nm, Nat.double(ES.low(hi, 1n+nm, s)))) == True{} : Bool}:
  match hi:
    case False{}:
      Lg.not_false(Nat.is_lt(1n+nm, Nat.double(s)), hhi)
    case True{}:
      Lg.not_false(Nat.is_lt(1n+nm, Nat.double(NN(s))), lows_t(nm, s, sl, s0, hhi))

# ---- the recovery id ----

def jb(b: Bool) -> Nat:
  match b:
    case True{}:
      0n
    case False{}:
      1n

# x = r + j n for r = x mod n, j = 0 when x < n and 1 otherwise (x < 2 n)
def xrec(+nm: Nat, +x: Nat, +hx2: {Nat.is_lt(x, Nat.double(1n+nm)) == True{} : Bool}, b: Bool, +hb: {Nat.is_lt(x, 1n+nm) == b : Bool}) -> {Nat.add(Nat.mod(x, 1n+nm), Nat.mul(jb(b), 1n+nm)) == x : Nat}:
  match b:
    case True{}:
      %ESYM(Nat, Nat.mod(x, 1n+nm), x, SQ.mred(nm, x, hb)) : {Nat.add(_, 0n) == x : Nat}
      NA.add_zero(x)
    case False{}:
      AR.mod_big_c(nm, x, hx2, N.not_lt_le(x, 1n+nm, hb))

def idn(+b: Bool, +hi: Bool, +q: Nat) -> Nat:
  Nat.add(ES.ge2(b), ES.flip(hi, q))

def id_u(b: Bool, hi: Bool, q: Nat, +hq: {Nat.is_lt(q, 2n) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(idn(b, hi, q))) == idn(b, hi, q) : Nat}:
  match b hi q:
    case True{} True{} 0n:
      {==}
    case True{} True{} 1n:
      {==}
    case True{} True{} 2n+ +q2:
      Empty.absurd({U32.to_nat(U32.from_nat(idn(True{}, True{}, 2n+q2))) == idn(True{}, True{}, 2n+q2) : Nat}, N.lt_zero_absurd(q2, hq))
    case True{} False{} 0n:
      {==}
    case True{} False{} 1n:
      {==}
    case True{} False{} 2n+ +q2:
      Empty.absurd({U32.to_nat(U32.from_nat(idn(True{}, False{}, 2n+q2))) == idn(True{}, False{}, 2n+q2) : Nat}, N.lt_zero_absurd(q2, hq))
    case False{} True{} 0n:
      {==}
    case False{} True{} 1n:
      {==}
    case False{} True{} 2n+ +q2:
      Empty.absurd({U32.to_nat(U32.from_nat(idn(False{}, True{}, 2n+q2))) == idn(False{}, True{}, 2n+q2) : Nat}, N.lt_zero_absurd(q2, hq))
    case False{} False{} 0n:
      {==}
    case False{} False{} 1n:
      {==}
    case False{} False{} 2n+ +q2:
      Empty.absurd({U32.to_nat(U32.from_nat(idn(False{}, False{}, 2n+q2))) == idn(False{}, False{}, 2n+q2) : Nat}, N.lt_zero_absurd(q2, hq))

def id_d(b: Bool, hi: Bool, q: Nat, +hq: {Nat.is_lt(q, 2n) == True{} : Bool}) -> {Nat.div(idn(b, hi, q), 2n) == jb(b) : Nat}:
  match b hi q:
    case True{} True{} 0n:
      {==}
    case True{} True{} 1n:
      {==}
    case True{} True{} 2n+ +q2:
      Empty.absurd({Nat.div(idn(True{}, True{}, 2n+q2), 2n) == jb(True{}) : Nat}, N.lt_zero_absurd(q2, hq))
    case True{} False{} 0n:
      {==}
    case True{} False{} 1n:
      {==}
    case True{} False{} 2n+ +q2:
      Empty.absurd({Nat.div(idn(True{}, False{}, 2n+q2), 2n) == jb(True{}) : Nat}, N.lt_zero_absurd(q2, hq))
    case False{} True{} 0n:
      {==}
    case False{} True{} 1n:
      {==}
    case False{} True{} 2n+ +q2:
      Empty.absurd({Nat.div(idn(False{}, True{}, 2n+q2), 2n) == jb(False{}) : Nat}, N.lt_zero_absurd(q2, hq))
    case False{} False{} 0n:
      {==}
    case False{} False{} 1n:
      {==}
    case False{} False{} 2n+ +q2:
      Empty.absurd({Nat.div(idn(False{}, False{}, 2n+q2), 2n) == jb(False{}) : Nat}, N.lt_zero_absurd(q2, hq))

def id_m(b: Bool, hi: Bool, q: Nat, +hq: {Nat.is_lt(q, 2n) == True{} : Bool}) -> {Nat.mod(idn(b, hi, q), 2n) == ES.flip(hi, q) : Nat}:
  match b hi q:
    case True{} True{} 0n:
      {==}
    case True{} True{} 1n:
      {==}
    case True{} True{} 2n+ +q2:
      Empty.absurd({Nat.mod(idn(True{}, True{}, 2n+q2), 2n) == ES.flip(True{}, 2n+q2) : Nat}, N.lt_zero_absurd(q2, hq))
    case True{} False{} 0n:
      {==}
    case True{} False{} 1n:
      {==}
    case True{} False{} 2n+ +q2:
      Empty.absurd({Nat.mod(idn(True{}, False{}, 2n+q2), 2n) == ES.flip(False{}, 2n+q2) : Nat}, N.lt_zero_absurd(q2, hq))
    case False{} True{} 0n:
      {==}
    case False{} True{} 1n:
      {==}
    case False{} True{} 2n+ +q2:
      Empty.absurd({Nat.mod(idn(False{}, True{}, 2n+q2), 2n) == ES.flip(True{}, 2n+q2) : Nat}, N.lt_zero_absurd(q2, hq))
    case False{} False{} 0n:
      {==}
    case False{} False{} 1n:
      {==}
    case False{} False{} 2n+ +q2:
      Empty.absurd({Nat.mod(idn(False{}, False{}, 2n+q2), 2n) == ES.flip(False{}, 2n+q2) : Nat}, N.lt_zero_absurd(q2, hq))

def id_l(b: Bool, hi: Bool, q: Nat, +hq: {Nat.is_lt(q, 2n) == True{} : Bool}) -> {Nat.is_lt(idn(b, hi, q), 4n) == True{} : Bool}:
  match b hi q:
    case True{} True{} 0n:
      {==}
    case True{} True{} 1n:
      {==}
    case True{} True{} 2n+ +q2:
      Empty.absurd({Nat.is_lt(idn(True{}, True{}, 2n+q2), 4n) == True{} : Bool}, N.lt_zero_absurd(q2, hq))
    case True{} False{} 0n:
      {==}
    case True{} False{} 1n:
      {==}
    case True{} False{} 2n+ +q2:
      Empty.absurd({Nat.is_lt(idn(True{}, False{}, 2n+q2), 4n) == True{} : Bool}, N.lt_zero_absurd(q2, hq))
    case False{} True{} 0n:
      {==}
    case False{} True{} 1n:
      {==}
    case False{} True{} 2n+ +q2:
      Empty.absurd({Nat.is_lt(idn(False{}, True{}, 2n+q2), 4n) == True{} : Bool}, N.lt_zero_absurd(q2, hq))
    case False{} False{} 0n:
      {==}
    case False{} False{} 1n:
      {==}
    case False{} False{} 2n+ +q2:
      Empty.absurd({Nat.is_lt(idn(False{}, False{}, 2n+q2), 4n) == True{} : Bool}, N.lt_zero_absurd(q2, hq))
