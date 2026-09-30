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
import ../../../math/number/nt_fld.bend as FD
import ./zm.bend as Z
import ./fld.bend as F
import ./nc.bend as NC
import ./glaw1.bend as G1
import ./glaw2.bend as G2
import ./glaw4.bend as G4
import ./glaw5.bend as G5
import ./pto.bend as PO
import ./aff1.bend as A1
import ./affx.bend as AX
import ./enc.bend as EC
import ./ecdn.bend as EN

# The group side of ECDSA, for a modulus 1 + mp with the field facts of
# glaw1.bend, a point g of the group with [n] g equiv O for a prime
# n = 1 + nm <= 2^256 and g not equiv O (so g has order exactly n):
# [u1] g + [u2] A for A equiv [ka] g is [(u1 + u2 ka) mod n] g, a multiple
# [k] g with k != 0 mod n is not the point at infinity, and the two checks
# of verification and recovery on such sums.

def pz(a: CS.SPoint) -> Nat:
  match a:
    case CS.SPoint{x, y, z}:
      z

# (X / Z : Y / Z : 1)
def nrm(+p: Nat, a: CS.SPoint) -> CS.SPoint:
  match a:
    case CS.SPoint{x, y, +z}:
      CS.SPoint{FS.mmul(p, x, FS.minv(p, z)), FS.mmul(p, y, FS.minv(p, z)), 1n}

# ---- the lemmas of affx.bend and aff1.bend on points ----

def w_z0(+mp: Nat, +hp: PM.Prime(1n+mp), a: CS.SPoint, +va: V(a), +hz: {DP(pz(a)) == 0n : Nat}) -> E(a, INF):
  match a:
    case CS.SPoint{+x, +y, +z}:
      AX.z0_eqv(mp, hp, x, y, z, va, hz)

def w_ta(+mp: Nat, +hp: PM.Prime(1n+mp), a: CS.SPoint, b: CS.SPoint, +va: V(a), +vb: V(b), +na: NZP(pz(a)), +nb: NZP(pz(b)), +h: E(a, b)) -> {TA(a) == TA(b) : CS.SAffine}:
  match a b:
    case CS.SPoint{+x1, +y1, +z1} CS.SPoint{+x2, +y2, +z2}:
      AX.ta_eqv(mp, hp, x1, y1, z1, x2, y2, z2, va, vb, na, nb, h)

def w_nz(+mp: Nat, +hp: PM.Prime(1n+mp), a: CS.SPoint, b: CS.SPoint, +vb: V(b), +na: NZP(pz(a)), +h: E(a, b)) -> NZP(pz(b)):
  match a b:
    case CS.SPoint{+x1, +y1, +z1} CS.SPoint{+x2, +y2, +z2}:
      AX.nz_eqv(mp, hp, x1, y1, z1, x2, y2, z2, vb, na, h)

def w_negx(+mp: Nat, a: CS.SPoint) -> {CS.aff_x(TA(NG(a))) == CS.aff_x(TA(a)) : Nat}:
  match a:
    case CS.SPoint{+x, +y, +z}:
      AX.neg_ax(mp, x, y, z)

def w_negz(+mp: Nat, a: CS.SPoint, +na: NZP(pz(a))) -> NZP(pz(NG(a))):
  match a:
    case CS.SPoint{x, y, z}:
      na

def w_inf(+mp: Nat, a: CS.SPoint, +na: NZP(pz(a))) -> {CS.is_inf(a) == False{} : Bool}:
  match a:
    case CS.SPoint{x, y, +z}:
      EN.nz_ne0(mp, z, na)

def w_nrm_v(+mp: Nat, +hp: PM.Prime(1n+mp), a: CS.SPoint, +va: V(a), +na: NZP(pz(a))) -> V(nrm(1n+mp, a)):
  match a:
    case CS.SPoint{+x, +y, +z}:
      A1.nrm_v(mp, hp, x, y, z, G1.v_onc(mp, x, y, z, va), G1.v_nz(mp, x, y, z, va), na)

def w_nrm_e(+mp: Nat, +hp: PM.Prime(1n+mp), a: CS.SPoint, +na: NZP(pz(a))) -> E(a, nrm(1n+mp, a)):
  match a:
    case CS.SPoint{+x, +y, +z}:
      A1.nrm_e(mp, hp, x, y, z, na)

def nrm_z(+mp: Nat, +h21: {Nat.is_lt(21n, 1n+mp) == True{} : Bool}, a: CS.SPoint) -> NZP(pz(nrm(1n+mp, a))):
  match a:
    case CS.SPoint{x, y, z}:
      NC.nz_small(mp, 0n, G2.lt1(mp, h21))

# ---- multiples of g ----

def fitn(+nm: Nat, OD, +x: Nat, +hx: LTN(x)) -> {C.fits(256n, x) == True{} : Bool}:
  EC.fit(one, h1, nm, hn256, x, hx)

def ord_e1(FPD, NQD, GD, +k: Nat, +nzk: NZN(k)) -> E(SM(IN(k), SM(k, g)), SM(1n, g)):
  %ETR(Nat, DN(Nat.mul(IN(k), k)), DN(Nat.mul(k, IN(k))), 1n, Equal.cong(Nat, Nat, z => Nat.mod(z, 1n+nm), Nat.mul(IN(k), k), Nat.mul(k, IN(k)), NA.mul_comm(IN(k), k)), FD.inv_mod(1n+nm, hq, k, nzk)) : {GS.equiv(1n+mp, SM(IN(k), SM(k, g)), GS.smul(1n+mp, _, g)) == True{} : Bool}
  PO.mul_mod(FPA, IN(k), k, nm, g, vg, hng)

# [k] g equiv O with k != 0 mod n: impossible
def ord(FPD, NQD, GD, +k: Nat, +nzk: NZN(k), +h: E(SM(k, g), INF)) -> Empty:
  +j = IN(k)
  +vk = G4.v_smul(FPA, k, g, vg)
  +vo = G2.v_inf(mp, h21)
  Lg.true_false(ETR(Bool, True{}, GS.equiv(1n+mp, g, INF), False{}, ESYM(Bool, GS.equiv(1n+mp, g, INF), True{},
    TR(g, SM(1n, g), INF, G4.v_smul(FPA, 1n, g, vg), SY(SM(1n, g), g, G4.unit_l(mp, g)),
      TR(SM(1n, g), SM(j, SM(k, g)), INF, G4.v_smul(FPA, j, SM(k, g), vk), SY(SM(j, SM(k, g)), SM(1n, g), ord_e1(FPA, NQA, GA, k, nzk)),
        TR(SM(j, SM(k, g)), SM(j, INF), INF, G4.v_smul(FPA, j, INF, vo), G4.smul_eqv(FPA, j, SM(k, g), INF, vk, vo, h), G5.smul_inf(FPA, j))))), hgo))

def knz_c(FPD, NQD, GD, +kp: CS.SPoint, +k: Nat, +nzk: NZN(k), +vkp: V(kp), +hkp: E(kp, SM(k, g)), c: Bool, +hc: {Nat.is_eq(DP(pz(kp)), 0n) == c : Bool}) -> NZP(pz(kp)):
  match c:
    case False{}:
      hc
    case True{}:
      Empty.absurd(NZP(pz(kp)), ord(FPA, NQA, GA, k, nzk, TR(SM(k, g), kp, INF, vkp, SY(kp, SM(k, g), hkp), w_z0(mp, hp, kp, vkp, N.eq_from_is_eq(DP(pz(kp)), 0n, hc)))))

# a point equiv [k] g, k != 0 mod n, has Z != 0
def knz(FPD, NQD, GD, +kp: CS.SPoint, +k: Nat, +nzk: NZN(k), +vkp: V(kp), +hkp: E(kp, SM(k, g))) -> NZP(pz(kp)):
  knz_c(FPA, NQA, GA, kp, k, nzk, vkp, hkp, Nat.is_eq(DP(pz(kp)), 0n), {==})

# [u1] g + [u2] A equiv [(u1 + u2 ka) mod n] g for A equiv [ka] g
def lin2(FPD, NQD, GD, OD, +u1: Nat, +u2: Nat, +a: CS.SPoint, +ka: Nat, +hu1: LTN(u1), +hu2: LTN(u2), +va: V(a), +ha: E(a, SM(ka, g))) -> E(PA(PM(u1, g), PM(u2, a)), SM(AN(u1, MN(u2, ka)), g)):
  +t1 = PM(u1, g)
  +s1 = SM(u1, g)
  +t2 = PM(u2, a)
  +s2 = SM(u2, a)
  +s3 = SM(u2, SM(ka, g))
  +s4 = SM(MN(u2, ka), g)
  +vt1 = G4.pmul_valid(FPA, u1, g, vg)
  +vs1 = G4.v_smul(FPA, u1, g, vg)
  +vt2 = G4.pmul_valid(FPA, u2, a, va)
  +vs2 = G4.v_smul(FPA, u2, a, va)
  +vka = G4.v_smul(FPA, ka, g, vg)
  +vs3 = G4.v_smul(FPA, u2, SM(ka, g), vka)
  +vs4 = G4.v_smul(FPA, MN(u2, ka), g, vg)
  +e1 = G4.pmul_smul(FPA, u1, g, vg, fitn(nm, OA, u1, hu1))
  +e2 = G4.pmul_smul(FPA, u2, a, va, fitn(nm, OA, u2, hu2))
  +e3 = G4.smul_eqv(FPA, u2, a, SM(ka, g), va, vka, ha)
  +e4 = PO.mul_mod(FPA, u2, ka, nm, g, vg, hng)
  +e24 = TR(t2, s2, s4, vs2, e2, TR(s2, s3, s4, vs3, e3, e4))
  TR(PA(t1, t2), PA(s1, t2), SM(AN(u1, MN(u2, ka)), g), G1.v_add(FPA, s1, t2, vs1, vt2), G2.e_add_l(mp, hp, t1, s1, t2, vt1, vs1, e1),
    TR(PA(s1, t2), PA(s1, s4), SM(AN(u1, MN(u2, ka)), g), G1.v_add(FPA, s1, s4, vs1, vs4), G2.e_add_r(mp, hp, s1, t2, s4, vt2, vs4, e24),
      PO.add_mod(FPA, u1, MN(u2, ka), nm, g, vg, hng)))

def negk_h(FPD, NQD, GD, +k: Nat) -> E(PA(SM(k, g), SM(NN(k), g)), INF):
  %ETR(Nat, DN(Nat.add(k, NN(k))), DN(Nat.add(NN(k), k)), 0n, Equal.cong(Nat, Nat, z => Nat.mod(z, 1n+nm), Nat.add(k, NN(k)), Nat.add(NN(k), k), NA.add_comm(k, NN(k))), Z.msub_add(nm, 0n, k)) : {GS.equiv(1n+mp, PA(SM(k, g), SM(NN(k), g)), GS.smul(1n+mp, _, g)) == True{} : Bool}
  PO.add_mod(FPA, k, NN(k), nm, g, vg, hng)

# [-k] g equiv -[k] g
def negk(FPD, NQD, GD, +k: Nat) -> E(SM(NN(k), g), NG(SM(k, g))):
  G5.inv_unique(FPA, SM(k, g), SM(NN(k), g), G4.v_smul(FPA, k, g, vg), G4.v_smul(FPA, NN(k), g, vg), negk_h(FPA, NQA, GA, k))

# ---- the check of verification ----

# R equiv [k] g: R is not infinity and has the affine x of any K equiv [k] g
def rr_pos(FPD, NQD, GD, +rr: CS.SPoint, +kp: CS.SPoint, +k: Nat, +nzk: NZN(k), +vkp: V(kp), +hkp: E(kp, SM(k, g)), +vrr: V(rr), +hrr: E(rr, SM(k, g))) -> {Bool.and(Bool.not(CS.is_inf(rr)), Nat.is_eq(DN(CS.aff_x(TA(rr))), DN(CS.aff_x(TA(kp))))) == True{} : Bool}:
  +nk = knz(FPA, NQA, GA, kp, k, nzk, vkp, hkp)
  +nr = knz(FPA, NQA, GA, rr, k, nzk, vrr, hrr)
  %ESYM(Bool, CS.is_inf(rr), False{}, w_inf(mp, rr, nr)) : {Bool.and(Bool.not(_), Nat.is_eq(DN(CS.aff_x(TA(rr))), DN(CS.aff_x(TA(kp))))) == True{} : Bool}
  %ESYM(CS.SAffine, TA(rr), TA(kp), w_ta(mp, hp, rr, kp, vrr, vkp, nr, nk, TR(rr, SM(k, g), kp, G4.v_smul(FPA, k, g, vg), hrr, SY(kp, SM(k, g), hkp)))) : {Nat.is_eq(DN(CS.aff_x(_)), DN(CS.aff_x(TA(kp)))) == True{} : Bool}
  N.is_eq_refl(DN(CS.aff_x(TA(kp))))

# R equiv [-k] g: the same
def rr_neg(FPD, NQD, GD, +rr: CS.SPoint, +kp: CS.SPoint, +k: Nat, +nzk: NZN(k), +vkp: V(kp), +hkp: E(kp, SM(k, g)), +vrr: V(rr), +hrr: E(rr, SM(NN(k), g))) -> {Bool.and(Bool.not(CS.is_inf(rr)), Nat.is_eq(DN(CS.aff_x(TA(rr))), DN(CS.aff_x(TA(kp))))) == True{} : Bool}:
  +nk = knz(FPA, NQA, GA, kp, k, nzk, vkp, hkp)
  +vsk = G4.v_smul(FPA, k, g, vg)
  +vnk = G2.v_neg(mp, kp, vkp)
  +hn = TR(rr, SM(NN(k), g), NG(kp), G4.v_smul(FPA, NN(k), g, vg), hrr, TR(SM(NN(k), g), NG(SM(k, g)), NG(kp), G2.v_neg(mp, SM(k, g), vsk), negk(FPA, NQA, GA, k), G5.e_neg(mp, SM(k, g), kp, SY(kp, SM(k, g), hkp))))
  +nn = w_negz(mp, kp, nk)
  +nr = w_nz(mp, hp, NG(kp), rr, vrr, nn, SY(rr, NG(kp), hn))
  %ESYM(Bool, CS.is_inf(rr), False{}, w_inf(mp, rr, nr)) : {Bool.and(Bool.not(_), Nat.is_eq(DN(CS.aff_x(TA(rr))), DN(CS.aff_x(TA(kp))))) == True{} : Bool}
  %ESYM(CS.SAffine, TA(rr), TA(NG(kp)), w_ta(mp, hp, rr, NG(kp), vrr, vnk, nr, nn, hn)) : {Nat.is_eq(DN(CS.aff_x(_)), DN(CS.aff_x(TA(kp)))) == True{} : Bool}
  %ESYM(Nat, CS.aff_x(TA(NG(kp))), CS.aff_x(TA(kp)), w_negx(mp, kp)) : {Nat.is_eq(DN(_), DN(CS.aff_x(TA(kp)))) == True{} : Bool}
  N.is_eq_refl(DN(CS.aff_x(TA(kp))))
