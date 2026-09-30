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
import ../../../../spec/crypto/secp256k1/schnorr.bend as SS
import ../../../math/number/nt_prime.bend as PM
import ./zm.bend as Z
import ./fld.bend as F
import ./glaw1.bend as G1
import ./glaw2.bend as G2
import ./glaw4.bend as G4
import ./glaw5.bend as G5
import ./pto.bend as PO
import ./afff.bend as AF
import ./aff1.bend as A1
import ./affx.bend as AX
import ./sqrt.bend as SQ
import ./enc.bend as EC
import ./sch_id.bend as SI
import ./sym.bend as S
import ./ident.bend as I
import ./id_enc.bend as IE

# BIP-340 on the group: the generic part, for a prime modulus 1 + mp (with
# the field facts of glaw1.bend), a prime group order 1 + nq and a
# generator g (a point of the group with [1 + nq] g equiv O and g not O).

# ---- the order of g ----

def nz_j(+nq: Nat, +j: Nat, +hj0: {Nat.is_eq(j, 0n) == False{} : Bool}, +hjn: LT(j, 1n+nq)) -> F.NZ(nq, j):
  %Equal.sym(Nat, Nat.mod(j, 1n+nq), j, SQ.mred(nq, j, hjn)) : {Nat.is_eq(_, 0n) == False{} : Bool}
  hj0

def one_g(+mp: Nat, +nq: Nat, +g: CS.SPoint, +i: Nat, +j: Nat, +h: {MN(j, i) == 1n : Nat}) -> {SM(Nat.mod(Nat.mul(i, j), 1n+nq), g) == PA(INF, g) : CS.SPoint}:
  %NA.mul_comm(j, i) : {SM(Nat.mod(_, 1n+nq), g) == PA(INF, g) : CS.SPoint}
  %Equal.sym(Nat, MN(j, i), 1n, h) : {SM(_, g) == PA(INF, g) : CS.SPoint}
  {==}

# [j] g equiv O with 0 < j < n: impossible
def ord_nz(FPD, GD, +j: Nat, +hj0: {Nat.is_eq(j, 0n) == False{} : Bool}, +hjn: LT(j, 1n+nq), +hz: E(SM(j, g), INF)) -> Empty:
  +i = FS.minv(1n+nq, j)
  +sj = SM(j, g)
  +vsj = G4.v_smul(FPA, j, g, vg)
  +vo = G2.v_inf(mp, h21)
  +e1 = Lg.subst(CS.SPoint, t => E(SM(i, sj), t), SM(Nat.mod(Nat.mul(i, j), 1n+nq), g), PA(INF, g), one_g(mp, nq, g, i, j, AF.inv_ok(nq, hq, j, nz_j(nq, j, hj0, hjn))), PO.mul_mod(FPA, i, j, nq, g, vg, hng))
  +e2 = TR(SM(i, sj), SM(i, INF), INF, G4.v_smul(FPA, i, INF, vo), G4.smul_eqv(FPA, i, sj, INF, vsj, vo, hz), PO.smul_inf(FPA, i))
  +e3 = TR(g, PA(INF, g), SM(i, sj), G1.v_add(FPA, INF, g, vo, vg), SY(PA(INF, g), g, G4.unit_l(mp, g)), SY(SM(i, sj), PA(INF, g), e1))
  Lg.true_false(Equal.trans(Bool, True{}, GS.equiv(1n+mp, g, INF), False{}, Equal.sym(Bool, GS.equiv(1n+mp, g, INF), True{}, TR(g, SM(i, sj), INF, G4.v_smul(FPA, i, sj, vsj), e3, e2)), hgo))

# ---- parity of y and p - y ----

def par0_c(+mp: Nat, +hodd: {Nat.mod(1n+mp, 2n) == 1n : Nat}, +rp: Nat, +hr: LT(1n+rp, 1n+mp), +hb: {Nat.mod(1n+rp, 2n) == 1n : Nat}, c: Nat, +hc: {Nat.mod(Nat.sub(mp, rp), 2n) == c : Nat}) -> {Nat.mod(Nat.sub(mp, rp), 2n) == 0n : Nat}:
  match c:
    case 0n:
      hc
    case 1n:
      Empty.absurd({Nat.mod(Nat.sub(mp, rp), 2n) == 0n : Nat}, SQ.par_ne(Nat.sub(mp, rp), 1n+rp, Equal.trans(Nat, Nat.mod(Nat.sub(mp, rp), 2n), 1n, Nat.mod(1n+rp, 2n), hc, Equal.sym(Nat, Nat.mod(1n+rp, 2n), 1n, hb)), Lg.subst(Nat, t => {Nat.mod(t, 2n) == 1n : Nat}, 1n+mp, Nat.add(Nat.sub(mp, rp), 1n+rp), Equal.sym(Nat, Nat.add(Nat.sub(mp, rp), 1n+rp), 1n+mp, SQ.neg_sum(mp, rp, hr)), hodd)))
    case 2n+ +q:
      Empty.absurd({Nat.mod(Nat.sub(mp, rp), 2n) == 0n : Nat}, EC.q_absurd(Nat.sub(mp, rp), q, hc))

# y odd, 0 < y < p, p odd: p - y is even
def par0(+mp: Nat, +hodd: {Nat.mod(1n+mp, 2n) == 1n : Nat}, y: Nat, +hy: LT(y, 1n+mp), +hb: {Nat.mod(y, 2n) == 1n : Nat}) -> {Nat.mod(FS.mneg(1n+mp, y), 2n) == 0n : Nat}:
  match y:
    case 0n:
      Empty.absurd({Nat.mod(FS.mneg(1n+mp, 0n), 2n) == 0n : Nat}, N.zero_succ(0n, hb))
    case 1n+ +rp:
      %Equal.sym(Nat, FS.mneg(1n+mp, 1n+rp), Nat.sub(mp, rp), SQ.neg_pos(mp, rp, hy)) : {Nat.mod(_, 2n) == 0n : Nat}
      par0_c(mp, hodd, rp, hy, hb, Nat.mod(Nat.sub(mp, rp), 2n), {==})

# ---- the even-y representative of [j] g ----

# for a = (x : y : z) equiv [j] g with affine (ax, ay) and b = ay mod 2:
# the point (ax, ey, 1) with ey = ay or p - ay even is what lift_x(ax)
# decompresses to, and it is [j] g or [n - j] g
def EvR(+mp: Nat, +nq: Nat, +g: CS.SPoint, +ax: Nat, +ay: Nat, +j: Nat, +b: Nat) -> Data:
  S.Both<{CS.decompress(1n+mp, ax, 0n) == Some{CS.SPoint{ax, SS.even_b(1n+mp, b, ay), 1n}} : MSP}, S.Both<E(CS.SPoint{ax, SS.even_b(1n+mp, b, ay), 1n}, SM(SS.even_b(1n+nq, b, j), g)), S.Both<V(CS.SPoint{ax, SS.even_b(1n+mp, b, ay), 1n}), S.Both<{Nat.mod(SS.even_b(1n+mp, b, ay), 2n) == 0n : Nat}, LT(SS.even_b(1n+mp, b, ay), 1n+mp)>>>>

def zsum(+nq: Nat, +j: Nat) -> {Nat.mod(Nat.add(j, FS.msub(1n+nq, 0n, j)), 1n+nq) == 0n : Nat}:
  %NA.add_comm(FS.msub(1n+nq, 0n, j), j) : {Nat.mod(_, 1n+nq) == 0n : Nat}
  Z.msub_add(nq, 0n, j)

def evp_c(FPD, SQD, GD, +x: Nat, +y: Nat, +z: Nat, +j: Nat, +va: V(PXYZ), +ha: E(PXYZ, SM(j, g)), +nzz: F.NZ(mp, z), b: Nat, +hb: {Nat.mod(AYV, 2n) == b : Nat}) -> EvR(mp, nq, g, AXV, AYV, j, b):
  match b:
    case 0n:
      +vna = A1.nrm_v(mp, hp, x, y, z, G1.v_onc(mp, x, y, z, va), G1.v_nz(mp, x, y, z, va), nzz)
      +hay = NR.dm_lt(mp, Nat.mul(y, FS.minv(1n+mp, z)))
      S.Both{Lg.subst(Nat, t => {CS.decompress(1n+mp, AXV, t) == Some{NAP} : MSP}, Nat.mod(AYV, 2n), 0n, hb, EC.decomp(DEC, AXV, AYV, hay, EC.aff_on(mp, hp, x, y, z, va, nzz))), S.Both{TR(NAP, PXYZ, SM(j, g), va, SY(PXYZ, NAP, A1.nrm_e(mp, hp, x, y, z, nzz)), ha), S.Both{vna, S.Both{hb, hay}}}}
    case 1n:
      +vna = A1.nrm_v(mp, hp, x, y, z, G1.v_onc(mp, x, y, z, va), G1.v_nz(mp, x, y, z, va), nzz)
      +hay = NR.dm_lt(mp, Nat.mul(y, FS.minv(1n+mp, z)))
      +hey = NR.dm_lt(mp, Nat.sub(Nat.add(0n, 1n+mp), Nat.mod(AYV, 1n+mp)))
      +hp0 = par0(mp, hodd, AYV, hay, hb)
      +hon2 = Lg.subst(Nat, t => {Nat.is_eq(t, CS.rhs(1n+mp, AXV)) == True{} : Bool}, MP(AYV, AYV), MP(EYV, EYV), Equal.sym(Nat, MP(EYV, EYV), MP(AYV, AYV), I.both_red(mp, Nat.mul(EYV, EYV), Nat.mul(AYV, AYV), IE.neg_sq(mp, AYV, 0n))), EC.aff_on(mp, hp, x, y, z, va, nzz))
      +a1 = SM(j, g)
      +b1 = SM(FS.mneg(1n+nq, j), g)
      +va1 = G4.v_smul(FPA, j, g, vg)
      +vb1 = G4.v_smul(FPA, FS.mneg(1n+nq, j), g, vg)
      +hsum = Lg.subst(Nat, t => E(PA(a1, b1), SM(t, g)), Nat.mod(Nat.add(j, FS.mneg(1n+nq, j)), 1n+nq), 0n, zsum(nq, j), PO.add_mod(FPA, j, FS.mneg(1n+nq, j), nq, g, vg, hng))
      +hun = G5.inv_unique(FPA, a1, b1, va1, vb1, hsum)
      +hne = G5.e_neg(mp, NAP, a1, TR(NAP, PXYZ, a1, va, SY(PXYZ, NAP, A1.nrm_e(mp, hp, x, y, z, nzz)), ha))
      S.Both{Lg.subst(Nat, t => {CS.decompress(1n+mp, AXV, t) == Some{NEP} : MSP}, Nat.mod(EYV, 2n), 0n, hp0, EC.decomp(DEC, AXV, EYV, hey, hon2)), S.Both{TR(NEG(NAP), NEG(a1), b1, G2.v_neg(mp, a1, va1), hne, SY(b1, NEG(a1), hun)), S.Both{G2.v_neg(mp, NAP, vna), S.Both{hp0, hey}}}}
    case 2n+ +q:
      Empty.absurd(EvR(mp, nq, g, AXV, AYV, j, 2n+q), EC.q_absurd(AYV, q, hb))

def nzz_c(FPD, GD, +x: Nat, +y: Nat, +z: Nat, +j: Nat, +hj0: {Nat.is_eq(j, 0n) == False{} : Bool}, +hjn: LT(j, 1n+nq), +va: V(PXYZ), +ha: E(PXYZ, SM(j, g)), c: Bool, +hc: {Nat.is_eq(Nat.mod(z, 1n+mp), 0n) == c : Bool}) -> F.NZ(mp, z):
  match c:
    case False{}:
      hc
    case True{}:
      Empty.absurd(F.NZ(mp, z), ord_nz(FPA, GA, j, hj0, hjn, TR(SM(j, g), PXYZ, INF, va, SY(PXYZ, SM(j, g), ha), AX.z0_eqv(mp, hp, x, y, z, va, N.eq_from_is_eq(Nat.mod(z, 1n+mp), 0n, hc)))))

# a equiv [j] g with 0 < j < n: its z is nonzero
def nzz(FPD, GD, +x: Nat, +y: Nat, +z: Nat, +j: Nat, +hj0: {Nat.is_eq(j, 0n) == False{} : Bool}, +hjn: LT(j, 1n+nq), +va: V(PXYZ), +ha: E(PXYZ, SM(j, g))) -> F.NZ(mp, z):
  nzz_c(FPA, GA, x, y, z, j, hj0, hjn, va, ha, Nat.is_eq(Nat.mod(z, 1n+mp), 0n), {==})

def evp(FPD, SQD, GD, a: CS.SPoint, +j: Nat, +hj0: {Nat.is_eq(j, 0n) == False{} : Bool}, +hjn: LT(j, 1n+nq), +va: V(a), +ha: E(a, SM(j, g))) -> EvR(mp, nq, g, CS.aff_x(CS.to_affine(1n+mp, a)), CS.aff_y(CS.to_affine(1n+mp, a)), j, Nat.mod(CS.aff_y(CS.to_affine(1n+mp, a)), 2n)):
  match a:
    case CS.SPoint{+x, +y, +z}:
      evp_c(FPA, SQA, GA, x, y, z, j, va, ha, nzz(FPA, GA, x, y, z, j, hj0, hjn, va, ha), Nat.mod(AYV, 2n), {==})

# ---- the verification equation ----

def inf_c(+mp: Nat, +z: Nat, +nz: F.NZ(mp, z), c: Bool, +hc: {Nat.is_eq(z, 0n) == c : Bool}) -> {Nat.is_eq(z, 0n) == False{} : Bool}:
  match c:
    case False{}:
      hc
    case True{}:
      Empty.absurd({Nat.is_eq(z, 0n) == False{} : Bool}, F.nz_absurd(mp, z, nz, Equal.cong(Nat, Nat, t => Nat.mod(t, 1n+mp), z, 0n, N.eq_from_is_eq(z, 0n, hc))))

def chk(+rx: Nat, +ey: Nat, +hev: {Nat.mod(ey, 2n) == 0n : Nat}) -> {SS.check_r(rx, False{}, CS.SAffine{rx, ey}) == True{} : Bool}:
  %Equal.sym(Nat, Nat.mod(ey, 2n), 0n, hev) : {Bool.and(True{}, Bool.and(Nat.is_eq(_, 0n), Nat.is_eq(rx, rx))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(rx, rx), True{}, N.is_eq_refl(rx)) : {Bool.and(True{}, Bool.and(True{}, _)) == True{} : Bool}
  {==}

# a point equiv (rx : ey : 1) with ey even passes BIP-340's check of R
def fin(+mp: Nat, +hp: PM.Prime(1n+mp), +h21: LT(21n, 1n+mp), rr: CS.SPoint, +rx: Nat, +ey: Nat, +vr: V(rr), +ve: V(CS.SPoint{rx, ey, 1n}), +h: E(rr, CS.SPoint{rx, ey, 1n}), +hrx: LT(rx, 1n+mp), +hey: LT(ey, 1n+mp), +hev: {Nat.mod(ey, 2n) == 0n : Nat}) -> {SS.check_r(rx, CS.is_inf(rr), CS.to_affine(1n+mp, rr)) == True{} : Bool}:
  match rr:
    case CS.SPoint{+x, +y, +z}:
      +nzr = AX.nz_eqv(mp, hp, rx, ey, 1n, x, y, z, vr, AF.one_nz(mp, h21), SY(PXYZ, CS.SPoint{rx, ey, 1n}, h))
      %Equal.sym(Bool, Nat.is_eq(z, 0n), False{}, inf_c(mp, z, nzr, Nat.is_eq(z, 0n), {==})) : {SS.check_r(rx, _, CS.to_affine(1n+mp, PXYZ)) == True{} : Bool}
      %Equal.sym(CS.SAffine, CS.to_affine(1n+mp, PXYZ), CS.SAffine{rx, ey}, Equal.trans(CS.SAffine, CS.to_affine(1n+mp, PXYZ), CS.to_affine(1n+mp, CS.SPoint{rx, ey, 1n}), CS.SAffine{rx, ey}, AX.ta_eqv(mp, hp, x, y, z, rx, ey, 1n, vr, ve, nzr, AF.one_nz(mp, h21), h), EC.aff_one(mp, hp, rx, ey, hrx, hey))) : {SS.check_r(rx, False{}, _) == True{} : Bool}
      chk(rx, ey, hev)

def sk_eq(+nq: Nat, +k: Nat, +e: Nat, +d: Nat, +hk: LT(k, 1n+nq)) -> {AN(AN(k, MN(e, d)), MN(FS.mneg(1n+nq, e), d)) == k : Nat}:
  Equal.trans(Nat, AN(AN(k, MN(e, d)), MN(FS.mneg(1n+nq, e), d)), Nat.mod(k, 1n+nq), k, I.both_red(nq, Nat.add(AN(k, MN(e, d)), MN(FS.mneg(1n+nq, e), d)), k, Equal.trans(Nat, Nat.mod(AN(AN(k, MN(e, d)), MN(FS.mneg(1n+nq, e), d)), 1n+nq), Nat.mod(k, 1n+nq), Nat.mod(Nat.mod(k, 1n+nq), 1n+nq), SI.sc_k(nq, k, e, d), Equal.sym(Nat, Nat.mod(Nat.mod(k, 1n+nq), 1n+nq), Nat.mod(k, 1n+nq), NR.mod_mod(nq, k)))), SQ.mred(nq, k, hk))

# R' = [s] g + [n - e] P' with s = k + e d (mod n), P' equiv [d] g, and
# (rx : ey : 1) equiv [k] g with ey even: BIP-340's check of R' passes
def vrf(FPD, +one: Nat, +h1: {one == 1n : Nat}, +nq: Nat, +hn256: {Nat.is_le(1n+nq, C.shift(256n, one)) == True{} : Bool}, +g: CS.SPoint, +vg: V(g), +hng: E(SM(1n+nq, g), INF), +d: Nat, +k: Nat, +e: Nat, +pp: CS.SPoint, +rx: Nat, +ey: Nat, +hk: LT(k, 1n+nq), +vp: V(pp), +hpp: E(pp, SM(d, g)), +ve: V(CS.SPoint{rx, ey, 1n}), +hre: E(CS.SPoint{rx, ey, 1n}, SM(k, g)), +hrx: LT(rx, 1n+mp), +hey: LT(ey, 1n+mp), +hev: {Nat.mod(ey, 2n) == 0n : Nat}) -> {SS.check_r(rx, CS.is_inf(PA(PMU(AN(k, MN(e, d)), g), PMU(FS.mneg(1n+nq, e), pp))), CS.to_affine(1n+mp, PA(PMU(AN(k, MN(e, d)), g), PMU(FS.mneg(1n+nq, e), pp)))) == True{} : Bool}:
  +sv = AN(k, MN(e, d))
  +ne = FS.mneg(1n+nq, e)
  +u1 = PMU(sv, g)
  +u2 = PMU(ne, pp)
  +vu1 = G4.pmul_valid(FPA, sv, g, vg)
  +vu2 = G4.pmul_valid(FPA, ne, pp, vp)
  +vs1 = G4.v_smul(FPA, sv, g, vg)
  +w2 = SM(MN(ne, d), g)
  +vw2 = G4.v_smul(FPA, MN(ne, d), g, vg)
  +vdg = G4.v_smul(FPA, d, g, vg)
  +t1 = G4.pmul_smul(FPA, sv, g, vg, EC.fit(one, h1, nq, hn256, sv, NR.dm_lt(nq, Nat.add(k, MN(e, d)))))
  +t2a = G4.pmul_smul(FPA, ne, pp, vp, EC.fit(one, h1, nq, hn256, ne, NR.dm_lt(nq, Nat.sub(Nat.add(0n, 1n+nq), Nat.mod(e, 1n+nq)))))
  +t2b = G4.smul_eqv(FPA, ne, pp, SM(d, g), vp, vdg, hpp)
  +t2c = PO.mul_mod(FPA, ne, d, nq, g, vg, hng)
  +t2 = TR(u2, SM(ne, pp), w2, G4.v_smul(FPA, ne, pp, vp), t2a, TR(SM(ne, pp), SM(ne, SM(d, g)), w2, G4.v_smul(FPA, ne, SM(d, g), vdg), t2b, t2c))
  +t3 = TR(PA(u1, u2), PA(SM(sv, g), u2), PA(SM(sv, g), w2), G1.v_add(FPA, SM(sv, g), u2, vs1, vu2), G2.e_add_l(mp, hp, u1, SM(sv, g), u2, vu1, vs1, t1), G2.e_add_r(mp, hp, SM(sv, g), u2, w2, vu2, vw2, t2))
  +t4 = Lg.subst(Nat, t => E(PA(SM(sv, g), w2), SM(t, g)), AN(sv, MN(ne, d)), k, sk_eq(nq, k, e, d, hk), PO.add_mod(FPA, sv, MN(ne, d), nq, g, vg, hng))
  +vkg = G4.v_smul(FPA, k, g, vg)
  +t5 = TR(PA(u1, u2), PA(SM(sv, g), w2), SM(k, g), G1.v_add(FPA, SM(sv, g), w2, vs1, vw2), t3, t4)
  fin(mp, hp, h21, PA(u1, u2), rx, ey, G1.v_add(FPA, u1, u2, vu1, vu2), ve, TR(PA(u1, u2), SM(k, g), CS.SPoint{rx, ey, 1n}, vkg, t5, SY(CS.SPoint{rx, ey, 1n}, SM(k, g), hre)), hrx, hey, hev)
