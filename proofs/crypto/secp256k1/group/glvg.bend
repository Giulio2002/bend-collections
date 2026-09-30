import Base
import ../../../lib/logic.bend as Lg
import ../../../../spec/crypto/secp256k1/field.bend as FS
import ../../../../spec/crypto/secp256k1/curve.bend as CS
import ../../../../spec/crypto/secp256k1/group.bend as GS
import ../../../math/number/nt_prime.bend as PM
import ./bnx.bend as X
import ./certb.bend as CB
import ./gfp.bend as GF
import ./glvp.bend as GP
import ./glv.bend as GLV
import ./glvc.bend as GC

# The GLV law of secp256k1 on the multiples of G: with
# beta = X.bvalo(one, GC.betal()) and lambda = X.bvalo(one, GC.laml())
# (beta^3 == 1 in GF(p): GC.beta_cube; lambda^2 + lambda + 1 == K n:
# GC.lam_eq), phi([k] G) equiv [lambda] ([k] G) for every k. Hypotheses:
# hp, hc (the facts about p of laws_group.bend), hg (G is a point of the
# group: ptv.bend, g_valid) and hf (phi(G) equiv [lambda] G: glvf.bend,
# phi_g).
#
# NOT proved: phi(A) equiv [lambda] A for an arbitrary point A of the group
# (it needs #E(F_p) = n, i.e. that every point is a multiple of G).

def glv(+one: Nat, +h1: {one == 1n : Nat}, +hp: PM.Prime(FS.prime(one)), +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}, +hg: {GS.valid(FS.prime(one), CS.g(one)) == True{} : Bool}, +hf: {GS.equiv(FS.prime(one), GP.phi(FS.prime(one), X.bvalo(one, GC.betal()), CS.g(one)), GS.smul(FS.prime(one), X.bvalo(one, GC.laml()), CS.g(one))) == True{} : Bool}, +k: Nat) -> {GS.equiv(FS.prime(one), GP.phi(FS.prime(one), X.bvalo(one, GC.betal()), GS.smul(FS.prime(one), k, CS.g(one))), GS.smul(FS.prime(one), X.bvalo(one, GC.laml()), GS.smul(FS.prime(one), k, CS.g(one)))) == True{} : Bool}:
  Lg.subst(Nat, q => {GS.equiv(q, GP.phi(q, X.bvalo(one, GC.betal()), GS.smul(q, k, CS.g(one))), GS.smul(q, X.bvalo(one, GC.laml()), GS.smul(q, k, CS.g(one)))) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)),
    GLV.glv_main(GF.pm(one), GF.hp_m(one, h1, hp), CB.p_mod3(one, h1), GF.hc_m(one, h1, hc), GF.h21_m(one, h1), X.bvalo(one, GC.betal()), GC.beta_cube_m(one, h1), X.bvalo(one, GC.laml()), CS.g(one), Lg.subst(Nat, q => {GS.valid(q, CS.g(one)) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), hg), Lg.subst(Nat, q => {GS.equiv(q, GP.phi(q, X.bvalo(one, GC.betal()), CS.g(one)), GS.smul(q, X.bvalo(one, GC.laml()), CS.g(one))) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), hf), k))
