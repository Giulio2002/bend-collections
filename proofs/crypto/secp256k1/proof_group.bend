import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/secp256k1/field.bend as FS
import ../../../spec/crypto/secp256k1/curve.bend as CS
import ../../../spec/crypto/secp256k1/group.bend as GS
import ../../lib/logic.bend as Lg
import ../../math/number/nt_prime.bend as PM
import ./laws_group.bend as Laws
import ./group/gfp.bend as GF
import ./group/glaw1.bend as G1
import ./group/glaw2.bend as G2
import ./group/glaw3.bend as G3
import ./group/glaw4.bend as G4
import ./group/certb.bend as CB

# The group law of secp256k1 (laws_group.bend):
# `bend proofs/crypto/secp256k1/proof_group.bend`. Each clause is the lemma
# of group/glaw*.bend for the modulus 1 + pm, moved to FS.prime(one) with
# FS.prime(one) == 1 + pm (group/certb.bend).

def Laws.Group.closed(one, h1, hp, hc, a, b, va, vb):
  Lg.subst(Nat, p => {GS.valid(p, CS.padd(p, a, b)) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), G1.v_add(GF.pm(one), GF.hp_m(one, h1, hp), CB.p_mod3(one, h1), GF.hc_m(one, h1, hc), GF.h21_m(one, h1), a, b, Lg.subst(Nat, p => {GS.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va), Lg.subst(Nat, p => {GS.valid(p, b) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), vb)))

def Laws.Group.infinity(one, h1, hp, hc):
  Lg.subst(Nat, p => {GS.valid(p, CS.infinity()) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), G2.v_inf(GF.pm(one), GF.h21_m(one, h1)))

def Laws.Group.neg_closed(one, h1, hp, hc, a, va):
  Lg.subst(Nat, p => {GS.valid(p, GS.neg(p, a)) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), G2.v_neg(GF.pm(one), a, Lg.subst(Nat, p => {GS.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va)))

def Laws.Group.commutative(one, h1, hp, hc, a, b):
  Lg.subst(Nat, p => {CS.padd(p, a, b) == CS.padd(p, b, a) : CS.SPoint}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), G1.add_comm(GF.pm(one), a, b))

def Laws.Group.associative(one, h1, hp, hc, a, b, c, va, vb, vc):
  Lg.subst(Nat, p => {GS.equiv(p, CS.padd(p, CS.padd(p, a, b), c), CS.padd(p, a, CS.padd(p, b, c))) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), G3.assoc(GF.pm(one), a, b, c, Lg.subst(Nat, p => {GS.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va), Lg.subst(Nat, p => {GS.valid(p, b) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), vb), Lg.subst(Nat, p => {GS.valid(p, c) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), vc)))

def Laws.Group.identity(one, h1, hp, hc, a):
  Lg.subst(Nat, p => {GS.equiv(p, CS.padd(p, a, CS.infinity()), a) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), G2.unit(GF.pm(one), a))

def Laws.Group.inverse(one, h1, hp, hc, a):
  Lg.subst(Nat, p => {GS.equiv(p, CS.padd(p, a, GS.neg(p, a)), CS.infinity()) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), G2.inv(GF.pm(one), a))

def Laws.Group.double(one, h1, hp, hc, a, va):
  Lg.subst(Nat, p => {CS.pdbl(p, a) == CS.padd(p, a, a) : CS.SPoint}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), G2.dbl(GF.pm(one), a, Lg.subst(Nat, p => {GS.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va)))

def Laws.Equiv.refl(one, h1, hp, hc, a):
  Lg.subst(Nat, p => {GS.equiv(p, a, a) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), G2.e_refl(GF.pm(one), a))

def Laws.Equiv.sym(one, h1, hp, hc, a, b, h):
  Lg.subst(Nat, p => {GS.equiv(p, b, a) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), G2.e_sym(GF.pm(one), a, b, Lg.subst(Nat, p => {GS.equiv(p, a, b) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), h)))

def Laws.Equiv.trans(one, h1, hp, hc, a, b, c, vb, hab, hbc):
  Lg.subst(Nat, p => {GS.equiv(p, a, c) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), G2.e_trans(GF.pm(one), GF.hp_m(one, h1, hp), a, b, c, Lg.subst(Nat, p => {GS.valid(p, b) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), vb), Lg.subst(Nat, p => {GS.equiv(p, a, b) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), hab), Lg.subst(Nat, p => {GS.equiv(p, b, c) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), hbc)))

def Laws.Equiv.add_left(one, h1, hp, hc, a, a2, b, va, va2, h):
  Lg.subst(Nat, p => {GS.equiv(p, CS.padd(p, a, b), CS.padd(p, a2, b)) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), G2.e_add_l(GF.pm(one), GF.hp_m(one, h1, hp), a, a2, b, Lg.subst(Nat, p => {GS.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va), Lg.subst(Nat, p => {GS.valid(p, a2) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va2), Lg.subst(Nat, p => {GS.equiv(p, a, a2) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), h)))

def Laws.Equiv.add_right(one, h1, hp, hc, a, b, b2, vb, vb2, h):
  Lg.subst(Nat, p => {GS.equiv(p, CS.padd(p, a, b), CS.padd(p, a, b2)) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), G2.e_add_r(GF.pm(one), GF.hp_m(one, h1, hp), a, b, b2, Lg.subst(Nat, p => {GS.valid(p, b) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), vb), Lg.subst(Nat, p => {GS.valid(p, b2) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), vb2), Lg.subst(Nat, p => {GS.equiv(p, b, b2) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), h)))

def Laws.Scalar.closed(one, h1, hp, hc, k, a, va):
  Lg.subst(Nat, p => {GS.valid(p, GS.smul(p, k, a)) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), G4.v_smul(GF.pm(one), GF.hp_m(one, h1, hp), CB.p_mod3(one, h1), GF.hc_m(one, h1, hc), GF.h21_m(one, h1), k, a, Lg.subst(Nat, p => {GS.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va)))

def Laws.Scalar.add(one, h1, hp, hc, j, k, a, va):
  Lg.subst(Nat, p => {GS.equiv(p, GS.smul(p, Nat.add(j, k), a), CS.padd(p, GS.smul(p, j, a), GS.smul(p, k, a))) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), G4.smul_add(GF.pm(one), GF.hp_m(one, h1, hp), CB.p_mod3(one, h1), GF.hc_m(one, h1, hc), GF.h21_m(one, h1), j, k, a, Lg.subst(Nat, p => {GS.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va)))

def Laws.Scalar.mul(one, h1, hp, hc, j, k, a, va):
  Lg.subst(Nat, p => {GS.equiv(p, GS.smul(p, Nat.mul(j, k), a), GS.smul(p, j, GS.smul(p, k, a))) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), G4.smul_mul(GF.pm(one), GF.hp_m(one, h1, hp), CB.p_mod3(one, h1), GF.hc_m(one, h1, hc), GF.h21_m(one, h1), j, k, a, Lg.subst(Nat, p => {GS.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va)))

def Laws.Scalar.equiv(one, h1, hp, hc, k, a, a2, va, va2, h):
  Lg.subst(Nat, p => {GS.equiv(p, GS.smul(p, k, a), GS.smul(p, k, a2)) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), G4.smul_eqv(GF.pm(one), GF.hp_m(one, h1, hp), CB.p_mod3(one, h1), GF.hc_m(one, h1, hc), GF.h21_m(one, h1), k, a, a2, Lg.subst(Nat, p => {GS.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va), Lg.subst(Nat, p => {GS.valid(p, a2) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va2), Lg.subst(Nat, p => {GS.equiv(p, a, a2) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), h)))

def Laws.Scalar.pmul_closed(one, h1, hp, hc, k, a, va):
  Lg.subst(Nat, p => {GS.valid(p, CS.pmul(p, k, a)) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), G4.pmul_valid(GF.pm(one), GF.hp_m(one, h1, hp), CB.p_mod3(one, h1), GF.hc_m(one, h1, hc), GF.h21_m(one, h1), k, a, Lg.subst(Nat, p => {GS.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va)))

def Laws.Scalar.pmul_low(one, h1, hp, hc, k, a, va):
  Lg.subst(Nat, p => {GS.equiv(p, CS.pmul(p, k, a), GS.smul(p, C.low(256n, k), a)) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), G4.pmul_low(GF.pm(one), GF.hp_m(one, h1, hp), CB.p_mod3(one, h1), GF.hc_m(one, h1, hc), GF.h21_m(one, h1), k, a, Lg.subst(Nat, p => {GS.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va)))

def Laws.Scalar.pmul(one, h1, hp, hc, k, a, va, hk):
  Lg.subst(Nat, p => {GS.equiv(p, CS.pmul(p, k, a), GS.smul(p, k, a)) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), G4.pmul_smul(GF.pm(one), GF.hp_m(one, h1, hp), CB.p_mod3(one, h1), GF.hc_m(one, h1, hc), GF.h21_m(one, h1), k, a, Lg.subst(Nat, p => {GS.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va), hk))
