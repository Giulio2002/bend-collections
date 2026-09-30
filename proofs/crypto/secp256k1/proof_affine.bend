import Base
import ../../../spec/crypto/secp256k1/field.bend as FS
import ../../../spec/crypto/secp256k1/curve.bend as CS
import ../../../spec/crypto/secp256k1/group.bend as GS
import ../../../spec/crypto/secp256k1/affine.bend as GA
import ../../lib/logic.bend as Lg
import ../../math/number/nt_prime.bend as PM
import ./laws_affine.bend as Laws
import ./group/gfp.bend as GF
import ./group/certb.bend as CB
import ./group/aff1.bend as A1
import ./group/aff2.bend as A2
import ./group/aff3.bend as A3
import ./group/aff4.bend as A4

# The affine group law of secp256k1 (laws_affine.bend):
# `bend proofs/crypto/secp256k1/proof_affine.bend`. Each clause is the lemma
# of group/aff*.bend for the modulus 1 + pm, moved to FS.prime(one) with
# FS.prime(one) == 1 + pm (group/certb.bend).

def Laws.Affine.identity_right(p, a):
  A3.a_unit_r(p, a)

def Laws.Affine.identity_left(p, a):
  A3.a_unit_l(p, a)

def Laws.Affine.sum(one, h1, hp, hc, a, b, va, vb):
  Lg.subst(Nat, p => {GA.of_proj(p, CS.padd(p, a, b)) == GA.add(p, GA.of_proj(p, a), GA.of_proj(p, b)) : GA.APoint}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), A2.corr(GF.pm(one), GF.hp_m(one, h1, hp), CB.p_mod3(one, h1), GF.hc_m(one, h1, hc), GF.h21_m(one, h1), a, b, Lg.subst(Nat, p => {GS.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va), Lg.subst(Nat, p => {GS.valid(p, b) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), vb)))

def Laws.Affine.of_equiv(one, h1, hp, hc, a, b, va, vb, h):
  Lg.subst(Nat, p => {GA.of_proj(p, a) == GA.of_proj(p, b) : GA.APoint}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), A1.aff_eqv(GF.pm(one), GF.hp_m(one, h1, hp), a, b, Lg.subst(Nat, p => {GS.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va), Lg.subst(Nat, p => {GS.valid(p, b) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), vb), Lg.subst(Nat, p => {GS.equiv(p, a, b) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), h)))

def Laws.Affine.equiv_of(one, h1, hp, hc, a, b, va, vb, h):
  Lg.subst(Nat, p => {GS.equiv(p, a, b) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), A4.eqv_aff(GF.pm(one), GF.hp_m(one, h1, hp), GF.h21_m(one, h1), a, b, Lg.subst(Nat, p => {GS.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va), Lg.subst(Nat, p => {GS.valid(p, b) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), vb), Lg.subst(Nat, p => {GA.of_proj(p, a) == GA.of_proj(p, b) : GA.APoint}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), h)))

def Laws.Affine.of_valid(one, h1, hp, hc, a, va):
  Lg.subst(Nat, p => {GA.valid(p, GA.of_proj(p, a)) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), A3.aff_val(GF.pm(one), GF.hp_m(one, h1, hp), a, Lg.subst(Nat, p => {GS.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va)))

def Laws.Affine.to_valid(one, h1, hp, hc, a, va):
  Lg.subst(Nat, p => {GS.valid(p, GA.to_proj(a)) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), A3.lift_v(GF.pm(one), GF.hp_m(one, h1, hp), CB.p_mod3(one, h1), GF.hc_m(one, h1, hc), GF.h21_m(one, h1), a, Lg.subst(Nat, p => {GA.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va)))

def Laws.Affine.of_to(one, h1, hp, hc, a, va):
  Lg.subst(Nat, p => {GA.of_proj(p, GA.to_proj(a)) == a : GA.APoint}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), A3.lift_a(GF.pm(one), GF.hp_m(one, h1, hp), GF.h21_m(one, h1), a, Lg.subst(Nat, p => {GA.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va)))

def Laws.Affine.closed(one, h1, hp, hc, a, b, va, vb):
  Lg.subst(Nat, p => {GA.valid(p, GA.add(p, a, b)) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), A3.a_closed(GF.pm(one), GF.hp_m(one, h1, hp), CB.p_mod3(one, h1), GF.hc_m(one, h1, hc), GF.h21_m(one, h1), a, b, Lg.subst(Nat, p => {GA.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va), Lg.subst(Nat, p => {GA.valid(p, b) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), vb)))

def Laws.Affine.commutative(one, h1, hp, hc, a, b, va, vb):
  Lg.subst(Nat, p => {GA.add(p, a, b) == GA.add(p, b, a) : GA.APoint}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), A3.a_comm(GF.pm(one), GF.hp_m(one, h1, hp), CB.p_mod3(one, h1), GF.hc_m(one, h1, hc), GF.h21_m(one, h1), a, b, Lg.subst(Nat, p => {GA.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va), Lg.subst(Nat, p => {GA.valid(p, b) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), vb)))

def Laws.Affine.associative(one, h1, hp, hc, a, b, c, va, vb, vc):
  Lg.subst(Nat, p => {GA.add(p, GA.add(p, a, b), c) == GA.add(p, a, GA.add(p, b, c)) : GA.APoint}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), A3.a_assoc(GF.pm(one), GF.hp_m(one, h1, hp), CB.p_mod3(one, h1), GF.hc_m(one, h1, hc), GF.h21_m(one, h1), a, b, c, Lg.subst(Nat, p => {GA.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va), Lg.subst(Nat, p => {GA.valid(p, b) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), vb), Lg.subst(Nat, p => {GA.valid(p, c) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), vc)))

def Laws.Affine.inverse(one, h1, hp, hc, a, va):
  Lg.subst(Nat, p => {GA.add(p, a, GA.neg(p, a)) == GA.AInf{} : GA.APoint}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), A3.a_inv(GF.pm(one), GF.hp_m(one, h1, hp), CB.p_mod3(one, h1), GF.hc_m(one, h1, hc), GF.h21_m(one, h1), a, Lg.subst(Nat, p => {GA.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va)))

def Laws.Affine.neg_closed(one, h1, hp, hc, a, va):
  Lg.subst(Nat, p => {GA.valid(p, GA.neg(p, a)) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), A3.a_neg_valid(GF.pm(one), GF.hp_m(one, h1, hp), CB.p_mod3(one, h1), GF.hc_m(one, h1, hc), GF.h21_m(one, h1), a, Lg.subst(Nat, p => {GA.valid(p, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va)))
