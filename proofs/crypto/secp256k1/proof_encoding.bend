import Base
import ../../../spec/crypto/secp256k1/field.bend as FS
import ../../../spec/crypto/secp256k1/curve.bend as CS
import ../../../spec/crypto/secp256k1/group.bend as GS
import ../../../spec/crypto/secp256k1/encoding.bend as EN
import ../../lib/logic.bend as Lg
import ../../math/number/nt_prime.bend as PM
import ./laws_encoding.bend as Laws
import ./group/bnx.bend as X
import ./group/certb.bend as CB
import ./group/gfp.bend as GF
import ./group/encb.bend as EB
import ./group/encg.bend as EG
import ./group/sqrt.bend as SQ
import ./group/enc.bend as EC
import ./group/encv.bend as EV

# The SEC 1 encoding clauses (laws_encoding.bend):
# `bend proofs/crypto/secp256k1/proof_encoding.bend`. Each is the lemma of
# group/sqrt.bend, enc.bend, encv.bend for the modulus 1 + pm, moved to
# FS.prime(one) with FS.prime(one) == 1 + pm (group/certb.bend).

def Laws.Sqrt.square(one, h1, hp, a, y0, ha):
  Lg.subst(Nat, p => {FS.mmul(p, FS.fsqrt(p, a), FS.fsqrt(p, a)) == Nat.mod(a, p) : Nat}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), SQ.sq_ok(GF.pm(one), GF.hp_m(one, h1, hp), X.bvalo(one, EB.s4l()), EG.he_m(one, h1), a, y0, Lg.subst(Nat, p => {Nat.mod(a, p) == FS.mmul(p, y0, y0) : Nat}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), ha)))

def Laws.Sqrt.parity(one, h1, hp, r, y, hr, hy, hsq):
  Lg.subst(Nat, p => {CS.pick_parity(p, r, Nat.mod(y, 2n)) == y : Nat}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), SQ.pick(GF.pm(one), GF.hp_m(one, h1, hp), EG.hodd_m(one, h1), r, y, Lg.subst(Nat, p => {Nat.is_lt(r, p) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), hr), Lg.subst(Nat, p => {Nat.is_lt(y, p) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), hy), Lg.subst(Nat, p => {FS.mmul(p, r, r) == FS.mmul(p, y, y) : Nat}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), hsq)))

def Laws.Encoding.uncompressed_affine(one, h1, hp, x, y, hx, hy, hc):
  Lg.subst(Nat, p => {CS.decode(p, CS.encode_uncompressed(p, CS.SPoint{x, y, 1n})) == Some{CS.SPoint{x, y, 1n}} : Maybe<&2, CS.SPoint>}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), EC.rt_u1(one, h1, GF.pm(one), GF.hp_m(one, h1, hp), X.bvalo(one, EB.s4l()), EG.he_m(one, h1), EG.hodd_m(one, h1), EG.h256_m(one, h1), x, y, Lg.subst(Nat, p => {Nat.is_lt(x, p) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), hx), Lg.subst(Nat, p => {Nat.is_lt(y, p) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), hy), Lg.subst(Nat, p => {CS.on_curve(p, x, y) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), hc)))

def Laws.Encoding.compressed_affine(one, h1, hp, x, y, hx, hy, hc):
  Lg.subst(Nat, p => {CS.decode(p, CS.encode_compressed(p, CS.SPoint{x, y, 1n})) == Some{CS.SPoint{x, y, 1n}} : Maybe<&2, CS.SPoint>}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), EC.rt_c1(one, h1, GF.pm(one), GF.hp_m(one, h1, hp), X.bvalo(one, EB.s4l()), EG.he_m(one, h1), EG.hodd_m(one, h1), EG.h256_m(one, h1), x, y, Lg.subst(Nat, p => {Nat.is_lt(x, p) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), hx), Lg.subst(Nat, p => {Nat.is_lt(y, p) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), hy), Lg.subst(Nat, p => {CS.on_curve(p, x, y) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), hc)))

def Laws.Encoding.uncompressed(one, h1, hp, x, y, z, hv, hz):
  Lg.subst(Nat, p => {CS.decode(p, CS.encode_uncompressed(p, CS.SPoint{x, y, z})) == Some{CS.SPoint{FS.mmul(p, x, FS.minv(p, z)), FS.mmul(p, y, FS.minv(p, z)), 1n}} : Maybe<&2, CS.SPoint>}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), EC.rt_u(one, h1, GF.pm(one), GF.hp_m(one, h1, hp), X.bvalo(one, EB.s4l()), EG.he_m(one, h1), EG.hodd_m(one, h1), EG.h256_m(one, h1), x, y, z, Lg.subst(Nat, p => {GS.valid(p, CS.SPoint{x, y, z}) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), hv), Lg.subst(Nat, p => {Nat.is_eq(Nat.mod(z, p), 0n) == False{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), hz)))

def Laws.Encoding.compressed(one, h1, hp, x, y, z, hv, hz):
  Lg.subst(Nat, p => {CS.decode(p, CS.encode_compressed(p, CS.SPoint{x, y, z})) == Some{CS.SPoint{FS.mmul(p, x, FS.minv(p, z)), FS.mmul(p, y, FS.minv(p, z)), 1n}} : Maybe<&2, CS.SPoint>}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), EC.rt_c(one, h1, GF.pm(one), GF.hp_m(one, h1, hp), X.bvalo(one, EB.s4l()), EG.he_m(one, h1), EG.hodd_m(one, h1), EG.h256_m(one, h1), x, y, z, Lg.subst(Nat, p => {GS.valid(p, CS.SPoint{x, y, z}) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), hv), Lg.subst(Nat, p => {Nat.is_eq(Nat.mod(z, p), 0n) == False{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), hz)))

def Laws.Encoding.decode_valid(one, h1, hp, hc, bs):
  Lg.subst(Nat, p => {EN.decoded_ok(p, CS.decode(p, bs)) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)), EV.decode_ok(GF.pm(one), GF.hp_m(one, h1, hp), CB.p_mod3(one, h1), GF.hc_m(one, h1, hc), GF.h21_m(one, h1), bs))
