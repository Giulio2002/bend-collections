import Base
import ../../../../spec/lib/common.bend as C
import ../../../../spec/crypto/curve25519/field.bend as FS
import ../../../../spec/crypto/curve25519/edwards.bend as G
import ../../../../spec/crypto/ed25519.bend as ED
import ../../../../spec/crypto/ed25519_group.bend as GE
import ../../../../spec/crypto/sha512.bend as SHA
import ../../../lib/nat.bend as N
import ../../secp256k1/group/bnx.bend as X
import ./pfacts.bend as PF
import ./lfacts.bend as LF
import ./cpar2.bend as CQ
import ./vs2.bend as VS2
import ./vs3.bend as VS3

# Ed25519.verify_sign (spec/crypto/ed25519_group.bend): the theorem of
# vs3.bend at p = FS.prime(one), with the literal facts of edwards25519
# (p = 8 m + 5 below 2^255, L below 2^256: cpar2.bend, lfacts.bend).

# the verification of the specification, as a function of the modulus
def vp(+one: Nat, +seed: List<&2, U32>, +msg: List<&2, U32>, +p: Nat) -> Bool:
  ED.verify_with(one, p, ED.dconst(one, p), ED.public_key_at(one, p, seed), msg, ED.first(32n, ED.sign_at(one, p, seed, msg)), FS.value(ED.rest(32n, ED.sign_at(one, p, seed, msg))), Nat.is_lt(FS.value(ED.rest(32n, ED.sign_at(one, p, seed, msg))), ED.ell(one)))

# the same at 1 + mp, as a function of the signature
def vq(+one: Nat, +mp: Nat, +seed: List<&2, U32>, +msg: List<&2, U32>, +sg: List<&2, U32>) -> Bool:
  ED.verify_with(one, 1n+mp, ED.dconst(one, 1n+mp), ED.public_of(one, 1n+mp, ED.dconst(one, 1n+mp), SHA.sha512_bytes(seed)), msg, ED.first(32n, sg), FS.value(ED.rest(32n, sg)), Nat.is_lt(FS.value(ED.rest(32n, sg)), ED.ell(one)))

def core(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hc: G.Curve(mp, ED.dconst(one, 1n+mp)), +m: Nat, +h58: {Nat.div(Nat.sub(1n+mp, 5n), 8n) == m : Nat}, +hk: {Nat.div(mp, 2n) == Nat.add(Nat.add(1n, Nat.add(m, m)), Nat.add(1n, Nat.add(m, m))) : Nat}, +hp255: {Nat.is_le(1n+mp, C.shift(255n, one)) == True{} : Bool}, +lp: Nat, +hle: {ED.ell(one) == 1n+lp : Nat}, +hl256: {Nat.is_le(1n+lp, C.shift(256n, one)) == True{} : Bool}, +hlb: {G.nmul(1n+mp, ED.dconst(one, 1n+mp), 1n+lp, GE.affine(1n+mp, ED.base(1n+mp, ED.dconst(one, 1n+mp)))) == G.azero() : G.APt}, +seed: List<&2, U32>, +msg: List<&2, U32>) -> {vp(one, seed, msg, 1n+mp) == True{} : Bool}:
  %Equal.sym(List<&2, U32>, ED.sign_with(one, 1n+mp, ED.dconst(one, 1n+mp), SHA.sha512_bytes(seed), msg), ED.sign_body(one, 1n+mp, ED.dconst(one, 1n+mp), SHA.sha512_bytes(seed), msg), VS2.sign_with_eq(one, 1n+mp, ED.dconst(one, 1n+mp), SHA.sha512_bytes(seed), msg)) : {vq(one, mp, seed, msg, _) == True{} : Bool}
  VS3.sv_true(one, h1, mp, ED.dconst(one, 1n+mp), hc, m, h58, hk, hp255, lp, hle, hl256, hlb, seed, msg)

# the hypotheses at 1 + mp
def tc(+one: Nat, +h1: {one == 1n : Nat}, +hc: G.Curve(X.bvalo(one, PF.p1l()), ED.dconst(one, FS.prime(one)))) -> G.Curve(X.bvalo(one, PF.p1l()), ED.dconst(one, 1n+X.bvalo(one, PF.p1l()))):
  %PF.p_suc(one, h1) : G.Curve(X.bvalo(one, PF.p1l()), ED.dconst(one, _))
  hc

def tl(+one: Nat, +h1: {one == 1n : Nat}, +hl: GE.BaseOrder(one, FS.prime(one))) -> {G.nmul(1n+X.bvalo(one, PF.p1l()), ED.dconst(one, 1n+X.bvalo(one, PF.p1l())), 1n+X.bvalo(one, PF.l1l()), GE.affine(1n+X.bvalo(one, PF.p1l()), ED.base(1n+X.bvalo(one, PF.p1l()), ED.dconst(one, 1n+X.bvalo(one, PF.p1l()))))) == G.azero() : G.APt}:
  %LF.l_suc(one, h1) : {G.nmul(1n+X.bvalo(one, PF.p1l()), ED.dconst(one, 1n+X.bvalo(one, PF.p1l())), _, GE.affine(1n+X.bvalo(one, PF.p1l()), ED.base(1n+X.bvalo(one, PF.p1l()), ED.dconst(one, 1n+X.bvalo(one, PF.p1l()))))) == G.azero() : G.APt}
  %PF.p_suc(one, h1) : GE.BaseOrder(one, _)
  hl

def vs0(+one: Nat, +h1: {one == 1n : Nat}, +hc: G.Curve(X.bvalo(one, PF.p1l()), ED.dconst(one, FS.prime(one))), +hl: GE.BaseOrder(one, FS.prime(one)), +seed: List<&2, U32>, +msg: List<&2, U32>) -> {ED.verify(one, ED.public_key(one, seed), msg, ED.sign(one, seed, msg)) == True{} : Bool}:
  %Equal.sym(Nat, FS.prime(one), 1n+X.bvalo(one, PF.p1l()), PF.p_suc(one, h1)) : {vp(one, seed, msg, _) == True{} : Bool}
  core(one, h1, X.bvalo(one, PF.p1l()), tc(one, h1, hc), X.bvalo(one, PF.e58l()), CQ.h58(one, h1), CQ.hk(one, h1), CQ.p_le255(one, h1), X.bvalo(one, PF.l1l()), LF.l_suc(one, h1), CQ.l_le256(one, h1), tl(one, h1, hl), seed, msg)

# 1 + mp == p gives mp == the literal p - 1
def mp_is(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}) -> {X.bvalo(one, PF.p1l()) == mp : Nat}:
  N.succ_inj(X.bvalo(one, PF.p1l()), mp, Equal.trans(Nat, 1n+X.bvalo(one, PF.p1l()), FS.prime(one), 1n+mp, Equal.sym(Nat, FS.prime(one), 1n+X.bvalo(one, PF.p1l()), PF.p_suc(one, h1)), hm))

def tm(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}, +hc: G.Curve(mp, ED.dconst(one, FS.prime(one)))) -> G.Curve(X.bvalo(one, PF.p1l()), ED.dconst(one, FS.prime(one))):
  %Equal.sym(Nat, X.bvalo(one, PF.p1l()), mp, mp_is(one, h1, mp, hm)) : G.Curve(_, ED.dconst(one, FS.prime(one)))
  hc

# RFC 8032 correctness
def verify_sign(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}, +hc: G.Curve(mp, ED.dconst(one, FS.prime(one))), +hl: GE.BaseOrder(one, FS.prime(one)), +seed: List<&2, U32>, +msg: List<&2, U32>) -> GE.Ed25519.verify_sign(one, h1, mp, hm, hc, hl, seed, msg):
  vs0(one, h1, tm(one, h1, mp, hm, hc), hl, seed, msg)
