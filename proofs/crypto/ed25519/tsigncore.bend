import Base
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/ed25519.bend as SE
import ../../../spec/crypto/sha512.bend as SHA
import ../../../src/crypto/hash.bend as H
import ../../../src/crypto/ed25519/point.bend as PT
import ../../../src/crypto/ed25519/ed25519.bend as E
import ../../lib/logic.bend as L
import ./pcodec.bend as PC
import ./bytes.bend as BY
import ../curve25519/prime.bend as PRM
import ./tcommon.bend as TC
import ./tsign.bend as TS
import ./pbase.bend as PB

# Signing with the constants of context(xs) equals RFC 8032 (shared by the
# two signing roots).

def ed_sign_ctx(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +seed: List<&2, U32>, +msg: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}) -> SE.Ed25519.sign_ctx(one, h1, xs, seed, msg, hs):
  +pp = PB.pp1(one)
  +P = {1n+pp : Nat}
  +D = SE.dconst(one, P)
  +h = H.sha512(seed)
  +sh = SHA.sha512_bytes(seed)
  +cs = PT.consts(xs)
  +e1 = TS.sign_rel(one, h1, pp, PRM.hP(one, h1), cs, PC.cr(one, h1, xs), D, PC.rd2(one, h1, pp, PRM.hP(one, h1), xs), PT.base(cs), TC.base_of(one, h1, xs), h, BY.sha_okb(seed), msg)
  +e2 = Equal.cong(List<&2, U32>, List<&2, U32>, z => SE.sign_with(one, P, D, z, msg), h, sh, BY.sha_eq(seed))
  +e12 = Equal.trans(List<&2, U32>, E.sign_key(E.expand_ctx(E.context(xs), seed), msg), SE.sign_with(one, P, D, h, msg), SE.sign_at(one, P, seed, msg), e1, e2)
  L.subst(Nat, z => {E.sign_key(E.expand_ctx(E.context(xs), seed), msg) == SE.sign_at(one, z, seed, msg) : List<&2, U32>}, P, FS.prime(one), Equal.sym(Nat, FS.prime(one), P, PRM.prime_eq(one, h1)), e12)
