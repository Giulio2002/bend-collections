import Base
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/ed25519.bend as SE
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../../src/crypto/ed25519/scalar.bend as ESC
import ../../../src/crypto/ed25519/ed25519.bend as E
import ../curve25519/limbs.bend as LM
import ./scalar3.bend as S3
import ./sclause.bend as SL
import ../../../src/crypto/sign.bend as SG
import ../../../spec/crypto/sign.bend as SS
import ./pbase.bend as PB

# Gate for Ed25519 (with proof_keys.bend, proof_sign.bend and
# proof_verify.bend, split so each root stays small): the scalar clauses of
# spec/crypto/ed25519.bend and the rejections of spec/crypto/sign.bend.

def scalar_reduce(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +hb: {FS.bytes_ok(64n, bs) == True{} : Bool}) -> SE.Scalar.reduce(one, h1, bs, hb):
  +M = {1n+S3.mmL(one) : Nat}
  Equal.trans(Nat, FS.value(ESC.reduce(bs)), Nat.mod(FS.value(bs), M), Nat.mod(FS.value(bs), SE.ell(one)), SL.reduce_m(one, h1, bs, LM.okb_lea(64n, bs, 255n, PB.ok(64n, bs, hb))), Equal.cong(Nat, Nat, z => Nat.mod(FS.value(bs), z), M, SE.ell(one), PB.ell_m(one, h1)))

def scalar_mul_add(+one: Nat, +h1: {one == 1n : Nat}, +k: List<&2, U32>, +s: List<&2, U32>, +r: List<&2, U32>, +hk: {FS.tight(k) == True{} : Bool}, +hs: {FS.tight(s) == True{} : Bool}, +hr: {FS.tight(r) == True{} : Bool}, +hsl: {Nat.is_lt(FS.value(s), SE.ell(one)) == True{} : Bool}, +hrl: {Nat.is_lt(FS.value(r), SE.ell(one)) == True{} : Bool}) -> SE.Scalar.mul_add(one, h1, k, s, r, hk, hs, hr, hsl, hrl):
  +M = {1n+S3.mmL(one) : Nat}
  +X = Nat.add(FS.value(r), Nat.mul(FS.value(k), FS.value(s)))
  +e = SL.mul_add_m(one, h1, k, s, r, PB.ok(32n, k, hk), PB.ok(32n, s, hs), PB.ok(32n, r, hr), PB.below(one, h1, FS.value(s), hsl), PB.below(one, h1, FS.value(r), hrl))
  Equal.trans(Nat, FS.value(ESC.mul_add(k, s, r)), Nat.mod(X, M), Nat.mod(X, SE.ell(one)), e, Equal.cong(Nat, Nat, z => Nat.mod(X, z), M, SE.ell(one), PB.ell_m(one, h1)))

# ---- Ed25519 ----

# the constants and the base point of an input list, related

def sign_reject_seed(+seed: List<&2, U32>, +h: {FS.tight(seed) == False{} : Bool}) -> SS.Sign.reject_seed(seed, h):
  %Equal.sym(Bool, X.valid_bytes(32n, seed), FS.bytes_ok(32n, seed), PB.valid_eq(32n, seed)) : {SG.keypair_if(seed, _) == None{} : Maybe<&2, SG.Keypair>}
  %Equal.sym(Bool, FS.tight(seed), False{}, h) : {SG.keypair_if(seed, _) == None{} : Maybe<&2, SG.Keypair>}
  {==}

def sign_reject_key(+sk: List<&2, U32>, +msg: List<&2, U32>, +h: {FS.tight(sk) == False{} : Bool}) -> SS.Sign.reject_key(sk, msg, h):
  %Equal.sym(Bool, X.valid_bytes(32n, sk), FS.bytes_ok(32n, sk), PB.valid_eq(32n, sk)) : {SG.sign_if(sk, msg, _) == None{} : Maybe<&2, List<&2, U32>>}
  %Equal.sym(Bool, FS.tight(sk), False{}, h) : {SG.sign_if(sk, msg, _) == None{} : Maybe<&2, List<&2, U32>>}
  {==}

def sign_reject(+pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>, +h: {Bool.and(FS.tight(pk), FS.bytes_ok(64n, sig)) == False{} : Bool}) -> SS.Sign.reject(pk, msg, sig, h):
  %Equal.sym(Bool, X.valid_bytes(32n, pk), FS.bytes_ok(32n, pk), PB.valid_eq(32n, pk)) : {SG.verify_if(pk, msg, sig, Bool.and(_, X.valid_bytes(64n, sig))) == False{} : Bool}
  %Equal.sym(Bool, X.valid_bytes(64n, sig), FS.bytes_ok(64n, sig), PB.valid_eq(64n, sig)) : {SG.verify_if(pk, msg, sig, Bool.and(FS.bytes_ok(32n, pk), _)) == False{} : Bool}
  %Equal.sym(Bool, Bool.and(FS.tight(pk), FS.bytes_ok(64n, sig)), False{}, h) : {SG.verify_if(pk, msg, sig, _) == False{} : Bool}
  {==}

def sign_reject_signing_key(+seed: List<&2, U32>, +h: {FS.tight(seed) == False{} : Bool}) -> SS.Sign.reject_signing_key(seed, h):
  %Equal.sym(Bool, X.valid_bytes(32n, seed), FS.bytes_ok(32n, seed), PB.valid_eq(32n, seed)) : {SG.key_if(seed, _) == None{} : Maybe<&2, E.Key>}
  %Equal.sym(Bool, FS.tight(seed), False{}, h) : {SG.key_if(seed, _) == None{} : Maybe<&2, E.Key>}
  {==}
