import Base
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/x25519.bend as SX
import ../../../spec/crypto/ed25519.bend as SE
import ../../../spec/crypto/sha512.bend as SHA
import ../../../src/crypto/hash.bend as H
import ../../../src/crypto/curve25519/field.bend as F
import ../../../src/crypto/ed25519/point.bend as PT
import ../../../src/crypto/ed25519/scalar.bend as ESC
import ../../../src/crypto/ed25519/ed25519.bend as E
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../../src/crypto/sign.bend as SG
import ../../../spec/crypto/sign.bend as SS
import ../../lib/u32.bend as U
import ../../lib/logic.bend as L
import ../curve25519/limbs.bend as LM
import ../curve25519/prime.bend as PRM
import ./scalar3.bend as S3
import ./bytes.bend as BY
import ./top.bend as TP

# Gate for Ed25519: `bend proofs/crypto/ed25519/proof.bend` checks every
# clause of spec/crypto/ed25519.bend (scalars mod L, key generation, signing
# and verification equal to the RFC 8032 transcription) and of
# spec/crypto/sign.bend (the facade), for every input.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def pp1(+one: Nat) -> Nat:
  PRM.pp_of(one)

def ok(+n: Nat, +a: List<&2, U32>, +h: {FS.bytes_ok(n, a) == True{} : Bool}) -> {LM.okb(n, a, 255n) == True{} : Bool}:
  LM.bytes_okb(n, a, h)

def ell_m(+one: Nat, +h1: {one == 1n : Nat}) -> {1n+S3.mmL(one) == SE.ell(one) : Nat}:
  S3.ell_eq(one, h1)

# ---- scalars ----

def scalar_reduce(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +hb: {FS.bytes_ok(64n, bs) == True{} : Bool}) -> SE.Scalar.reduce(one, h1, bs, hb):
  +M = {1n+S3.mmL(one) : Nat}
  Equal.trans(Nat, FS.value(ESC.reduce(bs)), Nat.mod(FS.value(bs), M), Nat.mod(FS.value(bs), SE.ell(one)), S3.reduce_m(one, h1, bs, LM.okb_lea(64n, bs, 255n, ok(64n, bs, hb))), Equal.cong(Nat, Nat, z => Nat.mod(FS.value(bs), z), M, SE.ell(one), ell_m(one, h1)))

def below(+one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +h: {Nat.is_lt(x, SE.ell(one)) == True{} : Bool}) -> {Nat.is_lt(x, 1n+S3.mmL(one)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(x, z) == True{} : Bool}, SE.ell(one), 1n+S3.mmL(one), Equal.sym(Nat, 1n+S3.mmL(one), SE.ell(one), ell_m(one, h1)), h)

def scalar_mul_add(+one: Nat, +h1: {one == 1n : Nat}, +k: List<&2, U32>, +s: List<&2, U32>, +r: List<&2, U32>, +hk: {FS.tight(k) == True{} : Bool}, +hs: {FS.tight(s) == True{} : Bool}, +hr: {FS.tight(r) == True{} : Bool}, +hsl: {Nat.is_lt(FS.value(s), SE.ell(one)) == True{} : Bool}, +hrl: {Nat.is_lt(FS.value(r), SE.ell(one)) == True{} : Bool}) -> SE.Scalar.mul_add(one, h1, k, s, r, hk, hs, hr, hsl, hrl):
  +M = {1n+S3.mmL(one) : Nat}
  +X = Nat.add(FS.value(r), Nat.mul(FS.value(k), FS.value(s)))
  +e = S3.mul_add_m(one, h1, k, s, r, LM.okb_lea(32n, k, 255n, ok(32n, k, hk)), ok(32n, s, hs), ok(32n, r, hr), below(one, h1, FS.value(s), hsl), below(one, h1, FS.value(r), hrl))
  Equal.trans(Nat, FS.value(ESC.mul_add(k, s, r)), Nat.mod(X, M), Nat.mod(X, SE.ell(one)), e, Equal.cong(Nat, Nat, z => Nat.mod(X, z), M, SE.ell(one), ell_m(one, h1)))

# ---- Ed25519 ----

def ed_public(+one: Nat, +h1: {one == 1n : Nat}, +seed: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}) -> SE.Ed25519.public(one, h1, seed, hs):
  +pp = pp1(one)
  +P = {1n+pp : Nat}
  +h = H.sha512(seed)
  +sh = SHA.sha512_bytes(seed)
  +e1 = TP.public_rel(one, h1, pp, PRM.hP(one, h1), seed, h, BY.sha_okb(seed))
  +e2 = Equal.cong(List<&2, U32>, List<&2, U32>, z => SE.public_of(one, P, SE.dconst(one, P), z), h, sh, BY.sha_eq(seed))
  +e3 = Equal.cong(Nat, List<&2, U32>, z => SE.public_of(one, z, SE.dconst(one, z), sh), P, FS.prime(one), Equal.sym(Nat, FS.prime(one), P, PRM.prime_eq(one, h1)))
  Equal.trans(List<&2, U32>, E.public_of(PT.consts(seed), seed, h), SE.public_of(one, P, SE.dconst(one, P), h), SE.public_of(one, FS.prime(one), SE.dconst(one, FS.prime(one)), sh), e1, Equal.trans(List<&2, U32>, SE.public_of(one, P, SE.dconst(one, P), h), SE.public_of(one, P, SE.dconst(one, P), sh), SE.public_of(one, FS.prime(one), SE.dconst(one, FS.prime(one)), sh), e2, e3))

def ed_sign(+one: Nat, +h1: {one == 1n : Nat}, +seed: List<&2, U32>, +msg: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}) -> SE.Ed25519.sign(one, h1, seed, msg, hs):
  +pp = pp1(one)
  +P = {1n+pp : Nat}
  +h = H.sha512(seed)
  +sh = SHA.sha512_bytes(seed)
  +e1 = TP.sign_rel(one, h1, pp, PRM.hP(one, h1), seed, h, BY.sha_okb(seed), msg)
  +e2 = Equal.cong(List<&2, U32>, List<&2, U32>, z => SE.sign_with(one, P, SE.dconst(one, P), z, msg), h, sh, BY.sha_eq(seed))
  +e3 = Equal.cong(Nat, List<&2, U32>, z => SE.sign_with(one, z, SE.dconst(one, z), sh, msg), P, FS.prime(one), Equal.sym(Nat, FS.prime(one), P, PRM.prime_eq(one, h1)))
  Equal.trans(List<&2, U32>, E.sign_with(PT.consts(seed), seed, h, msg), SE.sign_with(one, P, SE.dconst(one, P), h, msg), SE.sign_with(one, FS.prime(one), SE.dconst(one, FS.prime(one)), sh, msg), e1, Equal.trans(List<&2, U32>, SE.sign_with(one, P, SE.dconst(one, P), h, msg), SE.sign_with(one, P, SE.dconst(one, P), sh, msg), SE.sign_with(one, FS.prime(one), SE.dconst(one, FS.prime(one)), sh, msg), e2, e3))

def ed_verify(+one: Nat, +h1: {one == 1n : Nat}, +pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>, +hp: {FS.tight(pk) == True{} : Bool}, +hg: {FS.bytes_ok(64n, sig) == True{} : Bool}) -> SE.Ed25519.verify(one, h1, pk, msg, sig, hp, hg):
  +pp = pp1(one)
  +P = {1n+pp : Nat}
  +D = SE.dconst(one, P)
  +el = SE.ell(one)
  +cs = PT.consts(pk)
  +hsig = ok(64n, sig, hg)
  +rb = F.take(32n, sig)
  +sb = F.drop(32n, sig)
  +srb = SE.first(32n, sig)
  +ssb = SE.rest(32n, sig)
  +hrb = BY.take_okb(32n, 32n, sig, 255n, hsig)
  +hsb = BY.drop_okb(32n, 32n, sig, 255n, hsig)
  +lt = Nat.is_lt(FS.value(sb), el)
  +slt = Nat.is_lt(FS.value(ssb), el)
  +e0 = Equal.trans(Bool, ESC.lt_l(sb), Nat.is_lt(FS.value(sb), 1n+S3.mmL(one)), lt, S3.lt_l_m(one, h1, sb, hsb), Equal.cong(Nat, Bool, z => Nat.is_lt(FS.value(sb), z), 1n+S3.mmL(one), el, ell_m(one, h1)))
  +e1 = Equal.cong(Bool, Bool, z => E.verify_with(cs, pk, msg, rb, sb, z), ESC.lt_l(sb), lt, e0)
  +e2 = TP.verify_with_rel(one, h1, pp, PRM.hP(one, h1), pk, ok(32n, pk, hp), msg, rb, hrb, sb, hsb, lt)
  +e3 = Equal.cong(List<&2, U32>, Bool, z => SE.verify_with(one, P, D, pk, msg, z, FS.value(sb), lt), rb, srb, BY.take_eq(32n, sig))
  +e4 = Equal.cong(List<&2, U32>, Bool, z => SE.verify_with(one, P, D, pk, msg, srb, FS.value(z), Nat.is_lt(FS.value(z), el)), sb, ssb, BY.drop_eq(32n, sig))
  +e5 = Equal.cong(Nat, Bool, z => SE.verify_with(one, z, SE.dconst(one, z), pk, msg, srb, FS.value(ssb), slt), P, FS.prime(one), Equal.sym(Nat, FS.prime(one), P, PRM.prime_eq(one, h1)))
  +V0 = E.verify_with(cs, pk, msg, rb, sb, ESC.lt_l(sb))
  +V1 = E.verify_with(cs, pk, msg, rb, sb, lt)
  +V2 = SE.verify_with(one, P, D, pk, msg, rb, FS.value(sb), lt)
  +V3 = SE.verify_with(one, P, D, pk, msg, srb, FS.value(sb), lt)
  +V4 = SE.verify_with(one, P, D, pk, msg, srb, FS.value(ssb), slt)
  +V5 = SE.verify_with(one, FS.prime(one), SE.dconst(one, FS.prime(one)), pk, msg, srb, FS.value(ssb), slt)
  Equal.trans(Bool, V0, V1, V5, e1, Equal.trans(Bool, V1, V2, V5, e2, Equal.trans(Bool, V2, V3, V5, e3, Equal.trans(Bool, V3, V4, V5, e4, e5))))

# ---- the facade, src/crypto/sign.bend ----

def valid_eq(+n: Nat, +xs: List<&2, U32>) -> {X.valid_bytes(n, xs) == FS.bytes_ok(n, xs) : Bool}:
  match n xs:
    case 0n Nil{}:
      {==}
    case 0n Con{y, yt}:
      {==}
    case 1n+m Nil{}:
      {==}
    case 1n+ +m Con{+y, +yt}:
      +e1 = U.is_lt_nat(y, 256)
      +e2 = valid_eq(m, yt)
      Equal.trans(Bool, Bool.and(U32.is_lt(y, 256), X.valid_bytes(m, yt)), Bool.and(Nat.is_lt(v(y), 256n), X.valid_bytes(m, yt)), Bool.and(Nat.is_lt(v(y), 256n), FS.bytes_ok(m, yt)), Equal.cong(Bool, Bool, z => Bool.and(z, X.valid_bytes(m, yt)), U32.is_lt(y, 256), Nat.is_lt(v(y), 256n), e1), Equal.cong(Bool, Bool, z => Bool.and(Nat.is_lt(v(y), 256n), z), X.valid_bytes(m, yt), FS.bytes_ok(m, yt), e2))

def sign_keypair(+one: Nat, +h1: {one == 1n : Nat}, +seed: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}) -> SS.Sign.keypair(one, h1, seed, hs):
  %Equal.sym(Bool, X.valid_bytes(32n, seed), FS.bytes_ok(32n, seed), valid_eq(32n, seed)) : {SG.keypair_if(seed, _) == Some{SG.Keypair{seed, SE.public_key(one, seed)}} : Maybe<&2, SG.Keypair>}
  %Equal.sym(Bool, FS.tight(seed), True{}, hs) : {SG.keypair_if(seed, _) == Some{SG.Keypair{seed, SE.public_key(one, seed)}} : Maybe<&2, SG.Keypair>}
  Equal.cong(List<&2, U32>, Maybe<&2, SG.Keypair>, z => Some{SG.Keypair{seed, z}}, E.public_key(seed), SE.public_key(one, seed), ed_public(one, h1, seed, hs))

def sign_sign(+one: Nat, +h1: {one == 1n : Nat}, +sk: List<&2, U32>, +msg: List<&2, U32>, +hs: {FS.tight(sk) == True{} : Bool}) -> SS.Sign.sign(one, h1, sk, msg, hs):
  %Equal.sym(Bool, X.valid_bytes(32n, sk), FS.bytes_ok(32n, sk), valid_eq(32n, sk)) : {SG.sign_if(sk, msg, _) == Some{SE.sign(one, sk, msg)} : Maybe<&2, List<&2, U32>>}
  %Equal.sym(Bool, FS.tight(sk), True{}, hs) : {SG.sign_if(sk, msg, _) == Some{SE.sign(one, sk, msg)} : Maybe<&2, List<&2, U32>>}
  Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, z => Some{z}, E.sign_raw(sk, msg), SE.sign(one, sk, msg), ed_sign(one, h1, sk, msg, hs))

def sign_verify(+one: Nat, +h1: {one == 1n : Nat}, +pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>, +hp: {FS.tight(pk) == True{} : Bool}, +hg: {FS.bytes_ok(64n, sig) == True{} : Bool}) -> SS.Sign.verify(one, h1, pk, msg, sig, hp, hg):
  %Equal.sym(Bool, X.valid_bytes(32n, pk), FS.bytes_ok(32n, pk), valid_eq(32n, pk)) : {SG.verify_if(pk, msg, sig, Bool.and(_, X.valid_bytes(64n, sig))) == SE.verify(one, pk, msg, sig) : Bool}
  %Equal.sym(Bool, X.valid_bytes(64n, sig), FS.bytes_ok(64n, sig), valid_eq(64n, sig)) : {SG.verify_if(pk, msg, sig, Bool.and(FS.bytes_ok(32n, pk), _)) == SE.verify(one, pk, msg, sig) : Bool}
  %Equal.sym(Bool, FS.tight(pk), True{}, hp) : {SG.verify_if(pk, msg, sig, Bool.and(_, FS.bytes_ok(64n, sig))) == SE.verify(one, pk, msg, sig) : Bool}
  %Equal.sym(Bool, FS.bytes_ok(64n, sig), True{}, hg) : {SG.verify_if(pk, msg, sig, Bool.and(True{}, _)) == SE.verify(one, pk, msg, sig) : Bool}
  ed_verify(one, h1, pk, msg, sig, hp, hg)

def sign_reject_seed(+seed: List<&2, U32>, +h: {FS.tight(seed) == False{} : Bool}) -> SS.Sign.reject_seed(seed, h):
  %Equal.sym(Bool, X.valid_bytes(32n, seed), FS.bytes_ok(32n, seed), valid_eq(32n, seed)) : {SG.keypair_if(seed, _) == None{} : Maybe<&2, SG.Keypair>}
  %Equal.sym(Bool, FS.tight(seed), False{}, h) : {SG.keypair_if(seed, _) == None{} : Maybe<&2, SG.Keypair>}
  {==}

def sign_reject_key(+sk: List<&2, U32>, +msg: List<&2, U32>, +h: {FS.tight(sk) == False{} : Bool}) -> SS.Sign.reject_key(sk, msg, h):
  %Equal.sym(Bool, X.valid_bytes(32n, sk), FS.bytes_ok(32n, sk), valid_eq(32n, sk)) : {SG.sign_if(sk, msg, _) == None{} : Maybe<&2, List<&2, U32>>}
  %Equal.sym(Bool, FS.tight(sk), False{}, h) : {SG.sign_if(sk, msg, _) == None{} : Maybe<&2, List<&2, U32>>}
  {==}

def sign_reject(+pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>, +h: {Bool.and(FS.tight(pk), FS.bytes_ok(64n, sig)) == False{} : Bool}) -> SS.Sign.reject(pk, msg, sig, h):
  %Equal.sym(Bool, X.valid_bytes(32n, pk), FS.bytes_ok(32n, pk), valid_eq(32n, pk)) : {SG.verify_if(pk, msg, sig, Bool.and(_, X.valid_bytes(64n, sig))) == False{} : Bool}
  %Equal.sym(Bool, X.valid_bytes(64n, sig), FS.bytes_ok(64n, sig), valid_eq(64n, sig)) : {SG.verify_if(pk, msg, sig, Bool.and(FS.bytes_ok(32n, pk), _)) == False{} : Bool}
  %Equal.sym(Bool, Bool.and(FS.tight(pk), FS.bytes_ok(64n, sig)), False{}, h) : {SG.verify_if(pk, msg, sig, _) == False{} : Bool}
  {==}
