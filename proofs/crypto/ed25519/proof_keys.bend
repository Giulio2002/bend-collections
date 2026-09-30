import Base
import ../../../src/crypto/sign.bend as SG
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/ed25519.bend as SE
import ../../../spec/crypto/sha512.bend as SHA
import ../../../src/crypto/sha512/stream.bend as HS
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../../src/crypto/ed25519/point.bend as PT
import ../../../src/crypto/ed25519/ed25519.bend as E
import ../../lib/logic.bend as L
import ./pcodec.bend as PC
import ./bytes.bend as BY
import ../../../spec/crypto/sign.bend as SS
import ../curve25519/prime.bend as PRM
import ./tcommon.bend as TC
import ./pbase.bend as PB

# Gate: Ed25519.public, Ed25519.key_public (spec/crypto/ed25519.bend) and
# Sign.keypair, Sign.key_public (spec/crypto/sign.bend), for every seed.

def keypair_if_eq(+seed: List<&2, U32>, +ok: Bool, +pk: List<&2, U32>, +hok: {ok == True{} : Bool}, +e: {E.public_key(seed) == pk : List<&2, U32>}) -> {SG.keypair_if(seed, ok) == Some{SG.Keypair{seed, pk}} : Maybe<&2, SG.Keypair>}:
  match ok:
    case True{}:
      Equal.cong(List<&2, U32>, Maybe<&2, SG.Keypair>, z => Some{SG.Keypair{seed, z}}, E.public_key(seed), pk, e)
    case False{}:
      Empty.absurd({SG.keypair_if(seed, False{}) == Some{SG.Keypair{seed, pk}} : Maybe<&2, SG.Keypair>}, L.true_false(Equal.sym(Bool, False{}, True{}, hok)))

def key_pub_eq(+seed: List<&2, U32>, +ok: Bool, +V: List<&2, U32>, +hok: {ok == True{} : Bool}, +e: {E.key_public(E.expand(seed)) == V : List<&2, U32>}) -> {SS.key_pub(SG.key_if(seed, ok)) == Some{V} : Maybe<&2, List<&2, U32>>}:
  match ok:
    case True{}:
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, z => Some{z}, E.key_public(E.expand(seed)), V, e)
    case False{}:
      Empty.absurd({SS.key_pub(SG.key_if(seed, False{})) == Some{V} : Maybe<&2, List<&2, U32>>}, L.true_false(Equal.sym(Bool, False{}, True{}, hok)))

def keypair_ctx_if_eq(+ctx: E.Ctx, +seed: List<&2, U32>, +ok: Bool, +pk: List<&2, U32>, +hok: {ok == True{} : Bool}, +e: {E.public_key_ctx(ctx, seed) == pk : List<&2, U32>}) -> {SG.keypair_ctx_if(ctx, seed, ok) == Some{SG.Keypair{seed, pk}} : Maybe<&2, SG.Keypair>}:
  match ok:
    case True{}:
      Equal.cong(List<&2, U32>, Maybe<&2, SG.Keypair>, z => Some{SG.Keypair{seed, z}}, E.public_key_ctx(ctx, seed), pk, e)
    case False{}:
      Empty.absurd({SG.keypair_ctx_if(ctx, seed, False{}) == Some{SG.Keypair{seed, pk}} : Maybe<&2, SG.Keypair>}, L.true_false(Equal.sym(Bool, False{}, True{}, hok)))

def key_pub_ctx_eq(+ctx: E.Ctx, +seed: List<&2, U32>, +ok: Bool, +V: List<&2, U32>, +hok: {ok == True{} : Bool}, +e: {E.key_public(E.expand_ctx(ctx, seed)) == V : List<&2, U32>}) -> {SS.key_pub(SG.key_ctx_if(ctx, seed, ok)) == Some{V} : Maybe<&2, List<&2, U32>>}:
  match ok:
    case True{}:
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, z => Some{z}, E.key_public(E.expand_ctx(ctx, seed)), V, e)
    case False{}:
      Empty.absurd({SS.key_pub(SG.key_ctx_if(ctx, seed, False{})) == Some{V} : Maybe<&2, List<&2, U32>>}, L.true_false(Equal.sym(Bool, False{}, True{}, hok)))

def ed_public_ctx(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +seed: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}) -> SE.Ed25519.public_ctx(one, h1, xs, seed, hs):
  +pp = PB.pp1(one)
  +P = {1n+pp : Nat}
  +D = SE.dconst(one, P)
  +h = HS.hash(seed)
  +sh = SHA.sha512_bytes(seed)
  +cs = PT.consts(xs)
  +e1 = TC.public_rel(one, h1, pp, PRM.hP(one, h1), cs, PC.cr(one, h1, xs), D, PC.rd2(one, h1, pp, PRM.hP(one, h1), xs), PT.base(cs), TC.base_of(one, h1, xs), h, BY.sha_okb(seed))
  +e2 = Equal.cong(List<&2, U32>, List<&2, U32>, z => SE.public_of(one, P, D, z), h, sh, BY.sha_eq(seed))
  +e12 = Equal.trans(List<&2, U32>, E.public_key_ctx(E.context(xs), seed), E.public_go(E.context(xs), seed), SE.public_key_at(one, P, seed), PB.public_eq(E.context(xs), seed), Equal.trans(List<&2, U32>, E.public_go(E.context(xs), seed), SE.public_of(one, P, D, h), SE.public_key_at(one, P, seed), e1, e2))
  L.subst(Nat, z => {E.public_key_ctx(E.context(xs), seed) == SE.public_key_at(one, z, seed) : List<&2, U32>}, P, FS.prime(one), Equal.sym(Nat, FS.prime(one), P, PRM.prime_eq(one, h1)), e12)

def ed_public(+one: Nat, +h1: {one == 1n : Nat}, +seed: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}) -> SE.Ed25519.public(one, h1, seed, hs):
  ed_public_ctx(one, h1, seed, seed, hs)

def ed_key_public(+one: Nat, +h1: {one == 1n : Nat}, +seed: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}) -> SE.Ed25519.key_public(one, h1, seed, hs):
  Equal.trans(List<&2, U32>, E.key_public(E.expand(seed)), E.public_key(seed), SE.public_key(one, seed), PB.kp_eq(E.context(seed), seed), ed_public(one, h1, seed, hs))

def sign_keypair(+one: Nat, +h1: {one == 1n : Nat}, +seed: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}) -> SS.Sign.keypair(one, h1, seed, hs):
  keypair_if_eq(seed, X.valid_bytes(32n, seed), SE.public_key(one, seed), PB.valid_ok(32n, seed, hs), ed_public(one, h1, seed, hs))

def sign_key_public(+one: Nat, +h1: {one == 1n : Nat}, +seed: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}) -> SS.Sign.key_public(one, h1, seed, hs):
  key_pub_eq(seed, X.valid_bytes(32n, seed), SE.public_key(one, seed), PB.valid_ok(32n, seed, hs), ed_key_public(one, h1, seed, hs))

def sign_keypair_ctx(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +seed: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}) -> SS.Sign.keypair_ctx(one, h1, xs, seed, hs):
  keypair_ctx_if_eq(E.context(xs), seed, X.valid_bytes(32n, seed), SE.public_key(one, seed), PB.valid_ok(32n, seed, hs), ed_public_ctx(one, h1, xs, seed, hs))

def sign_key_public_ctx(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +seed: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}) -> SS.Sign.key_public_ctx(one, h1, xs, seed, hs):
  key_pub_ctx_eq(E.context(xs), seed, X.valid_bytes(32n, seed), SE.public_key(one, seed), PB.valid_ok(32n, seed, hs), Equal.trans(List<&2, U32>, E.key_public(E.expand_ctx(E.context(xs), seed)), E.public_key_ctx(E.context(xs), seed), SE.public_key(one, seed), PB.kp_eq(E.context(xs), seed), ed_public_ctx(one, h1, xs, seed, hs)))
