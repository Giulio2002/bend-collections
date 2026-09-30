import Base
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../../src/crypto/ed25519/ed25519.bend as E
import ../../lib/logic.bend as L
import ../curve25519/limbs.bend as LM
import ../../../src/crypto/sign.bend as SG
import ../../../spec/crypto/sign.bend as SS
import ../../lib/u32.bend as U
import ../curve25519/prime.bend as PRM

# Helpers of the Ed25519 proof roots: p - 1, byte bounds, L, the facade's
# optional results.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def pp1(+one: Nat) -> Nat:
  PRM.pp_of(one)

def ok(+n: Nat, +a: List<&2, U32>, +h: {FS.bytes_ok(n, a) == True{} : Bool}) -> {LM.okb(n, a, 255n) == True{} : Bool}:
  LM.bytes_okb(n, a, h)

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

def valid_ok(+n: Nat, +xs: List<&2, U32>, +h: {FS.bytes_ok(n, xs) == True{} : Bool}) -> {X.valid_bytes(n, xs) == True{} : Bool}:
  Equal.trans(Bool, X.valid_bytes(n, xs), FS.bytes_ok(n, xs), True{}, valid_eq(n, xs), h)

def keypair_if_eq(+seed: List<&2, U32>, +ok: Bool, +pk: List<&2, U32>, +hok: {ok == True{} : Bool}, +e: {E.public_key(seed) == pk : List<&2, U32>}) -> {SG.keypair_if(seed, ok) == Some{SG.Keypair{seed, pk}} : Maybe<&2, SG.Keypair>}:
  match ok:
    case True{}:
      Equal.cong(List<&2, U32>, Maybe<&2, SG.Keypair>, z => Some{SG.Keypair{seed, z}}, E.public_key(seed), pk, e)
    case False{}:
      Empty.absurd({SG.keypair_if(seed, False{}) == Some{SG.Keypair{seed, pk}} : Maybe<&2, SG.Keypair>}, L.true_false(Equal.sym(Bool, False{}, True{}, hok)))

def sign_if_eq(+sk: List<&2, U32>, +msg: List<&2, U32>, +ok: Bool, +S: List<&2, U32>, +hok: {ok == True{} : Bool}, +e: {E.sign_raw(sk, msg) == S : List<&2, U32>}) -> {SG.sign_if(sk, msg, ok) == Some{S} : Maybe<&2, List<&2, U32>>}:
  match ok:
    case True{}:
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, z => Some{z}, E.sign_raw(sk, msg), S, e)
    case False{}:
      Empty.absurd({SG.sign_if(sk, msg, False{}) == Some{S} : Maybe<&2, List<&2, U32>>}, L.true_false(Equal.sym(Bool, False{}, True{}, hok)))

def verify_if_eq(+pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>, +ok: Bool, +V: Bool, +hok: {ok == True{} : Bool}, +e: {E.verify_raw(pk, msg, sig) == V : Bool}) -> {SG.verify_if(pk, msg, sig, ok) == V : Bool}:
  match ok:
    case True{}:
      e
    case False{}:
      Empty.absurd({SG.verify_if(pk, msg, sig, False{}) == V : Bool}, L.true_false(Equal.sym(Bool, False{}, True{}, hok)))

def key_pub_eq(+seed: List<&2, U32>, +ok: Bool, +V: List<&2, U32>, +hok: {ok == True{} : Bool}, +e: {E.key_public(E.expand(seed)) == V : List<&2, U32>}) -> {SS.key_pub(SG.key_if(seed, ok)) == Some{V} : Maybe<&2, List<&2, U32>>}:
  match ok:
    case True{}:
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, z => Some{z}, E.key_public(E.expand(seed)), V, e)
    case False{}:
      Empty.absurd({SS.key_pub(SG.key_if(seed, False{})) == Some{V} : Maybe<&2, List<&2, U32>>}, L.true_false(Equal.sym(Bool, False{}, True{}, hok)))

def key_sig_eq(+seed: List<&2, U32>, +msg: List<&2, U32>, +ok: Bool, +S: List<&2, U32>, +hok: {ok == True{} : Bool}, +e: {E.sign_key(E.expand(seed), msg) == S : List<&2, U32>}) -> {SS.key_sig(SG.key_if(seed, ok), msg) == Some{S} : Maybe<&2, List<&2, U32>>}:
  match ok:
    case True{}:
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, z => Some{z}, E.sign_key(E.expand(seed), msg), S, e)
    case False{}:
      Empty.absurd({SS.key_sig(SG.key_if(seed, False{}), msg) == Some{S} : Maybe<&2, List<&2, U32>>}, L.true_false(Equal.sym(Bool, False{}, True{}, hok)))

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

def key_sig_ctx_eq(+ctx: E.Ctx, +seed: List<&2, U32>, +msg: List<&2, U32>, +ok: Bool, +S: List<&2, U32>, +hok: {ok == True{} : Bool}, +e: {E.sign_key(E.expand_ctx(ctx, seed), msg) == S : List<&2, U32>}) -> {SS.key_sig(SG.key_ctx_if(ctx, seed, ok), msg) == Some{S} : Maybe<&2, List<&2, U32>>}:
  match ok:
    case True{}:
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, z => Some{z}, E.sign_key(E.expand_ctx(ctx, seed), msg), S, e)
    case False{}:
      Empty.absurd({SS.key_sig(SG.key_ctx_if(ctx, seed, False{}), msg) == Some{S} : Maybe<&2, List<&2, U32>>}, L.true_false(Equal.sym(Bool, False{}, True{}, hok)))

def verify_ctx_if_eq(+ctx: E.Ctx, +pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>, +ok: Bool, +V: Bool, +hok: {ok == True{} : Bool}, +e: {E.verify_ctx(ctx, pk, msg, sig) == V : Bool}) -> {SG.verify_ctx_if(ctx, pk, msg, sig, ok) == V : Bool}:
  match ok:
    case True{}:
      e
    case False{}:
      Empty.absurd({SG.verify_ctx_if(ctx, pk, msg, sig, False{}) == V : Bool}, L.true_false(Equal.sym(Bool, False{}, True{}, hok)))
