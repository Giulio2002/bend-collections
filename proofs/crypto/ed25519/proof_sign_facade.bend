import Base
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/ed25519.bend as SE
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../../src/crypto/ed25519/ed25519.bend as E
import ../../lib/logic.bend as L
import ../../../spec/crypto/sign.bend as SS
import ./pbase.bend as PB
import ../../../src/crypto/sign.bend as SG
import ./tsigncore.bend as TK
import ./fbspec.bend as FB

# Gate: Sign.sign, Sign.key_sign, Sign.key_sign_ctx (spec/crypto/sign.bend),
# for every seed and message (Ed25519.sign_ctx: tsigncore.bend).

def sign_if_eq(+sk: List<&2, U32>, +msg: List<&2, U32>, +ok: Bool, +S: List<&2, U32>, +hok: {ok == True{} : Bool}, +e: {E.sign_raw(sk, msg) == S : List<&2, U32>}) -> {SG.sign_if(sk, msg, ok) == Some{S} : Maybe<&2, List<&2, U32>>}:
  match ok:
    case True{}:
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, z => Some{z}, E.sign_raw(sk, msg), S, e)
    case False{}:
      Empty.absurd({SG.sign_if(sk, msg, False{}) == Some{S} : Maybe<&2, List<&2, U32>>}, L.true_false(Equal.sym(Bool, False{}, True{}, hok)))

def key_sig_eq(+seed: List<&2, U32>, +msg: List<&2, U32>, +ok: Bool, +S: List<&2, U32>, +hok: {ok == True{} : Bool}, +e: {E.sign_key(E.expand(seed), msg) == S : List<&2, U32>}) -> {SS.key_sig(SG.key_if(seed, ok), msg) == Some{S} : Maybe<&2, List<&2, U32>>}:
  match ok:
    case True{}:
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, z => Some{z}, E.sign_key(E.expand(seed), msg), S, e)
    case False{}:
      Empty.absurd({SS.key_sig(SG.key_if(seed, False{}), msg) == Some{S} : Maybe<&2, List<&2, U32>>}, L.true_false(Equal.sym(Bool, False{}, True{}, hok)))

def key_sig_ctx_eq(+ctx: E.Ctx, +seed: List<&2, U32>, +msg: List<&2, U32>, +ok: Bool, +S: List<&2, U32>, +hok: {ok == True{} : Bool}, +e: {E.sign_key(E.expand_ctx(ctx, seed), msg) == S : List<&2, U32>}) -> {SS.key_sig(SG.key_ctx_if(ctx, seed, ok), msg) == Some{S} : Maybe<&2, List<&2, U32>>}:
  match ok:
    case True{}:
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, z => Some{z}, E.sign_key(E.expand_ctx(ctx, seed), msg), S, e)
    case False{}:
      Empty.absurd({SS.key_sig(SG.key_ctx_if(ctx, seed, False{}), msg) == Some{S} : Maybe<&2, List<&2, U32>>}, L.true_false(Equal.sym(Bool, False{}, True{}, hok)))

def ed_sign(+one: Nat, +h1: {one == 1n : Nat}, +seed: List<&2, U32>, +msg: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}) -> SE.Ed25519.sign(one, h1, seed, msg, hs):
  TK.ed_sign_one(one, h1, seed, msg, hs)

def ed_sign_key(+one: Nat, +h1: {one == 1n : Nat}, +seed: List<&2, U32>, +msg: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}, lw1: FB.LawE(one, PB.pp1(one)), lw2: FB.LawE(one, PB.pp1(one))) -> SE.Ed25519.sign_key(one, h1, seed, msg, hs):
  TK.ed_sign_ctx(one, h1, seed, seed, msg, hs, lw1, lw2)

# ---- the facade, src/crypto/sign.bend ----

def sign_sign(+one: Nat, +h1: {one == 1n : Nat}, +sk: List<&2, U32>, +msg: List<&2, U32>, +hs: {FS.tight(sk) == True{} : Bool}) -> SS.Sign.sign(one, h1, sk, msg, hs):
  sign_if_eq(sk, msg, X.valid_bytes(32n, sk), SE.sign(one, sk, msg), PB.valid_ok(32n, sk, hs), ed_sign(one, h1, sk, msg, hs))

def sign_key_sign(+one: Nat, +h1: {one == 1n : Nat}, +seed: List<&2, U32>, +msg: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}, lw1: FB.LawE(one, PB.pp1(one)), lw2: FB.LawE(one, PB.pp1(one))) -> SS.Sign.key_sign(one, h1, seed, msg, hs):
  key_sig_eq(seed, msg, X.valid_bytes(32n, seed), SE.sign(one, seed, msg), PB.valid_ok(32n, seed, hs), ed_sign_key(one, h1, seed, msg, hs, lw1, lw2))

def sign_key_sign_ctx(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +seed: List<&2, U32>, +msg: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}, lw1: FB.LawE(one, PB.pp1(one)), lw2: FB.LawE(one, PB.pp1(one))) -> SS.Sign.key_sign_ctx(one, h1, xs, seed, msg, hs):
  key_sig_ctx_eq(E.context(xs), seed, msg, X.valid_bytes(32n, seed), SE.sign(one, seed, msg), PB.valid_ok(32n, seed, hs), TK.ed_sign_ctx(one, h1, xs, seed, msg, hs, lw1, lw2))
