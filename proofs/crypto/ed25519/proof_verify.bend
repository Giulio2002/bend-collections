import Base
import ../../../src/crypto/sign.bend as SG
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/ed25519.bend as SE
import ../../../src/crypto/curve25519/field.bend as F
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../../src/crypto/ed25519/point.bend as PT
import ../../../src/crypto/ed25519/scalar.bend as ESC
import ../../../src/crypto/ed25519/ed25519.bend as E
import ../../lib/logic.bend as L
import ./scalar3.bend as S3
import ./bytes.bend as BY
import ../../../spec/crypto/sign.bend as SS
import ../curve25519/prime.bend as PRM
import ./tverify.bend as TV
import ./pbase.bend as PB
import ./tscal.bend as TH
import ./fbspec.bend as FB

# Gate: Ed25519.verify and Sign.verify, for every key, message and
# signature.

def verify_if_eq(+pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>, +ok: Bool, +V: Bool, +hok: {ok == True{} : Bool}, +e: {E.verify_raw(pk, msg, sig) == V : Bool}) -> {SG.verify_if(pk, msg, sig, ok) == V : Bool}:
  match ok:
    case True{}:
      e
    case False{}:
      Empty.absurd({SG.verify_if(pk, msg, sig, False{}) == V : Bool}, L.true_false(Equal.sym(Bool, False{}, True{}, hok)))

def verify_ctx_if_eq(+ctx: E.Ctx, +pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>, +ok: Bool, +V: Bool, +hok: {ok == True{} : Bool}, +e: {E.verify_ctx(ctx, pk, msg, sig) == V : Bool}) -> {SG.verify_ctx_if(ctx, pk, msg, sig, ok) == V : Bool}:
  match ok:
    case True{}:
      e
    case False{}:
      Empty.absurd({SG.verify_ctx_if(ctx, pk, msg, sig, False{}) == V : Bool}, L.true_false(Equal.sym(Bool, False{}, True{}, hok)))

def ed_verify_ctx(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>, +hp: {FS.tight(pk) == True{} : Bool}, +hg: {FS.bytes_ok(64n, sig) == True{} : Bool}, lq: FB.LawQ(one, PB.pp1(one)), lw: FB.LawW(one, PB.pp1(one)), lv1: FB.LawV(one, PB.pp1(one)), lv2: FB.LawV(one, PB.pp1(one))) -> SE.Ed25519.verify_ctx(one, h1, xs, pk, msg, sig, hp, hg):
  +pp = PB.pp1(one)
  +P = {1n+pp : Nat}
  +D = SE.dconst(one, P)
  +el = SE.ell(one)
  +cs = PT.consts(xs)
  +B = PT.base(cs)
  +hsig = PB.ok(64n, sig, hg)
  +rb = F.take(32n, sig)
  +sb = F.drop(32n, sig)
  +srb = SE.first(32n, sig)
  +ssb = SE.rest(32n, sig)
  +hrb = BY.take_okb(32n, 32n, sig, 255n, hsig)
  +hsb = BY.drop_okb(32n, 32n, sig, 255n, hsig)
  +lt = Nat.is_lt(FS.value(sb), el)
  +slt = Nat.is_lt(FS.value(ssb), el)
  +e0 = Equal.trans(Bool, ESC.lt_l(sb), Nat.is_lt(FS.value(sb), 1n+S3.mmL(one)), lt, S3.lt_l_m(one, h1, sb, hsb), Equal.cong(Nat, Bool, z => Nat.is_lt(FS.value(sb), z), 1n+S3.mmL(one), el, TH.ell_m(one, h1)))
  +e1 = Equal.cong(Bool, Bool, z => E.verify_with_t(cs, PT.base_table(cs, B), pk, msg, rb, sb, z), ESC.lt_l(sb), lt, e0)
  +e2 = TV.verify_with_rel_t(one, h1, pp, PRM.hP(one, h1), xs, pk, PB.ok(32n, pk, hp), msg, rb, hrb, sb, hsb, lt, lq, lw, lv1, lv2)
  +e3 = Equal.cong(List<&2, U32>, Bool, z => SE.verify_with(one, P, D, pk, msg, z, FS.value(sb), lt), rb, srb, BY.take_eq(32n, sig))
  +e4 = Equal.cong(List<&2, U32>, Bool, z => SE.verify_with(one, P, D, pk, msg, srb, FS.value(z), Nat.is_lt(FS.value(z), el)), sb, ssb, BY.drop_eq(32n, sig))
  +e5 = Equal.cong(Nat, Bool, z => SE.verify_with(one, z, SE.dconst(one, z), pk, msg, srb, FS.value(ssb), slt), P, FS.prime(one), Equal.sym(Nat, FS.prime(one), P, PRM.prime_eq(one, h1)))
  +V0 = E.verify_with_t(cs, PT.base_table(cs, B), pk, msg, rb, sb, ESC.lt_l(sb))
  +V1 = E.verify_with_t(cs, PT.base_table(cs, B), pk, msg, rb, sb, lt)
  +V2 = SE.verify_with(one, P, D, pk, msg, rb, FS.value(sb), lt)
  +V3 = SE.verify_with(one, P, D, pk, msg, srb, FS.value(sb), lt)
  +V4 = SE.verify_with(one, P, D, pk, msg, srb, FS.value(ssb), slt)
  +V5 = SE.verify_with(one, FS.prime(one), SE.dconst(one, FS.prime(one)), pk, msg, srb, FS.value(ssb), slt)
  Equal.trans(Bool, E.verify_ctx(E.context(xs), pk, msg, sig), V0, V5, PB.verify_eq(E.context(xs), pk, msg, sig), Equal.trans(Bool, V0, V1, V5, e1, Equal.trans(Bool, V1, V2, V5, e2, Equal.trans(Bool, V2, V3, V5, e3, Equal.trans(Bool, V3, V4, V5, e4, e5)))))

def ed_verify(+one: Nat, +h1: {one == 1n : Nat}, +pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>, +hp: {FS.tight(pk) == True{} : Bool}, +hg: {FS.bytes_ok(64n, sig) == True{} : Bool}) -> SE.Ed25519.verify(one, h1, pk, msg, sig, hp, hg):
  +pp = PB.pp1(one)
  +P = {1n+pp : Nat}
  +D = SE.dconst(one, P)
  +el = SE.ell(one)
  +cs = PT.consts(pk)
  +B = PT.base(cs)
  +hsig = PB.ok(64n, sig, hg)
  +rb = F.take(32n, sig)
  +sb = F.drop(32n, sig)
  +srb = SE.first(32n, sig)
  +ssb = SE.rest(32n, sig)
  +hrb = BY.take_okb(32n, 32n, sig, 255n, hsig)
  +hsb = BY.drop_okb(32n, 32n, sig, 255n, hsig)
  +lt = Nat.is_lt(FS.value(sb), el)
  +slt = Nat.is_lt(FS.value(ssb), el)
  +e0 = Equal.trans(Bool, ESC.lt_l(sb), Nat.is_lt(FS.value(sb), 1n+S3.mmL(one)), lt, S3.lt_l_m(one, h1, sb, hsb), Equal.cong(Nat, Bool, z => Nat.is_lt(FS.value(sb), z), 1n+S3.mmL(one), el, TH.ell_m(one, h1)))
  +e1 = Equal.cong(Bool, Bool, z => E.verify_with(cs, B, pk, msg, rb, sb, z), ESC.lt_l(sb), lt, e0)
  +e2 = TV.verify_with_rel(one, h1, pp, PRM.hP(one, h1), pk, pk, PB.ok(32n, pk, hp), msg, rb, hrb, sb, hsb, lt)
  +e3 = Equal.cong(List<&2, U32>, Bool, z => SE.verify_with(one, P, D, pk, msg, z, FS.value(sb), lt), rb, srb, BY.take_eq(32n, sig))
  +e4 = Equal.cong(List<&2, U32>, Bool, z => SE.verify_with(one, P, D, pk, msg, srb, FS.value(z), Nat.is_lt(FS.value(z), el)), sb, ssb, BY.drop_eq(32n, sig))
  +e5 = Equal.cong(Nat, Bool, z => SE.verify_with(one, z, SE.dconst(one, z), pk, msg, srb, FS.value(ssb), slt), P, FS.prime(one), Equal.sym(Nat, FS.prime(one), P, PRM.prime_eq(one, h1)))
  +V0 = E.verify_with(cs, B, pk, msg, rb, sb, ESC.lt_l(sb))
  +V1 = E.verify_with(cs, B, pk, msg, rb, sb, lt)
  +V2 = SE.verify_with(one, P, D, pk, msg, rb, FS.value(sb), lt)
  +V3 = SE.verify_with(one, P, D, pk, msg, srb, FS.value(sb), lt)
  +V4 = SE.verify_with(one, P, D, pk, msg, srb, FS.value(ssb), slt)
  +V5 = SE.verify_with(one, FS.prime(one), SE.dconst(one, FS.prime(one)), pk, msg, srb, FS.value(ssb), slt)
  Equal.trans(Bool, E.verify_raw(pk, msg, sig), V0, V5, PB.verify1_eq(E.lite(pk), pk, msg, sig), Equal.trans(Bool, V0, V1, V5, e1, Equal.trans(Bool, V1, V2, V5, e2, Equal.trans(Bool, V2, V3, V5, e3, Equal.trans(Bool, V3, V4, V5, e4, e5)))))

def sign_verify(+one: Nat, +h1: {one == 1n : Nat}, +pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>, +hp: {FS.tight(pk) == True{} : Bool}, +hg: {FS.bytes_ok(64n, sig) == True{} : Bool}) -> SS.Sign.verify(one, h1, pk, msg, sig, hp, hg):
  verify_if_eq(pk, msg, sig, Bool.and(X.valid_bytes(32n, pk), X.valid_bytes(64n, sig)), SE.verify(one, pk, msg, sig), L.and_intro(X.valid_bytes(32n, pk), X.valid_bytes(64n, sig), PB.valid_ok(32n, pk, hp), PB.valid_ok(64n, sig, hg)), ed_verify(one, h1, pk, msg, sig, hp, hg))

def sign_verify_ctx(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>, +hp: {FS.tight(pk) == True{} : Bool}, +hg: {FS.bytes_ok(64n, sig) == True{} : Bool}, lq: FB.LawQ(one, PB.pp1(one)), lw: FB.LawW(one, PB.pp1(one)), lv1: FB.LawV(one, PB.pp1(one)), lv2: FB.LawV(one, PB.pp1(one))) -> SS.Sign.verify_ctx(one, h1, xs, pk, msg, sig, hp, hg):
  verify_ctx_if_eq(E.context(xs), pk, msg, sig, Bool.and(X.valid_bytes(32n, pk), X.valid_bytes(64n, sig)), SE.verify(one, pk, msg, sig), L.and_intro(X.valid_bytes(32n, pk), X.valid_bytes(64n, sig), PB.valid_ok(32n, pk, hp), PB.valid_ok(64n, sig, hg)), ed_verify_ctx(one, h1, xs, pk, msg, sig, hp, hg, lq, lw, lv1, lv2))
