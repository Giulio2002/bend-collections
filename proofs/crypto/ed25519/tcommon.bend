import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/x25519.bend as SX
import ../../../spec/crypto/ed25519.bend as SE
import ../../../src/crypto/curve25519/field.bend as F
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../../src/crypto/ed25519/point.bend as PT
import ../../../src/crypto/ed25519/ed25519.bend as E
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../curve25519/limbs.bend as LM
import ../curve25519/xbits.bend as XB
import ../fe/rel.bend as RE
import ./prel.bend as PR
import ./pcodec.bend as PC
import ./pdec.bend as PD
import ./bytes.bend as BY
import ../curve25519/prime.bend as PRM
import ./pbase.bend as PB
import ./pfb.bend as PFB
import ./fbspec.bend as FB

# Shared steps of the Ed25519 proofs: scalar multiplications and encoding
# related to the spec's, the scalars from digests, the public key.

def bits_eq(+one: Nat, +h1: {one == 1n : Nat}, +k: List<&2, U32>, +hk: {LM.okb(32n, k, 255n) == True{} : Bool}) -> {X.bitlen(k) == C.shift(8n, one) : Nat}:
  Equal.trans(Nat, X.bitlen(k), 256n, C.shift(8n, one), BY.bitlen_256(k, hk), Equal.cong(Nat, Nat, z => C.shift(8n, z), 1n, one, Equal.sym(Nat, one, 1n, h1)))

# [k] p, k 32 bytes: the implementation runs over bitlen(k) = 256 bits, the
# spec over 2^8 one

def mul_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd2: RE.Rel(one, pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +k: List<&2, U32>, +hk: {LM.okb(32n, k, 255n) == True{} : Bool}, +p: PT.Pt, +sp: SE.EPt, +hp: PR.Rp(one, pp, p, sp)) -> PR.Rp(one, pp, PT.mul(cs, k, p), SE.mul(one, 1n+pp, D, FS.value(k), sp)):
  %Equal.sym(Nat, X.bitlen(k), C.shift(8n, one), bits_eq(one, h1, k, hk)) : PR.Rp(one, pp, PT.smul(p, _, cs, k, PT.identity()), SE.mul(one, 1n+pp, D, FS.value(k), sp))
  PR.smul_rel(one, h1, pp, hP, p, C.shift(8n, one), cs, hR, D, rd2, k, LM.okb_lea(32n, k, 255n, hk), sp, hp, PT.identity(), SE.identity(), PD.identity_rel(one, h1, pp))

# the same for the branching multiplication (public scalars)

def mul_vt_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd2: RE.Rel(one, pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +k: List<&2, U32>, +hk: {LM.okb(32n, k, 255n) == True{} : Bool}, +p: PT.Pt, +sp: SE.EPt, +hp: PR.Rp(one, pp, p, sp)) -> PR.Rp(one, pp, PT.mul_vt(cs, k, p), SE.mul(one, 1n+pp, D, FS.value(k), sp)):
  %Equal.sym(Nat, X.bitlen(k), C.shift(8n, one), bits_eq(one, h1, k, hk)) : PR.Rp(one, pp, PT.smul_vt(p, _, cs, k, PT.identity()), SE.mul(one, 1n+pp, D, FS.value(k), sp))
  PR.smul_vt_rel(one, h1, pp, hP, p, C.shift(8n, one), cs, hR, D, rd2, k, LM.okb_lea(32n, k, 255n, hk), sp, hp, PT.identity(), SE.identity(), PD.identity_rel(one, h1, pp))

# encode, the spec's byte count 2^5 one

def enc_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +p: PT.Pt, +sp: SE.EPt, +hp: PR.Rp(one, pp, p, sp)) -> {PT.encode(R, p) == SE.encode(one, 1n+pp, sp) : List<&2, U32>}:
  L.subst(Nat, z => {PT.encode(R, p) == SE.encode_n(z, 1n+pp, sp) : List<&2, U32>}, 32n, C.shift(5n, one), Equal.cong(Nat, Nat, z => C.shift(5n, z), 1n, one, Equal.sym(Nat, one, 1n, h1)), PC.encode_rel(one, h1, pp, hP, R, hR, p, sp, hp))

# ---- scalars from digests ----

def secret_eq(+h: List<&2, U32>) -> {FS.value(X.clamp(F.take(32n, h))) == SE.secret(h) : Nat}:
  +t = F.take(32n, h)
  +st = SE.first(32n, h)
  Equal.cong(List<&2, U32>, Nat, z => FS.value(z), X.clamp(t), SX.clamp(st), Equal.trans(List<&2, U32>, X.clamp(t), SX.clamp(t), SX.clamp(st), XB.clamp_eq(t), Equal.cong(List<&2, U32>, List<&2, U32>, z => SX.clamp(z), t, st, BY.take_eq(32n, h))))

def public_body_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd2: RE.Rel(one, pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +B: PT.Pt, +hB: PR.Rp(one, pp, B, SE.base(1n+pp, D)), +h: List<&2, U32>, +hh: {LM.okb(64n, h, 255n) == True{} : Bool}) -> {E.public_of(cs, B, h) == SE.public_body(one, 1n+pp, D, h) : List<&2, U32>}:
  +P = {1n+pp : Nat}
  +R = PT.cs_r(cs)
  +sk = X.clamp(F.take(32n, h))
  +hs = XB.clamp_okb(F.take(32n, h), BY.take_okb(32n, 32n, h, 255n, hh))
  +SB = SE.base(P, D)
  +rm = mul_rel(one, h1, pp, hP, cs, hR, D, rd2, sk, hs, B, SB, hB)
  +e1 = enc_rel(one, h1, pp, hP, R, hR, PT.mul(cs, sk, B), SE.mul(one, P, D, FS.value(sk), SB), rm)
  Equal.trans(List<&2, U32>, PT.encode(R, PT.mul(cs, sk, B)), SE.encode(one, P, SE.mul(one, P, D, FS.value(sk), SB)), SE.encode(one, P, SE.mul(one, P, D, SE.secret(h), SB)), e1, Equal.cong(Nat, List<&2, U32>, z => SE.encode(one, P, SE.mul(one, P, D, z, SB)), FS.value(sk), SE.secret(h), secret_eq(h)))

def pub_guard(+one: Nat, +p: Nat, +d: Nat, +h: List<&2, U32>, +x: List<&2, U32>, +e: {x == SE.public_body(one, p, d, h) : List<&2, U32>}) -> {x == SE.public_of(one, p, d, h) : List<&2, U32>}:
  match d:
    case 0n:
      e
    case 1n+ +q:
      e

def public_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd2: RE.Rel(one, pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +B: PT.Pt, +hB: PR.Rp(one, pp, B, SE.base(1n+pp, D)), +h: List<&2, U32>, +hh: {LM.okb(64n, h, 255n) == True{} : Bool}) -> {E.public_of(cs, B, h) == SE.public_of(one, 1n+pp, D, h) : List<&2, U32>}:
  pub_guard(one, 1n+pp, D, h, E.public_of(cs, B, h), public_body_rel(one, h1, pp, hP, cs, hR, D, rd2, B, hB, h, hh))

# the same with the table of the base point: the table form of [s]B
# (pfb.bend), then the group law (FB.LawE)
def public_t_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +rd2: RE.Rel(one, pp, PT.cs_d2(cs), FS.fadd(1n+pp, SE.dconst(one, 1n+pp), SE.dconst(one, 1n+pp))), +B: PT.Pt, +hB: PR.Rp(one, pp, B, SE.base(1n+pp, SE.dconst(one, 1n+pp))), +h: List<&2, U32>, +hh: {LM.okb(64n, h, 255n) == True{} : Bool}, lw: FB.LawE(one, pp)) -> {E.public_of_t(cs, PT.base_table(cs, B), h) == SE.public_of(one, 1n+pp, SE.dconst(one, 1n+pp), h) : List<&2, U32>}:
  +P = {1n+pp : Nat}
  +D = SE.dconst(one, P)
  +R = PT.cs_r(cs)
  +sk = X.clamp(F.take(32n, h))
  +hs = LM.okb_bytes(32n, sk, XB.clamp_okb(F.take(32n, h), BY.take_okb(32n, 32n, h, 255n, hh)))
  +SB = SE.base(P, D)
  +X0 = PT.mul_base(R, PT.base_table(cs, B), sk)
  +rm = PFB.mul_base_rel(one, h1, pp, hP, cs, hR, rd2, B, hB, sk, hs)
  +e1 = enc_rel(one, h1, pp, hP, R, hR, X0, FB.smulb(one, P, D, sk), rm)
  +e2 = lw(sk, hs)
  +e3 = Equal.cong(Nat, List<&2, U32>, z => SE.encode(one, P, SE.mul(one, P, D, z, SB)), FS.value(sk), SE.secret(h), secret_eq(h))
  pub_guard(one, P, D, h, E.public_of_t(cs, PT.base_table(cs, B), h), Equal.trans(List<&2, U32>, PT.encode(R, X0), SE.encode(one, P, FB.smulb(one, P, D, sk)), SE.public_body(one, P, D, h), e1, Equal.trans(List<&2, U32>, SE.encode(one, P, FB.smulb(one, P, D, sk)), SE.encode(one, P, SE.mul(one, P, D, FS.value(sk), SB)), SE.public_body(one, P, D, h), e2, e3)))

def base_of(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>) -> PR.Rp(one, PB.pp1(one), PT.base(PT.consts(xs)), SE.base(1n+PB.pp1(one), SE.dconst(one, 1n+PB.pp1(one)))):
  +pp = PB.pp1(one)
  +hP = PRM.hP(one, h1)
  PD.base_rel(one, h1, pp, hP, PT.consts(xs), PC.cr(one, h1, xs), SE.dconst(one, 1n+pp), PC.rd(one, h1, pp, hP, xs), PC.rs(one, h1, pp, hP, xs))
