import Base
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/ed25519.bend as SE
import ../../../src/crypto/ed25519/point.bend as PT
import ../../../src/crypto/ed25519/ed25519.bend as E
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../curve25519/limbs.bend as LM
import ./prel.bend as PR
import ./pcodec.bend as PC
import ./pdec.bend as PD
import ./tcommon.bend as TC

# Verification (RFC 8032 5.1.7) against spec/crypto/ed25519.bend.

def check_some(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +xs: List<&2, U32>, +pk: List<&2, U32>, +msg: List<&2, U32>, +rb: List<&2, U32>, +sb: List<&2, U32>, +hsb: {LM.okb(32n, sb, 255n) == True{} : Bool}, +r: PT.Pt, +sr: SE.EPt, +hr: PR.Rp(one, pp, r, sr), +a: PT.Pt, +sa: SE.EPt, +ha: PR.Rp(one, pp, a, sa)) -> {E.check(PT.consts(xs), PT.base(PT.consts(xs)), sb, rb, pk, msg, Some{r}, Some{a}) == SE.check(one, 1n+pp, SE.dconst(one, 1n+pp), FS.value(sb), rb, pk, msg, Some{sr}, Some{sa}) : Bool}:
  +P = {1n+pp : Nat}
  +D = SE.dconst(one, P)
  +cs = PT.consts(xs)
  +R = PT.cs_r(cs)
  +hR = PC.cr(one, h1, xs)
  +B = PT.base(cs)
  +SB = SE.base(P, D)
  +hB = PD.base_rel(one, h1, pp, hP, cs, hR, D, PC.rd(one, h1, pp, hP, xs), PC.rs(one, h1, pp, hP, xs))
  +rd2 = PC.rd2(one, h1, pp, hP, xs)
  +k = E.hram(rb, pk, msg)
  +Ks = SE.hram(one, rb, pk, msg)
  +eK = TC.hk_val(one, h1, rb, rb, {==}, pk, pk, {==}, msg)
  +okk = TC.hk_okb(one, h1, rb, pk, msg)
  +ka = PT.mul_vt(cs, k, a)
  +ska = SE.mul(one, P, D, FS.value(k), sa)
  +m1 = TC.mul_vt_rel(one, h1, pp, hP, cs, hR, D, rd2, sb, hsb, B, SB, hB)
  +m2 = TC.mul_vt_rel(one, h1, pp, hP, cs, hR, D, rd2, k, okk, a, sa, ha)
  +ad = PR.add_rel(one, h1, pp, hP, cs, hR, D, rd2, r, ka, sr, ska, hr, m2)
  +lhs = SE.mul(one, P, D, FS.value(sb), SB)
  +eq = PC.equal_rel(one, h1, pp, hP, R, hR, PT.mul_vt(cs, sb, B), PT.add(cs, r, ka), lhs, SE.add(P, D, sr, ska), m1, ad)
  Equal.trans(Bool, PT.equal(R, PT.mul_vt(cs, sb, B), PT.add(cs, r, ka)), SE.equal(P, lhs, SE.add(P, D, sr, ska)), SE.equal(P, lhs, SE.add(P, D, sr, SE.mul(one, P, D, Ks, sa))), eq, Equal.cong(Nat, Bool, z => SE.equal(P, lhs, SE.add(P, D, sr, SE.mul(one, P, D, z, sa))), FS.value(k), Ks, eK))

def check_a(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +xs: List<&2, U32>, +pk: List<&2, U32>, +msg: List<&2, U32>, +rb: List<&2, U32>, +sb: List<&2, U32>, +hsb: {LM.okb(32n, sb, 255n) == True{} : Bool}, +r: PT.Pt, +sr: SE.EPt, +hr: PR.Rp(one, pp, r, sr), +aa: Maybe<&2, PT.Pt>, +saa: Maybe<&2, SE.EPt>, +haa: PC.MR(one, pp, aa, saa)) -> {E.check(PT.consts(xs), PT.base(PT.consts(xs)), sb, rb, pk, msg, Some{r}, aa) == SE.check(one, 1n+pp, SE.dconst(one, 1n+pp), FS.value(sb), rb, pk, msg, Some{sr}, saa) : Bool}:
  match aa saa:
    case None{} None{}:
      {==}
    case Some{+a} Some{+sa}:
      check_some(one, h1, pp, hP, xs, pk, msg, rb, sb, hsb, r, sr, hr, a, sa, haa)
    case None{} Some{+sa}:
      Empty.absurd({E.check(PT.consts(xs), PT.base(PT.consts(xs)), sb, rb, pk, msg, Some{r}, None{}) == SE.check(one, 1n+pp, SE.dconst(one, 1n+pp), FS.value(sb), rb, pk, msg, Some{sr}, Some{sa}) : Bool}, L.true_false(haa))
    case Some{+a} None{}:
      Empty.absurd({E.check(PT.consts(xs), PT.base(PT.consts(xs)), sb, rb, pk, msg, Some{r}, Some{a}) == SE.check(one, 1n+pp, SE.dconst(one, 1n+pp), FS.value(sb), rb, pk, msg, Some{sr}, None{}) : Bool}, L.true_false(haa))

def check_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +xs: List<&2, U32>, +pk: List<&2, U32>, +msg: List<&2, U32>, +rb: List<&2, U32>, +sb: List<&2, U32>, +hsb: {LM.okb(32n, sb, 255n) == True{} : Bool}, +ra: Maybe<&2, PT.Pt>, +sra: Maybe<&2, SE.EPt>, +hra: PC.MR(one, pp, ra, sra), +aa: Maybe<&2, PT.Pt>, +saa: Maybe<&2, SE.EPt>, +haa: PC.MR(one, pp, aa, saa)) -> {E.check(PT.consts(xs), PT.base(PT.consts(xs)), sb, rb, pk, msg, ra, aa) == SE.check(one, 1n+pp, SE.dconst(one, 1n+pp), FS.value(sb), rb, pk, msg, sra, saa) : Bool}:
  match ra sra:
    case None{} None{}:
      {==}
    case Some{+r} Some{+sr}:
      check_a(one, h1, pp, hP, xs, pk, msg, rb, sb, hsb, r, sr, hra, aa, saa, haa)
    case None{} Some{+sr}:
      Empty.absurd({E.check(PT.consts(xs), PT.base(PT.consts(xs)), sb, rb, pk, msg, None{}, aa) == SE.check(one, 1n+pp, SE.dconst(one, 1n+pp), FS.value(sb), rb, pk, msg, Some{sr}, saa) : Bool}, L.true_false(hra))
    case Some{+r} None{}:
      Empty.absurd({E.check(PT.consts(xs), PT.base(PT.consts(xs)), sb, rb, pk, msg, Some{r}, aa) == SE.check(one, 1n+pp, SE.dconst(one, 1n+pp), FS.value(sb), rb, pk, msg, None{}, saa) : Bool}, L.true_false(hra))

def verify_with_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +xs: List<&2, U32>, +pk: List<&2, U32>, +hpk: {LM.okb(32n, pk, 255n) == True{} : Bool}, +msg: List<&2, U32>, +rb: List<&2, U32>, +hrb: {LM.okb(32n, rb, 255n) == True{} : Bool}, +sb: List<&2, U32>, +hsb: {LM.okb(32n, sb, 255n) == True{} : Bool}, +s_ok: Bool) -> {E.verify_with(PT.consts(xs), PT.base(PT.consts(xs)), pk, msg, rb, sb, s_ok) == SE.verify_with(one, 1n+pp, SE.dconst(one, 1n+pp), pk, msg, rb, FS.value(sb), s_ok) : Bool}:
  match s_ok:
    case True{}:
      +P = {1n+pp : Nat}
      +D = SE.dconst(one, P)
      +cs = PT.consts(xs)
      +hR = PC.cr(one, h1, xs)
      +rd = PC.rd(one, h1, pp, hP, xs)
      +rs = PC.rs(one, h1, pp, hP, xs)
      check_rel(one, h1, pp, hP, xs, pk, msg, rb, sb, hsb, PT.decode(cs, rb), SE.decode(P, D, rb), PD.decode_rel(one, h1, pp, hP, cs, hR, D, rd, rs, rb, hrb), PT.decode(cs, pk), SE.decode(P, D, pk), PD.decode_rel(one, h1, pp, hP, cs, hR, D, rd, rs, pk, hpk))
    case False{}:
      {==}
