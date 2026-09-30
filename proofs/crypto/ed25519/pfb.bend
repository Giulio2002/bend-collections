import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../spec/crypto/ed25519.bend as SE
import ../../../src/crypto/curve25519/limbs.bend as LS
import ../../../src/crypto/ed25519/point.bend as PT
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../math/natural/arith.bend as NR
import ../fe/nl.bend as NL
import ../fe/rel.bend as RE
import ../fe/pack.bend as PK
import ../fe/conv.bend as CV
import ./prel.bend as PR
import ./pdec.bend as PD
import ./ptab.bend as PT2
import ./pickr.bend as PKR
import ./fbspec.bend as FB
import ./pwinf.bend as WF

# The table multiplication of the base point
# (src/crypto/ed25519/point.bend fb, mul_base) against its mirror over the
# specification's points (fbspec.bend sfb, smulb): related point by point,
# for every table built from a related point and every list of digits
# below 16.

# every digit below 16
def dok(ds: List<&2, Nat>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{d, dt}:
      Bool.and(Nat.is_lt(d, 16n), dok(dt))

# 16 p
def dbl4_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +p: PT.Pt, +sp: SE.EPt, +hp: PR.Rp(one, pp, p, sp)) -> PR.Rp(one, pp, PT.dbl4(R, p), FB.sdbl4(1n+pp, sp)):
  +P = {1n+pp : Nat}
  +p1 = PT.double(R, p)
  +s1 = SE.double(P, sp)
  +g1 = PR.double_rel(one, h1, pp, hP, R, hR, p, sp, hp)
  +p2 = PT.double(R, p1)
  +s2 = SE.double(P, s1)
  +g2 = PR.double_rel(one, h1, pp, hP, R, hR, p1, s1, g1)
  +p3 = PT.double(R, p2)
  +s3 = SE.double(P, s2)
  +g3 = PR.double_rel(one, h1, pp, hP, R, hR, p2, s2, g2)
  PR.double_rel(one, h1, pp, hP, R, hR, p3, s3, g3)

# the sum over rows and digits, for the table of a related point
def fb_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd2: RE.Rel(one, pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +n: Nat, +p: PT.Pt, +sp: SE.EPt, +hp: PR.Rp(one, pp, p, sp), +ds: List<&2, Nat>, +hd: {dok(ds) == True{} : Bool}, +acc: PT.Pt, +sacc: SE.EPt, +hacc: PR.Rp(one, pp, acc, sacc)) -> PR.Rp(one, pp, PT.fb(PT.cs_r(cs), PT.table(n, cs, p), ds, acc), FB.sfb(1n+pp, D, FB.stab(n, 1n+pp, D, sp), ds, sacc)):
  match n:
    case 0n:
      hacc
    case 1n+ +k:
      match ds:
        case Nil{}:
          hacc
        case Con{+d, +dt}:
          +R = PT.cs_r(cs)
          +q = PT.look(d, PT.row(cs, p))
          +sq = FB.snth(d, FB.srow(1n+pp, D, sp))
          +hq = PKR.row_rel(one, h1, pp, hP, cs, hR, D, rd2, p, sp, hp, d, L.and_left(Nat.is_lt(d, 16n), dok(dt), hd))
          fb_rel(one, h1, pp, hP, cs, hR, D, rd2, k, PT.dbl4(R, p), FB.sdbl4(1n+pp, sp), dbl4_rel(one, h1, pp, hP, R, hR, p, sp, hp), dt, L.and_right(Nat.is_lt(d, 16n), dok(dt), hd), PT.add_c(R, acc, q), SE.add(1n+pp, D, sacc, sq), PT2.add_c_rel(one, h1, pp, hP, R, hR, D, acc, q, sacc, sq, hacc, hq))

# ---- indexed entries (public digits) ----

# entry j of [cached(m), cached(m + p), ...] (n entries) against the
# specification's [sm, sm + sp, ...]
def nth_go_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd2: RE.Rel(one, pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +n: Nat, +p: PT.Pt, +sp: SE.EPt, +hp: PR.Rp(one, pp, p, sp), +m: PT.Pt, +sm: SE.EPt, +hm: PR.Rp(one, pp, m, sm), +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}) -> PT2.Rc(one, pp, D, PT.nthc(j, PT.row_go(n, cs, p, m)), FB.snth(j, FB.srow_go(n, 1n+pp, D, sp, sm))):
  match n:
    case 0n:
      Empty.absurd(PT2.Rc(one, pp, D, PT.nthc(j, PT.row_go(0n, cs, p, m)), FB.snth(j, FB.srow_go(0n, 1n+pp, D, sp, sm))), N.lt_zero_absurd(j, hj))
    case 1n+ +k:
      match j:
        case 0n:
          PT2.cached_rel(one, h1, pp, hP, cs, hR, D, rd2, m, sm, hm)
        case 1n+ +j2:
          nth_go_rel(one, h1, pp, hP, cs, hR, D, rd2, k, p, sp, hp, PT.add(cs, m, p), SE.add(1n+pp, D, sm, sp), PR.add_rel(one, h1, pp, hP, cs, hR, D, rd2, m, p, sm, sp, hm, hp), j2, hj)

# entry d of the row of a related point, by index
def nth_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd2: RE.Rel(one, pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +p: PT.Pt, +sp: SE.EPt, +hp: PR.Rp(one, pp, p, sp), +d: Nat, +hd: {Nat.is_lt(d, 16n) == True{} : Bool}) -> PT2.Rc(one, pp, D, PT.nthc(d, PT.row(cs, p)), FB.snth(d, FB.srow(1n+pp, D, sp))):
  match d:
    case 0n:
      PT2.cached_rel(one, h1, pp, hP, cs, hR, D, rd2, PT.identity(), SE.identity(), PD.identity_rel(one, h1, pp))
    case 1n+ +j:
      nth_go_rel(one, h1, pp, hP, cs, hR, D, rd2, 15n, p, sp, hp, p, sp, hp, j, hd)

def fbv_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd2: RE.Rel(one, pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +n: Nat, +p: PT.Pt, +sp: SE.EPt, +hp: PR.Rp(one, pp, p, sp), +ds: List<&2, Nat>, +hd: {dok(ds) == True{} : Bool}, +acc: PT.Pt, +sacc: SE.EPt, +hacc: PR.Rp(one, pp, acc, sacc)) -> PR.Rp(one, pp, PT.fbv(PT.cs_r(cs), PT.table(n, cs, p), ds, acc), FB.sfb(1n+pp, D, FB.stab(n, 1n+pp, D, sp), ds, sacc)):
  match n:
    case 0n:
      hacc
    case 1n+ +k:
      match ds:
        case Nil{}:
          hacc
        case Con{+d, +dt}:
          +R = PT.cs_r(cs)
          +q = PT.nthc(d, PT.row(cs, p))
          +sq = FB.snth(d, FB.srow(1n+pp, D, sp))
          +hq = nth_rel(one, h1, pp, hP, cs, hR, D, rd2, p, sp, hp, d, L.and_left(Nat.is_lt(d, 16n), dok(dt), hd))
          fbv_rel(one, h1, pp, hP, cs, hR, D, rd2, k, PT.dbl4(R, p), FB.sdbl4(1n+pp, sp), dbl4_rel(one, h1, pp, hP, R, hR, p, sp, hp), dt, L.and_right(Nat.is_lt(d, 16n), dok(dt), hd), PT.add_c(R, acc, q), SE.add(1n+pp, D, sacc, sq), PT2.add_c_rel(one, h1, pp, hP, R, hR, D, acc, q, sacc, sq, hacc, hq))

# the digits of bytes below 256 are below 16
def nibs_ok(+bs: List<&2, U32>, +hb: {FV.below(LS.nat_of(bs), 256n) == True{} : Bool}) -> {dok(PT.nibs(bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +bt}:
      +n = U32.to_nat(b)
      L.and_intro(Nat.is_lt(Nat.mod(n, 16n), 16n), dok(Con{Nat.div(n, 16n), PT.nibs(bt)}), NR.dm_lt(15n, n), L.and_intro(Nat.is_lt(Nat.div(n, 16n), 16n), dok(PT.nibs(bt)), PK.div_ltk(4n, n, 16n, NL.below_head(n, LS.nat_of(bt), 256n, hb)), nibs_ok(bt, NL.below_tail(n, LS.nat_of(bt), 256n, hb))))

# the row count: 2^17 / 2^11 == 2^6
def cnt_eq(+one: Nat, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}) -> {Nat.div(R, 2048n) == C.shift(6n, one) : Nat}:
  +q = WD.sc(6n, one)
  +e1 = Equal.trans(Nat, Nat.add(Nat.mul(q, 2048n), 0n), Nat.mul(q, 2048n), R, N.add_zero(Nat.mul(q, 2048n)), Equal.trans(Nat, Nat.mul(q, 2048n), WD.sc(11n, q), R, AR.mul_sc(11n, q), Equal.sym(Nat, R, WD.sc(17n, one), hR)))
  L.subst(Nat, z => {Nat.div(z, 2048n) == q : Nat}, Nat.add(Nat.mul(q, 2048n), 0n), R, e1, NR.div_of(q, 2047n, 0n, {==}))

# [k] B by the table of a base point related to the specification's
def mul_base_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +rd2: RE.Rel(one, pp, PT.cs_d2(cs), FS.fadd(1n+pp, SE.dconst(one, 1n+pp), SE.dconst(one, 1n+pp))), +B: PT.Pt, +hB: PR.Rp(one, pp, B, SE.base(1n+pp, SE.dconst(one, 1n+pp))), +k: List<&2, U32>, +hk: {FS.bytes_ok(32n, k) == True{} : Bool}) -> PR.Rp(one, pp, PT.mul_base(PT.cs_r(cs), PT.base_table(cs, B), k), FB.smulb(one, 1n+pp, SE.dconst(one, 1n+pp), k)):
  +P = {1n+pp : Nat}
  +D = SE.dconst(one, P)
  +R = PT.cs_r(cs)
  +n = Nat.div(R, 2048n)
  +g = fb_rel(one, h1, pp, hP, cs, hR, D, rd2, n, B, SE.base(P, D), hB, PT.nibs(k), nibs_ok(k, CV.nat_below(32n, k, hk)), PT.identity(), SE.identity(), PD.identity_rel(one, h1, pp))
  L.subst(Nat, z => PR.Rp(one, pp, PT.fb(R, PT.table(n, cs, B), PT.nibs(k), PT.identity()), FB.sfb(P, D, FB.stab(z, P, D, SE.base(P, D)), PT.nibs(k), SE.identity())), n, C.shift(6n, one), cnt_eq(one, R, hR), g)

# the same with indexed entries (public scalars)
def mul_base_vt_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +rd2: RE.Rel(one, pp, PT.cs_d2(cs), FS.fadd(1n+pp, SE.dconst(one, 1n+pp), SE.dconst(one, 1n+pp))), +B: PT.Pt, +hB: PR.Rp(one, pp, B, SE.base(1n+pp, SE.dconst(one, 1n+pp))), +k: List<&2, U32>, +hk: {FS.bytes_ok(32n, k) == True{} : Bool}) -> PR.Rp(one, pp, PT.mul_base_vt(PT.cs_r(cs), PT.base_table(cs, B), k), FB.smulb(one, 1n+pp, SE.dconst(one, 1n+pp), k)):
  +P = {1n+pp : Nat}
  +D = SE.dconst(one, P)
  +R = PT.cs_r(cs)
  +n = Nat.div(R, 2048n)
  +g = fbv_rel(one, h1, pp, hP, cs, hR, D, rd2, n, B, SE.base(P, D), hB, PT.nibs(k), nibs_ok(k, CV.nat_below(32n, k, hk)), PT.identity(), SE.identity(), PD.identity_rel(one, h1, pp))
  L.subst(Nat, z => PR.Rp(one, pp, PT.fbv(R, PT.table(n, cs, B), PT.nibs(k), PT.identity()), FB.sfb(P, D, FB.stab(z, P, D, SE.base(P, D)), PT.nibs(k), SE.identity())), n, C.shift(6n, one), cnt_eq(one, R, hR), g)

# ---- 4-bit windows ----

def win_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd2: RE.Rel(one, pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +a: PT.Pt, +sa: SE.EPt, +ha: PR.Rp(one, pp, a, sa), +ds: List<&2, Nat>, +hd: {dok(ds) == True{} : Bool}) -> PR.Rp(one, pp, PT.win(PT.cs_r(cs), PT.row(cs, a), ds), FB.swin(1n+pp, D, FB.srow(1n+pp, D, sa), ds)):
  match ds:
    case Nil{}:
      PD.identity_rel(one, h1, pp)
    case Con{+d, +dt}:
      +R = PT.cs_r(cs)
      +w = PT.win(R, PT.row(cs, a), dt)
      +sw = FB.swin(1n+pp, D, FB.srow(1n+pp, D, sa), dt)
      +hw = win_rel(one, h1, pp, hP, cs, hR, D, rd2, a, sa, ha, dt, L.and_right(Nat.is_lt(d, 16n), dok(dt), hd))
      +hq = nth_rel(one, h1, pp, hP, cs, hR, D, rd2, a, sa, ha, d, L.and_left(Nat.is_lt(d, 16n), dok(dt), hd))
      PT2.add_c_rel(one, h1, pp, hP, R, hR, D, PT.dbl4(R, w), PT.nthc(d, PT.row(cs, a)), FB.sdbl4(1n+pp, sw), FB.snth(d, FB.srow(1n+pp, D, sa)), dbl4_rel(one, h1, pp, hP, R, hR, w, sw, hw), hq)

def mul_win_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd2: RE.Rel(one, pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +k: List<&2, U32>, +hk: {FS.bytes_ok(32n, k) == True{} : Bool}, +a: PT.Pt, +sa: SE.EPt, +ha: PR.Rp(one, pp, a, sa)) -> PR.Rp(one, pp, PT.mul_win(cs, k, a), FB.smulw(1n+pp, D, k, sa)):
  +R = PT.cs_r(cs)
  +rw = PT.row(cs, a)
  +ds = PT.nibs(k)
  L.subst(PT.Pt, z => PR.Rp(one, pp, z, FB.smulw(1n+pp, D, k, sa)), PT.win(R, rw, ds), PT.winf(R, rw, ds), Equal.sym(PT.Pt, PT.winf(R, rw, ds), PT.win(R, rw, ds), WF.winf_eq(R, rw, ds)), win_rel(one, h1, pp, hP, cs, hR, D, rd2, a, sa, ha, ds, nibs_ok(k, CV.nat_below(32n, k, hk))))
