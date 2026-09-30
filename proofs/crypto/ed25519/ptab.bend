import Base
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/ed25519.bend as SE
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/ed25519/point.bend as PT
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../fe/rel.bend as RE
import ./prel.bend as PR
import ./pcodec.bend as PC
import ./fbspec.bend as FB

# Prepared points (src/crypto/ed25519/point.bend Cp: Y + X, Y - X, 2 d T,
# 2 Z) against the specification's points: the relation Rc, kept by
# cached, and add_c related to the specification's addition.

def TA(+one: Nat, +pp: Nat, +a: FE.Fe, +s: SE.EPt) -> Data:
  RE.Rel(one, pp, a, FS.fadd(1n+pp, FB.sy(s), FB.sx(s)))

def TB(+one: Nat, +pp: Nat, +b: FE.Fe, +s: SE.EPt) -> Data:
  RE.Rel(one, pp, b, FS.fsub(1n+pp, FB.sy(s), FB.sx(s)))

def TC(+one: Nat, +pp: Nat, +D: Nat, +c: FE.Fe, +s: SE.EPt) -> Data:
  RE.Rel(one, pp, c, FS.fmul(1n+pp, FB.st(s), FS.fadd(1n+pp, D, D)))

def TD(+one: Nat, +pp: Nat, +d: FE.Fe, +s: SE.EPt) -> Data:
  RE.Rel(one, pp, d, FS.fadd(1n+pp, FB.sz(s), FB.sz(s)))

# q is the prepared form of a point related to s
def Rc(+one: Nat, +pp: Nat, +D: Nat, +q: PT.Cp, +s: SE.EPt) -> Data:
  match q:
    case PT.Cp{a, b, c, d}:
      PR.DP(TA(one, pp, a, s), PR.DP(TB(one, pp, b, s), PR.DP(TC(one, pp, D, c, s), TD(one, pp, d, s))))

def mk(+one: Nat, +pp: Nat, +D: Nat, +a: FE.Fe, +b: FE.Fe, +c: FE.Fe, +d: FE.Fe, +s: SE.EPt, +ra: TA(one, pp, a, s), +rb: TB(one, pp, b, s), +rc: TC(one, pp, D, c, s), +rd: TD(one, pp, d, s)) -> Rc(one, pp, D, PT.Cp{a, b, c, d}, s):
  (ra, (rb, (rc, rd)))

def cA(+one: Nat, +pp: Nat, +D: Nat, +a: FE.Fe, +b: FE.Fe, +c: FE.Fe, +d: FE.Fe, +s: SE.EPt, +h: Rc(one, pp, D, PT.Cp{a, b, c, d}, s)) -> TA(one, pp, a, s):
  PR.fst(TA(one, pp, a, s), PR.DP(TB(one, pp, b, s), PR.DP(TC(one, pp, D, c, s), TD(one, pp, d, s))), h)

def cB(+one: Nat, +pp: Nat, +D: Nat, +a: FE.Fe, +b: FE.Fe, +c: FE.Fe, +d: FE.Fe, +s: SE.EPt, +h: Rc(one, pp, D, PT.Cp{a, b, c, d}, s)) -> TB(one, pp, b, s):
  PR.fst(TB(one, pp, b, s), PR.DP(TC(one, pp, D, c, s), TD(one, pp, d, s)), PR.snd(TA(one, pp, a, s), PR.DP(TB(one, pp, b, s), PR.DP(TC(one, pp, D, c, s), TD(one, pp, d, s))), h))

def cC(+one: Nat, +pp: Nat, +D: Nat, +a: FE.Fe, +b: FE.Fe, +c: FE.Fe, +d: FE.Fe, +s: SE.EPt, +h: Rc(one, pp, D, PT.Cp{a, b, c, d}, s)) -> TC(one, pp, D, c, s):
  PR.fst(TC(one, pp, D, c, s), TD(one, pp, d, s), PR.snd(TB(one, pp, b, s), PR.DP(TC(one, pp, D, c, s), TD(one, pp, d, s)), PR.snd(TA(one, pp, a, s), PR.DP(TB(one, pp, b, s), PR.DP(TC(one, pp, D, c, s), TD(one, pp, d, s))), h)))

def cD(+one: Nat, +pp: Nat, +D: Nat, +a: FE.Fe, +b: FE.Fe, +c: FE.Fe, +d: FE.Fe, +s: SE.EPt, +h: Rc(one, pp, D, PT.Cp{a, b, c, d}, s)) -> TD(one, pp, d, s):
  PR.snd(TC(one, pp, D, c, s), TD(one, pp, d, s), PR.snd(TB(one, pp, b, s), PR.DP(TC(one, pp, D, c, s), TD(one, pp, d, s)), PR.snd(TA(one, pp, a, s), PR.DP(TB(one, pp, b, s), PR.DP(TC(one, pp, D, c, s), TD(one, pp, d, s))), h)))

# the prepared form of a related point
def cached_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd2: RE.Rel(one, pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +p: PT.Pt, +sp: SE.EPt, +hp: PR.Rp(one, pp, p, sp)) -> Rc(one, pp, D, PT.cached(cs, p), sp):
  match p sp:
    case PT.Pt{+x, +y, +z, +t} SE.EPt{+a, +b, +c, +d}:
      +R = PT.cs_r(cs)
      +rx = PR.rX(one, pp, x, y, z, t, a, b, c, d, hp)
      +ry = PR.rY(one, pp, x, y, z, t, a, b, c, d, hp)
      +rz = PR.rZ(one, pp, x, y, z, t, a, b, c, d, hp)
      +rt = PR.rT(one, pp, x, y, z, t, a, b, c, d, hp)
      mk(one, pp, D, FE.add(R, y, x), FE.sub(R, y, x), FE.mul(R, t, PT.cs_d2(cs)), FE.add(R, z, z), SE.EPt{a, b, c, d}, PR.radd(one, h1, pp, hP, R, hR, y, x, b, a, ry, rx), PR.rsub(one, h1, pp, hP, R, hR, y, x, b, a, ry, rx), PR.rmul(one, h1, pp, hP, R, hR, t, PT.cs_d2(cs), d, FS.fadd(1n+pp, D, D), rt, rd2), PR.radd(one, h1, pp, hP, R, hR, z, z, c, c, rz, rz))

# a (b c) == (a c) b in the field
def fmul_rot(+pp: Nat, +a: Nat, +b: Nat, +c: Nat) -> {FS.fmul(1n+pp, a, FS.fmul(1n+pp, b, c)) == FS.fmul(1n+pp, FS.fmul(1n+pp, a, c), b) : Nat}:
  +P = {1n+pp : Nat}
  +e1 = NR.mod_mul_r(pp, a, Nat.mul(b, c))
  +e2 = NR.mod_mul_l(pp, Nat.mul(a, c), b)
  +e3 = Equal.trans(Nat, Nat.mul(a, Nat.mul(b, c)), Nat.mul(a, Nat.mul(c, b)), Nat.mul(Nat.mul(a, c), b), Equal.cong(Nat, Nat, z => Nat.mul(a, z), Nat.mul(b, c), Nat.mul(c, b), NA.mul_comm(b, c)), Equal.sym(Nat, Nat.mul(Nat.mul(a, c), b), Nat.mul(a, Nat.mul(c, b)), NA.mul_assoc(a, c, b)))
  Equal.trans(Nat, FS.fmul(P, a, FS.fmul(P, b, c)), Nat.mod(Nat.mul(a, Nat.mul(b, c)), P), FS.fmul(P, FS.fmul(P, a, c), b), e1, Equal.trans(Nat, Nat.mod(Nat.mul(a, Nat.mul(b, c)), P), Nat.mod(Nat.mul(Nat.mul(a, c), b), P), FS.fmul(P, FS.fmul(P, a, c), b), Equal.cong(Nat, Nat, z => Nat.mod(z, P), Nat.mul(a, Nat.mul(b, c)), Nat.mul(Nat.mul(a, c), b), e3), Equal.sym(Nat, FS.fmul(P, FS.fmul(P, a, c), b), Nat.mod(Nat.mul(Nat.mul(a, c), b), P), e2)))

# a (b + b) == (a + a) b in the field
def fmul_dbl(+pp: Nat, +a: Nat, +b: Nat) -> {FS.fmul(1n+pp, a, FS.fadd(1n+pp, b, b)) == FS.fmul(1n+pp, FS.fadd(1n+pp, a, a), b) : Nat}:
  +P = {1n+pp : Nat}
  +e1 = NR.mod_mul_r(pp, a, Nat.add(b, b))
  +e2 = NR.mod_mul_l(pp, Nat.add(a, a), b)
  +e3 = Equal.trans(Nat, Nat.mul(a, Nat.add(b, b)), Nat.add(Nat.mul(a, b), Nat.mul(a, b)), Nat.mul(Nat.add(a, a), b), NA.mul_add_left(a, b, b), Equal.sym(Nat, Nat.mul(Nat.add(a, a), b), Nat.add(Nat.mul(a, b), Nat.mul(a, b)), NA.mul_add_right(a, a, b)))
  Equal.trans(Nat, FS.fmul(P, a, FS.fadd(P, b, b)), Nat.mod(Nat.mul(a, Nat.add(b, b)), P), FS.fmul(P, FS.fadd(P, a, a), b), e1, Equal.trans(Nat, Nat.mod(Nat.mul(a, Nat.add(b, b)), P), Nat.mod(Nat.mul(Nat.add(a, a), b), P), FS.fmul(P, FS.fadd(P, a, a), b), Equal.cong(Nat, Nat, z => Nat.mod(z, P), Nat.mul(a, Nat.add(b, b)), Nat.mul(Nat.add(a, a), b), e3), Equal.sym(Nat, FS.fmul(P, FS.fadd(P, a, a), b), Nat.mod(Nat.mul(Nat.add(a, a), b), P), e2)))

# p + q for a prepared q is the specification's addition
def add_c_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +D: Nat, +p: PT.Pt, +q: PT.Cp, +sp: SE.EPt, +sq: SE.EPt, +hp: PR.Rp(one, pp, p, sp), +hq: Rc(one, pp, D, q, sq)) -> PR.Rp(one, pp, PT.add_c(R, p, q), SE.add(1n+pp, D, sp, sq)):
  match p q sp sq:
    case PT.Pt{+x1, +y1, +z1, +t1} PT.Cp{+ypx, +ymx, +t2d, +z2} SE.EPt{+a1, +b1, +c1, +d1} SE.EPt{+a2, +b2, +c2, +d2}:
      +P = {1n+pp : Nat}
      +S2 = {SE.EPt{a2, b2, c2, d2} : SE.EPt}
      +rx1 = PR.rX(one, pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +ry1 = PR.rY(one, pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +rz1 = PR.rZ(one, pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +rt1 = PR.rT(one, pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +qa = cA(one, pp, D, ypx, ymx, t2d, z2, S2, hq)
      +qb = cB(one, pp, D, ypx, ymx, t2d, z2, S2, hq)
      +qc = cC(one, pp, D, ypx, ymx, t2d, z2, S2, hq)
      +qd = cD(one, pp, D, ypx, ymx, t2d, z2, S2, hq)
      +ea = FE.mul(R, FE.sub(R, y1, x1), ymx)
      +EA = FS.fmul(P, FS.fsub(P, b1, a1), FS.fsub(P, b2, a2))
      +eb = FE.mul(R, FE.add(R, y1, x1), ypx)
      +EB = FS.fmul(P, FS.fadd(P, b1, a1), FS.fadd(P, b2, a2))
      +ec = FE.mul(R, t1, t2d)
      +EC = FS.fmul(P, FS.fmul(P, d1, FS.fadd(P, D, D)), d2)
      +ed = FE.mul(R, z1, z2)
      +ED = FS.fmul(P, FS.fadd(P, c1, c1), c2)
      +ra = PR.rmul(one, h1, pp, hP, R, hR, FE.sub(R, y1, x1), ymx, FS.fsub(P, b1, a1), FS.fsub(P, b2, a2), PR.rsub(one, h1, pp, hP, R, hR, y1, x1, b1, a1, ry1, rx1), qb)
      +rb = PR.rmul(one, h1, pp, hP, R, hR, FE.add(R, y1, x1), ypx, FS.fadd(P, b1, a1), FS.fadd(P, b2, a2), PR.radd(one, h1, pp, hP, R, hR, y1, x1, b1, a1, ry1, rx1), qa)
      +rc = PC.r_val(one, pp, ec, FS.fmul(P, d1, FS.fmul(P, d2, FS.fadd(P, D, D))), EC, fmul_rot(pp, d1, d2, FS.fadd(P, D, D)), PR.rmul(one, h1, pp, hP, R, hR, t1, t2d, d1, FS.fmul(P, d2, FS.fadd(P, D, D)), rt1, qc))
      +rdd = PC.r_val(one, pp, ed, FS.fmul(P, c1, FS.fadd(P, c2, c2)), ED, fmul_dbl(pp, c1, c2), PR.rmul(one, h1, pp, hP, R, hR, z1, z2, c1, FS.fadd(P, c2, c2), rz1, qd))
      +re = PR.rsub(one, h1, pp, hP, R, hR, eb, ea, EB, EA, rb, ra)
      +rf = PR.rsub(one, h1, pp, hP, R, hR, ed, ec, ED, EC, rdd, rc)
      +rg = PR.radd(one, h1, pp, hP, R, hR, ed, ec, ED, EC, rdd, rc)
      +rh = PR.radd(one, h1, pp, hP, R, hR, eb, ea, EB, EA, rb, ra)
      +e = FE.sub(R, eb, ea)
      +f = FE.sub(R, ed, ec)
      +g = FE.add(R, ed, ec)
      +h = FE.add(R, eb, ea)
      +EE = FS.fsub(P, EB, EA)
      +FF = FS.fsub(P, ED, EC)
      +GG = FS.fadd(P, ED, EC)
      +HH = FS.fadd(P, EB, EA)
      PR.mk(one, pp, FE.mul(R, e, f), FE.mul(R, g, h), FE.mul(R, f, g), FE.mul(R, e, h), FS.fmul(P, EE, FF), FS.fmul(P, GG, HH), FS.fmul(P, FF, GG), FS.fmul(P, EE, HH), PR.rmul(one, h1, pp, hP, R, hR, e, f, EE, FF, re, rf), PR.rmul(one, h1, pp, hP, R, hR, g, h, GG, HH, rg, rh), PR.rmul(one, h1, pp, hP, R, hR, f, g, FF, GG, rf, rg), PR.rmul(one, h1, pp, hP, R, hR, e, h, EE, HH, re, rh))
