import Base
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/x25519.bend as SX
import ../../../spec/crypto/ed25519.bend as SE
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../../src/crypto/ed25519/point.bend as PT
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../curve25519/limbs.bend as LM
import ../curve25519/xbits.bend as XB
import ../fe/rel.bend as RE
import ../fe/ops.bend as OP

# edwards25519 point operations of src/crypto/ed25519/point.bend (on the
# fast field) against spec/crypto/ed25519.bend: the point relation Rp (each
# coordinate RE.Rel), kept by addition, doubling, selection and both
# double-and-add scalar multiplications (constant time and branching), for
# every point.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def DP(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

def fst(-A: Data, -B: Data, +p: DP(A, B)) -> A:
  match p:
    case (a, b):
      a

def snd(-A: Data, -B: Data, +p: DP(A, B)) -> B:
  match p:
    case (a, b):
      b

def Rp(+one: Nat, +pp: Nat, +p: PT.Pt, +q: SE.EPt) -> Data:
  match p q:
    case PT.Pt{x, y, z, t} SE.EPt{a, b, c, d}:
      DP(RE.Rel(one, pp, x, a), DP(RE.Rel(one, pp, y, b), DP(RE.Rel(one, pp, z, c), RE.Rel(one, pp, t, d))))

def mk(+one: Nat, +pp: Nat, +x: FE.Fe, +y: FE.Fe, +z: FE.Fe, +t: FE.Fe, +a: Nat, +b: Nat, +c: Nat, +d: Nat, +rx: RE.Rel(one, pp, x, a), +ry: RE.Rel(one, pp, y, b), +rz: RE.Rel(one, pp, z, c), +rt: RE.Rel(one, pp, t, d)) -> Rp(one, pp, PT.Pt{x, y, z, t}, SE.EPt{a, b, c, d}):
  (rx, (ry, (rz, rt)))

def rX(+one: Nat, +pp: Nat, +x: FE.Fe, +y: FE.Fe, +z: FE.Fe, +t: FE.Fe, +a: Nat, +b: Nat, +c: Nat, +d: Nat, +h: Rp(one, pp, PT.Pt{x, y, z, t}, SE.EPt{a, b, c, d})) -> RE.Rel(one, pp, x, a):
  fst(RE.Rel(one, pp, x, a), DP(RE.Rel(one, pp, y, b), DP(RE.Rel(one, pp, z, c), RE.Rel(one, pp, t, d))), h)

def rY(+one: Nat, +pp: Nat, +x: FE.Fe, +y: FE.Fe, +z: FE.Fe, +t: FE.Fe, +a: Nat, +b: Nat, +c: Nat, +d: Nat, +h: Rp(one, pp, PT.Pt{x, y, z, t}, SE.EPt{a, b, c, d})) -> RE.Rel(one, pp, y, b):
  fst(RE.Rel(one, pp, y, b), DP(RE.Rel(one, pp, z, c), RE.Rel(one, pp, t, d)), snd(RE.Rel(one, pp, x, a), DP(RE.Rel(one, pp, y, b), DP(RE.Rel(one, pp, z, c), RE.Rel(one, pp, t, d))), h))

def rZ(+one: Nat, +pp: Nat, +x: FE.Fe, +y: FE.Fe, +z: FE.Fe, +t: FE.Fe, +a: Nat, +b: Nat, +c: Nat, +d: Nat, +h: Rp(one, pp, PT.Pt{x, y, z, t}, SE.EPt{a, b, c, d})) -> RE.Rel(one, pp, z, c):
  fst(RE.Rel(one, pp, z, c), RE.Rel(one, pp, t, d), snd(RE.Rel(one, pp, y, b), DP(RE.Rel(one, pp, z, c), RE.Rel(one, pp, t, d)), snd(RE.Rel(one, pp, x, a), DP(RE.Rel(one, pp, y, b), DP(RE.Rel(one, pp, z, c), RE.Rel(one, pp, t, d))), h)))

def rT(+one: Nat, +pp: Nat, +x: FE.Fe, +y: FE.Fe, +z: FE.Fe, +t: FE.Fe, +a: Nat, +b: Nat, +c: Nat, +d: Nat, +h: Rp(one, pp, PT.Pt{x, y, z, t}, SE.EPt{a, b, c, d})) -> RE.Rel(one, pp, t, d):
  snd(RE.Rel(one, pp, z, c), RE.Rel(one, pp, t, d), snd(RE.Rel(one, pp, y, b), DP(RE.Rel(one, pp, z, c), RE.Rel(one, pp, t, d)), snd(RE.Rel(one, pp, x, a), DP(RE.Rel(one, pp, y, b), DP(RE.Rel(one, pp, z, c), RE.Rel(one, pp, t, d))), h)))

# relation-level field operations
def radd(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +y: FE.Fe, +a: Nat, +b: Nat, +rx: RE.Rel(one, pp, x, a), +ry: RE.Rel(one, pp, y, b)) -> RE.Rel(one, pp, FE.add(R, x, y), FS.fadd(1n+pp, a, b)):
  RE.r_add(one, h1, pp, hP, R, hR, x, y, a, b, rx, ry)

def rsub(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +y: FE.Fe, +a: Nat, +b: Nat, +rx: RE.Rel(one, pp, x, a), +ry: RE.Rel(one, pp, y, b)) -> RE.Rel(one, pp, FE.sub(R, x, y), FS.fsub(1n+pp, a, b)):
  RE.r_sub(one, h1, pp, hP, R, hR, x, y, a, b, rx, ry)

def rmul(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +y: FE.Fe, +a: Nat, +b: Nat, +rx: RE.Rel(one, pp, x, a), +ry: RE.Rel(one, pp, y, b)) -> RE.Rel(one, pp, FE.mul(R, x, y), FS.fmul(1n+pp, a, b)):
  RE.r_mul(one, h1, pp, hP, R, hR, x, y, a, b, rx, ry)

def rsq(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +a: Nat, +rx: RE.Rel(one, pp, x, a)) -> RE.Rel(one, pp, FE.sq(R, x), FS.fmul(1n+pp, a, a)):
  RE.r_mul(one, h1, pp, hP, R, hR, x, x, a, a, rx, rx)

# ---- addition ----

def add_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd2: RE.Rel(one, pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +p: PT.Pt, +q: PT.Pt, +sp: SE.EPt, +sq: SE.EPt, +hp: Rp(one, pp, p, sp), +hq: Rp(one, pp, q, sq)) -> Rp(one, pp, PT.add(cs, p, q), SE.add(1n+pp, D, sp, sq)):
  match p q sp sq:
    case PT.Pt{+x1, +y1, +z1, +t1} PT.Pt{+x2, +y2, +z2, +t2} SE.EPt{+a1, +b1, +c1, +d1} SE.EPt{+a2, +b2, +c2, +d2}:
      +P = {1n+pp : Nat}
      +rx1 = rX(one, pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +ry1 = rY(one, pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +rz1 = rZ(one, pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +rt1 = rT(one, pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +rx2 = rX(one, pp, x2, y2, z2, t2, a2, b2, c2, d2, hq)
      +ry2 = rY(one, pp, x2, y2, z2, t2, a2, b2, c2, d2, hq)
      +rz2 = rZ(one, pp, x2, y2, z2, t2, a2, b2, c2, d2, hq)
      +rt2 = rT(one, pp, x2, y2, z2, t2, a2, b2, c2, d2, hq)
      +ra = rmul(one, h1, pp, hP, PT.cs_r(cs), hR, FE.sub(PT.cs_r(cs), y1, x1), FE.sub(PT.cs_r(cs), y2, x2), FS.fsub(P, b1, a1), FS.fsub(P, b2, a2), rsub(one, h1, pp, hP, PT.cs_r(cs), hR, y1, x1, b1, a1, ry1, rx1), rsub(one, h1, pp, hP, PT.cs_r(cs), hR, y2, x2, b2, a2, ry2, rx2))
      +rb = rmul(one, h1, pp, hP, PT.cs_r(cs), hR, FE.add(PT.cs_r(cs), y1, x1), FE.add(PT.cs_r(cs), y2, x2), FS.fadd(P, b1, a1), FS.fadd(P, b2, a2), radd(one, h1, pp, hP, PT.cs_r(cs), hR, y1, x1, b1, a1, ry1, rx1), radd(one, h1, pp, hP, PT.cs_r(cs), hR, y2, x2, b2, a2, ry2, rx2))
      +rc = rmul(one, h1, pp, hP, PT.cs_r(cs), hR, FE.mul(PT.cs_r(cs), t1, PT.cs_d2(cs)), t2, FS.fmul(P, d1, FS.fadd(P, D, D)), d2, rmul(one, h1, pp, hP, PT.cs_r(cs), hR, t1, PT.cs_d2(cs), d1, FS.fadd(P, D, D), rt1, rd2), rt2)
      +rdd = rmul(one, h1, pp, hP, PT.cs_r(cs), hR, FE.add(PT.cs_r(cs), z1, z1), z2, FS.fadd(P, c1, c1), c2, radd(one, h1, pp, hP, PT.cs_r(cs), hR, z1, z1, c1, c1, rz1, rz1), rz2)
      +ea = FE.mul(PT.cs_r(cs), FE.sub(PT.cs_r(cs), y1, x1), FE.sub(PT.cs_r(cs), y2, x2))
      +EA = FS.fmul(P, FS.fsub(P, b1, a1), FS.fsub(P, b2, a2))
      +eb = FE.mul(PT.cs_r(cs), FE.add(PT.cs_r(cs), y1, x1), FE.add(PT.cs_r(cs), y2, x2))
      +EB = FS.fmul(P, FS.fadd(P, b1, a1), FS.fadd(P, b2, a2))
      +ec = FE.mul(PT.cs_r(cs), FE.mul(PT.cs_r(cs), t1, PT.cs_d2(cs)), t2)
      +EC = FS.fmul(P, FS.fmul(P, d1, FS.fadd(P, D, D)), d2)
      +ed = FE.mul(PT.cs_r(cs), FE.add(PT.cs_r(cs), z1, z1), z2)
      +ED = FS.fmul(P, FS.fadd(P, c1, c1), c2)
      +re = rsub(one, h1, pp, hP, PT.cs_r(cs), hR, eb, ea, EB, EA, rb, ra)
      +rf = rsub(one, h1, pp, hP, PT.cs_r(cs), hR, ed, ec, ED, EC, rdd, rc)
      +rg = radd(one, h1, pp, hP, PT.cs_r(cs), hR, ed, ec, ED, EC, rdd, rc)
      +rh = radd(one, h1, pp, hP, PT.cs_r(cs), hR, eb, ea, EB, EA, rb, ra)
      +e = FE.sub(PT.cs_r(cs), eb, ea)
      +f = FE.sub(PT.cs_r(cs), ed, ec)
      +g = FE.add(PT.cs_r(cs), ed, ec)
      +h = FE.add(PT.cs_r(cs), eb, ea)
      +EE = FS.fsub(P, EB, EA)
      +FF = FS.fsub(P, ED, EC)
      +GG = FS.fadd(P, ED, EC)
      +HH = FS.fadd(P, EB, EA)
      mk(one, pp, FE.mul(PT.cs_r(cs), e, f), FE.mul(PT.cs_r(cs), g, h), FE.mul(PT.cs_r(cs), f, g), FE.mul(PT.cs_r(cs), e, h), FS.fmul(P, EE, FF), FS.fmul(P, GG, HH), FS.fmul(P, FF, GG), FS.fmul(P, EE, HH), rmul(one, h1, pp, hP, PT.cs_r(cs), hR, e, f, EE, FF, re, rf), rmul(one, h1, pp, hP, PT.cs_r(cs), hR, g, h, GG, HH, rg, rh), rmul(one, h1, pp, hP, PT.cs_r(cs), hR, f, g, FF, GG, rf, rg), rmul(one, h1, pp, hP, PT.cs_r(cs), hR, e, h, EE, HH, re, rh))
# ---- doubling ----

def double_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +p: PT.Pt, +sp: SE.EPt, +hp: Rp(one, pp, p, sp)) -> Rp(one, pp, PT.double(R, p), SE.double(1n+pp, sp)):
  match p sp:
    case PT.Pt{+x1, +y1, +z1, +t1} SE.EPt{+a1, +b1, +c1, +d1}:
      +P = {1n+pp : Nat}
      +rx1 = rX(one, pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +ry1 = rY(one, pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +rz1 = rZ(one, pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +a = FE.sq(R, x1)
      +A = FS.fmul(P, a1, a1)
      +ra = rsq(one, h1, pp, hP, R, hR, x1, a1, rx1)
      +b = FE.sq(R, y1)
      +B = FS.fmul(P, b1, b1)
      +rb = rsq(one, h1, pp, hP, R, hR, y1, b1, ry1)
      +zz = FE.sq(R, z1)
      +ZZ = FS.fmul(P, c1, c1)
      +rzz = rsq(one, h1, pp, hP, R, hR, z1, c1, rz1)
      +cc = FE.add(R, zz, zz)
      +CC = FS.fadd(P, ZZ, ZZ)
      +rcc = radd(one, h1, pp, hP, R, hR, zz, zz, ZZ, ZZ, rzz, rzz)
      +h = FE.add(R, a, b)
      +HH = FS.fadd(P, A, B)
      +rh = radd(one, h1, pp, hP, R, hR, a, b, A, B, ra, rb)
      +xy = FE.add(R, x1, y1)
      +XY = FS.fadd(P, a1, b1)
      +rxy = radd(one, h1, pp, hP, R, hR, x1, y1, a1, b1, rx1, ry1)
      +e = FE.sub(R, h, FE.sq(R, xy))
      +EE = FS.fsub(P, HH, FS.fmul(P, XY, XY))
      +re = rsub(one, h1, pp, hP, R, hR, h, FE.sq(R, xy), HH, FS.fmul(P, XY, XY), rh, rsq(one, h1, pp, hP, R, hR, xy, XY, rxy))
      +g = FE.sub(R, a, b)
      +GG = FS.fsub(P, A, B)
      +rg = rsub(one, h1, pp, hP, R, hR, a, b, A, B, ra, rb)
      +f = FE.add(R, cc, g)
      +FF = FS.fadd(P, CC, GG)
      +rf = radd(one, h1, pp, hP, R, hR, cc, g, CC, GG, rcc, rg)
      mk(one, pp, FE.mul(R, e, f), FE.mul(R, g, h), FE.mul(R, f, g), FE.mul(R, e, h), FS.fmul(P, EE, FF), FS.fmul(P, GG, HH), FS.fmul(P, FF, GG), FS.fmul(P, EE, HH), rmul(one, h1, pp, hP, R, hR, e, f, EE, FF, re, rf), rmul(one, h1, pp, hP, R, hR, g, h, GG, HH, rg, rh), rmul(one, h1, pp, hP, R, hR, f, g, FF, GG, rf, rg), rmul(one, h1, pp, hP, R, hR, e, h, EE, HH, re, rh))
# ---- selection ----

def sel0(+p: PT.Pt, +q: PT.Pt) -> {PT.select(0, p, q) == p : PT.Pt}:
  match p q:
    case PT.Pt{+x1, +y1, +z1, +t1} PT.Pt{+x2, +y2, +z2, +t2}:
      %Equal.sym(FE.Fe, FE.select(0, x1, x2), x1, OP.select0(x1, x2)) : {PT.Pt{_, FE.select(0, y1, y2), FE.select(0, z1, z2), FE.select(0, t1, t2)} == PT.Pt{x1, y1, z1, t1} : PT.Pt}
      %Equal.sym(FE.Fe, FE.select(0, y1, y2), y1, OP.select0(y1, y2)) : {PT.Pt{x1, _, FE.select(0, z1, z2), FE.select(0, t1, t2)} == PT.Pt{x1, y1, z1, t1} : PT.Pt}
      %Equal.sym(FE.Fe, FE.select(0, z1, z2), z1, OP.select0(z1, z2)) : {PT.Pt{x1, y1, _, FE.select(0, t1, t2)} == PT.Pt{x1, y1, z1, t1} : PT.Pt}
      %Equal.sym(FE.Fe, FE.select(0, t1, t2), t1, OP.select0(t1, t2)) : {PT.Pt{x1, y1, z1, _} == PT.Pt{x1, y1, z1, t1} : PT.Pt}
      {==}

def sel1(+p: PT.Pt, +q: PT.Pt) -> {PT.select(1, p, q) == q : PT.Pt}:
  match p q:
    case PT.Pt{+x1, +y1, +z1, +t1} PT.Pt{+x2, +y2, +z2, +t2}:
      %Equal.sym(FE.Fe, FE.select(1, x1, x2), x2, OP.select1(x1, x2)) : {PT.Pt{_, FE.select(1, y1, y2), FE.select(1, z1, z2), FE.select(1, t1, t2)} == PT.Pt{x2, y2, z2, t2} : PT.Pt}
      %Equal.sym(FE.Fe, FE.select(1, y1, y2), y2, OP.select1(y1, y2)) : {PT.Pt{x2, _, FE.select(1, z1, z2), FE.select(1, t1, t2)} == PT.Pt{x2, y2, z2, t2} : PT.Pt}
      %Equal.sym(FE.Fe, FE.select(1, z1, z2), z2, OP.select1(z1, z2)) : {PT.Pt{x2, y2, _, FE.select(1, t1, t2)} == PT.Pt{x2, y2, z2, t2} : PT.Pt}
      %Equal.sym(FE.Fe, FE.select(1, t1, t2), t2, OP.select1(t1, t2)) : {PT.Pt{x2, y2, z2, _} == PT.Pt{x2, y2, z2, t2} : PT.Pt}
      {==}

def sel_rel(+one: Nat, +pp: Nat, +s: U32, +b: Nat, +hs: {v(s) == b : Nat}, +hb: {Nat.is_le(b, 1n) == True{} : Bool}, +p: PT.Pt, +q: PT.Pt, +sp: SE.EPt, +sq: SE.EPt, +hp: Rp(one, pp, p, sp), +hq: Rp(one, pp, q, sq)) -> Rp(one, pp, PT.select(s, p, q), SE.pick(b, sp, sq)):
  match b:
    case 0n:
      %Equal.sym(U32, s, 0, XB.u0(s, hs)) : Rp(one, pp, PT.select(_, p, q), sp)
      %Equal.sym(PT.Pt, PT.select(0, p, q), p, sel0(p, q)) : Rp(one, pp, _, sp)
      hp
    case 1n:
      %Equal.sym(U32, s, 1, XB.u1(s, hs)) : Rp(one, pp, PT.select(_, p, q), sq)
      %Equal.sym(PT.Pt, PT.select(1, p, q), q, sel1(p, q)) : Rp(one, pp, _, sq)
      hq
    case 2n+z:
      Empty.absurd(Rp(one, pp, PT.select(s, p, q), sq), L.false_true(hb))

# the branching step: q2 on a zero bit, q2 + p on a one bit
def bit_rel(+one: Nat, +pp: Nat, +cs: PT.Cs, +s: U32, +b: Nat, +hs: {v(s) == b : Nat}, +hb: {Nat.is_le(b, 1n) == True{} : Bool}, +p: PT.Pt, +q2: PT.Pt, +sq2: SE.EPt, +sr: SE.EPt, +hq: Rp(one, pp, q2, sq2), +hr: Rp(one, pp, PT.add(cs, q2, p), sr)) -> Rp(one, pp, PT.smul_bit(U32.is_eq(s, 0), cs, p, q2), SE.pick(b, sq2, sr)):
  match b:
    case 0n:
      %Equal.sym(U32, s, 0, XB.u0(s, hs)) : Rp(one, pp, PT.smul_bit(U32.is_eq(_, 0), cs, p, q2), sq2)
      hq
    case 1n:
      %Equal.sym(U32, s, 1, XB.u1(s, hs)) : Rp(one, pp, PT.smul_bit(U32.is_eq(_, 0), cs, p, q2), sr)
      hr
    case 2n+z:
      Empty.absurd(Rp(one, pp, PT.smul_bit(U32.is_eq(s, 0), cs, p, q2), sr), L.false_true(hb))

# ---- double-and-add ----

def smul_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +n: Nat, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd2: RE.Rel(one, pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +bs: List<&2, U32>, +hbs: {LM.lea(bs, 255n) == True{} : Bool}, +p: PT.Pt, +sp: SE.EPt, +hp: Rp(one, pp, p, sp), +q: PT.Pt, +sq: SE.EPt, +hq: Rp(one, pp, q, sq)) -> Rp(one, pp, PT.smul(n, cs, bs, p, q), SE.smul(1n+pp, D, n, FS.value(bs), sp, sq)):
  match n:
    case 0n:
      hq
    case 1n+ +t:
      +q2 = PT.double(PT.cs_r(cs), q)
      +sq2 = SE.double(1n+pp, sq)
      +hq2 = double_rel(one, h1, pp, hP, PT.cs_r(cs), hR, q, sq, hq)
      +r = PT.add(cs, q2, p)
      +sr = SE.add(1n+pp, D, sq2, sp)
      +hr = add_rel(one, h1, pp, hP, cs, hR, D, rd2, q2, p, sq2, sp, hq2, hp)
      +hs = sel_rel(one, pp, X.kbit(bs, t), SX.kbit(FS.value(bs), t), XB.kbit_val(bs, t, hbs), XB.kbit_le(bs, t, hbs), q2, r, sq2, sr, hq2, hr)
      smul_rel(one, h1, pp, hP, t, cs, hR, D, rd2, bs, hbs, p, sp, hp, PT.select(X.kbit(bs, t), q2, r), SE.pick(SX.kbit(FS.value(bs), t), sq2, sr), hs)

def smul_vt_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +n: Nat, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd2: RE.Rel(one, pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +bs: List<&2, U32>, +hbs: {LM.lea(bs, 255n) == True{} : Bool}, +p: PT.Pt, +sp: SE.EPt, +hp: Rp(one, pp, p, sp), +q: PT.Pt, +sq: SE.EPt, +hq: Rp(one, pp, q, sq)) -> Rp(one, pp, PT.smul_vt(n, cs, bs, p, q), SE.smul(1n+pp, D, n, FS.value(bs), sp, sq)):
  match n:
    case 0n:
      hq
    case 1n+ +t:
      +q2 = PT.double(PT.cs_r(cs), q)
      +sq2 = SE.double(1n+pp, sq)
      +hq2 = double_rel(one, h1, pp, hP, PT.cs_r(cs), hR, q, sq, hq)
      +sr = SE.add(1n+pp, D, sq2, sp)
      +hr = add_rel(one, h1, pp, hP, cs, hR, D, rd2, q2, p, sq2, sp, hq2, hp)
      +hs = bit_rel(one, pp, cs, X.kbit(bs, t), SX.kbit(FS.value(bs), t), XB.kbit_val(bs, t, hbs), XB.kbit_le(bs, t, hbs), p, q2, sq2, sr, hq2, hr)
      smul_vt_rel(one, h1, pp, hP, t, cs, hR, D, rd2, bs, hbs, p, sp, hp, PT.smul_bit(U32.is_eq(X.kbit(bs, t), 0), cs, p, q2), SE.pick(SX.kbit(FS.value(bs), t), sq2, sr), hs)
