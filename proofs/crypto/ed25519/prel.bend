import Base
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/x25519.bend as SX
import ../../../spec/crypto/ed25519.bend as SE
import ../../../src/crypto/curve25519/field.bend as F
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../../src/crypto/ed25519/point.bend as PT
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../curve25519/limbs.bend as LM
import ../curve25519/fieldops.bend as FO
import ../curve25519/mulw.bend as MW
import ../curve25519/cong.bend as G
import ../curve25519/rel.bend as RL
import ../curve25519/xbits.bend as XB

# edwards25519 point operations of src/crypto/ed25519/point.bend against
# spec/crypto/ed25519.bend: the point relation Rp (each coordinate RL.R),
# kept by addition, doubling, selection and double-and-add scalar
# multiplication, for every point.

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

def Rp(+pp: Nat, +p: PT.Pt, +q: SE.EPt) -> Data:
  match p q:
    case PT.Pt{x, y, z, t} SE.EPt{a, b, c, d}:
      DP(RL.R(pp, x, a), DP(RL.R(pp, y, b), DP(RL.R(pp, z, c), RL.R(pp, t, d))))

def mk(+pp: Nat, +x: List<&2, U32>, +y: List<&2, U32>, +z: List<&2, U32>, +t: List<&2, U32>, +a: Nat, +b: Nat, +c: Nat, +d: Nat, +rx: RL.R(pp, x, a), +ry: RL.R(pp, y, b), +rz: RL.R(pp, z, c), +rt: RL.R(pp, t, d)) -> Rp(pp, PT.Pt{x, y, z, t}, SE.EPt{a, b, c, d}):
  (rx, (ry, (rz, rt)))

def rX(+pp: Nat, +x: List<&2, U32>, +y: List<&2, U32>, +z: List<&2, U32>, +t: List<&2, U32>, +a: Nat, +b: Nat, +c: Nat, +d: Nat, +h: Rp(pp, PT.Pt{x, y, z, t}, SE.EPt{a, b, c, d})) -> RL.R(pp, x, a):
  fst(RL.R(pp, x, a), DP(RL.R(pp, y, b), DP(RL.R(pp, z, c), RL.R(pp, t, d))), h)

def rY(+pp: Nat, +x: List<&2, U32>, +y: List<&2, U32>, +z: List<&2, U32>, +t: List<&2, U32>, +a: Nat, +b: Nat, +c: Nat, +d: Nat, +h: Rp(pp, PT.Pt{x, y, z, t}, SE.EPt{a, b, c, d})) -> RL.R(pp, y, b):
  fst(RL.R(pp, y, b), DP(RL.R(pp, z, c), RL.R(pp, t, d)), snd(RL.R(pp, x, a), DP(RL.R(pp, y, b), DP(RL.R(pp, z, c), RL.R(pp, t, d))), h))

def rZ(+pp: Nat, +x: List<&2, U32>, +y: List<&2, U32>, +z: List<&2, U32>, +t: List<&2, U32>, +a: Nat, +b: Nat, +c: Nat, +d: Nat, +h: Rp(pp, PT.Pt{x, y, z, t}, SE.EPt{a, b, c, d})) -> RL.R(pp, z, c):
  fst(RL.R(pp, z, c), RL.R(pp, t, d), snd(RL.R(pp, y, b), DP(RL.R(pp, z, c), RL.R(pp, t, d)), snd(RL.R(pp, x, a), DP(RL.R(pp, y, b), DP(RL.R(pp, z, c), RL.R(pp, t, d))), h)))

def rT(+pp: Nat, +x: List<&2, U32>, +y: List<&2, U32>, +z: List<&2, U32>, +t: List<&2, U32>, +a: Nat, +b: Nat, +c: Nat, +d: Nat, +h: Rp(pp, PT.Pt{x, y, z, t}, SE.EPt{a, b, c, d})) -> RL.R(pp, t, d):
  snd(RL.R(pp, z, c), RL.R(pp, t, d), snd(RL.R(pp, y, b), DP(RL.R(pp, z, c), RL.R(pp, t, d)), snd(RL.R(pp, x, a), DP(RL.R(pp, y, b), DP(RL.R(pp, z, c), RL.R(pp, t, d))), h)))

# relation-level field operations
def o(+pp: Nat, +x: List<&2, U32>, +a: Nat, +r: RL.R(pp, x, a)) -> {LM.okb(32n, x, 255n) == True{} : Bool}:
  RL.r_o(pp, x, a, r)

def c(+pp: Nat, +x: List<&2, U32>, +a: Nat, +r: RL.R(pp, x, a)) -> G.ceq(pp, FS.value(x), a):
  RL.r_c(pp, x, a, r)

def radd(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +y: List<&2, U32>, +a: Nat, +b: Nat, +rx: RL.R(pp, x, a), +ry: RL.R(pp, y, b)) -> RL.R(pp, F.add(x, y), FS.fadd(1n+pp, a, b)):
  (FO.add_okb(one, h1, x, y, o(pp, x, a, rx), o(pp, y, b, ry)), RL.rc_add(one, h1, pp, hP, x, y, a, b, o(pp, x, a, rx), c(pp, x, a, rx), o(pp, y, b, ry), c(pp, y, b, ry)))

def rsub(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +y: List<&2, U32>, +a: Nat, +b: Nat, +rx: RL.R(pp, x, a), +ry: RL.R(pp, y, b)) -> RL.R(pp, F.sub(x, y), FS.fsub(1n+pp, a, b)):
  (FO.sub_okb(one, h1, x, y, o(pp, x, a, rx), o(pp, y, b, ry)), RL.rc_sub(one, h1, pp, hP, x, y, a, b, o(pp, x, a, rx), c(pp, x, a, rx), o(pp, y, b, ry), c(pp, y, b, ry)))

def rmul(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +y: List<&2, U32>, +a: Nat, +b: Nat, +rx: RL.R(pp, x, a), +ry: RL.R(pp, y, b)) -> RL.R(pp, F.mul(x, y), FS.fmul(1n+pp, a, b)):
  (MW.mul_okb(one, h1, x, y, o(pp, x, a, rx), o(pp, y, b, ry)), RL.rc_mul(one, h1, pp, hP, x, y, a, b, o(pp, x, a, rx), c(pp, x, a, rx), o(pp, y, b, ry), c(pp, y, b, ry)))

def rsq(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +a: Nat, +rx: RL.R(pp, x, a)) -> RL.R(pp, F.sq(x), FS.fmul(1n+pp, a, a)):
  rmul(one, h1, pp, hP, x, x, a, a, rx, rx)

# ---- addition ----

def add_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +D: Nat, +rd2: RL.R(pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +p: PT.Pt, +q: PT.Pt, +sp: SE.EPt, +sq: SE.EPt, +hp: Rp(pp, p, sp), +hq: Rp(pp, q, sq)) -> Rp(pp, PT.add(cs, p, q), SE.add(1n+pp, D, sp, sq)):
  match p q sp sq:
    case PT.Pt{+x1, +y1, +z1, +t1} PT.Pt{+x2, +y2, +z2, +t2} SE.EPt{+a1, +b1, +c1, +d1} SE.EPt{+a2, +b2, +c2, +d2}:
      +P = {1n+pp : Nat}
      +rx1 = rX(pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +ry1 = rY(pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +rz1 = rZ(pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +rt1 = rT(pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +rx2 = rX(pp, x2, y2, z2, t2, a2, b2, c2, d2, hq)
      +ry2 = rY(pp, x2, y2, z2, t2, a2, b2, c2, d2, hq)
      +rz2 = rZ(pp, x2, y2, z2, t2, a2, b2, c2, d2, hq)
      +rt2 = rT(pp, x2, y2, z2, t2, a2, b2, c2, d2, hq)
      +ra = rmul(one, h1, pp, hP, F.sub(y1, x1), F.sub(y2, x2), FS.fsub(P, b1, a1), FS.fsub(P, b2, a2), rsub(one, h1, pp, hP, y1, x1, b1, a1, ry1, rx1), rsub(one, h1, pp, hP, y2, x2, b2, a2, ry2, rx2))
      +rb = rmul(one, h1, pp, hP, F.add(y1, x1), F.add(y2, x2), FS.fadd(P, b1, a1), FS.fadd(P, b2, a2), radd(one, h1, pp, hP, y1, x1, b1, a1, ry1, rx1), radd(one, h1, pp, hP, y2, x2, b2, a2, ry2, rx2))
      +rc = rmul(one, h1, pp, hP, F.mul(t1, PT.cs_d2(cs)), t2, FS.fmul(P, d1, FS.fadd(P, D, D)), d2, rmul(one, h1, pp, hP, t1, PT.cs_d2(cs), d1, FS.fadd(P, D, D), rt1, rd2), rt2)
      +rdd = rmul(one, h1, pp, hP, F.add(z1, z1), z2, FS.fadd(P, c1, c1), c2, radd(one, h1, pp, hP, z1, z1, c1, c1, rz1, rz1), rz2)
      +ea = F.mul(F.sub(y1, x1), F.sub(y2, x2))
      +EA = FS.fmul(P, FS.fsub(P, b1, a1), FS.fsub(P, b2, a2))
      +eb = F.mul(F.add(y1, x1), F.add(y2, x2))
      +EB = FS.fmul(P, FS.fadd(P, b1, a1), FS.fadd(P, b2, a2))
      +ec = F.mul(F.mul(t1, PT.cs_d2(cs)), t2)
      +EC = FS.fmul(P, FS.fmul(P, d1, FS.fadd(P, D, D)), d2)
      +ed = F.mul(F.add(z1, z1), z2)
      +ED = FS.fmul(P, FS.fadd(P, c1, c1), c2)
      +re = rsub(one, h1, pp, hP, eb, ea, EB, EA, rb, ra)
      +rf = rsub(one, h1, pp, hP, ed, ec, ED, EC, rdd, rc)
      +rg = radd(one, h1, pp, hP, ed, ec, ED, EC, rdd, rc)
      +rh = radd(one, h1, pp, hP, eb, ea, EB, EA, rb, ra)
      +e = F.sub(eb, ea)
      +f = F.sub(ed, ec)
      +g = F.add(ed, ec)
      +h = F.add(eb, ea)
      +EE = FS.fsub(P, EB, EA)
      +FF = FS.fsub(P, ED, EC)
      +GG = FS.fadd(P, ED, EC)
      +HH = FS.fadd(P, EB, EA)
      mk(pp, F.mul(e, f), F.mul(g, h), F.mul(f, g), F.mul(e, h), FS.fmul(P, EE, FF), FS.fmul(P, GG, HH), FS.fmul(P, FF, GG), FS.fmul(P, EE, HH), rmul(one, h1, pp, hP, e, f, EE, FF, re, rf), rmul(one, h1, pp, hP, g, h, GG, HH, rg, rh), rmul(one, h1, pp, hP, f, g, FF, GG, rf, rg), rmul(one, h1, pp, hP, e, h, EE, HH, re, rh))

# ---- doubling ----

def double_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +p: PT.Pt, +sp: SE.EPt, +hp: Rp(pp, p, sp)) -> Rp(pp, PT.double(p), SE.double(1n+pp, sp)):
  match p sp:
    case PT.Pt{+x1, +y1, +z1, +t1} SE.EPt{+a1, +b1, +c1, +d1}:
      +P = {1n+pp : Nat}
      +rx1 = rX(pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +ry1 = rY(pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +rz1 = rZ(pp, x1, y1, z1, t1, a1, b1, c1, d1, hp)
      +a = F.sq(x1)
      +A = FS.fmul(P, a1, a1)
      +ra = rsq(one, h1, pp, hP, x1, a1, rx1)
      +b = F.sq(y1)
      +B = FS.fmul(P, b1, b1)
      +rb = rsq(one, h1, pp, hP, y1, b1, ry1)
      +zz = F.sq(z1)
      +ZZ = FS.fmul(P, c1, c1)
      +rzz = rsq(one, h1, pp, hP, z1, c1, rz1)
      +cc = F.add(zz, zz)
      +CC = FS.fadd(P, ZZ, ZZ)
      +rcc = radd(one, h1, pp, hP, zz, zz, ZZ, ZZ, rzz, rzz)
      +h = F.add(a, b)
      +HH = FS.fadd(P, A, B)
      +rh = radd(one, h1, pp, hP, a, b, A, B, ra, rb)
      +xy = F.add(x1, y1)
      +XY = FS.fadd(P, a1, b1)
      +rxy = radd(one, h1, pp, hP, x1, y1, a1, b1, rx1, ry1)
      +e = F.sub(h, F.sq(xy))
      +EE = FS.fsub(P, HH, FS.fmul(P, XY, XY))
      +re = rsub(one, h1, pp, hP, h, F.sq(xy), HH, FS.fmul(P, XY, XY), rh, rsq(one, h1, pp, hP, xy, XY, rxy))
      +g = F.sub(a, b)
      +GG = FS.fsub(P, A, B)
      +rg = rsub(one, h1, pp, hP, a, b, A, B, ra, rb)
      +f = F.add(cc, g)
      +FF = FS.fadd(P, CC, GG)
      +rf = radd(one, h1, pp, hP, cc, g, CC, GG, rcc, rg)
      mk(pp, F.mul(e, f), F.mul(g, h), F.mul(f, g), F.mul(e, h), FS.fmul(P, EE, FF), FS.fmul(P, GG, HH), FS.fmul(P, FF, GG), FS.fmul(P, EE, HH), rmul(one, h1, pp, hP, e, f, EE, FF, re, rf), rmul(one, h1, pp, hP, g, h, GG, HH, rg, rh), rmul(one, h1, pp, hP, f, g, FF, GG, rf, rg), rmul(one, h1, pp, hP, e, h, EE, HH, re, rh))

# ---- selection ----

def sel_eq0(+one: Nat, +h1: {one == 1n : Nat}, +p: PT.Pt, +q: PT.Pt, +sp: SE.EPt, +sq: SE.EPt, +pp: Nat, +hp: Rp(pp, p, sp), +hq: Rp(pp, q, sq)) -> {PT.select(0, p, q) == p : PT.Pt}:
  match p q sp sq:
    case PT.Pt{+x1, +y1, +z1, +t1} PT.Pt{+x2, +y2, +z2, +t2} SE.EPt{+a1, +b1, +c1, +d1} SE.EPt{+a2, +b2, +c2, +d2}:
      +ox1 = o(pp, x1, a1, rX(pp, x1, y1, z1, t1, a1, b1, c1, d1, hp))
      +oy1 = o(pp, y1, b1, rY(pp, x1, y1, z1, t1, a1, b1, c1, d1, hp))
      +oz1 = o(pp, z1, c1, rZ(pp, x1, y1, z1, t1, a1, b1, c1, d1, hp))
      +ot1 = o(pp, t1, d1, rT(pp, x1, y1, z1, t1, a1, b1, c1, d1, hp))
      +ox2 = o(pp, x2, a2, rX(pp, x2, y2, z2, t2, a2, b2, c2, d2, hq))
      +oy2 = o(pp, y2, b2, rY(pp, x2, y2, z2, t2, a2, b2, c2, d2, hq))
      +oz2 = o(pp, z2, c2, rZ(pp, x2, y2, z2, t2, a2, b2, c2, d2, hq))
      +ot2 = o(pp, t2, d2, rT(pp, x2, y2, z2, t2, a2, b2, c2, d2, hq))
      %Equal.sym(List<&2, U32>, F.select(0, x1, x2), x1, FO.select0(one, h1, 32n, x1, x2, ox1, ox2)) : {PT.Pt{_, F.select(0, y1, y2), F.select(0, z1, z2), F.select(0, t1, t2)} == PT.Pt{x1, y1, z1, t1} : PT.Pt}
      %Equal.sym(List<&2, U32>, F.select(0, y1, y2), y1, FO.select0(one, h1, 32n, y1, y2, oy1, oy2)) : {PT.Pt{x1, _, F.select(0, z1, z2), F.select(0, t1, t2)} == PT.Pt{x1, y1, z1, t1} : PT.Pt}
      %Equal.sym(List<&2, U32>, F.select(0, z1, z2), z1, FO.select0(one, h1, 32n, z1, z2, oz1, oz2)) : {PT.Pt{x1, y1, _, F.select(0, t1, t2)} == PT.Pt{x1, y1, z1, t1} : PT.Pt}
      %Equal.sym(List<&2, U32>, F.select(0, t1, t2), t1, FO.select0(one, h1, 32n, t1, t2, ot1, ot2)) : {PT.Pt{x1, y1, z1, _} == PT.Pt{x1, y1, z1, t1} : PT.Pt}
      {==}

def sel_eq1(+one: Nat, +h1: {one == 1n : Nat}, +p: PT.Pt, +q: PT.Pt, +sp: SE.EPt, +sq: SE.EPt, +pp: Nat, +hp: Rp(pp, p, sp), +hq: Rp(pp, q, sq)) -> {PT.select(1, p, q) == q : PT.Pt}:
  match p q sp sq:
    case PT.Pt{+x1, +y1, +z1, +t1} PT.Pt{+x2, +y2, +z2, +t2} SE.EPt{+a1, +b1, +c1, +d1} SE.EPt{+a2, +b2, +c2, +d2}:
      +ox1 = o(pp, x1, a1, rX(pp, x1, y1, z1, t1, a1, b1, c1, d1, hp))
      +oy1 = o(pp, y1, b1, rY(pp, x1, y1, z1, t1, a1, b1, c1, d1, hp))
      +oz1 = o(pp, z1, c1, rZ(pp, x1, y1, z1, t1, a1, b1, c1, d1, hp))
      +ot1 = o(pp, t1, d1, rT(pp, x1, y1, z1, t1, a1, b1, c1, d1, hp))
      +ox2 = o(pp, x2, a2, rX(pp, x2, y2, z2, t2, a2, b2, c2, d2, hq))
      +oy2 = o(pp, y2, b2, rY(pp, x2, y2, z2, t2, a2, b2, c2, d2, hq))
      +oz2 = o(pp, z2, c2, rZ(pp, x2, y2, z2, t2, a2, b2, c2, d2, hq))
      +ot2 = o(pp, t2, d2, rT(pp, x2, y2, z2, t2, a2, b2, c2, d2, hq))
      %Equal.sym(List<&2, U32>, F.select(1, x1, x2), x2, FO.select1(one, h1, 32n, x1, x2, ox1, ox2)) : {PT.Pt{_, F.select(1, y1, y2), F.select(1, z1, z2), F.select(1, t1, t2)} == PT.Pt{x2, y2, z2, t2} : PT.Pt}
      %Equal.sym(List<&2, U32>, F.select(1, y1, y2), y2, FO.select1(one, h1, 32n, y1, y2, oy1, oy2)) : {PT.Pt{x2, _, F.select(1, z1, z2), F.select(1, t1, t2)} == PT.Pt{x2, y2, z2, t2} : PT.Pt}
      %Equal.sym(List<&2, U32>, F.select(1, z1, z2), z2, FO.select1(one, h1, 32n, z1, z2, oz1, oz2)) : {PT.Pt{x2, y2, _, F.select(1, t1, t2)} == PT.Pt{x2, y2, z2, t2} : PT.Pt}
      %Equal.sym(List<&2, U32>, F.select(1, t1, t2), t2, FO.select1(one, h1, 32n, t1, t2, ot1, ot2)) : {PT.Pt{x2, y2, z2, _} == PT.Pt{x2, y2, z2, t2} : PT.Pt}
      {==}

def sel_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +s: U32, +b: Nat, +hs: {v(s) == b : Nat}, +hb: {Nat.is_le(b, 1n) == True{} : Bool}, +p: PT.Pt, +q: PT.Pt, +sp: SE.EPt, +sq: SE.EPt, +hp: Rp(pp, p, sp), +hq: Rp(pp, q, sq)) -> Rp(pp, PT.select(s, p, q), SE.pick(b, sp, sq)):
  match b:
    case 0n:
      %Equal.sym(U32, s, 0, XB.u0(s, hs)) : Rp(pp, PT.select(_, p, q), sp)
      %Equal.sym(PT.Pt, PT.select(0, p, q), p, sel_eq0(one, h1, p, q, sp, sq, pp, hp, hq)) : Rp(pp, _, sp)
      hp
    case 1n:
      %Equal.sym(U32, s, 1, XB.u1(s, hs)) : Rp(pp, PT.select(_, p, q), sq)
      %Equal.sym(PT.Pt, PT.select(1, p, q), q, sel_eq1(one, h1, p, q, sp, sq, pp, hp, hq)) : Rp(pp, _, sq)
      hq
    case 2n+z:
      Empty.absurd(Rp(pp, PT.select(s, p, q), sq), L.false_true(hb))

# ---- double-and-add ----

def smul_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +n: Nat, +cs: PT.Cs, +D: Nat, +rd2: RL.R(pp, PT.cs_d2(cs), FS.fadd(1n+pp, D, D)), +bs: List<&2, U32>, +hbs: {LM.lea(bs, 255n) == True{} : Bool}, +p: PT.Pt, +sp: SE.EPt, +hp: Rp(pp, p, sp), +q: PT.Pt, +sq: SE.EPt, +hq: Rp(pp, q, sq)) -> Rp(pp, PT.smul(n, cs, bs, p, q), SE.smul(1n+pp, D, n, FS.value(bs), sp, sq)):
  match n:
    case 0n:
      hq
    case 1n+ +t:
      +q2 = PT.double(q)
      +sq2 = SE.double(1n+pp, sq)
      +hq2 = double_rel(one, h1, pp, hP, q, sq, hq)
      +r = PT.add(cs, q2, p)
      +sr = SE.add(1n+pp, D, sq2, sp)
      +hr = add_rel(one, h1, pp, hP, cs, D, rd2, q2, p, sq2, sp, hq2, hp)
      +hs = sel_rel(one, h1, pp, X.kbit(bs, t), SX.kbit(FS.value(bs), t), XB.kbit_val(bs, t, hbs), XB.kbit_le(bs, t, hbs), q2, r, sq2, sr, hq2, hr)
      smul_rel(one, h1, pp, hP, t, cs, D, rd2, bs, hbs, p, sp, hp, PT.select(X.kbit(bs, t), q2, r), SE.pick(SX.kbit(FS.value(bs), t), sq2, sr), hs)
