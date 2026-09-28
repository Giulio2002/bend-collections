import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/x25519.bend as S
import ../../../src/crypto/curve25519/field.bend as F
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ./limbs.bend as LM
import ./consts.bend as K
import ./fieldops.bend as FO
import ./canon.bend as CN
import ./cong.bend as G
import ./rel.bend as RL
import ./mulw.bend as MW
import ./pow.bend as PW
import ./xbits.bend as XB
import ./prime.bend as PR

# X25519 == RFC 7748 (spec/crypto/curve25519/x25519.bend): the ladder state
# of the implementation is related to the specification's state field by
# field (RL.R), the swap bit is equal; every rung keeps the relation; the
# final cswap, inversion, product and encoding give the same bytes.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def Rst(+pp: Nat, st: X.St, sst: S.LSt) -> Type:
  match st sst:
    case X.St{x2, z2, x3, z3, sw} S.LSt{a2, b2, a3, b3, sws}:
      RL.R(pp, x2, a2) & (RL.R(pp, z2, b2) & (RL.R(pp, x3, a3) & (RL.R(pp, z3, b3) & ({U32.to_nat(sw) == sws : Nat} & {Nat.is_le(sws, 1n) == True{} : Bool}))))

# ---- conditional swaps ----

def o_sel(+one: Nat, +h1: {one == 1n : Nat}, +sw: U32, +s: Nat, +hs: {v(sw) == s : Nat}, +hb: {Nat.is_le(s, 1n) == True{} : Bool}, +a: List<&2, U32>, +b: List<&2, U32>, +oa: {LM.okb(32n, a, 255n) == True{} : Bool}, +ob: {LM.okb(32n, b, 255n) == True{} : Bool}) -> {LM.okb(32n, F.select(sw, a, b), 255n) == True{} : Bool}:
  match s:
    case 0n:
      %Equal.sym(U32, sw, 0, XB.u0(sw, hs)) : {LM.okb(32n, F.select(_, a, b), 255n) == True{} : Bool}
      %Equal.sym(List<&2, U32>, F.select(0, a, b), a, FO.select0(one, h1, 32n, a, b, oa, ob)) : {LM.okb(32n, _, 255n) == True{} : Bool}
      oa
    case 1n:
      %Equal.sym(U32, sw, 1, XB.u1(sw, hs)) : {LM.okb(32n, F.select(_, a, b), 255n) == True{} : Bool}
      %Equal.sym(List<&2, U32>, F.select(1, a, b), b, FO.select1(one, h1, 32n, a, b, oa, ob)) : {LM.okb(32n, _, 255n) == True{} : Bool}
      ob
    case 2n+q:
      Empty.absurd({LM.okb(32n, F.select(sw, a, b), 255n) == True{} : Bool}, L.false_true(hb))

def c_fst(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +sw: U32, +s: Nat, +hs: {v(sw) == s : Nat}, +hb: {Nat.is_le(s, 1n) == True{} : Bool}, +a: List<&2, U32>, +b: List<&2, U32>, +A: Nat, +B: Nat, +oa: {LM.okb(32n, a, 255n) == True{} : Bool}, +ca: G.ceq(pp, FS.value(a), A), +ob: {LM.okb(32n, b, 255n) == True{} : Bool}, +cb: G.ceq(pp, FS.value(b), B)) -> G.ceq(pp, FS.value(F.select(sw, a, b)), S.cs_fst(s, A, B)):
  match s:
    case 0n:
      %Equal.sym(U32, sw, 0, XB.u0(sw, hs)) : G.ceq(pp, FS.value(F.select(_, a, b)), A)
      %Equal.sym(List<&2, U32>, F.select(0, a, b), a, FO.select0(one, h1, 32n, a, b, oa, ob)) : G.ceq(pp, FS.value(_), A)
      ca
    case 1n:
      %Equal.sym(U32, sw, 1, XB.u1(sw, hs)) : G.ceq(pp, FS.value(F.select(_, a, b)), B)
      %Equal.sym(List<&2, U32>, F.select(1, a, b), b, FO.select1(one, h1, 32n, a, b, oa, ob)) : G.ceq(pp, FS.value(_), B)
      cb
    case 2n+q:
      Empty.absurd(G.ceq(pp, FS.value(F.select(sw, a, b)), B), L.false_true(hb))

def c_snd(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +sw: U32, +s: Nat, +hs: {v(sw) == s : Nat}, +hb: {Nat.is_le(s, 1n) == True{} : Bool}, +a: List<&2, U32>, +b: List<&2, U32>, +A: Nat, +B: Nat, +oa: {LM.okb(32n, a, 255n) == True{} : Bool}, +ca: G.ceq(pp, FS.value(a), A), +ob: {LM.okb(32n, b, 255n) == True{} : Bool}, +cb: G.ceq(pp, FS.value(b), B)) -> G.ceq(pp, FS.value(F.select(sw, b, a)), S.cs_snd(s, A, B)):
  match s:
    case 0n:
      %Equal.sym(U32, sw, 0, XB.u0(sw, hs)) : G.ceq(pp, FS.value(F.select(_, b, a)), B)
      %Equal.sym(List<&2, U32>, F.select(0, b, a), b, FO.select0(one, h1, 32n, b, a, ob, oa)) : G.ceq(pp, FS.value(_), B)
      cb
    case 1n:
      %Equal.sym(U32, sw, 1, XB.u1(sw, hs)) : G.ceq(pp, FS.value(F.select(_, b, a)), A)
      %Equal.sym(List<&2, U32>, F.select(1, b, a), a, FO.select1(one, h1, 32n, b, a, ob, oa)) : G.ceq(pp, FS.value(_), A)
      ca
    case 2n+q:
      Empty.absurd(G.ceq(pp, FS.value(F.select(sw, b, a)), A), L.false_true(hb))

# ---- one step ----

def a24_c(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +c24: List<&2, U32>, +hv: {K.valo(one, c24) == S.a24(one) : Nat}) -> G.ceq(pp, FS.value(c24), S.a24(one)):
  G.c_eq(pp, FS.value(c24), S.a24(one), Equal.trans(Nat, FS.value(c24), K.valo(one, c24), S.a24(one), Equal.sym(Nat, K.valo(one, c24), FS.value(c24), K.valo_value(one, h1, c24)), hv))

def step_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +c24: List<&2, U32>, +oc: {LM.okb(32n, c24, 255n) == True{} : Bool}, +hv: {K.valo(one, c24) == S.a24(one) : Nat}, +x1: List<&2, U32>, +X1: Nat, +o1: {LM.okb(32n, x1, 255n) == True{} : Bool}, +c1: G.ceq(pp, FS.value(x1), X1), +x2: List<&2, U32>, +X2: Nat, +o2: {LM.okb(32n, x2, 255n) == True{} : Bool}, +c2: G.ceq(pp, FS.value(x2), X2), +z2: List<&2, U32>, +Z2: Nat, +oz2: {LM.okb(32n, z2, 255n) == True{} : Bool}, +cz2: G.ceq(pp, FS.value(z2), Z2), +x3: List<&2, U32>, +X3: Nat, +o3: {LM.okb(32n, x3, 255n) == True{} : Bool}, +c3: G.ceq(pp, FS.value(x3), X3), +z3: List<&2, U32>, +Z3: Nat, +oz3: {LM.okb(32n, z3, 255n) == True{} : Bool}, +cz3: G.ceq(pp, FS.value(z3), Z3), +kt: U32, +KT: Nat, +hk: {v(kt) == KT : Nat}, +hkb: {Nat.is_le(KT, 1n) == True{} : Bool}) -> Rst(pp, X.step(c24, x1, x2, z2, x3, z3, kt), S.step(one, 1n+pp, X1, X2, Z2, X3, Z3, KT)):
  +P = {1n+pp : Nat}
  +A24 = S.a24(one)
  +cc = a24_c(one, h1, pp, c24, hv)
  +a = F.add(x2, z2)
  +A = FS.fadd(P, X2, Z2)
  +oa = FO.add_okb(one, h1, x2, z2, o2, oz2)
  +ca = RL.rc_add(one, h1, pp, hP, x2, z2, X2, Z2, o2, c2, oz2, cz2)
  +aa = F.sq(a)
  +AA = FS.fmul(P, A, A)
  +oaa = MW.sq_okb(one, h1, a, oa)
  +caa = RL.rc_sq(one, h1, pp, hP, a, A, oa, ca)
  +b = F.sub(x2, z2)
  +B = FS.fsub(P, X2, Z2)
  +ob = FO.sub_okb(one, h1, x2, z2, o2, oz2)
  +cb = RL.rc_sub(one, h1, pp, hP, x2, z2, X2, Z2, o2, c2, oz2, cz2)
  +bb = F.sq(b)
  +BB = FS.fmul(P, B, B)
  +obb = MW.sq_okb(one, h1, b, ob)
  +cbb = RL.rc_sq(one, h1, pp, hP, b, B, ob, cb)
  +e = F.sub(aa, bb)
  +E = FS.fsub(P, AA, BB)
  +oe = FO.sub_okb(one, h1, aa, bb, oaa, obb)
  +ce = RL.rc_sub(one, h1, pp, hP, aa, bb, AA, BB, oaa, caa, obb, cbb)
  +c = F.add(x3, z3)
  +CC = FS.fadd(P, X3, Z3)
  +occ = FO.add_okb(one, h1, x3, z3, o3, oz3)
  +ccc = RL.rc_add(one, h1, pp, hP, x3, z3, X3, Z3, o3, c3, oz3, cz3)
  +d = F.sub(x3, z3)
  +D = FS.fsub(P, X3, Z3)
  +od = FO.sub_okb(one, h1, x3, z3, o3, oz3)
  +cd = RL.rc_sub(one, h1, pp, hP, x3, z3, X3, Z3, o3, c3, oz3, cz3)
  +da = F.mul(d, a)
  +DA = FS.fmul(P, D, A)
  +oda = MW.mul_okb(one, h1, d, a, od, oa)
  +cda = RL.rc_mul(one, h1, pp, hP, d, a, D, A, od, cd, oa, ca)
  +cb2 = F.mul(c, b)
  +CB = FS.fmul(P, CC, B)
  +ocb = MW.mul_okb(one, h1, c, b, occ, ob)
  +ccb = RL.rc_mul(one, h1, pp, hP, c, b, CC, B, occ, ccc, ob, cb)
  +out1 = (MW.mul_okb(one, h1, aa, bb, oaa, obb), RL.rc_mul(one, h1, pp, hP, aa, bb, AA, BB, oaa, caa, obb, cbb))
  +ec = F.mul(e, c24)
  +EC = FS.fmul(P, E, A24)
  +oec = MW.mul_okb(one, h1, e, c24, oe, oc)
  +cec = RL.rc_mul(one, h1, pp, hP, e, c24, E, A24, oe, ce, oc, cc)
  +sm = F.add(aa, ec)
  +SM = FS.fadd(P, AA, EC)
  +osm = FO.add_okb(one, h1, aa, ec, oaa, oec)
  +csm = RL.rc_add(one, h1, pp, hP, aa, ec, AA, EC, oaa, caa, oec, cec)
  +out2 = (MW.mul_okb(one, h1, e, sm, oe, osm), RL.rc_mul(one, h1, pp, hP, e, sm, E, SM, oe, ce, osm, csm))
  +sg = F.add(da, cb2)
  +SG = FS.fadd(P, DA, CB)
  +osg = FO.add_okb(one, h1, da, cb2, oda, ocb)
  +csg = RL.rc_add(one, h1, pp, hP, da, cb2, DA, CB, oda, cda, ocb, ccb)
  +out3 = (MW.sq_okb(one, h1, sg, osg), RL.rc_sq(one, h1, pp, hP, sg, SG, osg, csg))
  +t = F.sub(da, cb2)
  +T = FS.fsub(P, DA, CB)
  +ot = FO.sub_okb(one, h1, da, cb2, oda, ocb)
  +ct = RL.rc_sub(one, h1, pp, hP, da, cb2, DA, CB, oda, cda, ocb, ccb)
  +ott = MW.sq_okb(one, h1, t, ot)
  +ctt = RL.rc_sq(one, h1, pp, hP, t, T, ot, ct)
  +out4 = (MW.mul_okb(one, h1, x1, F.sq(t), o1, ott), RL.rc_mul(one, h1, pp, hP, x1, F.sq(t), X1, FS.fmul(P, T, T), o1, c1, ott, ctt))
  (out1, (out2, (out3, (out4, (hk, hkb)))))

# ---- one rung: swap ^= k_t, cswap, step ----

def rung_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +c24: List<&2, U32>, +oc: {LM.okb(32n, c24, 255n) == True{} : Bool}, +hv: {K.valo(one, c24) == S.a24(one) : Nat}, +x1: List<&2, U32>, +X1: Nat, +o1: {LM.okb(32n, x1, 255n) == True{} : Bool}, +c1: G.ceq(pp, FS.value(x1), X1), st: X.St, sst: S.LSt, h: Rst(pp, st, sst), +kt: U32, +KT: Nat, +hk: {v(kt) == KT : Nat}, +hkb: {Nat.is_le(KT, 1n) == True{} : Bool}) -> Rst(pp, X.rung(c24, x1, st, kt), S.rung(one, 1n+pp, X1, sst, KT)):
  match st sst:
    case X.St{+x2, +z2, +x3, +z3, +sw} S.LSt{+a2, +b2, +a3, +b3, +sws}:
      (r2, h2) = h
      (+o2, +c2) = r2
      (rz2, h3) = h2
      (+oz2, +cz2) = rz2
      (r3, h4) = h3
      (+o3, +c3) = r3
      (rz3, h5) = h4
      (+oz3, +cz3) = rz3
      (+hs, +hsb) = h5
      +w = U32.xor(sw, kt)
      +W = S.bxor(sws, KT)
      +hw = XB.xor_bits(sw, kt, sws, KT, hs, hk, hsb, hkb)
      +hwb = XB.bxor_le(sws, KT, hkb)
      step_rel(one, h1, pp, hP, c24, oc, hv, x1, X1, o1, c1, F.select(w, x2, x3), S.cs_fst(W, a2, a3), o_sel(one, h1, w, W, hw, hwb, x2, x3, o2, o3), c_fst(one, h1, pp, w, W, hw, hwb, x2, x3, a2, a3, o2, c2, o3, c3), F.select(w, z2, z3), S.cs_fst(W, b2, b3), o_sel(one, h1, w, W, hw, hwb, z2, z3, oz2, oz3), c_fst(one, h1, pp, w, W, hw, hwb, z2, z3, b2, b3, oz2, cz2, oz3, cz3), F.select(w, x3, x2), S.cs_snd(W, a2, a3), o_sel(one, h1, w, W, hw, hwb, x3, x2, o3, o2), c_snd(one, h1, pp, w, W, hw, hwb, x2, x3, a2, a3, o2, c2, o3, c3), F.select(w, z3, z2), S.cs_snd(W, b2, b3), o_sel(one, h1, w, W, hw, hwb, z3, z2, oz3, oz2), c_snd(one, h1, pp, w, W, hw, hwb, z2, z3, b2, b3, oz2, cz2, oz3, cz3), kt, KT, hk, hkb)

# ---- the ladder ----

def ladder_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +n: Nat, +c24: List<&2, U32>, +oc: {LM.okb(32n, c24, 255n) == True{} : Bool}, +hv: {K.valo(one, c24) == S.a24(one) : Nat}, +kc: List<&2, U32>, +hkc: {LM.lea(kc, 255n) == True{} : Bool}, +x1: List<&2, U32>, +X1: Nat, +o1: {LM.okb(32n, x1, 255n) == True{} : Bool}, +c1: G.ceq(pp, FS.value(x1), X1), st: X.St, sst: S.LSt, h: Rst(pp, st, sst)) -> Rst(pp, X.ladder(n, c24, kc, x1, st), S.ladder(one, 1n+pp, n, FS.value(kc), X1, sst)):
  match n:
    case 0n:
      h
    case 1n+ +t:
      +kt = X.kbit(kc, t)
      +KT = S.kbit(FS.value(kc), t)
      ladder_rel(one, h1, pp, hP, t, c24, oc, hv, kc, hkc, x1, X1, o1, c1, X.rung(c24, x1, st, kt), S.rung(one, 1n+pp, X1, sst, KT), rung_rel(one, h1, pp, hP, c24, oc, hv, x1, X1, o1, c1, st, sst, h, kt, KT, XB.kbit_val(kc, t, hkc), XB.kbit_le(kc, t, hkc)))

# ---- the end: cswap, x2 / z2, encode ----

def finish_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, st: X.St, sst: S.LSt, h: Rst(pp, st, sst)) -> {X.finish(st) == S.finish(1n+pp, sst) : List<&2, U32>}:
  match st sst:
    case X.St{+x2, +z2, +x3, +z3, +sw} S.LSt{+a2, +b2, +a3, +b3, +sws}:
      (r2, h2) = h
      (+o2, +c2) = r2
      (rz2, h3) = h2
      (+oz2, +cz2) = rz2
      (r3, h4) = h3
      (+o3, +c3) = r3
      (rz3, h5) = h4
      (+oz3, +cz3) = rz3
      (+hs, +hsb) = h5
      +P = {1n+pp : Nat}
      +xs = F.select(sw, x2, x3)
      +XS = S.cs_fst(sws, a2, a3)
      +zs = F.select(sw, z2, z3)
      +ZS = S.cs_fst(sws, b2, b3)
      +ox = o_sel(one, h1, sw, sws, hs, hsb, x2, x3, o2, o3)
      +cx = c_fst(one, h1, pp, sw, sws, hs, hsb, x2, x3, a2, a3, o2, c2, o3, c3)
      +oz = o_sel(one, h1, sw, sws, hs, hsb, z2, z3, oz2, oz3)
      +cz = c_fst(one, h1, pp, sw, sws, hs, hsb, z2, z3, b2, b3, oz2, cz2, oz3, cz3)
      +oi = PW.inv_okb(one, h1, zs, oz)
      +ci = RL.rc_inv(one, h1, pp, hP, zs, ZS, oz, cz)
      +m = F.mul(xs, F.inv(zs))
      +MM = FS.fmul(P, XS, FS.finv(P, ZS))
      +om = MW.mul_okb(one, h1, xs, F.inv(zs), ox, oi)
      +cm = RL.rc_mul(one, h1, pp, hP, xs, F.inv(zs), XS, FS.finv(P, ZS), ox, cx, oi, ci)
      +y = F.freeze(m)
      +oy = CN.freeze_okb(one, h1, pp, hP, m, om)
      +ey = Equal.trans(Nat, FS.value(y), Nat.mod(FS.value(m), P), Nat.mod(MM, P), CN.freeze_val(one, h1, pp, hP, m, om), cm)
      +e1 = Equal.sym(List<&2, U32>, S.le_bytes(32n, FS.value(y)), y, XB.bytes_le(32n, y, oy))
      Equal.trans(List<&2, U32>, y, S.le_bytes(32n, FS.value(y)), S.le_bytes(32n, Nat.mod(MM, P)), e1, Equal.cong(Nat, List<&2, U32>, z => S.le_bytes(32n, z), FS.value(y), Nat.mod(MM, P), ey))

# ---- X25519 ----

def a24_shape() -> {X.a24() == Con{65, Con{219, Con{1, K.rep(29n, 0, Nil{})}}} : List<&2, U32>}:
  {==}

def a24_valo(+one: Nat) -> {K.valo(one, X.a24()) == S.a24(one) : Nat}:
  %Equal.sym(List<&2, U32>, X.a24(), Con{65, Con{219, Con{1, K.rep(29n, 0, Nil{})}}}, a24_shape()) : {K.valo(one, _) == S.a24(one) : Nat}
  %Equal.sym(Nat, K.valo(one, K.rep(29n, 0, Nil{})), 0n, K.run0(one, 29n, Nil{})) : {Nat.add(Nat.mul(one, v(65)), C.shift(8n, Nat.add(Nat.mul(one, v(219)), C.shift(8n, Nat.add(Nat.mul(one, v(1)), C.shift(8n, _)))))) == S.a24(one) : Nat}
  {==}

def x25519_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +k: List<&2, U32>, +u: List<&2, U32>, +hk: {LM.okb(32n, k, 255n) == True{} : Bool}, +hu: {LM.okb(32n, u, 255n) == True{} : Bool}) -> {X.x25519_raw(k, u) == S.finish(1n+pp, S.ladder(one, 1n+pp, X.nbits(k), FS.value(X.clamp(k)), Nat.mod(S.decode_u(u), 1n+pp), S.LSt{1n, 0n, Nat.mod(S.decode_u(u), 1n+pp), 1n, 0n})) : List<&2, U32>}:
  +P = {1n+pp : Nat}
  +x1 = F.of_bytes(u)
  +X1 = Nat.mod(S.decode_u(u), P)
  +o1 = XB.mask_okb(31n, u, hu)
  +c1 = G.c_trans(pp, FS.value(F.mask_top(u)), FS.value(S.mask_last(u)), X1, G.c_eq(pp, FS.value(F.mask_top(u)), FS.value(S.mask_last(u)), Equal.cong(List<&2, U32>, Nat, z => FS.value(z), F.mask_top(u), S.mask_last(u), XB.mask_eq(u))), G.c_sym(pp, X1, FS.value(S.mask_last(u)), G.c_mod(pp, FS.value(S.mask_last(u)))))
  +kc = X.clamp(k)
  +hkc = LM.okb_lea(32n, kc, 255n, XB.clamp_okb(k, hk))
  +r1 = ({==}, G.c_eq(pp, FS.value(F.one()), 1n, {==}))
  +r0 = ({==}, G.c_eq(pp, FS.value(F.zero()), 0n, {==}))
  +r1b = ({==}, G.c_eq(pp, FS.value(F.one()), 1n, {==}))
  +h0 = (r1, (r0, ((o1, c1), (r1b, ({==}, {==})))))
  +hl = ladder_rel(one, h1, pp, hP, X.nbits(k), X.a24(), {==}, a24_valo(one), kc, hkc, x1, X1, o1, c1, X.St{F.one(), F.zero(), x1, F.one(), 0}, S.LSt{1n, 0n, X1, 1n, 0n}, h0)
  finish_rel(one, h1, pp, hP, X.ladder(X.nbits(k), X.a24(), kc, x1, X.St{F.one(), F.zero(), x1, F.one(), 0}), S.ladder(one, P, X.nbits(k), FS.value(kc), X1, S.LSt{1n, 0n, X1, 1n, 0n}), hl)

def x25519_value(+one: Nat, +h1: {one == 1n : Nat}, +k: List<&2, U32>, +u: List<&2, U32>, +hk: {FS.tight(k) == True{} : Bool}, +hu: {FS.tight(u) == True{} : Bool}) -> S.X25519.value(one, h1, k, u, hk, hu):
  +pp = PR.pp_of(one)
  +P = {1n+pp : Nat}
  +X1 = Nat.mod(S.decode_u(u), P)
  +st0 = S.LSt{1n, 0n, X1, 1n, 0n}
  %Equal.sym(Nat, FS.prime(one), P, PR.prime_eq(one, h1)) : {X.x25519_raw(k, u) == S.x25519_p(one, _, k, u) : List<&2, U32>}
  %XB.nbits_eq(k) : {X.x25519_raw(k, u) == S.finish(P, S.ladder(one, P, _, S.decode_scalar(k), X1, st0)) : List<&2, U32>}
  %Equal.cong(List<&2, U32>, Nat, z => FS.value(z), X.clamp(k), S.clamp(k), XB.clamp_eq(k)) : {X.x25519_raw(k, u) == S.finish(P, S.ladder(one, P, X.nbits(k), _, X1, st0)) : List<&2, U32>}
  x25519_rel(one, h1, pp, PR.hP(one, h1), k, u, LM.bytes_okb(32n, k, hk), LM.bytes_okb(32n, u, hu))
