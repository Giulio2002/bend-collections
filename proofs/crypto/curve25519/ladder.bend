import Base
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../spec/crypto/curve25519/x25519.bend as S
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ./limbs.bend as LM
import ./cong.bend as G
import ./xbits.bend as XB
import ./prime.bend as PR
import ../fe/pw.bend as PW
import ../fe/rel.bend as RE
import ../fe/conv.bend as CV
import ../fe/cst.bend as CS
import ./xlem.bend as XL

# X25519 == RFC 7748 (spec/crypto/curve25519/x25519.bend) over the fast
# field: the ladder state of the implementation is related to the
# specification's state field by field (RE.Rel: ok limbs, value congruent
# mod p), the swap bit is equal; every rung keeps the relation; the final
# cswap, inversion, product and encoding give the same bytes.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

def DP(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

def Rst(+one: Nat, +pp: Nat, st: X.St, sst: S.LSt) -> Data:
  match st sst:
    case X.St{x2, z2, x3, z3, sw} S.LSt{a2, b2, a3, b3, sws}:
      DP(RE.Rel(one, pp, x2, a2), DP(RE.Rel(one, pp, z2, b2), DP(RE.Rel(one, pp, x3, a3), DP(RE.Rel(one, pp, z3, b3), DP({U32.to_nat(sw) == sws : Nat}, {Nat.is_le(sws, 1n) == True{} : Bool})))))

# ---- one step ----

def step_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +c24: Nat, +hc24: {c24 == S.a24(one) : Nat}, +hcl: {Nat.is_lt(c24, WD.sc(17n, one)) == True{} : Bool}, +x1: FE.Fe, +X1: Nat, +r1: RE.Rel(one, pp, x1, X1), +x2: FE.Fe, +X2: Nat, +r2: RE.Rel(one, pp, x2, X2), +z2: FE.Fe, +Z2: Nat, +rz2: RE.Rel(one, pp, z2, Z2), +x3: FE.Fe, +X3: Nat, +r3: RE.Rel(one, pp, x3, X3), +z3: FE.Fe, +Z3: Nat, +rz3: RE.Rel(one, pp, z3, Z3), +kt: U32, +KT: Nat, +hk: {v(kt) == KT : Nat}, +hkb: {Nat.is_le(KT, 1n) == True{} : Bool}) -> Rst(one, pp, X.step(R, c24, x1, x2, z2, x3, z3, kt), S.step(one, 1n+pp, X1, X2, Z2, X3, Z3, KT)):
  +P = {1n+pp : Nat}
  +a = FE.add(R, x2, z2)
  +A = FS.fadd(P, X2, Z2)
  +ra = RE.r_add(one, h1, pp, hP, R, hR, x2, z2, X2, Z2, r2, rz2)
  +aa = FE.sq(R, a)
  +AA = FS.fmul(P, A, A)
  +raa = RE.r_sq(one, h1, pp, hP, R, hR, a, A, ra)
  +b = FE.sub(R, x2, z2)
  +B = FS.fsub(P, X2, Z2)
  +rb = RE.r_sub(one, h1, pp, hP, R, hR, x2, z2, X2, Z2, r2, rz2)
  +bb = FE.sq(R, b)
  +BB = FS.fmul(P, B, B)
  +rbb = RE.r_sq(one, h1, pp, hP, R, hR, b, B, rb)
  +e = FE.sub(R, aa, bb)
  +E = FS.fsub(P, AA, BB)
  +re = RE.r_sub(one, h1, pp, hP, R, hR, aa, bb, AA, BB, raa, rbb)
  +c = FE.add(R, x3, z3)
  +CC = FS.fadd(P, X3, Z3)
  +rc = RE.r_add(one, h1, pp, hP, R, hR, x3, z3, X3, Z3, r3, rz3)
  +d = FE.sub(R, x3, z3)
  +D = FS.fsub(P, X3, Z3)
  +rd = RE.r_sub(one, h1, pp, hP, R, hR, x3, z3, X3, Z3, r3, rz3)
  +da = FE.mul(R, d, a)
  +DA = FS.fmul(P, D, A)
  +rda = RE.r_mul(one, h1, pp, hP, R, hR, d, a, D, A, rd, ra)
  +cb = FE.mul(R, c, b)
  +CB = FS.fmul(P, CC, B)
  +rcb = RE.r_mul(one, h1, pp, hP, R, hR, c, b, CC, B, rc, rb)
  +o1 = RE.r_mul(one, h1, pp, hP, R, hR, aa, bb, AA, BB, raa, rbb)
  +ec = FE.mul_small(R, e, c24)
  +EC = FS.fmul(P, E, S.a24(one))
  +rec = L.subst(Nat, t => RE.Rel(one, pp, ec, FS.fmul(P, E, t)), c24, S.a24(one), hc24, RE.r_mul_small(one, h1, pp, hP, R, hR, e, E, c24, hcl, re))
  +sm = FE.add(R, aa, ec)
  +SM = FS.fadd(P, AA, EC)
  +rsm = RE.r_add(one, h1, pp, hP, R, hR, aa, ec, AA, EC, raa, rec)
  +o2 = RE.r_mul(one, h1, pp, hP, R, hR, e, sm, E, SM, re, rsm)
  +sg = FE.add(R, da, cb)
  +SG = FS.fadd(P, DA, CB)
  +rsg = RE.r_add(one, h1, pp, hP, R, hR, da, cb, DA, CB, rda, rcb)
  +o3 = RE.r_sq(one, h1, pp, hP, R, hR, sg, SG, rsg)
  +t = FE.sub(R, da, cb)
  +T = FS.fsub(P, DA, CB)
  +rt = RE.r_sub(one, h1, pp, hP, R, hR, da, cb, DA, CB, rda, rcb)
  +rtt = RE.r_sq(one, h1, pp, hP, R, hR, t, T, rt)
  +o4 = RE.r_mul(one, h1, pp, hP, R, hR, x1, FE.sq(R, t), X1, FS.fmul(P, T, T), r1, rtt)
  (o1, (o2, (o3, (o4, (hk, hkb)))))

# ---- one rung: swap ^= k_t, cswap, step ----

def rung_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +c24: Nat, +hc24: {c24 == S.a24(one) : Nat}, +hcl: {Nat.is_lt(c24, WD.sc(17n, one)) == True{} : Bool}, +x1: FE.Fe, +X1: Nat, +r1: RE.Rel(one, pp, x1, X1), +st: X.St, +sst: S.LSt, +h: Rst(one, pp, st, sst), +kt: U32, +KT: Nat, +hk: {v(kt) == KT : Nat}, +hkb: {Nat.is_le(KT, 1n) == True{} : Bool}) -> Rst(one, pp, X.rung(R, c24, x1, st, kt), S.rung(one, 1n+pp, X1, sst, KT)):
  match st sst:
    case X.St{+x2, +z2, +x3, +z3, +sw} S.LSt{+a2, +b2, +a3, +b3, +sws}:
      (+r2, +h2) = h
      (+rz2, +h3) = h2
      (+r3, +h4) = h3
      (+rz3, +h5) = h4
      (+hs, +hsb) = h5
      +w = U32.xor(sw, kt)
      +W = S.bxor(sws, KT)
      +hw = XB.xor_bits(sw, kt, sws, KT, hs, hk, hsb, hkb)
      +hwb = XB.bxor_le(sws, KT, hkb)
      step_rel(one, h1, pp, hP, R, hR, c24, hc24, hcl, x1, X1, r1, FE.select(w, x2, x3), S.cs_fst(W, a2, a3), XL.sel_fst(one, pp, w, W, hw, hwb, x2, x3, a2, a3, r2, r3), FE.select(w, z2, z3), S.cs_fst(W, b2, b3), XL.sel_fst(one, pp, w, W, hw, hwb, z2, z3, b2, b3, rz2, rz3), FE.select(w, x3, x2), S.cs_snd(W, a2, a3), XL.sel_snd(one, pp, w, W, hw, hwb, x2, x3, a2, a3, r2, r3), FE.select(w, z3, z2), S.cs_snd(W, b2, b3), XL.sel_snd(one, pp, w, W, hw, hwb, z2, z3, b2, b3, rz2, rz3), kt, KT, hk, hkb)

# ---- the ladder ----

def ladder_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +n: Nat, +c24: Nat, +hc24: {c24 == S.a24(one) : Nat}, +hcl: {Nat.is_lt(c24, WD.sc(17n, one)) == True{} : Bool}, +kc: List<&2, U32>, +hkc: {LM.lea(kc, 255n) == True{} : Bool}, +x1: FE.Fe, +X1: Nat, +r1: RE.Rel(one, pp, x1, X1), +st: X.St, +sst: S.LSt, +h: Rst(one, pp, st, sst)) -> Rst(one, pp, X.ladder(n, R, c24, kc, x1, st), S.ladder(one, 1n+pp, n, FS.value(kc), X1, sst)):
  match n:
    case 0n:
      h
    case 1n+ +t:
      +kt = X.kbit(kc, t)
      +KT = S.kbit(FS.value(kc), t)
      ladder_rel(one, h1, pp, hP, R, hR, t, c24, hc24, hcl, kc, hkc, x1, X1, r1, X.rung(R, c24, x1, st, kt), S.rung(one, 1n+pp, X1, sst, KT), rung_rel(one, h1, pp, hP, R, hR, c24, hc24, hcl, x1, X1, r1, st, sst, h, kt, KT, XB.kbit_val(kc, t, hkc), XB.kbit_le(kc, t, hkc)))

# ---- the end: cswap, x2 / z2, encode ----

def finish_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +st: X.St, +sst: S.LSt, +h: Rst(one, pp, st, sst)) -> {X.finish(R, st) == S.finish(1n+pp, sst) : List<&2, U32>}:
  match st sst:
    case X.St{+x2, +z2, +x3, +z3, +sw} S.LSt{+a2, +b2, +a3, +b3, +sws}:
      (+r2, +h2) = h
      (+rz2, +h3) = h2
      (+r3, +h4) = h3
      (+rz3, +h5) = h4
      (+hs, +hsb) = h5
      +P = {1n+pp : Nat}
      +xs = FE.select(sw, x2, x3)
      +XS = S.cs_fst(sws, a2, a3)
      +zs = FE.select(sw, z2, z3)
      +ZS = S.cs_fst(sws, b2, b3)
      +rxs = XL.sel_fst(one, pp, sw, sws, hs, hsb, x2, x3, a2, a3, r2, r3)
      +rzs = XL.sel_fst(one, pp, sw, sws, hs, hsb, z2, z3, b2, b3, rz2, rz3)
      +ri = RE.r_inv(one, h1, pp, hP, R, hR, zs, ZS, rzs)
      +m = FE.mul(R, xs, FE.inv(R, zs))
      +MM = FS.fmul(P, XS, FS.finv(P, ZS))
      +rm = RE.r_mul(one, h1, pp, hP, R, hR, xs, FE.inv(R, zs), XS, FS.finv(P, ZS), rxs, ri)
      +om = RE.o(one, pp, m, MM, rm)
      +y = FE.to_bytes(R, m)
      +ey = Equal.trans(Nat, FS.value(y), Nat.mod(FV.value(m), P), Nat.mod(MM, P), CV.to_bytes_value(one, h1, pp, hP, R, hR, m, om), RE.c(one, pp, m, MM, rm))
      +e1 = Equal.sym(List<&2, U32>, S.le_bytes(32n, FS.value(y)), y, XB.bytes_le(32n, y, LM.bytes_okb(32n, y, CV.to_bytes_tight(one, h1, R, m))))
      Equal.trans(List<&2, U32>, y, S.le_bytes(32n, FS.value(y)), S.le_bytes(32n, Nat.mod(MM, P)), e1, Equal.cong(Nat, List<&2, U32>, z => S.le_bytes(32n, z), FS.value(y), Nat.mod(MM, P), ey))

# ---- X25519 ----

def x25519_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +c24: Nat, +hc24: {c24 == S.a24(one) : Nat}, +hcl: {Nat.is_lt(c24, WD.sc(17n, one)) == True{} : Bool}, +k: List<&2, U32>, +u: List<&2, U32>, +hk: {FS.tight(k) == True{} : Bool}, +hu: {FS.tight(u) == True{} : Bool}) -> {X.x25519_g(R, c24, k, u) == S.finish(1n+pp, S.ladder(one, 1n+pp, X.nbits(k), FS.value(X.clamp(k)), Nat.mod(S.decode_u(u), 1n+pp), S.LSt{1n, 0n, Nat.mod(S.decode_u(u), 1n+pp), 1n, 0n})) : List<&2, U32>}:
  +P = {1n+pp : Nat}
  +x1 = FE.of_bytes(u)
  +X1 = Nat.mod(S.decode_u(u), P)
  +c1 = G.c_trans(pp, FV.value(x1), S.decode_u(u), X1, G.c_eq(pp, FV.value(x1), S.decode_u(u), XL.decode_u_fe(one, h1, u, hu)), G.c_sym(pp, X1, S.decode_u(u), G.c_mod(pp, S.decode_u(u))))
  +r1 = RE.mk(one, pp, x1, X1, CV.of_bytes_ok(one, h1, u), c1)
  +kc = X.clamp(k)
  +hkc = LM.okb_lea(32n, kc, 255n, XB.clamp_okb(k, LM.bytes_okb(32n, k, hk)))
  +oone = XL.small_ok(one, h1, 1n, XL.one_lt19(one, h1))
  +ozero = XL.small_ok(one, h1, 0n, PW.sc_pos(19n, one, h1))
  +rone = RE.mk(one, pp, FE.one(), 1n, oone, G.c_eq(pp, FV.value(FE.one()), 1n, {==}))
  +rzero = RE.mk(one, pp, FE.zero(), 0n, ozero, G.c_eq(pp, FV.value(FE.zero()), 0n, {==}))
  +st0 = {X.St{FE.one(), FE.zero(), x1, FE.one(), 0} : X.St}
  +sst0 = {S.LSt{1n, 0n, X1, 1n, 0n} : S.LSt}
  +hl = ladder_rel(one, h1, pp, hP, R, hR, X.nbits(k), c24, hc24, hcl, kc, hkc, x1, X1, r1, st0, sst0, (rone, (rzero, (r1, (rone, ({==}, {==}))))))
  finish_rel(one, h1, pp, hP, R, hR, X.ladder(X.nbits(k), R, c24, kc, x1, st0), S.ladder(one, P, X.nbits(k), FS.value(kc), X1, sst0), hl)

# the constants of x25519_raw (the radix: ../fe/cst.bend)
def a24_of_eq(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>) -> {X.a24_of(xs) == S.a24(one) : Nat}:
  Equal.trans(Nat, X.a24(X.one_of(xs)), X.a24(one), S.a24(one), Equal.cong(Nat, Nat, t => X.a24(t), X.one_of(xs), one, CS.one_of_eq(one, h1, xs)), XL.a24_eq(one))

def a24_of_lt(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>) -> {Nat.is_lt(X.a24_of(xs), WD.sc(17n, one)) == True{} : Bool}:
  L.subst(Nat, t => {Nat.is_lt(t, WD.sc(17n, one)) == True{} : Bool}, X.a24(one), X.a24_of(xs), Equal.trans(Nat, X.a24(one), S.a24(one), X.a24_of(xs), XL.a24_eq(one), Equal.sym(Nat, X.a24_of(xs), S.a24(one), a24_of_eq(one, h1, xs))), XL.a24_lt(one, h1))

def x25519_value(+one: Nat, +h1: {one == 1n : Nat}, +k: List<&2, U32>, +u: List<&2, U32>, +hk: {FS.tight(k) == True{} : Bool}, +hu: {FS.tight(u) == True{} : Bool}) -> S.X25519.value(one, h1, k, u, hk, hu):
  +pp = PR.pp_of(one)
  +P = {1n+pp : Nat}
  +X1 = Nat.mod(S.decode_u(u), P)
  +st0 = {S.LSt{1n, 0n, X1, 1n, 0n} : S.LSt}
  %Equal.sym(Nat, FS.prime(one), P, PR.prime_eq(one, h1)) : {X.x25519_raw(k, u) == S.x25519_p(one, _, k, u) : List<&2, U32>}
  %XB.nbits_eq(k) : {X.x25519_raw(k, u) == S.finish(P, S.ladder(one, P, _, S.decode_scalar(k), X1, st0)) : List<&2, U32>}
  %Equal.cong(List<&2, U32>, Nat, z => FS.value(z), X.clamp(k), S.clamp(k), XB.clamp_eq(k)) : {X.x25519_raw(k, u) == S.finish(P, S.ladder(one, P, X.nbits(k), _, X1, st0)) : List<&2, U32>}
  x25519_rel(one, h1, pp, PR.hP(one, h1), X.radix_of(k), CS.radix_of_eq(one, h1, k), X.a24_of(k), a24_of_eq(one, h1, k), a24_of_lt(one, h1, k), k, u, hk, hu)
