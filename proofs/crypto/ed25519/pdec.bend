import Base
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../spec/crypto/curve25519/x25519.bend as SX
import ../../../spec/crypto/ed25519.bend as SE
import ../../../src/crypto/curve25519/field.bend as F
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../../src/crypto/ed25519/point.bend as PT
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/u32.bend as U
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../curve25519/limbs.bend as LM
import ./bytefield.bend as LO
import ../curve25519/cong.bend as G
import ../curve25519/xbits.bend as XB
import ../curve25519/xlem.bend as LD
import ../curve25519/num.bend as M3
import ../fe/rel.bend as RE
import ../fe/conv.bend as CV
import ./prel.bend as PR
import ./pcodec.bend as PC

# Decoding (RFC 8032 5.1.3) of src/crypto/ed25519/point.bend (on the fast
# field) against spec/crypto/ed25519.bend: for every 32-byte string both
# reject, or both accept with related points; and the base point.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def hv_p(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}) -> {Nat.add(LO.valo(one, F.comp_p()), 1n+pp) == LO.T(one) : Nat}:
  +P = {1n+pp : Nat}
  +e1 = M3.cong_l(LO.valo(one, F.comp_p()), Nat.add(P, 38n), P, LO.comp_p_val(one, h1, pp, hP))
  +e2 = Equal.trans(Nat, Nat.add(Nat.add(P, 38n), P), Nat.add(P, Nat.add(38n, P)), Nat.add(Nat.add(P, P), 38n), NA.add_assoc(P, 38n, P), Equal.trans(Nat, Nat.add(P, Nat.add(38n, P)), Nat.add(P, Nat.add(P, 38n)), Nat.add(Nat.add(P, P), 38n), M3.cong_r(P, Nat.add(38n, P), Nat.add(P, 38n), NA.add_comm(38n, P)), Equal.sym(Nat, Nat.add(Nat.add(P, P), 38n), Nat.add(P, Nat.add(P, 38n)), NA.add_assoc(P, P, 38n))))
  Equal.trans(Nat, Nat.add(LO.valo(one, F.comp_p()), P), Nat.add(Nat.add(P, 38n), P), LO.T(one), e1, Equal.trans(Nat, Nat.add(Nat.add(P, 38n), P), Nat.add(Nat.add(P, P), 38n), LO.T(one), e2, Equal.sym(Nat, LO.T(one), Nat.add(Nat.add(P, P), 38n), LO.t_val(one, h1, pp, hP))))

def ge_p_eq(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +y: List<&2, U32>, +hy: {LM.okb(32n, y, 255n) == True{} : Bool}) -> {PT.ge_p(y) == Bool.not(Nat.is_lt(FS.value(y), 1n+pp)) : Bool}:
  Equal.cong(Bool, Bool, z => Bool.not(z), U32.is_eq(LM.cc(F.carry(F.addl(y, F.comp_p()), 0)), 0), Nat.is_lt(FS.value(y), 1n+pp), LO.lt_by(one, h1, pp, y, F.comp_p(), hy, {==}, hv_p(one, h1, pp, hP), Nat.is_lt(v(LM.cc(F.carry(F.addl(y, F.comp_p()), 0))), one), {==}))

# ---- the end of decoding: the sign of x ----

def dec_fin_rel_core(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +a: Nat, +rx: RE.Rel(one, pp, x, a), +ha: {Nat.mod(a, 1n+pp) == a : Nat}, +y: FE.Fe, +b: Nat, +ry: RE.Rel(one, pp, y, b), +x0: U32, +b0: Nat, +hx0: {v(x0) == b0 : Nat}, +hb0: {Nat.is_le(b0, 1n) == True{} : Bool}, +fs: Bool) -> PC.MR(one, pp, PT.dec_fin(R, x, y, x0, fs), SE.dec_fin(1n+pp, a, b, b0, fs)):
  match fs:
    case True{}:
      {==}
    case False{}:
      +P = {1n+pp : Nat}
      +s = U32.xor(FE.parity(R, x), x0)
      +S = SX.bxor(Nat.mod(a, 2n), b0)
      +hs = XB.xor_bits(FE.parity(R, x), x0, Nat.mod(a, 2n), b0, PC.par_rel(one, h1, pp, hP, R, hR, x, a, rx, ha), hx0, PC.mod2_le(a), hb0)
      +hsb = XB.bxor_le(Nat.mod(a, 2n), b0, hb0)
      +nx = FE.neg(R, x)
      +NX = FS.fsub(P, 0n, a)
      +rn = PR.rsub(one, h1, pp, hP, R, hR, FE.zero(), x, 0n, a, PC.r_zero(one, h1, pp), rx)
      +x2 = FE.select(s, x, nx)
      +X2 = SX.cs_fst(S, a, NX)
      +r2 = LD.sel_fst(one, pp, s, S, hs, hsb, x, nx, a, NX, rx, rn)
      PR.mk(one, pp, x2, y, FE.one(), FE.mul(R, x2, y), X2, b, 1n, FS.fmul(P, X2, b), r2, ry, PC.r_one(one, h1, pp), PR.rmul(one, h1, pp, hP, R, hR, x2, y, X2, b, r2, ry))

def fail_eq(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +a: Nat, +rx: RE.Rel(one, pp, x, a), +ha: {Nat.mod(a, 1n+pp) == a : Nat}, +x0: U32, +b0: Nat, +hx0: {v(x0) == b0 : Nat}) -> {Bool.and(FE.is_zero(R, x), U32.is_eq(x0, 1)) == Bool.and(Nat.is_eq(a, 0n), Nat.is_eq(b0, 1n)) : Bool}:
  +e1 = PC.iz_rel(one, h1, pp, hP, R, hR, x, a, rx, ha)
  +e2 = Equal.trans(Bool, U32.is_eq(x0, 1), Nat.is_eq(v(x0), 1n), Nat.is_eq(b0, 1n), PC.u32_eq_nat(x0, 1), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 1n), v(x0), b0, hx0))
  Equal.trans(Bool, Bool.and(FE.is_zero(R, x), U32.is_eq(x0, 1)), Bool.and(Nat.is_eq(a, 0n), U32.is_eq(x0, 1)), Bool.and(Nat.is_eq(a, 0n), Nat.is_eq(b0, 1n)), Equal.cong(Bool, Bool, z => Bool.and(z, U32.is_eq(x0, 1)), FE.is_zero(R, x), Nat.is_eq(a, 0n), e1), Equal.cong(Bool, Bool, z => Bool.and(Nat.is_eq(a, 0n), z), U32.is_eq(x0, 1), Nat.is_eq(b0, 1n), e2))

def dec_fin_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +a: Nat, +rx: RE.Rel(one, pp, x, a), +ha: {Nat.mod(a, 1n+pp) == a : Nat}, +y: FE.Fe, +b: Nat, +ry: RE.Rel(one, pp, y, b), +x0: U32, +b0: Nat, +hx0: {v(x0) == b0 : Nat}, +hb0: {Nat.is_le(b0, 1n) == True{} : Bool}) -> PC.MR(one, pp, PT.dec_fin(R, x, y, x0, Bool.and(FE.is_zero(R, x), U32.is_eq(x0, 1))), SE.dec_fin(1n+pp, a, b, b0, Bool.and(Nat.is_eq(a, 0n), Nat.is_eq(b0, 1n)))):
  +fs = Bool.and(Nat.is_eq(a, 0n), Nat.is_eq(b0, 1n))
  %Equal.sym(Bool, Bool.and(FE.is_zero(R, x), U32.is_eq(x0, 1)), fs, fail_eq(one, h1, pp, hP, R, hR, x, a, rx, ha, x0, b0, hx0)) : PC.MR(one, pp, PT.dec_fin(R, x, y, x0, _), SE.dec_fin(1n+pp, a, b, b0, fs))
  dec_fin_rel_core(one, h1, pp, hP, R, hR, x, a, rx, ha, y, b, ry, x0, b0, hx0, hb0, fs)

# ---- the root choice ----

def dec_root_rel_core(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +rs: RE.Rel(one, pp, PT.cs_s(cs), SE.sqm1(1n+pp)), +x: FE.Fe, +a: Nat, +rx: RE.Rel(one, pp, x, a), +ha: {Nat.mod(a, 1n+pp) == a : Nat}, +y: FE.Fe, +b: Nat, +ry: RE.Rel(one, pp, y, b), +x0: U32, +b0: Nat, +hx0: {v(x0) == b0 : Nat}, +hb0: {Nat.is_le(b0, 1n) == True{} : Bool}, +su: Bool, +snu: Bool) -> PC.MR(one, pp, PT.dec_root(cs, x, y, x0, su, snu), SE.dec_root(1n+pp, a, b, b0, su, snu)):
  match su snu:
    case True{} _:
      dec_fin_rel(one, h1, pp, hP, PT.cs_r(cs), hR, x, a, rx, ha, y, b, ry, x0, b0, hx0, hb0)
    case False{} True{}:
      +P = {1n+pp : Nat}
      +R = PT.cs_r(cs)
      +x1 = FE.mul(R, x, PT.cs_s(cs))
      +X1 = FS.fmul(P, a, SE.sqm1(P))
      +r1 = PR.rmul(one, h1, pp, hP, R, hR, x, PT.cs_s(cs), a, SE.sqm1(P), rx, rs)
      dec_fin_rel(one, h1, pp, hP, R, hR, x1, X1, r1, PC.red(pp, Nat.mul(a, SE.sqm1(P))), y, b, ry, x0, b0, hx0, hb0)
    case False{} False{}:
      {==}

def dec_root_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +rs: RE.Rel(one, pp, PT.cs_s(cs), SE.sqm1(1n+pp)), +x: FE.Fe, +a: Nat, +rx: RE.Rel(one, pp, x, a), +ha: {Nat.mod(a, 1n+pp) == a : Nat}, +y: FE.Fe, +b: Nat, +ry: RE.Rel(one, pp, y, b), +x0: U32, +b0: Nat, +hx0: {v(x0) == b0 : Nat}, +hb0: {Nat.is_le(b0, 1n) == True{} : Bool}, +iu: Bool, +inu: Bool, +su: Bool, +snu: Bool, +hu: {iu == su : Bool}, +hnu: {inu == snu : Bool}) -> PC.MR(one, pp, PT.dec_root(cs, x, y, x0, iu, inu), SE.dec_root(1n+pp, a, b, b0, su, snu)):
  %Equal.sym(Bool, iu, su, hu) : PC.MR(one, pp, PT.dec_root(cs, x, y, x0, _, inu), SE.dec_root(1n+pp, a, b, b0, su, snu))
  %Equal.sym(Bool, inu, snu, hnu) : PC.MR(one, pp, PT.dec_root(cs, x, y, x0, su, _), SE.dec_root(1n+pp, a, b, b0, su, snu))
  dec_root_rel_core(one, h1, pp, hP, cs, hR, rs, x, a, rx, ha, y, b, ry, x0, b0, hx0, hb0, su, snu)

def dec_y_rel_core(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd: RE.Rel(one, pp, PT.cs_d(cs), D), +rs: RE.Rel(one, pp, PT.cs_s(cs), SE.sqm1(1n+pp)), +y: FE.Fe, +Y: Nat, +ry: RE.Rel(one, pp, y, Y), +x0: U32, +b0: Nat, +hx0: {v(x0) == b0 : Nat}, +hb0: {Nat.is_le(b0, 1n) == True{} : Bool}, +bad: Bool) -> PC.MR(one, pp, PT.dec_y(cs, y, x0, bad), SE.dec_y(1n+pp, D, Y, b0, bad)):
  match bad:
    case True{}:
      {==}
    case False{}:
      +P = {1n+pp : Nat}
      +R = PT.cs_r(cs)
      +yy = FE.sq(R, y)
      +YY = FS.fmul(P, Y, Y)
      +ryy = PR.rsq(one, h1, pp, hP, R, hR, y, Y, ry)
      +u = FE.sub(R, yy, FE.one())
      +UU = FS.fsub(P, YY, 1n)
      +ru = PR.rsub(one, h1, pp, hP, R, hR, yy, FE.one(), YY, 1n, ryy, PC.r_one(one, h1, pp))
      +vv = FE.add(R, FE.mul(R, PT.cs_d(cs), yy), FE.one())
      +VV = FS.fadd(P, FS.fmul(P, D, YY), 1n)
      +rv = PR.radd(one, h1, pp, hP, R, hR, FE.mul(R, PT.cs_d(cs), yy), FE.one(), FS.fmul(P, D, YY), 1n, PR.rmul(one, h1, pp, hP, R, hR, PT.cs_d(cs), yy, D, YY, rd, ryy), PC.r_one(one, h1, pp))
      +v3 = FE.mul(R, FE.sq(R, vv), vv)
      +V3 = FS.fmul(P, FS.fmul(P, VV, VV), VV)
      +rv3 = PR.rmul(one, h1, pp, hP, R, hR, FE.sq(R, vv), vv, FS.fmul(P, VV, VV), VV, PR.rsq(one, h1, pp, hP, R, hR, vv, VV, rv), rv)
      +v7 = FE.mul(R, FE.sq(R, v3), vv)
      +V7 = FS.fmul(P, FS.fmul(P, V3, V3), VV)
      +rv7 = PR.rmul(one, h1, pp, hP, R, hR, FE.sq(R, v3), vv, FS.fmul(P, V3, V3), VV, PR.rsq(one, h1, pp, hP, R, hR, v3, V3, rv3), rv)
      +uv7 = FE.mul(R, u, v7)
      +UV7 = FS.fmul(P, UU, V7)
      +ruv7 = PR.rmul(one, h1, pp, hP, R, hR, u, v7, UU, V7, ru, rv7)
      +pw = FE.pow_p58(R, uv7)
      +PWV = FS.fpow(P, UV7, Nat.div(Nat.sub(P, 5n), 8n))
      +rpw = RE.r_p58(one, h1, pp, hP, R, hR, uv7, UV7, ruv7)
      +x = FE.mul(R, FE.mul(R, u, v3), pw)
      +XX = FS.fmul(P, FS.fmul(P, UU, V3), PWV)
      +rx = PR.rmul(one, h1, pp, hP, R, hR, FE.mul(R, u, v3), pw, FS.fmul(P, UU, V3), PWV, PR.rmul(one, h1, pp, hP, R, hR, u, v3, UU, V3, ru, rv3), rpw)
      +vxx = FE.mul(R, vv, FE.sq(R, x))
      +VXX = FS.fmul(P, VV, FS.fmul(P, XX, XX))
      +rvxx = PR.rmul(one, h1, pp, hP, R, hR, vv, FE.sq(R, x), VV, FS.fmul(P, XX, XX), rv, PR.rsq(one, h1, pp, hP, R, hR, x, XX, rx))
      +NU = FS.fsub(P, 0n, UU)
      +rnu = PR.rsub(one, h1, pp, hP, R, hR, FE.zero(), u, 0n, UU, PC.r_zero(one, h1, pp), ru)
      +eu = PC.eq_rel(one, h1, pp, hP, R, hR, vxx, u, VXX, UU, rvxx, ru, PC.red(pp, Nat.mul(VV, FS.fmul(P, XX, XX))), PC.red(pp, Nat.sub(Nat.add(YY, P), Nat.mod(1n, P))))
      +enu = PC.eq_rel(one, h1, pp, hP, R, hR, vxx, FE.neg(R, u), VXX, NU, rvxx, rnu, PC.red(pp, Nat.mul(VV, FS.fmul(P, XX, XX))), PC.red(pp, Nat.sub(Nat.add(0n, P), Nat.mod(UU, P))))
      dec_root_rel(one, h1, pp, hP, cs, hR, rs, x, XX, rx, PC.red(pp, Nat.mul(FS.fmul(P, UU, V3), PWV)), y, Y, ry, x0, b0, hx0, hb0, FE.eq(R, vxx, u), FE.eq(R, vxx, FE.neg(R, u)), Nat.is_eq(VXX, UU), Nat.is_eq(VXX, NU), eu, enu)

def decode_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd: RE.Rel(one, pp, PT.cs_d(cs), D), +rs: RE.Rel(one, pp, PT.cs_s(cs), SE.sqm1(1n+pp)), +bs: List<&2, U32>, +hb: {LM.okb(32n, bs, 255n) == True{} : Bool}) -> PC.MR(one, pp, PT.decode(cs, bs), SE.decode(1n+pp, D, bs)):
  +P = {1n+pp : Nat}
  +yb = F.mask_top(bs)
  +Y = FS.value(SX.mask_last(bs))
  +hyv = Equal.cong(List<&2, U32>, Nat, z => FS.value(z), F.mask_top(bs), SX.mask_last(bs), XB.mask_eq(bs))
  +hy = XB.mask_okb(31n, bs, hb)
  +hl = LM.okb_lea(32n, bs, 255n, hb)
  +hbad = Equal.trans(Bool, PT.ge_p(yb), Bool.not(Nat.is_lt(FS.value(yb), P)), Bool.not(Nat.is_lt(Y, P)), ge_p_eq(one, h1, pp, hP, yb, hy), Equal.cong(Nat, Bool, z => Bool.not(Nat.is_lt(z, P)), FS.value(yb), Y, hyv))
  +y = FE.of_bytes(bs)
  +ry = RE.mk(one, pp, y, Y, CV.of_bytes_ok(one, h1, bs), G.c_eq(pp, FV.value(y), Y, LD.decode_u_fe(one, h1, bs, LM.okb_bytes(32n, bs, hb))))
  %Equal.sym(Bool, PT.ge_p(yb), Bool.not(Nat.is_lt(Y, P)), hbad) : PC.MR(one, pp, PT.dec_y(cs, y, X.kbit(bs, 255n), _), SE.decode(P, D, bs))
  dec_y_rel_core(one, h1, pp, hP, cs, hR, D, rd, rs, y, Y, ry, X.kbit(bs, 255n), SX.kbit(FS.value(bs), 255n), XB.kbit_val(bs, 255n, hl), XB.kbit_le(bs, 255n, hl), Bool.not(Nat.is_lt(Y, P)))

# ---- the base point ----

def le_bytes_ok(+n: Nat, +x: Nat) -> {LM.okb(n, SX.le_bytes(n, x), 255n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      +r = Nat.mod(x, 256n)
      +hr = NR.dm_lt(255n, x)
      +e = U.to_nat_from_nat(r, 8n, {==}, hr)
      +h = L.subst(Nat, z => {Nat.is_le(z, 255n) == True{} : Bool}, r, v(U32.from_nat(r)), Equal.sym(Nat, v(U32.from_nat(r)), r, e), N.lt_succ_le(r, 255n, hr))
      L.and_intro(Nat.is_le(v(U32.from_nat(r)), 255n), LM.okb(m, SX.le_bytes(m, Nat.div(x, 256n)), 255n), h, le_bytes_ok(m, Nat.div(x, 256n)))

def identity_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat) -> PR.Rp(one, pp, PT.identity(), SE.identity()):
  PR.mk(one, pp, FE.zero(), FE.one(), FE.one(), FE.zero(), 0n, 1n, 1n, 0n, PC.r_zero(one, h1, pp), PC.r_one(one, h1, pp), PC.r_one(one, h1, pp), PC.r_zero(one, h1, pp))

def base_of_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +m: Maybe<&2, PT.Pt>, +sm: Maybe<&2, SE.EPt>, +h: PC.MR(one, pp, m, sm)) -> PR.Rp(one, pp, PT.base_of(m), SE.base_of(sm)):
  match m sm:
    case None{} None{}:
      identity_rel(one, h1, pp)
    case Some{+p} Some{+sp}:
      h
    case None{} Some{sp}:
      Empty.absurd(PR.Rp(one, pp, PT.identity(), sp), L.true_false(h))
    case Some{p} None{}:
      Empty.absurd(PR.Rp(one, pp, p, SE.identity()), L.true_false(h))

def small_r_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +r: Nat, +k: Nat, +hk: {Nat.is_lt(k, 8n) == True{} : Bool}) -> RE.Rel(one, pp, PT.small_r(r, k), k):
  match r:
    case 0n:
      PC.r_small(one, h1, pp, k, PC.small_lt(one, h1, k, hk))
    case 1n+q:
      PC.r_small(one, h1, pp, k, PC.small_lt(one, h1, k, hk))

def cs_small_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +cs: PT.Cs, +k: Nat, +hk: {Nat.is_lt(k, 8n) == True{} : Bool}) -> RE.Rel(one, pp, PT.cs_small(cs, k), k):
  match cs:
    case PT.Cs{+r, d, d2, s}:
      small_r_rel(one, h1, pp, r, k, hk)

def base_go_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd: RE.Rel(one, pp, PT.cs_d(cs), D), +rs: RE.Rel(one, pp, PT.cs_s(cs), SE.sqm1(1n+pp))) -> PR.Rp(one, pp, PT.base_go(cs), SE.base(1n+pp, D)):
  +P = {1n+pp : Nat}
  +R = PT.cs_r(cs)
  +c4 = PT.cs_small(cs, 4n)
  +c5 = PT.cs_small(cs, 5n)
  +m = FE.mul(R, c4, FE.inv(R, c5))
  +FM = FS.fmul(P, 4n, FS.finv(P, 5n))
  +rm = PR.rmul(one, h1, pp, hP, R, hR, c4, FE.inv(R, c5), 4n, FS.finv(P, 5n), cs_small_rel(one, h1, pp, cs, 4n, {==}), RE.r_inv(one, h1, pp, hP, R, hR, c5, 5n, cs_small_rel(one, h1, pp, cs, 5n, {==})))
  +eb = PC.bytes_rel(one, h1, pp, hP, R, hR, m, FM, rm, PC.red(pp, Nat.mul(4n, FS.finv(P, 5n))))
  %Equal.sym(List<&2, U32>, FE.to_bytes(R, m), SX.le_bytes(32n, FM), eb) : PR.Rp(one, pp, PT.base_of(PT.decode(cs, _)), SE.base(P, D))
  base_of_rel(one, h1, pp, PT.decode(cs, SX.le_bytes(32n, FM)), SE.decode(P, D, SX.le_bytes(32n, FM)), decode_rel(one, h1, pp, hP, cs, hR, D, rd, rs, SX.le_bytes(32n, FM), le_bytes_ok(32n, FM)))

def base_r_eq(+r: Nat, +c: PT.Cs) -> {PT.base_r(r, c) == PT.base_go(c) : PT.Pt}:
  match r:
    case 0n:
      {==}
    case 1n+q:
      {==}

def base_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +hR: {PT.cs_r(cs) == WD.sc(17n, one) : Nat}, +D: Nat, +rd: RE.Rel(one, pp, PT.cs_d(cs), D), +rs: RE.Rel(one, pp, PT.cs_s(cs), SE.sqm1(1n+pp))) -> PR.Rp(one, pp, PT.base(cs), SE.base(1n+pp, D)):
  L.subst(PT.Pt, z => PR.Rp(one, pp, z, SE.base(1n+pp, D)), PT.base_go(cs), PT.base(cs), Equal.sym(PT.Pt, PT.base(cs), PT.base_go(cs), base_r_eq(PT.cs_r(cs), cs)), base_go_rel(one, h1, pp, hP, cs, hR, D, rd, rs))
