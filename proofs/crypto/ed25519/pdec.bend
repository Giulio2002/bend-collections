import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/x25519.bend as SX
import ../../../spec/crypto/ed25519.bend as SE
import ../../../src/crypto/curve25519/field.bend as F
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../../src/crypto/ed25519/point.bend as PT
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/u32.bend as U
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../curve25519/limbs.bend as LM
import ../curve25519/consts.bend as K
import ../curve25519/fieldops.bend as FO
import ../curve25519/freeze.bend as FZ
import ../curve25519/cong.bend as G
import ../curve25519/rel.bend as RL
import ../curve25519/xbits.bend as XB
import ../curve25519/ladder.bend as LD
import ./scalar.bend as SC
import ./prel.bend as PR
import ./pcodec.bend as PC
import ../curve25519/num.bend as M3

# Decoding (RFC 8032 5.1.3) of src/crypto/ed25519/point.bend against
# spec/crypto/ed25519.bend: for every 32-byte string both reject, or both
# accept with related points; and the base point.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# y >= p exactly when the carry of y + 2^256 - p is not 0
def hv_p(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}) -> {Nat.add(K.valo(one, F.comp_p()), 1n+pp) == SC.T(one) : Nat}:
  +P = {1n+pp : Nat}
  +e1 = M3.cong_l(K.valo(one, F.comp_p()), Nat.add(P, 38n), P, FZ.comp_p_val(one, h1, pp, hP))
  +e2 = Equal.trans(Nat, Nat.add(Nat.add(P, 38n), P), Nat.add(P, Nat.add(38n, P)), Nat.add(Nat.add(P, P), 38n), NA.add_assoc(P, 38n, P), Equal.trans(Nat, Nat.add(P, Nat.add(38n, P)), Nat.add(P, Nat.add(P, 38n)), Nat.add(Nat.add(P, P), 38n), M3.cong_r(P, Nat.add(38n, P), Nat.add(P, 38n), NA.add_comm(38n, P)), Equal.sym(Nat, Nat.add(Nat.add(P, P), 38n), Nat.add(P, Nat.add(P, 38n)), NA.add_assoc(P, P, 38n))))
  Equal.trans(Nat, Nat.add(K.valo(one, F.comp_p()), P), Nat.add(Nat.add(P, 38n), P), SC.T(one), e1, Equal.trans(Nat, Nat.add(Nat.add(P, 38n), P), Nat.add(Nat.add(P, P), 38n), SC.T(one), e2, Equal.sym(Nat, SC.T(one), Nat.add(Nat.add(P, P), 38n), FZ.t_val(one, h1, pp, hP))))

def ge_p_eq(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +y: List<&2, U32>, +hy: {LM.okb(32n, y, 255n) == True{} : Bool}) -> {PT.ge_p(y) == Bool.not(Nat.is_lt(FS.value(y), 1n+pp)) : Bool}:
  Equal.cong(Bool, Bool, z => Bool.not(z), U32.is_eq(LM.cc(F.carry(F.addl(y, F.comp_p()), 0)), 0), Nat.is_lt(FS.value(y), 1n+pp), SC.lt_by(one, h1, pp, y, F.comp_p(), hy, {==}, hv_p(one, h1, pp, hP), Nat.is_lt(v(LM.cc(F.carry(F.addl(y, F.comp_p()), 0))), one), {==}))

# ---- the end of decoding: the sign of x ----

def dec_fin_rel_core(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +a: Nat, +rx: RL.R(pp, x, a), +ha: {Nat.mod(a, 1n+pp) == a : Nat}, +y: List<&2, U32>, +b: Nat, +ry: RL.R(pp, y, b), +x0: U32, +b0: Nat, +hx0: {v(x0) == b0 : Nat}, +hb0: {Nat.is_le(b0, 1n) == True{} : Bool}, +fs: Bool, +hf: {Bool.and(F.is_zero(x), U32.is_eq(x0, 1)) == fs : Bool}) -> PC.MR(pp, PT.dec_fin(x, y, x0, fs), SE.dec_fin(1n+pp, a, b, b0, fs)):
  match fs:
    case True{}:
      {==}
    case False{}:
      +P = {1n+pp : Nat}
      +s = U32.xor(F.parity(x), x0)
      +S = SX.bxor(Nat.mod(a, 2n), b0)
      +hs = XB.xor_bits(F.parity(x), x0, Nat.mod(a, 2n), b0, PC.par_rel(one, h1, pp, hP, x, a, rx, ha), hx0, PC.mod2_le(a), hb0)
      +hsb = XB.bxor_le(Nat.mod(a, 2n), b0, hb0)
      +nx = F.neg(x)
      +NX = FS.fsub(P, 0n, a)
      +rn = PR.rsub(one, h1, pp, hP, F.zero(), x, 0n, a, PC.r_zero(pp), rx)
      +ox = RL.r_o(pp, x, a, rx)
      +on = RL.r_o(pp, nx, NX, rn)
      +x2 = F.select(s, x, nx)
      +X2 = SX.cs_fst(S, a, NX)
      +r2 = RL.mkR(pp, x2, X2, LD.o_sel(one, h1, s, S, hs, hsb, x, nx, ox, on), LD.c_fst(one, h1, pp, s, S, hs, hsb, x, nx, a, NX, ox, RL.r_c(pp, x, a, rx), on, RL.r_c(pp, nx, NX, rn)))
      PR.mk(pp, x2, y, F.one(), F.mul(x2, y), X2, b, 1n, FS.fmul(P, X2, b), r2, ry, PC.r_one(pp), PR.rmul(one, h1, pp, hP, x2, y, X2, b, r2, ry))

def dec_fin_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +a: Nat, +rx: RL.R(pp, x, a), +ha: {Nat.mod(a, 1n+pp) == a : Nat}, +y: List<&2, U32>, +b: Nat, +ry: RL.R(pp, y, b), +x0: U32, +b0: Nat, +hx0: {v(x0) == b0 : Nat}, +hb0: {Nat.is_le(b0, 1n) == True{} : Bool}, +fs: Bool, +hf: {Bool.and(F.is_zero(x), U32.is_eq(x0, 1)) == fs : Bool}) -> PC.MR(pp, PT.dec_fin(x, y, x0, Bool.and(F.is_zero(x), U32.is_eq(x0, 1))), SE.dec_fin(1n+pp, a, b, b0, fs)):
  %Equal.sym(Bool, Bool.and(F.is_zero(x), U32.is_eq(x0, 1)), fs, hf) : PC.MR(pp, PT.dec_fin(x, y, x0, _), SE.dec_fin(1n+pp, a, b, b0, fs))
  dec_fin_rel_core(one, h1, pp, hP, x, a, rx, ha, y, b, ry, x0, b0, hx0, hb0, fs, hf)

def fail_eq(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +a: Nat, +rx: RL.R(pp, x, a), +ha: {Nat.mod(a, 1n+pp) == a : Nat}, +x0: U32, +b0: Nat, +hx0: {v(x0) == b0 : Nat}) -> {Bool.and(F.is_zero(x), U32.is_eq(x0, 1)) == Bool.and(Nat.is_eq(a, 0n), Nat.is_eq(b0, 1n)) : Bool}:
  +e1 = PC.iz_rel(one, h1, pp, hP, x, a, rx, ha)
  +e2 = Equal.trans(Bool, U32.is_eq(x0, 1), Nat.is_eq(v(x0), 1n), Nat.is_eq(b0, 1n), PC.u32_eq_nat(x0, 1), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 1n), v(x0), b0, hx0))
  Equal.trans(Bool, Bool.and(F.is_zero(x), U32.is_eq(x0, 1)), Bool.and(Nat.is_eq(a, 0n), U32.is_eq(x0, 1)), Bool.and(Nat.is_eq(a, 0n), Nat.is_eq(b0, 1n)), Equal.cong(Bool, Bool, z => Bool.and(z, U32.is_eq(x0, 1)), F.is_zero(x), Nat.is_eq(a, 0n), e1), Equal.cong(Bool, Bool, z => Bool.and(Nat.is_eq(a, 0n), z), U32.is_eq(x0, 1), Nat.is_eq(b0, 1n), e2))

# ---- the root choice ----

def dec_root_rel_core(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +rs: RL.R(pp, PT.cs_s(cs), SE.sqm1(1n+pp)), +x: List<&2, U32>, +a: Nat, +rx: RL.R(pp, x, a), +ha: {Nat.mod(a, 1n+pp) == a : Nat}, +y: List<&2, U32>, +b: Nat, +ry: RL.R(pp, y, b), +x0: U32, +b0: Nat, +hx0: {v(x0) == b0 : Nat}, +hb0: {Nat.is_le(b0, 1n) == True{} : Bool}, +u: List<&2, U32>, +vxx: List<&2, U32>, +iu: Bool, +inu: Bool, +su: Bool, +snu: Bool, +hu: {iu == su : Bool}, +hnu: {inu == snu : Bool}) -> PC.MR(pp, PT.dec_root(cs, x, y, x0, u, vxx, su, snu), SE.dec_root(1n+pp, a, b, b0, su, snu)):
  match su snu:
    case True{} _:
      dec_fin_rel(one, h1, pp, hP, x, a, rx, ha, y, b, ry, x0, b0, hx0, hb0, Bool.and(Nat.is_eq(a, 0n), Nat.is_eq(b0, 1n)), fail_eq(one, h1, pp, hP, x, a, rx, ha, x0, b0, hx0))
    case False{} True{}:
      +P = {1n+pp : Nat}
      +x1 = F.mul(x, PT.cs_s(cs))
      +X1 = FS.fmul(P, a, SE.sqm1(P))
      +r1 = PR.rmul(one, h1, pp, hP, x, PT.cs_s(cs), a, SE.sqm1(P), rx, rs)
      +h1r = PC.red(pp, Nat.mul(a, SE.sqm1(P)))
      dec_fin_rel(one, h1, pp, hP, x1, X1, r1, h1r, y, b, ry, x0, b0, hx0, hb0, Bool.and(Nat.is_eq(X1, 0n), Nat.is_eq(b0, 1n)), fail_eq(one, h1, pp, hP, x1, X1, r1, h1r, x0, b0, hx0))
    case False{} False{}:
      {==}

# ---- after the y check ----

def dec_root_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +rs: RL.R(pp, PT.cs_s(cs), SE.sqm1(1n+pp)), +x: List<&2, U32>, +a: Nat, +rx: RL.R(pp, x, a), +ha: {Nat.mod(a, 1n+pp) == a : Nat}, +y: List<&2, U32>, +b: Nat, +ry: RL.R(pp, y, b), +x0: U32, +b0: Nat, +hx0: {v(x0) == b0 : Nat}, +hb0: {Nat.is_le(b0, 1n) == True{} : Bool}, +u: List<&2, U32>, +vxx: List<&2, U32>, +iu: Bool, +inu: Bool, +su: Bool, +snu: Bool, +hu: {iu == su : Bool}, +hnu: {inu == snu : Bool}) -> PC.MR(pp, PT.dec_root(cs, x, y, x0, u, vxx, iu, inu), SE.dec_root(1n+pp, a, b, b0, su, snu)):
  %Equal.sym(Bool, iu, su, hu) : PC.MR(pp, PT.dec_root(cs, x, y, x0, u, vxx, _, inu), SE.dec_root(1n+pp, a, b, b0, su, snu))
  %Equal.sym(Bool, inu, snu, hnu) : PC.MR(pp, PT.dec_root(cs, x, y, x0, u, vxx, su, _), SE.dec_root(1n+pp, a, b, b0, su, snu))
  dec_root_rel_core(one, h1, pp, hP, cs, rs, x, a, rx, ha, y, b, ry, x0, b0, hx0, hb0, u, vxx, iu, inu, su, snu, hu, hnu)

def nf(+b: Bool, +h: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, L.true_false(h))

def dec_y_rel_core(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +D: Nat, +rd: RL.R(pp, PT.cs_d(cs), D), +rs: RL.R(pp, PT.cs_s(cs), SE.sqm1(1n+pp)), +y: List<&2, U32>, +Y: Nat, +hyv: {FS.value(y) == Y : Nat}, +hy: {LM.okb(32n, y, 255n) == True{} : Bool}, +x0: U32, +b0: Nat, +hx0: {v(x0) == b0 : Nat}, +hb0: {Nat.is_le(b0, 1n) == True{} : Bool}, +bad: Bool, +hbad: {PT.ge_p(y) == bad : Bool}, +hlt: {Bool.not(Nat.is_lt(Y, 1n+pp)) == bad : Bool}) -> PC.MR(pp, PT.dec_y(cs, y, x0, bad), SE.dec_y(1n+pp, D, Y, b0, bad)):
  match bad:
    case True{}:
      {==}
    case False{}:
      +P = {1n+pp : Nat}
      +lt = nf(Nat.is_lt(Y, P), hlt)
      +ry = RL.mkR(pp, y, Y, hy, G.c_eq(pp, FS.value(y), Y, hyv))
      +hYr = NR.mod_of(0n, pp, Y, lt)
      +yy = F.sq(y)
      +YY = FS.fmul(P, Y, Y)
      +ryy = PR.rsq(one, h1, pp, hP, y, Y, ry)
      +u = F.sub(yy, F.one())
      +UU = FS.fsub(P, YY, 1n)
      +ru = PR.rsub(one, h1, pp, hP, yy, F.one(), YY, 1n, ryy, PC.r_one(pp))
      +vv = F.add(F.mul(PT.cs_d(cs), yy), F.one())
      +VV = FS.fadd(P, FS.fmul(P, D, YY), 1n)
      +rv = PR.radd(one, h1, pp, hP, F.mul(PT.cs_d(cs), yy), F.one(), FS.fmul(P, D, YY), 1n, PR.rmul(one, h1, pp, hP, PT.cs_d(cs), yy, D, YY, rd, ryy), PC.r_one(pp))
      +v3 = F.mul(F.sq(vv), vv)
      +V3 = FS.fmul(P, FS.fmul(P, VV, VV), VV)
      +rv3 = PR.rmul(one, h1, pp, hP, F.sq(vv), vv, FS.fmul(P, VV, VV), VV, PR.rsq(one, h1, pp, hP, vv, VV, rv), rv)
      +v7 = F.mul(F.sq(v3), vv)
      +V7 = FS.fmul(P, FS.fmul(P, V3, V3), VV)
      +rv7 = PR.rmul(one, h1, pp, hP, F.sq(v3), vv, FS.fmul(P, V3, V3), VV, PR.rsq(one, h1, pp, hP, v3, V3, rv3), rv)
      +uv7 = F.mul(u, v7)
      +UV7 = FS.fmul(P, UU, V7)
      +ruv7 = PR.rmul(one, h1, pp, hP, u, v7, UU, V7, ru, rv7)
      +pw = F.pow_p58(uv7)
      +PWV = FS.fpow(P, UV7, Nat.div(Nat.sub(P, 5n), 8n))
      +rpw = RL.r_p58(one, h1, pp, hP, uv7, UV7, RL.r_o(pp, uv7, UV7, ruv7), RL.r_c(pp, uv7, UV7, ruv7))
      +x = F.mul(F.mul(u, v3), pw)
      +XX = FS.fmul(P, FS.fmul(P, UU, V3), PWV)
      +rx = PR.rmul(one, h1, pp, hP, F.mul(u, v3), pw, FS.fmul(P, UU, V3), PWV, PR.rmul(one, h1, pp, hP, u, v3, UU, V3, ru, rv3), rpw)
      +vxx = F.mul(vv, F.sq(x))
      +VXX = FS.fmul(P, VV, FS.fmul(P, XX, XX))
      +rvxx = PR.rmul(one, h1, pp, hP, vv, F.sq(x), VV, FS.fmul(P, XX, XX), rv, PR.rsq(one, h1, pp, hP, x, XX, rx))
      +NU = FS.fsub(P, 0n, UU)
      +rnu = PR.rsub(one, h1, pp, hP, F.zero(), u, 0n, UU, PC.r_zero(pp), ru)
      +eu = PC.eq_rel(one, h1, pp, hP, vxx, u, VXX, UU, rvxx, ru, PC.red(pp, Nat.mul(VV, FS.fmul(P, XX, XX))), PC.red(pp, Nat.sub(Nat.add(YY, P), Nat.mod(1n, P))))
      +enu = PC.eq_rel(one, h1, pp, hP, vxx, F.neg(u), VXX, NU, rvxx, rnu, PC.red(pp, Nat.mul(VV, FS.fmul(P, XX, XX))), PC.red(pp, Nat.sub(Nat.add(0n, P), Nat.mod(UU, P))))
      dec_root_rel(one, h1, pp, hP, cs, rs, x, XX, rx, PC.red(pp, Nat.mul(FS.fmul(P, UU, V3), PWV)), y, Y, ry, x0, b0, hx0, hb0, u, vxx, F.eq(vxx, u), F.eq(vxx, F.neg(u)), Nat.is_eq(VXX, UU), Nat.is_eq(VXX, NU), eu, enu)

def dec_y_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +D: Nat, +rd: RL.R(pp, PT.cs_d(cs), D), +rs: RL.R(pp, PT.cs_s(cs), SE.sqm1(1n+pp)), +y: List<&2, U32>, +Y: Nat, +hyv: {FS.value(y) == Y : Nat}, +hy: {LM.okb(32n, y, 255n) == True{} : Bool}, +x0: U32, +b0: Nat, +hx0: {v(x0) == b0 : Nat}, +hb0: {Nat.is_le(b0, 1n) == True{} : Bool}, +bad: Bool, +hbad: {PT.ge_p(y) == bad : Bool}, +hlt: {Bool.not(Nat.is_lt(Y, 1n+pp)) == bad : Bool}) -> PC.MR(pp, PT.dec_y(cs, y, x0, PT.ge_p(y)), SE.dec_y(1n+pp, D, Y, b0, bad)):
  %Equal.sym(Bool, PT.ge_p(y), bad, hbad) : PC.MR(pp, PT.dec_y(cs, y, x0, _), SE.dec_y(1n+pp, D, Y, b0, bad))
  dec_y_rel_core(one, h1, pp, hP, cs, D, rd, rs, y, Y, hyv, hy, x0, b0, hx0, hb0, bad, hbad, hlt)

def decode_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +D: Nat, +rd: RL.R(pp, PT.cs_d(cs), D), +rs: RL.R(pp, PT.cs_s(cs), SE.sqm1(1n+pp)), +bs: List<&2, U32>, +hb: {LM.okb(32n, bs, 255n) == True{} : Bool}) -> PC.MR(pp, PT.decode(cs, bs), SE.decode(1n+pp, D, bs)):
  +y = F.mask_top(bs)
  +Y = FS.value(SX.mask_last(bs))
  +hyv = Equal.cong(List<&2, U32>, Nat, z => FS.value(z), F.mask_top(bs), SX.mask_last(bs), XB.mask_eq(bs))
  +hy = XB.mask_okb(31n, bs, hb)
  +hl = LM.okb_lea(32n, bs, 255n, hb)
  +hbad = Equal.trans(Bool, PT.ge_p(y), Bool.not(Nat.is_lt(FS.value(y), 1n+pp)), Bool.not(Nat.is_lt(Y, 1n+pp)), ge_p_eq(one, h1, pp, hP, y, hy), Equal.cong(Nat, Bool, z => Bool.not(Nat.is_lt(z, 1n+pp)), FS.value(y), Y, hyv))
  dec_y_rel(one, h1, pp, hP, cs, D, rd, rs, y, Y, hyv, hy, X.kbit(bs, 255n), SX.kbit(FS.value(bs), 255n), XB.kbit_val(bs, 255n, hl), XB.kbit_le(bs, 255n, hl), Bool.not(Nat.is_lt(Y, 1n+pp)), hbad, {==})

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

def identity_rel(+pp: Nat) -> PR.Rp(pp, PT.identity(), SE.identity()):
  PR.mk(pp, F.zero(), F.one(), F.one(), F.zero(), 0n, 1n, 1n, 0n, PC.r_zero(pp), PC.r_one(pp), PC.r_one(pp), PC.r_zero(pp))

def base_of_rel(+pp: Nat, +m: Maybe<&2, PT.Pt>, +sm: Maybe<&2, SE.EPt>, +h: PC.MR(pp, m, sm)) -> PR.Rp(pp, PT.base_of(m), SE.base_of(sm)):
  match m sm:
    case None{} None{}:
      identity_rel(pp)
    case Some{+p} Some{+sp}:
      h
    case None{} Some{sp}:
      Empty.absurd(PR.Rp(pp, PT.identity(), sp), L.true_false(h))
    case Some{p} None{}:
      Empty.absurd(PR.Rp(pp, p, SE.identity()), L.true_false(h))

def base_rel(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +cs: PT.Cs, +D: Nat, +rd: RL.R(pp, PT.cs_d(cs), D), +rs: RL.R(pp, PT.cs_s(cs), SE.sqm1(1n+pp)), +xs: List<&2, U32>) -> PR.Rp(pp, PT.base(cs, xs), SE.base(1n+pp, D)):
  +P = {1n+pp : Nat}
  +m = F.mul(PT.lit(xs, F.small(4)), F.inv(PT.lit(xs, F.small(5))))
  +FM = FS.fmul(P, 4n, FS.finv(P, 5n))
  +r5 = PC.r_lit_small(pp, xs, 5, {==})
  +rm = PR.rmul(one, h1, pp, hP, PT.lit(xs, F.small(4)), F.inv(PT.lit(xs, F.small(5))), 4n, FS.finv(P, 5n), PC.r_lit_small(pp, xs, 4, {==}), RL.r_inv(one, h1, pp, hP, PT.lit(xs, F.small(5)), 5n, RL.r_o(pp, PT.lit(xs, F.small(5)), 5n, r5), RL.r_c(pp, PT.lit(xs, F.small(5)), 5n, r5)))
  +eb = PC.bytes_rel(one, h1, pp, hP, m, FM, rm, PC.red(pp, Nat.mul(4n, FS.finv(P, 5n))))
  %Equal.sym(List<&2, U32>, F.to_bytes(m), SX.le_bytes(32n, FM), eb) : PR.Rp(pp, PT.base_of(PT.decode(cs, _)), SE.base(P, D))
  base_of_rel(pp, PT.decode(cs, SX.le_bytes(32n, FM)), SE.decode(P, D, SX.le_bytes(32n, FM)), decode_rel(one, h1, pp, hP, cs, D, rd, rs, SX.le_bytes(32n, FM), le_bytes_ok(32n, FM)))
