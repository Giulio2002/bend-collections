import Base
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/u32.bend as U
import ../../math/natural/arith.bend as NR
import ../curve25519/cong.bend as G
import ./ops.bend as OP
import ./sub.bend as SB
import ./pow.bend as PO

# The representation relation of the curve proofs over the fast field:
# R(one, pp, x, a) is "x is ok (limbs below 2^19) and its value is a mod p".
# Every field operation maps related arguments to a result related to the
# specification's operation (spec/crypto/curve25519/field.bend: fadd, fsub,
# fmul, finv, fpow), as proofs/crypto/curve25519/rel.bend does for the
# byte-limb field.

def Rel(+one: Nat, +pp: Nat, +x: FE.Fe, +a: Nat) -> Data:
  Sigma<&2, &2, {FV.ok(one, x) == True{} : Bool}, _ => G.ceq(pp, FV.value(x), a)>

def mk(+one: Nat, +pp: Nat, +x: FE.Fe, +a: Nat, +o: {FV.ok(one, x) == True{} : Bool}, +c: G.ceq(pp, FV.value(x), a)) -> Rel(one, pp, x, a):
  (o, c)

def o(+one: Nat, +pp: Nat, +x: FE.Fe, +a: Nat, +r: Rel(one, pp, x, a)) -> {FV.ok(one, x) == True{} : Bool}:
  match r:
    case (h, c):
      h

def c(+one: Nat, +pp: Nat, +x: FE.Fe, +a: Nat, +r: Rel(one, pp, x, a)) -> G.ceq(pp, FV.value(x), a):
  match r:
    case (h, e):
      e

def r_add(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +y: FE.Fe, +a: Nat, +b: Nat, +rx: Rel(one, pp, x, a), +ry: Rel(one, pp, y, b)) -> Rel(one, pp, FE.add(R, x, y), FS.fadd(1n+pp, a, b)):
  +ox = o(one, pp, x, a, rx)
  +oy = o(one, pp, y, b, ry)
  +e = G.c_trans(pp, FV.value(FE.add(R, x, y)), Nat.add(FV.value(x), FV.value(y)), FS.fadd(1n+pp, a, b), OP.add_c(one, h1, pp, hP, R, hR, x, y), G.c_trans(pp, Nat.add(FV.value(x), FV.value(y)), Nat.add(a, b), FS.fadd(1n+pp, a, b), G.c_add(pp, FV.value(x), a, FV.value(y), b, c(one, pp, x, a, rx), c(one, pp, y, b, ry)), G.c_sym(pp, Nat.mod(Nat.add(a, b), 1n+pp), Nat.add(a, b), G.c_mod(pp, Nat.add(a, b)))))
  (OP.add_ok(one, h1, R, hR, x, y, ox, oy), e)

def r_sub(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +y: FE.Fe, +a: Nat, +b: Nat, +rx: Rel(one, pp, x, a), +ry: Rel(one, pp, y, b)) -> Rel(one, pp, FE.sub(R, x, y), FS.fsub(1n+pp, a, b)):
  +P = {1n+pp : Nat}
  +ox = o(one, pp, x, a, rx)
  +oy = o(one, pp, y, b, ry)
  +cx = c(one, pp, x, a, rx)
  +cy = c(one, pp, y, b, ry)
  +mb = Nat.mod(b, P)
  +e1 = SB.sub_c(one, h1, pp, hP, R, hR, x, y, oy)
  +e2 = G.c_eq(pp, Nat.sub(Nat.add(FV.value(x), P), Nat.mod(FV.value(y), P)), Nat.sub(Nat.add(FV.value(x), P), mb), Equal.cong(Nat, Nat, z => Nat.sub(Nat.add(FV.value(x), P), z), Nat.mod(FV.value(y), P), mb, cy))
  +e3 = G.c_subm(pp, FV.value(x), a, mb, cx, N.lt_le(mb, P, NR.dm_lt(pp, b)))
  +e4 = G.c_sym(pp, Nat.mod(Nat.sub(Nat.add(a, P), mb), P), Nat.sub(Nat.add(a, P), mb), G.c_mod(pp, Nat.sub(Nat.add(a, P), mb)))
  +e = G.c_trans(pp, FV.value(FE.sub(R, x, y)), Nat.sub(Nat.add(FV.value(x), P), Nat.mod(FV.value(y), P)), FS.fsub(P, a, b), e1, G.c_trans(pp, Nat.sub(Nat.add(FV.value(x), P), Nat.mod(FV.value(y), P)), Nat.sub(Nat.add(FV.value(x), P), mb), FS.fsub(P, a, b), e2, G.c_trans(pp, Nat.sub(Nat.add(FV.value(x), P), mb), Nat.sub(Nat.add(a, P), mb), FS.fsub(P, a, b), e3, e4)))
  (SB.sub_ok(one, h1, R, hR, x, y, ox), e)

def r_mul(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +y: FE.Fe, +a: Nat, +b: Nat, +rx: Rel(one, pp, x, a), +ry: Rel(one, pp, y, b)) -> Rel(one, pp, FE.mul(R, x, y), FS.fmul(1n+pp, a, b)):
  +ox = o(one, pp, x, a, rx)
  +oy = o(one, pp, y, b, ry)
  +e = G.c_trans(pp, FV.value(FE.mul(R, x, y)), Nat.mul(FV.value(x), FV.value(y)), FS.fmul(1n+pp, a, b), OP.mul_c(one, h1, pp, hP, R, hR, x, y), G.c_trans(pp, Nat.mul(FV.value(x), FV.value(y)), Nat.mul(a, b), FS.fmul(1n+pp, a, b), G.c_mul(pp, FV.value(x), a, FV.value(y), b, c(one, pp, x, a, rx), c(one, pp, y, b, ry)), G.c_sym(pp, Nat.mod(Nat.mul(a, b), 1n+pp), Nat.mul(a, b), G.c_mod(pp, Nat.mul(a, b)))))
  (OP.mul_ok(one, h1, R, hR, x, y, ox, oy), e)

def r_sq(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +a: Nat, +rx: Rel(one, pp, x, a)) -> Rel(one, pp, FE.sq(R, x), FS.fmul(1n+pp, a, a)):
  r_mul(one, h1, pp, hP, R, hR, x, x, a, a, rx, rx)

# k < 2^17 a constant with value K
def r_mul_small(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +a: Nat, +k: Nat, +hk: {Nat.is_lt(k, WD.sc(17n, one)) == True{} : Bool}, +rx: Rel(one, pp, x, a)) -> Rel(one, pp, FE.mul_small(R, x, k), FS.fmul(1n+pp, a, k)):
  +ox = o(one, pp, x, a, rx)
  +e = G.c_trans(pp, FV.value(FE.mul_small(R, x, k)), Nat.mul(FV.value(x), k), FS.fmul(1n+pp, a, k), OP.mul_small_c(one, h1, pp, hP, R, hR, x, k), G.c_trans(pp, Nat.mul(FV.value(x), k), Nat.mul(a, k), FS.fmul(1n+pp, a, k), G.c_mul(pp, FV.value(x), a, k, k, c(one, pp, x, a, rx), G.c_refl(pp, k)), G.c_sym(pp, Nat.mod(Nat.mul(a, k), 1n+pp), Nat.mul(a, k), G.c_mod(pp, Nat.mul(a, k)))))
  (OP.mul_small_ok(one, h1, R, hR, x, k, ox, hk), e)

def r_inv(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +a: Nat, +rx: Rel(one, pp, x, a)) -> Rel(one, pp, FE.inv(R, x), FS.finv(1n+pp, a)):
  +P = {1n+pp : Nat}
  +k = Nat.sub(P, 2n)
  +ox = o(one, pp, x, a, rx)
  +e = G.c_trans(pp, FV.value(FE.inv(R, x)), Nat.pow(FV.value(x), k), FS.finv(P, a), PO.inv_val(one, h1, pp, hP, R, hR, x, ox), G.c_trans(pp, Nat.pow(FV.value(x), k), Nat.pow(a, k), FS.finv(P, a), G.c_pow(pp, FV.value(x), a, k, c(one, pp, x, a, rx)), G.c_sym(pp, Nat.mod(Nat.pow(a, k), P), Nat.pow(a, k), G.c_mod(pp, Nat.pow(a, k)))))
  (PO.inv_okb(one, h1, R, hR, x, ox), e)

def r_p58(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +a: Nat, +rx: Rel(one, pp, x, a)) -> Rel(one, pp, FE.pow_p58(R, x), FS.fpow(1n+pp, a, Nat.div(Nat.sub(1n+pp, 5n), 8n))):
  +P = {1n+pp : Nat}
  +k = Nat.div(Nat.sub(P, 5n), 8n)
  +ox = o(one, pp, x, a, rx)
  +e = G.c_trans(pp, FV.value(FE.pow_p58(R, x)), Nat.pow(FV.value(x), k), FS.fpow(P, a, k), PO.p58_val(one, h1, pp, hP, R, hR, x, ox), G.c_trans(pp, Nat.pow(FV.value(x), k), Nat.pow(a, k), FS.fpow(P, a, k), G.c_pow(pp, FV.value(x), a, k, c(one, pp, x, a, rx)), G.c_sym(pp, Nat.mod(Nat.pow(a, k), P), Nat.pow(a, k), G.c_mod(pp, Nat.pow(a, k)))))
  (PO.p58_okb(one, h1, R, hR, x, ox), e)

# selection by a bit s (0 or 1)
def sel_z(+s: U32, +hs: {U32.to_nat(s) == 0n : Nat}, +x: FE.Fe, +y: FE.Fe) -> {FE.select(s, x, y) == x : FE.Fe}:
  Equal.trans(FE.Fe, FE.select(s, x, y), FE.select(0, x, y), x, Equal.cong(U32, FE.Fe, z => FE.select(z, x, y), s, 0, U.injective(s, 0, hs)), OP.select0(x, y))

def sel_o(+s: U32, +hs: {U32.to_nat(s) == 1n : Nat}, +x: FE.Fe, +y: FE.Fe) -> {FE.select(s, x, y) == y : FE.Fe}:
  Equal.trans(FE.Fe, FE.select(s, x, y), FE.select(1, x, y), y, Equal.cong(U32, FE.Fe, z => FE.select(z, x, y), s, 1, U.injective(s, 1, hs)), OP.select1(x, y))

# a relation through an element equation
def r_eq(+one: Nat, +pp: Nat, +x: FE.Fe, +y: FE.Fe, +a: Nat, +e: {x == y : FE.Fe}, +r: Rel(one, pp, y, a)) -> Rel(one, pp, x, a):
  L.subst(FE.Fe, z => Rel(one, pp, z, a), y, x, Equal.sym(FE.Fe, x, y, e), r)
