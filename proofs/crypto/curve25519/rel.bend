import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../src/crypto/curve25519/field.bend as F
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ./limbs.bend as LM
import ./fieldops.bend as FO
import ./mulw.bend as MW
import ./pow.bend as PW
import ./canon.bend as CN
import ./cong.bend as G

# The representation relation of the curve proofs: R(pp, x, a) is "x is a
# tight element whose value is a mod p". Every field operation maps related
# arguments to a result related to the specification's operation
# (spec/crypto/curve25519/field.bend: fadd, fsub, fmul, finv).

def R(+pp: Nat, +x: List<&2, U32>, +a: Nat) -> Type:
  {LM.okb(32n, x, 255n) == True{} : Bool} & G.ceq(pp, FS.value(x), a)

def r_add(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +y: List<&2, U32>, +a: Nat, +b: Nat, +ox: {LM.okb(32n, x, 255n) == True{} : Bool}, +cx: G.ceq(pp, FS.value(x), a), +oy: {LM.okb(32n, y, 255n) == True{} : Bool}, +cy: G.ceq(pp, FS.value(y), b)) -> R(pp, F.add(x, y), FS.fadd(1n+pp, a, b)):
  +e = G.c_trans(pp, FS.value(F.add(x, y)), Nat.add(FS.value(x), FS.value(y)), FS.fadd(1n+pp, a, b), FO.add_mod(one, h1, pp, hP, x, y, ox, oy), G.c_trans(pp, Nat.add(FS.value(x), FS.value(y)), Nat.add(a, b), FS.fadd(1n+pp, a, b), G.c_add(pp, FS.value(x), a, FS.value(y), b, cx, cy), G.c_sym(pp, Nat.mod(Nat.add(a, b), 1n+pp), Nat.add(a, b), G.c_mod(pp, Nat.add(a, b)))))
  (FO.add_okb(one, h1, x, y, ox, oy), e)

def r_sub(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +y: List<&2, U32>, +a: Nat, +b: Nat, +ox: {LM.okb(32n, x, 255n) == True{} : Bool}, +cx: G.ceq(pp, FS.value(x), a), +oy: {LM.okb(32n, y, 255n) == True{} : Bool}, +cy: G.ceq(pp, FS.value(y), b)) -> R(pp, F.sub(x, y), FS.fsub(1n+pp, a, b)):
  +P = {1n+pp : Nat}
  +mb = Nat.mod(b, P)
  +e1 = FO.sub_mod(one, h1, pp, hP, x, y, ox, oy)
  +e2 = G.c_eq(pp, Nat.sub(Nat.add(FS.value(x), P), Nat.mod(FS.value(y), P)), Nat.sub(Nat.add(FS.value(x), P), mb), Equal.cong(Nat, Nat, z => Nat.sub(Nat.add(FS.value(x), P), z), Nat.mod(FS.value(y), P), mb, cy))
  +e3 = G.c_subm(pp, FS.value(x), a, mb, cx, N.lt_le(mb, P, NR.dm_lt(pp, b)))
  +e4 = G.c_sym(pp, Nat.mod(Nat.sub(Nat.add(a, P), mb), P), Nat.sub(Nat.add(a, P), mb), G.c_mod(pp, Nat.sub(Nat.add(a, P), mb)))
  +e = G.c_trans(pp, FS.value(F.sub(x, y)), Nat.sub(Nat.add(FS.value(x), P), Nat.mod(FS.value(y), P)), FS.fsub(P, a, b), e1, G.c_trans(pp, Nat.sub(Nat.add(FS.value(x), P), Nat.mod(FS.value(y), P)), Nat.sub(Nat.add(FS.value(x), P), mb), FS.fsub(P, a, b), e2, G.c_trans(pp, Nat.sub(Nat.add(FS.value(x), P), mb), Nat.sub(Nat.add(a, P), mb), FS.fsub(P, a, b), e3, e4)))
  (FO.sub_okb(one, h1, x, y, ox, oy), e)

def r_mul(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +y: List<&2, U32>, +a: Nat, +b: Nat, +ox: {LM.okb(32n, x, 255n) == True{} : Bool}, +cx: G.ceq(pp, FS.value(x), a), +oy: {LM.okb(32n, y, 255n) == True{} : Bool}, +cy: G.ceq(pp, FS.value(y), b)) -> R(pp, F.mul(x, y), FS.fmul(1n+pp, a, b)):
  +e = G.c_trans(pp, FS.value(F.mul(x, y)), Nat.mul(FS.value(x), FS.value(y)), FS.fmul(1n+pp, a, b), MW.mul_mod(one, h1, pp, hP, x, y, ox, oy), G.c_trans(pp, Nat.mul(FS.value(x), FS.value(y)), Nat.mul(a, b), FS.fmul(1n+pp, a, b), G.c_mul(pp, FS.value(x), a, FS.value(y), b, cx, cy), G.c_sym(pp, Nat.mod(Nat.mul(a, b), 1n+pp), Nat.mul(a, b), G.c_mod(pp, Nat.mul(a, b)))))
  (MW.mul_okb(one, h1, x, y, ox, oy), e)

def r_sq(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +a: Nat, +ox: {LM.okb(32n, x, 255n) == True{} : Bool}, +cx: G.ceq(pp, FS.value(x), a)) -> R(pp, F.sq(x), FS.fmul(1n+pp, a, a)):
  r_mul(one, h1, pp, hP, x, x, a, a, ox, cx, ox, cx)

def r_inv(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +a: Nat, +ox: {LM.okb(32n, x, 255n) == True{} : Bool}, +cx: G.ceq(pp, FS.value(x), a)) -> R(pp, F.inv(x), FS.finv(1n+pp, a)):
  +P = {1n+pp : Nat}
  +k = Nat.sub(P, 2n)
  +e = G.c_trans(pp, FS.value(F.inv(x)), Nat.pow(FS.value(x), k), FS.finv(P, a), PW.inv_val(one, h1, pp, hP, x, ox), G.c_trans(pp, Nat.pow(FS.value(x), k), Nat.pow(a, k), FS.finv(P, a), G.c_pow(pp, FS.value(x), a, k, cx), G.c_sym(pp, Nat.mod(Nat.pow(a, k), P), Nat.pow(a, k), G.c_mod(pp, Nat.pow(a, k)))))
  (PW.inv_okb(one, h1, x, ox), e)

def r_p58(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +a: Nat, +ox: {LM.okb(32n, x, 255n) == True{} : Bool}, +cx: G.ceq(pp, FS.value(x), a)) -> R(pp, F.pow_p58(x), FS.fpow(1n+pp, a, Nat.div(Nat.sub(1n+pp, 5n), 8n))):
  +P = {1n+pp : Nat}
  +k = Nat.div(Nat.sub(P, 5n), 8n)
  +e = G.c_trans(pp, FS.value(F.pow_p58(x)), Nat.pow(FS.value(x), k), FS.fpow(P, a, k), PW.p58_val(one, h1, pp, hP, x, ox), G.c_trans(pp, Nat.pow(FS.value(x), k), Nat.pow(a, k), FS.fpow(P, a, k), G.c_pow(pp, FS.value(x), a, k, cx), G.c_sym(pp, Nat.mod(Nat.pow(a, k), P), Nat.pow(a, k), G.c_mod(pp, Nat.pow(a, k)))))
  (PW.p58_okb(one, h1, x, ox), e)
