import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/curve25519/limbs.bend as LS
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../curve25519/prime.bend as PR
import ./pw.bend as PW
import ./carry.bend as CA
import ./pass.bend as PS
import ./ops.bend as OP
import ./prod.bend as PD
import ./sqr.bend as SQ
import ./sub.bend as SB
import ./pow.bend as PO
import ./conv.bend as CV

# Gate for the fast field (src/crypto/curve25519/fe.bend):
# `bend proofs/crypto/fe/proof.bend` checks every clause of
# spec/crypto/curve25519/fe.bend, for every input.

def pp1(+one: Nat) -> Nat:
  PR.pp_of(one)

def rad(+n: Nat, +x: Nat) -> {FE.pow2(n, x) == WD.sc(n, x) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      Equal.cong(Nat, Nat, t => Nat.double(t), FE.pow2(m, x), WD.sc(m, x), rad(m, x))

def hR(+one: Nat) -> {FE.radix(one) == WD.sc(17n, one) : Nat}:
  rad(17n, one)

# a statement about p = 1 + pp, restated about FS.prime(one)
def at_p(+one: Nat, +h1: {one == 1n : Nat}, -M: Nat -> Type, pf: M(1n+pp1(one))) -> M(FS.prime(one)):
  L.subst(Nat, M, 1n+pp1(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+pp1(one), PR.prime_eq(one, h1)), pf)

def add_value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}, +hb: {FV.ok(one, b) == True{} : Bool}) -> FV.Add.value(one, h1, a, b, ha, hb):
  at_p(one, h1, z => {Nat.mod(FV.value(FE.add(FE.radix(one), a, b)), z) == FS.fadd(z, FV.value(a), FV.value(b)) : Nat}, OP.add_c(one, h1, pp1(one), PR.hP(one, h1), FE.radix(one), hR(one), a, b))

def add_ok(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}, +hb: {FV.ok(one, b) == True{} : Bool}) -> FV.Add.ok(one, h1, a, b, ha, hb):
  OP.add_ok(one, h1, FE.radix(one), hR(one), a, b, ha, hb)

def sub_value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}, +hb: {FV.ok(one, b) == True{} : Bool}) -> FV.Sub.value(one, h1, a, b, ha, hb):
  at_p(one, h1, z => {Nat.mod(FV.value(FE.sub(FE.radix(one), a, b)), z) == FS.fsub(z, FV.value(a), FV.value(b)) : Nat}, SB.sub_c(one, h1, pp1(one), PR.hP(one, h1), FE.radix(one), hR(one), a, b, hb))

def sub_ok(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}, +hb: {FV.ok(one, b) == True{} : Bool}) -> FV.Sub.ok(one, h1, a, b, ha, hb):
  SB.sub_ok(one, h1, FE.radix(one), hR(one), a, b, ha)

def mul_value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}, +hb: {FV.ok(one, b) == True{} : Bool}) -> FV.Mul.value(one, h1, a, b, ha, hb):
  at_p(one, h1, z => {Nat.mod(FV.value(FE.mul(FE.radix(one), a, b)), z) == FS.fmul(z, FV.value(a), FV.value(b)) : Nat}, OP.mul_c(one, h1, pp1(one), PR.hP(one, h1), FE.radix(one), hR(one), a, b, ha, hb))

def mul_ok(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}, +hb: {FV.ok(one, b) == True{} : Bool}) -> FV.Mul.ok(one, h1, a, b, ha, hb):
  OP.mul_ok(one, h1, FE.radix(one), hR(one), a, b, ha, hb)

def mul_fits(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}, +hb: {FV.ok(one, b) == True{} : Bool}) -> FV.Mul.fits(one, h1, a, b, ha, hb):
  +A = FE.to_list(a)
  +B = FE.to_list(b)
  L.subst(List<&2, Nat>, z => {FV.below(LS.fold(z), WD.sc(47n, one)) == True{} : Bool}, LS.conv(A, B), LS.convp(A, B), Equal.sym(List<&2, Nat>, LS.convp(A, B), LS.conv(A, B), PD.convp_eq(one, h1, A, B, ha, hb)), OP.cols_below(one, h1, a, b, ha, hb))

def sq_value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> FV.Sq.value(one, h1, a, ha):
  at_p(one, h1, z => {Nat.mod(FV.value(FE.sq(FE.radix(one), a)), z) == FS.fmul(z, FV.value(a), FV.value(a)) : Nat}, OP.sq_c(one, h1, pp1(one), PR.hP(one, h1), FE.radix(one), hR(one), a, ha))

def sq_ok(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> FV.Sq.ok(one, h1, a, ha):
  OP.sq_ok(one, h1, FE.radix(one), hR(one), a, ha)

def sq_fits(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> FV.Sq.fits(one, h1, a, ha):
  +A = FE.to_list(a)
  L.subst(List<&2, Nat>, z => {FV.below(LS.fold(z), WD.sc(47n, one)) == True{} : Bool}, LS.conv(A, A), LS.sqp(A), Equal.sym(List<&2, Nat>, LS.sqp(A), LS.conv(A, A), SQ.sqp_conv(one, h1, A, ha)), OP.cols_below(one, h1, a, a, ha, ha))

def mul_small_value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +k: Nat, +ha: {FV.ok(one, a) == True{} : Bool}, +hk: {Nat.is_lt(k, C.shift(17n, one)) == True{} : Bool}) -> FV.MulSmall.value(one, h1, a, k, ha, hk):
  at_p(one, h1, z => {Nat.mod(FV.value(FE.mul_small(FE.radix(one), a, k)), z) == FS.fmul(z, FV.value(a), k) : Nat}, OP.mul_small_c(one, h1, pp1(one), PR.hP(one, h1), FE.radix(one), hR(one), a, k))

def mul_small_ok(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +k: Nat, +ha: {FV.ok(one, a) == True{} : Bool}, +hk: {Nat.is_lt(k, C.shift(17n, one)) == True{} : Bool}) -> FV.MulSmall.ok(one, h1, a, k, ha, hk):
  OP.mul_small_ok(one, h1, FE.radix(one), hR(one), a, k, ha, hk)

def select_zero(+a: FE.Fe, +b: FE.Fe) -> FV.Select.zero(a, b):
  OP.select0(a, b)

def select_one(+a: FE.Fe, +b: FE.Fe) -> FV.Select.one(a, b):
  OP.select1(a, b)

def inv_value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> FV.Inv.value(one, h1, a, ha):
  at_p(one, h1, z => {Nat.mod(FV.value(FE.inv(FE.radix(one), a)), z) == FS.finv(z, FV.value(a)) : Nat}, PO.inv_val(one, h1, pp1(one), PR.hP(one, h1), FE.radix(one), hR(one), a, ha))

def inv_ok(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> FV.Inv.ok(one, h1, a, ha):
  PO.inv_okb(one, h1, FE.radix(one), hR(one), a, ha)

def p58_value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> FV.PowP58.value(one, h1, a, ha):
  at_p(one, h1, z => {Nat.mod(FV.value(FE.pow_p58(FE.radix(one), a)), z) == FS.fpow(z, FV.value(a), Nat.div(Nat.sub(z, 5n), 8n)) : Nat}, PO.p58_val(one, h1, pp1(one), PR.hP(one, h1), FE.radix(one), hR(one), a, ha))

def p58_ok(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> FV.PowP58.ok(one, h1, a, ha):
  PO.p58_okb(one, h1, FE.radix(one), hR(one), a, ha)

def freeze_value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> FV.Freeze.value(one, h1, a, ha):
  at_p(one, h1, z => {FV.value(FE.freeze(FE.radix(one), a)) == Nat.mod(FV.value(a), z) : Nat}, CV.freeze_value(one, h1, pp1(one), PR.hP(one, h1), FE.radix(one), hR(one), a, ha))

def freeze_canon(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> FV.Freeze.canon(one, h1, a, ha):
  at_p(one, h1, z => {Bool.and(FV.below(FE.to_list(FE.freeze(FE.radix(one), a)), WD.sc(17n, one)), Nat.is_lt(FV.value(FE.freeze(FE.radix(one), a)), z)) == True{} : Bool}, CV.freeze_canon(one, h1, pp1(one), PR.hP(one, h1), FE.radix(one), hR(one), a, ha))

def to_bytes_value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> FV.ToBytes.value(one, h1, a, ha):
  at_p(one, h1, z => {FS.value(FE.to_bytes(FE.radix(one), a)) == Nat.mod(FV.value(a), z) : Nat}, CV.to_bytes_value(one, h1, pp1(one), PR.hP(one, h1), FE.radix(one), hR(one), a, ha))

def to_bytes_tight(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> FV.ToBytes.tight(one, h1, a, ha):
  CV.to_bytes_tight(one, h1, FE.radix(one), a)

def of_bytes_value(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +hb: {FS.tight(bs) == True{} : Bool}) -> FV.OfBytes.value(one, h1, bs, hb):
  CV.of_bytes_value(one, h1, bs, hb)

def of_bytes_ok(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +hb: {FS.tight(bs) == True{} : Bool}) -> FV.OfBytes.ok(one, h1, bs, hb):
  CV.of_bytes_ok(one, h1, bs)

def eq_value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}, +hb: {FV.ok(one, b) == True{} : Bool}) -> FV.Eq.value(one, h1, a, b, ha, hb):
  at_p(one, h1, z => {FE.eq(FE.radix(one), a, b) == Nat.is_eq(Nat.mod(FV.value(a), z), Nat.mod(FV.value(b), z)) : Bool}, CV.eq_val(one, h1, pp1(one), PR.hP(one, h1), FE.radix(one), hR(one), a, b, ha, hb))

def is_zero_value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> FV.IsZero.value(one, h1, a, ha):
  at_p(one, h1, z => {FE.is_zero(FE.radix(one), a) == Nat.is_eq(Nat.mod(FV.value(a), z), 0n) : Bool}, CV.is_zero_val(one, h1, pp1(one), PR.hP(one, h1), FE.radix(one), hR(one), a, ha))

def parity_value(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> FV.Parity.value(one, h1, a, ha):
  at_p(one, h1, z => {U32.to_nat(FE.parity(FE.radix(one), a)) == Nat.mod(Nat.mod(FV.value(a), z), 2n) : Nat}, CV.parity_val(one, h1, pp1(one), PR.hP(one, h1), FE.radix(one), hR(one), a, ha))

def carry_fits(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, Nat>, +hx: {FV.below(xs, C.shift(47n, one)) == True{} : Bool}) -> FV.Carry.fits(one, h1, xs, hx):
  +R = FE.radix(one)
  +h = CA.sums_below(one, h1, R, hR(one), xs, 0n, WD.sc(47n, one), WD.sc(31n, one), hx, PW.sc_pos(31n, one, h1), PS.f_chain(one, h1, R, hR(one)))
  L.subst(Nat, z => {FV.below(FV.sums(R, xs, 0n), z) == True{} : Bool}, Nat.mul(R, WD.sc(31n, one)), WD.sc(48n, one), PS.f_re(one, h1, R, hR(one)), h)
