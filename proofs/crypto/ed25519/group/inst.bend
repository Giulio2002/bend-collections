import Base
import ../../../../spec/lib/common.bend as C
import ../../../../spec/crypto/curve25519/field.bend as FS
import ../../../../spec/crypto/curve25519/edwards.bend as G
import ../../../../spec/crypto/ed25519.bend as ED
import ../../../../spec/crypto/ed25519_group.bend as GE
import ../../../lib/logic.bend as Lg
import ./ext.bend as EX
import ./smul.bend as SM

# The clauses of spec/crypto/ed25519_group.bend: the theorems of ext.bend and
# smul.bend (stated for a modulus 1 + mp) at p = FS.prime(one), transported
# along hm : FS.prime(one) == 1 + mp.

# a valid point at p is a valid point at 1 + mp
def vm(+one: Nat, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}, +d: Nat, +a: ED.EPt, +ha: GE.Valid(FS.prime(one), d, a)) -> GE.Valid(1n+mp, d, a):
  %hm : GE.Valid(_, d, a)
  ha

def add_affine(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}, +hc: G.Curve(mp, ED.dconst(one, FS.prime(one))), +a: ED.EPt, +b: ED.EPt, +ha: GE.Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), a), +hb: GE.Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), b)) -> GE.Ed25519.add_affine(one, h1, mp, hm, hc, a, b, ha, hb):
  +d = ED.dconst(one, FS.prime(one))
  %Equal.sym(Nat, FS.prime(one), 1n+mp, hm) : GE.AddAffine(_, ED.dconst(one, FS.prime(one)), a, b)
  EX.add_aff(mp, d, hc, a, b, vm(one, mp, hm, d, a, ha), vm(one, mp, hm, d, b, hb))

def add_valid(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}, +hc: G.Curve(mp, ED.dconst(one, FS.prime(one))), +a: ED.EPt, +b: ED.EPt, +ha: GE.Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), a), +hb: GE.Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), b)) -> GE.Ed25519.add_valid(one, h1, mp, hm, hc, a, b, ha, hb):
  +d = ED.dconst(one, FS.prime(one))
  %Equal.sym(Nat, FS.prime(one), 1n+mp, hm) : GE.Valid(_, ED.dconst(one, FS.prime(one)), ED.add(_, ED.dconst(one, FS.prime(one)), a, b))
  EX.add_valid(mp, d, hc, a, b, vm(one, mp, hm, d, a, ha), vm(one, mp, hm, d, b, hb))

def double_affine(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}, +hc: G.Curve(mp, ED.dconst(one, FS.prime(one))), +a: ED.EPt, +ha: GE.Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), a)) -> GE.Ed25519.double_affine(one, h1, mp, hm, hc, a, ha):
  +d = ED.dconst(one, FS.prime(one))
  %Equal.sym(Nat, FS.prime(one), 1n+mp, hm) : GE.DoubleAffine(_, ED.dconst(one, FS.prime(one)), a)
  EX.dbl_aff(mp, d, hc, a, vm(one, mp, hm, d, a, ha))

def double_valid(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}, +hc: G.Curve(mp, ED.dconst(one, FS.prime(one))), +a: ED.EPt, +ha: GE.Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), a)) -> GE.Ed25519.double_valid(one, h1, mp, hm, hc, a, ha):
  +d = ED.dconst(one, FS.prime(one))
  %Equal.sym(Nat, FS.prime(one), 1n+mp, hm) : GE.Valid(_, ED.dconst(one, FS.prime(one)), ED.double(_, a))
  EX.dbl_valid(mp, d, hc, a, vm(one, mp, hm, d, a, ha))

def identity(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}, +hc: G.Curve(mp, ED.dconst(one, FS.prime(one)))) -> GE.Ed25519.identity(one, h1, mp, hm, hc):
  %Equal.sym(Nat, FS.prime(one), 1n+mp, hm) : GE.IdentityAffine(_)
  EX.id_aff(mp, ED.dconst(one, FS.prime(one)), hc)

def identity_valid(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}, +hc: G.Curve(mp, ED.dconst(one, FS.prime(one)))) -> GE.Ed25519.identity_valid(one, h1, mp, hm, hc):
  %Equal.sym(Nat, FS.prime(one), 1n+mp, hm) : GE.Valid(_, ED.dconst(one, FS.prime(one)), ED.identity())
  EX.id_valid(mp, ED.dconst(one, FS.prime(one)), hc)

def mul_affine(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}, +hc: G.Curve(mp, ED.dconst(one, FS.prime(one))), +k: Nat, +a: ED.EPt, +ha: GE.Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), a)) -> GE.Ed25519.mul_affine(one, h1, mp, hm, hc, k, a, ha):
  +d = ED.dconst(one, FS.prime(one))
  %Equal.sym(Nat, FS.prime(one), 1n+mp, hm) : GE.MulAffine(one, _, ED.dconst(one, FS.prime(one)), k, a)
  SM.mul_aff(one, mp, d, hc, k, a, vm(one, mp, hm, d, a, ha))

def mul_valid(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}, +hc: G.Curve(mp, ED.dconst(one, FS.prime(one))), +k: Nat, +a: ED.EPt, +ha: GE.Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), a)) -> GE.Ed25519.mul_valid(one, h1, mp, hm, hc, k, a, ha):
  +d = ED.dconst(one, FS.prime(one))
  %Equal.sym(Nat, FS.prime(one), 1n+mp, hm) : GE.Valid(_, ED.dconst(one, FS.prime(one)), ED.mul(one, _, ED.dconst(one, FS.prime(one)), k, a))
  SM.mul_valid(one, mp, d, hc, k, a, vm(one, mp, hm, d, a, ha))

def affine_on(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +hm: {FS.prime(one) == 1n+mp : Nat}, +hc: G.Curve(mp, ED.dconst(one, FS.prime(one))), +a: ED.EPt, +ha: GE.Valid(FS.prime(one), ED.dconst(one, FS.prime(one)), a)) -> GE.Ed25519.affine_on(one, h1, mp, hm, hc, a, ha):
  +d = ED.dconst(one, FS.prime(one))
  %Equal.sym(Nat, FS.prime(one), 1n+mp, hm) : G.OnCurve(_, ED.dconst(one, FS.prime(one)), GE.affine(_, a))
  EX.aff_on(mp, d, a, vm(one, mp, hm, d, a, ha))
