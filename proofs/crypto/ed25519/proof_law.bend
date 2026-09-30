import Base
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/edwards.bend as G
import ../../../spec/crypto/ed25519.bend as SE
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../curve25519/prime.bend as PRM
import ../secp256k1/group/bnx.bend as X
import ./group/pfacts.bend as PF
import ./pbase.bend as PB
import ./fbspec.bend as FB
import ./fblaw.bend as FL
import ./pbvalid.bend as PV

# Gate: the group-law statements the Ed25519 clauses with a context take
# (fbspec.bend LawE, LawQ: the table form of [k] B is the specification's
# [k] B), at the modulus of the Ed25519 proofs (p = 1 + PB.pp1(one)), from
# the curve parameters of edwards25519 (G.Curve: p prime, d not a square,
# a square root of -1; proofs/crypto/ed25519/group/cpar.bend from the
# certificate roots).

# p - 1 as the group-law proofs write it is p - 1 as the Ed25519 proofs do
def mp_eq(+one: Nat, +h1: {one == 1n : Nat}) -> {X.bvalo(one, PF.p1l()) == PB.pp1(one) : Nat}:
  N.succ_inj(X.bvalo(one, PF.p1l()), PB.pp1(one), Equal.trans(Nat, 1n+X.bvalo(one, PF.p1l()), FS.prime(one), 1n+PB.pp1(one), Equal.sym(Nat, FS.prime(one), 1n+X.bvalo(one, PF.p1l()), PF.p_suc(one, h1)), PRM.prime_eq(one, h1)))

# the curve parameters at 1 + PB.pp1(one)
def curve_pp(+one: Nat, +h1: {one == 1n : Nat}, +hc: G.Curve(X.bvalo(one, PF.p1l()), SE.dconst(one, FS.prime(one)))) -> G.Curve(PB.pp1(one), SE.dconst(one, 1n+PB.pp1(one))):
  +h2 = L.subst(Nat, z => G.Curve(z, SE.dconst(one, FS.prime(one))), X.bvalo(one, PF.p1l()), PB.pp1(one), mp_eq(one, h1), hc)
  L.subst(Nat, z => G.Curve(PB.pp1(one), SE.dconst(one, z)), FS.prime(one), 1n+PB.pp1(one), PRM.prime_eq(one, h1), h2)

def law_e(+one: Nat, +h1: {one == 1n : Nat}, +hc: G.Curve(PB.pp1(one), SE.dconst(one, 1n+PB.pp1(one)))) -> FB.LawE(one, PB.pp1(one)):
  FL.lawE(one, h1, PB.pp1(one), hc, PV.base_valid(PB.pp1(one), SE.dconst(one, 1n+PB.pp1(one)), hc))

def law_q(+one: Nat, +h1: {one == 1n : Nat}, +hc: G.Curve(PB.pp1(one), SE.dconst(one, 1n+PB.pp1(one)))) -> FB.LawQ(one, PB.pp1(one)):
  FL.lawQ(one, h1, PB.pp1(one), hc, PV.base_valid(PB.pp1(one), SE.dconst(one, 1n+PB.pp1(one)), hc))
