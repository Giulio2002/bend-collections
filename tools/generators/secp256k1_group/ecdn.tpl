import Base
import ../../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../../math/typed/width.bend as WW
import ../semiring.bend as SR
import ../../../lib/logic.bend as Lg
import ../../../lib/nat.bend as N
import ../../../math/natural/arith.bend as NR
import ../../../../spec/crypto/secp256k1/field.bend as FS
import ../../../math/number/nt_prime.bend as PM
import ../../../math/number/nt_fld.bend as FD
import ./zm.bend as Z
import ./fld.bend as F
import ./glaw2.bend as G2
import ./sqrt.bend as SQ
import ./ecd_id.bend as ID

# The scalars of ECDSA modulo a prime n = 1 + nm: with
# s = k^-1 (e + r d) and w = s^-1, e w + (r w) d == k (verification), and
# (-e) r^-1 + (s r^-1) k == d (recovery); with -s they give -k and the
# same d.

def nz_ne0_c(+mp: Nat, +x: Nat, +nz: F.NZ(mp, x), c: Bool, +hc: {Nat.is_eq(x, 0n) == c : Bool}) -> {Nat.is_eq(x, 0n) == False{} : Bool}:
  match c:
    case False{}:
      hc
    case True{}:
      Empty.absurd({Nat.is_eq(x, 0n) == False{} : Bool}, F.nz_absurd(mp, x, nz, Equal.cong(Nat, Nat, z => Nat.mod(z, 1n+mp), x, 0n, N.eq_from_is_eq(x, 0n, hc))))

# a nonzero residue is a nonzero number
def nz_ne0(+mp: Nat, +x: Nat, +nz: F.NZ(mp, x)) -> {Nat.is_eq(x, 0n) == False{} : Bool}:
  nz_ne0_c(mp, x, nz, Nat.is_eq(x, 0n), {==})

# a nonzero number below the modulus is a nonzero residue
def nz_of(+mp: Nat, +x: Nat, +hx: {Nat.is_lt(x, 1n+mp) == True{} : Bool}, +h0: {Nat.is_eq(x, 0n) == False{} : Bool}) -> F.NZ(mp, x):
  %Equal.sym(Nat, Nat.mod(x, 1n+mp), x, SQ.mred(mp, x, hx)) : {Nat.is_eq(_, 0n) == False{} : Bool}
  h0

def neg_nz(+mp: Nat, +y: Nat, +n: F.NZ(mp, y)) -> F.NZ(mp, FS.msub(1n+mp, 0n, y)):
  G2.neg_nz_c(mp, y, n, Nat.is_eq(Nat.mod(FS.msub(1n+mp, 0n, y), 1n+mp), 0n), {==})

def inv_l(NQD, +k: Nat, +nzk: NZN(k)) -> {1n == MN(k, IN(k)) : Nat}:
  Equal.sym(Nat, MN(k, IN(k)), 1n, FD.inv_mod(1n+nm, hq, k, nzk))

def inv_r(NQD, +k: Nat, +nzk: NZN(k)) -> {MN(k, IN(k)) == 1n : Nat}:
  FD.inv_mod(1n+nm, hq, k, nzk)

# a residue equal to k modulo n, k below n: it is k
def red_is(+nm: Nat, +u: Nat, +k: Nat, +hk: LTN(k), +h: {DN(DN(u)) == DN(k) : Nat}) -> {DN(u) == k : Nat}:
  ETR(Nat, DN(u), DN(k), k, ETR(Nat, DN(u), DN(DN(u)), DN(k), ESYM(Nat, DN(DN(u)), DN(u), NR.mod_mod(nm, u)), h), SQ.mred(nm, k, hk))

# verification, s kept: e w + (r w) d == k
def kk_pos(NQD, +e: Nat, +r: Nat, +d: Nat, +k: Nat, +nzk: NZN(k), +hk: LTN(k), +nzs: NZN(SS)) -> {AN(MN(e, IN(SS)), MN(MN(r, IN(SS)), d)) == k : Nat}:
  red_is(nm, Nat.add(MN(e, IN(SS)), MN(MN(r, IN(SS)), d)), k, hk, F.msub_z(nm, AN(MN(e, IN(SS)), MN(MN(r, IN(SS)), d)), k, ID.sv_pos(nm, e, r, d, k, IN(k), IN(SS), 0n, inv_l(NQA, k, nzk), inv_r(NQA, SS, nzs))))

# verification, s replaced by -s: e w + (r w) d == -k
def kk_neg(NQD, +e: Nat, +r: Nat, +d: Nat, +k: Nat, +nzk: NZN(k), +hk: LTN(k), +nzs: NZN(SS)) -> {AN(MN(e, IN(NN(SS))), MN(MN(r, IN(NN(SS))), d)) == NN(k) : Nat}:
  +kk = AN(MN(e, IN(NN(SS))), MN(MN(r, IN(NN(SS))), d))
  Equal.sym(Nat, NN(k), kk, SQ.neg_of(nm, k, kk, NR.dm_lt(nm, Nat.add(MN(e, IN(NN(SS))), MN(MN(r, IN(NN(SS))), d))),
    ETR(Nat, DN(Nat.add(k, kk)), DN(Nat.add(kk, k)), 0n, Equal.cong(Nat, Nat, z => Nat.mod(z, 1n+nm), Nat.add(k, kk), Nat.add(kk, k), NA.add_comm(k, kk)),
      F.z_red(nm, Nat.add(kk, k), ID.sv_neg(nm, e, r, d, k, IN(k), IN(NN(SS)), 0n, inv_l(NQA, k, nzk), inv_r(NQA, NN(SS), neg_nz(nm, SS, nzs)))))))

# recovery: (-e) r^-1 + (s r^-1) k == d
def rec_pos(NQD, +e: Nat, +r: Nat, +d: Nat, +k: Nat, +nzk: NZN(k), +nzr: NZN(r), +hd: LTN(d)) -> {AN(MN(NN(e), IN(r)), MN(MN(SS, IN(r)), k)) == d : Nat}:
  red_is(nm, Nat.add(MN(NN(e), IN(r)), MN(MN(SS, IN(r)), k)), d, hd, F.msub_z(nm, AN(MN(NN(e), IN(r)), MN(MN(SS, IN(r)), k)), d, ID.sr_pos(nm, e, r, d, k, IN(k), 0n, IN(r), inv_l(NQA, k, nzk), inv_r(NQA, r, nzr))))

def rec_neg(NQD, +e: Nat, +r: Nat, +d: Nat, +k: Nat, +nzk: NZN(k), +nzr: NZN(r), +hd: LTN(d)) -> {AN(MN(NN(e), IN(r)), MN(MN(NN(SS), IN(r)), NN(k))) == d : Nat}:
  red_is(nm, Nat.add(MN(NN(e), IN(r)), MN(MN(NN(SS), IN(r)), NN(k))), d, hd, F.msub_z(nm, AN(MN(NN(e), IN(r)), MN(MN(NN(SS), IN(r)), NN(k))), d, ID.sr_neg(nm, e, r, d, k, IN(k), 0n, IN(r), inv_l(NQA, k, nzk), inv_r(NQA, r, nzr))))
