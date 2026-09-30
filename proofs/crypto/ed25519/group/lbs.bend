import Base
import ../../../../spec/lib/common.bend as C
import ../../../../spec/crypto/curve25519/field.bend as FS
import ../../../../spec/crypto/curve25519/edwards.bend as G
import ../../../../spec/crypto/ed25519.bend as ED
import ../../../../spec/crypto/ed25519_group.bend as GE
import ./lite/lib/nat.bend as N
import ./lite/math/number/nt_prime.bend as PM
import ../../secp256k1/group/bnx.bend as X
import ./lite/crypto/secp256k1/group/fld.bend as F
import ./pfacts.bend as PF
import ./lfacts.bend as LF
import ./cpar.bend as CP
import ./cpar2.bend as CQ
import ./fq.bend as FQ
import ./lbt.bend as LT
import ./vs3.bend as VS3

# GE.BaseOrder ([L] B == (0, 1) for the specification's base point, order
# and d) from the statement of lbz.bend on the literals: the specification's
# base point decode(4 / 5) is the literal point (VS3.base_aff), d is the
# literal d (CP.d_is_s) and L the literal L (LF.l_is).

def nz5_c(+mp: Nat, +hp: PM.Prime(1n+mp), +h2: F.NZ(mp, 2n), +y: Nat, +h45: {FS.fmul(1n+mp, 5n, y) == 4n : Nat}, c: Bool, +hc: {Nat.is_eq(Nat.mod(5n, 1n+mp), 0n) == c : Bool}) -> F.NZ(mp, 5n):
  match c:
    case False{}:
      hc
    case True{}:
      +z4 = Equal.trans(Nat, Nat.mod(4n, 1n+mp), Nat.mod(FS.fmul(1n+mp, 5n, y), 1n+mp), 0n, Equal.cong(Nat, Nat, w => Nat.mod(w, 1n+mp), 4n, FS.fmul(1n+mp, 5n, y), Equal.sym(Nat, FS.fmul(1n+mp, 5n, y), 4n, h45)), F.z_mmul_l(mp, 5n, y, N.eq_from_is_eq(Nat.mod(5n, 1n+mp), 0n, hc)))
      Empty.absurd(F.NZ(mp, 5n), F.nz_absurd(mp, 2n, h2, F.zprod(mp, hp, 2n, 2n, z4, h2)))

# 4 / 5 is the literal y of the base point
def b45(+one: Nat, +h1: {one == 1n : Nat}, +hc: G.Curve(X.bvalo(one, PF.p1l()), X.bvalo(one, PF.dl()))) -> {FS.fmul(1n+X.bvalo(one, PF.p1l()), 4n, FS.finv(1n+X.bvalo(one, PF.p1l()), 5n)) == X.bvalo(one, PF.byl()) : Nat}:
  +mp = X.bvalo(one, PF.p1l())
  +by = X.bvalo(one, PF.byl())
  +hp = FQ.cv_prime(X.bvalo(one, PF.p1l()), X.bvalo(one, PF.dl()), hc)
  FQ.frac_val(mp, hp, 4n, 5n, by, nz5_c(mp, hp, FQ.cv_nz2(X.bvalo(one, PF.p1l()), X.bvalo(one, PF.dl()), hc), by, LT.by_45(one, h1), Nat.is_eq(Nat.mod(5n, 1n+mp), 0n), {==}), LT.by_lt(one, h1),
    Equal.cong(Nat, Nat, w => Nat.mod(w, 1n+mp), 4n, FS.fmul(1n+mp, by, 5n), Equal.sym(Nat, FS.fmul(1n+mp, by, 5n), 4n, Equal.trans(Nat, FS.fmul(1n+mp, by, 5n), FS.fmul(1n+mp, 5n, by), 4n, F.mmul_comm(mp, by, 5n), LT.by_45(one, h1)))))

def lb_spec(+one: Nat, +h1: {one == 1n : Nat}, +hc: G.Curve(X.bvalo(one, PF.p1l()), X.bvalo(one, PF.dl())), +hl: {G.nmul(1n+X.bvalo(one, PF.p1l()), X.bvalo(one, PF.dl()), X.bvalo(one, PF.ll()), G.APt{X.bvalo(one, PF.bxl()), X.bvalo(one, PF.byl())}) == G.azero() : G.APt}) -> GE.BaseOrder(one, FS.prime(one)):
  %Equal.sym(Nat, FS.prime(one), 1n+X.bvalo(one, PF.p1l()), PF.p_suc(one, h1)) : GE.BaseOrder(one, _)
  %Equal.sym(Nat, ED.dconst(one, 1n+X.bvalo(one, PF.p1l())), X.bvalo(one, PF.dl()), CP.d_is_s(one, h1, FQ.cv_prime(X.bvalo(one, PF.p1l()), X.bvalo(one, PF.dl()), hc))) : {G.nmul(1n+X.bvalo(one, PF.p1l()), _, ED.ell(one), GE.affine(1n+X.bvalo(one, PF.p1l()), ED.base(1n+X.bvalo(one, PF.p1l()), _))) == G.azero() : G.APt}
  %LF.l_is(one, h1) : {G.nmul(1n+X.bvalo(one, PF.p1l()), X.bvalo(one, PF.dl()), _, GE.affine(1n+X.bvalo(one, PF.p1l()), ED.base(1n+X.bvalo(one, PF.p1l()), X.bvalo(one, PF.dl())))) == G.azero() : G.APt}
  %Equal.sym(G.APt, GE.affine(1n+X.bvalo(one, PF.p1l()), ED.base(1n+X.bvalo(one, PF.p1l()), X.bvalo(one, PF.dl()))), G.APt{X.bvalo(one, PF.bxl()), X.bvalo(one, PF.byl())}, VS3.base_aff(one, h1, X.bvalo(one, PF.p1l()), X.bvalo(one, PF.dl()), hc, X.bvalo(one, PF.e58l()), CQ.h58(one, h1), CQ.hk(one, h1), CQ.p_le255(one, h1), X.bvalo(one, PF.bxl()), X.bvalo(one, PF.byl()), LT.bx_lt(one, h1), LT.by_lt(one, h1), LT.b_on(one, h1), LT.bx_even(one, h1), b45(one, h1, hc))) : {G.nmul(1n+X.bvalo(one, PF.p1l()), X.bvalo(one, PF.dl()), X.bvalo(one, PF.ll()), _) == G.azero() : G.APt}
  hl
