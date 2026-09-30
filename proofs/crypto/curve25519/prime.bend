import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ./num.bend as M

# p = FS.prime(one) = 2^255 - 19 as 1 + pp, the form of the modular lemmas
# (proofs/math/natural/arith.bend), with (1 + pp) + 19 == 2^255.

def pp_of(+one: Nat) -> Nat:
  Nat.sub(C.shift(255n, one), 20n)

def p20(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_le(20n, WD.sc(255n, one)) == True{} : Bool}:
  +a = L.subst(Nat, o => {Nat.is_le(20n, WD.sc(5n, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})
  N.le_trans(20n, WD.sc(5n, one), WD.sc(255n, one), a, M.sc_mono(250n, 5n, one))

# 20 + pp == 2^255
def pp_sum(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.add(20n, pp_of(one)) == WD.sc(255n, one) : Nat}:
  N.sub_add(WD.sc(255n, one), 20n, p20(one, h1))

def hP(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.add(1n+pp_of(one), 19n) == WD.sc(255n, one) : Nat}:
  +pp = pp_of(one)
  +e = Equal.cong(Nat, Nat, t => 1n+t, Nat.add(pp, 19n), Nat.add(19n, pp), NA.add_comm(pp, 19n))
  Equal.trans(Nat, Nat.add(1n+pp, 19n), Nat.add(20n, pp), WD.sc(255n, one), e, pp_sum(one, h1))

def prime_eq(+one: Nat, +h1: {one == 1n : Nat}) -> {FS.prime(one) == 1n+pp_of(one) : Nat}:
  +pp = pp_of(one)
  +e = Equal.cong(Nat, Nat, t => Nat.sub(t, 19n), WD.sc(255n, one), Nat.add(20n, pp), Equal.sym(Nat, Nat.add(20n, pp), WD.sc(255n, one), pp_sum(one, h1)))
  Equal.trans(Nat, Nat.sub(WD.sc(255n, one), 19n), Nat.sub(Nat.add(20n, pp), 19n), 1n+pp, e, N.add_sub_cancel(19n, 1n+pp))
