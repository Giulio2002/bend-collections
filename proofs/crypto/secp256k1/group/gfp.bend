import Base
import ../../../lib/nat.bend as N
import ../../../lib/logic.bend as Lg
import ../../../../spec/crypto/secp256k1/field.bend as FS
import ../../../math/number/nt_prime.bend as PM
import ./bnx.bend as X
import ./certb.bend as CB

# The facts about p = FS.prime(one) in the shape the group proofs take
# (modulus 1 + pm): pm = p - 1 as a number that is never expanded.

def pm(+one: Nat) -> Nat:
  X.bvalo(one, CB.p1l())

def hp_m(+one: Nat, +h1: {one == 1n : Nat}, +hp: PM.Prime(FS.prime(one))) -> PM.Prime(1n+pm(one)):
  Lg.subst(Nat, p => PM.Prime(p), FS.prime(one), 1n+pm(one), CB.p_suc(one, h1), hp)

def hc_s(+one: Nat, +h1: {one == 1n : Nat}, +hc: {Nat.is_eq(Nat.mod(Nat.pow(Nat.sub(1n+pm(one), 7n), Nat.div(Nat.sub(pm(one), 0n), 3n)), 1n+pm(one)), 1n) == False{} : Bool}) -> {Nat.is_eq(Nat.mod(Nat.pow(Nat.sub(1n+pm(one), 7n), Nat.div(pm(one), 3n)), 1n+pm(one)), 1n) == False{} : Bool}:
  %N.sub_zero(pm(one)) : {Nat.is_eq(Nat.mod(Nat.pow(Nat.sub(1n+pm(one), 7n), Nat.div(_, 3n)), 1n+pm(one)), 1n) == False{} : Bool}
  hc

# (-7)^((p-1)/3) != 1, from its statement on FS.prime(one)
def hc_m(+one: Nat, +h1: {one == 1n : Nat}, +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}) -> {Nat.is_eq(Nat.mod(Nat.pow(Nat.sub(1n+pm(one), 7n), Nat.div(pm(one), 3n)), 1n+pm(one)), 1n) == False{} : Bool}:
  hc_s(one, h1, Lg.subst(Nat, p => {Nat.is_eq(FS.mpow(p, Nat.sub(p, 7n), Nat.div(Nat.sub(p, 1n), 3n)), 1n) == False{} : Bool}, FS.prime(one), 1n+pm(one), CB.p_suc(one, h1), hc))

def h21_m(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_lt(21n, 1n+pm(one)) == True{} : Bool}:
  Lg.subst(Nat, p => {Nat.is_lt(21n, p) == True{} : Bool}, FS.prime(one), 1n+pm(one), CB.p_suc(one, h1), CB.p_gt21(one, h1))
