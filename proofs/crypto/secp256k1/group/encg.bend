import Base
import ../../../../spec/lib/common.bend as C
import ../../../../spec/crypto/secp256k1/field.bend as FS
import ../../../lib/logic.bend as Lg
import ./bnx.bend as X
import ./certb.bend as CB
import ./gfp.bend as GF
import ./encb.bend as EB

# The closed facts of encb.bend in the shape the encoding proofs take
# (modulus 1 + pm, pm = p - 1 never expanded).

def he_m(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.add(1n+GF.pm(one), 1n) == Nat.mul(X.bvalo(one, EB.s4l()), 4n) : Nat}:
  Lg.subst(Nat, p => {Nat.add(p, 1n) == Nat.mul(X.bvalo(one, EB.s4l()), 4n) : Nat}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), EB.p_q4(one, h1))

def hodd_m(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.mod(1n+GF.pm(one), 2n) == 1n : Nat}:
  Lg.subst(Nat, p => {Nat.mod(p, 2n) == 1n : Nat}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), EB.p_odd(one, h1))

def h256_m(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_le(1n+GF.pm(one), C.shift(256n, one)) == True{} : Bool}:
  Lg.subst(Nat, p => {Nat.is_le(p, C.shift(256n, one)) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), EB.p_le(one))
