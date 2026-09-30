import Base
import ../../../lib/logic.bend as Lg
import ../../../../spec/crypto/secp256k1/field.bend as FS
import ../../../../spec/crypto/secp256k1/curve.bend as CS
import ../../../../spec/crypto/secp256k1/group.bend as GS
import ../../../math/number/nt_prime.bend as PM
import ./bnx.bend as X
import ./certb.bend as CB
import ./gfp.bend as GF
import ./pto.bend as PO

# Scalars modulo the group order, on the specification's p = FS.prime(one)
# and n = FS.order(one): for a point A of the group with [n] A equiv O (hn;
# for A = G that is pte.bend's ng), [k] A depends only on k mod n. hp and hc
# are the facts about p of the group-law clauses (laws_group.bend).

# [k] A equiv [k mod n] A
def k_mod(+one: Nat, +h1: {one == 1n : Nat}, +hp: PM.Prime(FS.prime(one)), +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}, +k: Nat, +a: CS.SPoint, +va: {GS.valid(FS.prime(one), a) == True{} : Bool}, +hn: {GS.equiv(FS.prime(one), GS.smul(FS.prime(one), FS.order(one), a), CS.infinity()) == True{} : Bool}) -> {GS.equiv(FS.prime(one), GS.smul(FS.prime(one), k, a), GS.smul(FS.prime(one), Nat.mod(k, FS.order(one)), a)) == True{} : Bool}:
  Lg.subst(Nat, q => {GS.equiv(q, GS.smul(q, k, a), GS.smul(q, Nat.mod(k, FS.order(one)), a)) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)),
    Lg.subst(Nat, n => {GS.equiv(1n+GF.pm(one), GS.smul(1n+GF.pm(one), k, a), GS.smul(1n+GF.pm(one), Nat.mod(k, n), a)) == True{} : Bool}, 1n+X.bvalo(one, CB.n1l()), FS.order(one), Equal.sym(Nat, FS.order(one), 1n+X.bvalo(one, CB.n1l()), CB.n_suc(one, h1)), PO.smul_mod(GF.pm(one), GF.hp_m(one, h1, hp), CB.p_mod3(one, h1), GF.hc_m(one, h1, hc), GF.h21_m(one, h1), k, X.bvalo(one, CB.n1l()), a, Lg.subst(Nat, q => {GS.valid(q, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va), Lg.subst(Nat, q => {GS.equiv(q, GS.smul(q, 1n+X.bvalo(one, CB.n1l()), a), CS.infinity()) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), Lg.subst(Nat, n => {GS.equiv(FS.prime(one), GS.smul(FS.prime(one), n, a), CS.infinity()) == True{} : Bool}, FS.order(one), 1n+X.bvalo(one, CB.n1l()), CB.n_suc(one, h1), hn)))))

# [j] A + [k] A equiv [(j + k) mod n] A
def add_mod(+one: Nat, +h1: {one == 1n : Nat}, +hp: PM.Prime(FS.prime(one)), +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}, +j: Nat, +k: Nat, +a: CS.SPoint, +va: {GS.valid(FS.prime(one), a) == True{} : Bool}, +hn: {GS.equiv(FS.prime(one), GS.smul(FS.prime(one), FS.order(one), a), CS.infinity()) == True{} : Bool}) -> {GS.equiv(FS.prime(one), CS.padd(FS.prime(one), GS.smul(FS.prime(one), j, a), GS.smul(FS.prime(one), k, a)), GS.smul(FS.prime(one), Nat.mod(Nat.add(j, k), FS.order(one)), a)) == True{} : Bool}:
  Lg.subst(Nat, q => {GS.equiv(q, CS.padd(q, GS.smul(q, j, a), GS.smul(q, k, a)), GS.smul(q, Nat.mod(Nat.add(j, k), FS.order(one)), a)) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)),
    Lg.subst(Nat, n => {GS.equiv(1n+GF.pm(one), CS.padd(1n+GF.pm(one), GS.smul(1n+GF.pm(one), j, a), GS.smul(1n+GF.pm(one), k, a)), GS.smul(1n+GF.pm(one), Nat.mod(Nat.add(j, k), n), a)) == True{} : Bool}, 1n+X.bvalo(one, CB.n1l()), FS.order(one), Equal.sym(Nat, FS.order(one), 1n+X.bvalo(one, CB.n1l()), CB.n_suc(one, h1)), PO.add_mod(GF.pm(one), GF.hp_m(one, h1, hp), CB.p_mod3(one, h1), GF.hc_m(one, h1, hc), GF.h21_m(one, h1), j, k, X.bvalo(one, CB.n1l()), a, Lg.subst(Nat, q => {GS.valid(q, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va), Lg.subst(Nat, q => {GS.equiv(q, GS.smul(q, 1n+X.bvalo(one, CB.n1l()), a), CS.infinity()) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), Lg.subst(Nat, n => {GS.equiv(FS.prime(one), GS.smul(FS.prime(one), n, a), CS.infinity()) == True{} : Bool}, FS.order(one), 1n+X.bvalo(one, CB.n1l()), CB.n_suc(one, h1), hn)))))

# [j] ([k] A) equiv [(j k) mod n] A
def mul_mod(+one: Nat, +h1: {one == 1n : Nat}, +hp: PM.Prime(FS.prime(one)), +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}, +j: Nat, +k: Nat, +a: CS.SPoint, +va: {GS.valid(FS.prime(one), a) == True{} : Bool}, +hn: {GS.equiv(FS.prime(one), GS.smul(FS.prime(one), FS.order(one), a), CS.infinity()) == True{} : Bool}) -> {GS.equiv(FS.prime(one), GS.smul(FS.prime(one), j, GS.smul(FS.prime(one), k, a)), GS.smul(FS.prime(one), Nat.mod(Nat.mul(j, k), FS.order(one)), a)) == True{} : Bool}:
  Lg.subst(Nat, q => {GS.equiv(q, GS.smul(q, j, GS.smul(q, k, a)), GS.smul(q, Nat.mod(Nat.mul(j, k), FS.order(one)), a)) == True{} : Bool}, 1n+GF.pm(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1)),
    Lg.subst(Nat, n => {GS.equiv(1n+GF.pm(one), GS.smul(1n+GF.pm(one), j, GS.smul(1n+GF.pm(one), k, a)), GS.smul(1n+GF.pm(one), Nat.mod(Nat.mul(j, k), n), a)) == True{} : Bool}, 1n+X.bvalo(one, CB.n1l()), FS.order(one), Equal.sym(Nat, FS.order(one), 1n+X.bvalo(one, CB.n1l()), CB.n_suc(one, h1)), PO.mul_mod(GF.pm(one), GF.hp_m(one, h1, hp), CB.p_mod3(one, h1), GF.hc_m(one, h1, hc), GF.h21_m(one, h1), j, k, X.bvalo(one, CB.n1l()), a, Lg.subst(Nat, q => {GS.valid(q, a) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), va), Lg.subst(Nat, q => {GS.equiv(q, GS.smul(q, 1n+X.bvalo(one, CB.n1l()), a), CS.infinity()) == True{} : Bool}, FS.prime(one), 1n+GF.pm(one), CB.p_suc(one, h1), Lg.subst(Nat, n => {GS.equiv(FS.prime(one), GS.smul(FS.prime(one), n, a), CS.infinity()) == True{} : Bool}, FS.order(one), 1n+X.bvalo(one, CB.n1l()), CB.n_suc(one, h1), hn)))))
