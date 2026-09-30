import Base
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../curve25519/num.bend as M

# Powers of two with the symbolic one (2^k = WD.sc(k, one), one == 1n)
# and the few closed inequalities the limb bounds of the field need, each
# derived from doublings (the checker never forms a closed 2^k).

def P(+k: Nat, +one: Nat) -> Nat:
  WD.sc(k, one)

def sc_pos(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_lt(0n, WD.sc(k, one)) == True{} : Bool}:
  L.subst(Nat, o => {Nat.is_lt(0n, WD.sc(k, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), WD.sc_pos(k))

def one_one(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.mul(one, one) == one : Nat}:
  L.subst(Nat, o => {Nat.mul(o, o) == o : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})

# 2^j 2^k == 2^(j + k)
def scsc(+j: Nat, +k: Nat, +one: Nat, +h1: {one == 1n : Nat}) -> {Nat.mul(WD.sc(j, one), WD.sc(k, one)) == WD.sc(Nat.add(j, k), one) : Nat}:
  Equal.trans(Nat, Nat.mul(WD.sc(j, one), WD.sc(k, one)), WD.sc(Nat.add(j, k), Nat.mul(one, one)), WD.sc(Nat.add(j, k), one), M.mul_sc2(j, k, one, one), M.cong_sc(Nat.add(j, k), Nat.mul(one, one), one, one_one(one, h1)))

# 2^a <= 2^(d + a)
def le_sc(+d: Nat, +a: Nat, +one: Nat) -> {Nat.is_le(WD.sc(a, one), WD.sc(Nat.add(d, a), one)) == True{} : Bool}:
  M.sc_mono(d, a, one)

# 2^a < 2^(d + 1 + a)
def lt_sc(+d: Nat, +a: Nat, +one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_lt(WD.sc(a, one), WD.sc(Nat.add(d, 1n+a), one)) == True{} : Bool}:
  +x = WD.sc(a, one)
  +a1 = N.lt_add_left(0n, x, x, sc_pos(a, one, h1))
  +a2 = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(x, x)) == True{} : Bool}, Nat.add(x, 0n), x, N.add_zero(x), a1)
  +a3 = L.subst(Nat, z => {Nat.is_lt(x, z) == True{} : Bool}, Nat.add(x, x), WD.sc(1n+a, one), M.sc_dbl(a, one), a2)
  N.lt_le_trans(x, WD.sc(1n+a, one), WD.sc(Nat.add(d, 1n+a), one), a3, M.sc_mono(d, 1n+a, one))

# 2^k + 2^k == 2^(k+1)
def dbl(+k: Nat, +one: Nat) -> {Nat.add(WD.sc(k, one), WD.sc(k, one)) == WD.sc(1n+k, one) : Nat}:
  M.sc_dbl(k, one)

# a <= 2^k, b <= 2^k -> a + b <= 2^(k+1)
def add_le_dbl(+a: Nat, +b: Nat, +k: Nat, +one: Nat, +ha: {Nat.is_le(a, WD.sc(k, one)) == True{} : Bool}, +hb: {Nat.is_le(b, WD.sc(k, one)) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, b), WD.sc(1n+k, one)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(Nat.add(a, b), z) == True{} : Bool}, Nat.add(WD.sc(k, one), WD.sc(k, one)), WD.sc(1n+k, one), dbl(k, one), M.le_add2(a, b, WD.sc(k, one), WD.sc(k, one), ha, hb))

# x k <= x m for k <= m
def mul_le_r(+x: Nat, +k: Nat, +m: Nat, +h: {Nat.is_le(k, m) == True{} : Bool}) -> {Nat.is_le(Nat.mul(x, k), Nat.mul(x, m)) == True{} : Bool}:
  M.le_mul2(x, k, x, m, N.le_refl(x), h)

# 2^k == 1 + (2^k - 1)
def pos_succ(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat) -> {1n+Nat.sub(WD.sc(k, one), 1n) == WD.sc(k, one) : Nat}:
  N.sub_add(WD.sc(k, one), 1n, N.lt_succ_le_succ(0n, WD.sc(k, one), sc_pos(k, one, h1)))

# x < S -> x + one <= S
def succ_le(+one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +S: Nat, +h: {Nat.is_lt(x, S) == True{} : Bool}) -> {Nat.is_le(Nat.add(x, one), S) == True{} : Bool}:
  L.subst(Nat, o => {Nat.is_le(Nat.add(x, o), S) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), L.subst(Nat, t => {Nat.is_le(t, S) == True{} : Bool}, 1n+x, Nat.add(x, 1n), Equal.trans(Nat, 1n+x, 1n+Nat.add(x, 0n), Nat.add(x, 1n), Equal.cong(Nat, Nat, t => 1n+t, x, Nat.add(x, 0n), Equal.sym(Nat, Nat.add(x, 0n), x, N.add_zero(x))), Equal.sym(Nat, Nat.add(x, 1n), 1n+Nat.add(x, 0n), N.add_succ(x, 0n))), N.lt_succ_le_succ(x, S, h)))
