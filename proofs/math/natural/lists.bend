import Base
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as A
import ../../../src/math/natural.bend as M
import ./gcd.bend as G
import ./lcm.bend as LC
import ./spec.bend as S

# sum and prod are List.sum and List.prod (Lean 4 Mathlib
# Mathlib/Algebra/BigOperators/Group/List: List.sum_cons, List.prod_cons),
# and gcd_all / lcm_all are the gcd and lcm of a list: they divide / are
# divided by every element, and every common divisor / multiple divides /
# is divided by them (Mathlib Mathlib/Algebra/GCDMonoid/Finset:
# Finset.gcd_dvd, Finset.dvd_gcd, Finset.dvd_lcm, Finset.lcm_dvd). Python:
# math.gcd(*xs), math.lcm(*xs), math.prod, sum; gcd() == 0, lcm() == 1.

# ---- sum and prod ----

def sum_go(+xs: List<&2, Nat>, +acc: Nat) -> {M.sum_go(xs, acc) == Nat.add(acc, S.lsum(xs)) : Nat}:
  match xs:
    case Nil{}:
      Equal.sym(Nat, Nat.add(acc, 0n), acc, A.add_zero(acc))
    case Con{+x, +t}:
      Equal.trans(Nat, M.sum_go(t, Nat.add(acc, x)), Nat.add(Nat.add(acc, x), S.lsum(t)), Nat.add(acc, Nat.add(x, S.lsum(t))), sum_go(t, Nat.add(acc, x)), A.add_assoc(acc, x, S.lsum(t)))

def sum_ok(+xs: List<&2, Nat>) -> {M.sum(xs) == S.lsum(xs) : Nat}:
  sum_go(xs, 0n)

def prod_go(+xs: List<&2, Nat>, +acc: Nat) -> {M.prod_go(xs, acc) == Nat.mul(acc, S.lprod(xs)) : Nat}:
  match xs:
    case Nil{}:
      Equal.sym(Nat, Nat.mul(acc, 1n), acc, A.mul_one(acc))
    case Con{+x, +t}:
      Equal.trans(Nat, M.prod_go(t, Nat.mul(acc, x)), Nat.mul(Nat.mul(acc, x), S.lprod(t)), Nat.mul(acc, Nat.mul(x, S.lprod(t))), prod_go(t, Nat.mul(acc, x)), A.mul_assoc(acc, x, S.lprod(t)))

def prod_ok(+xs: List<&2, Nat>) -> {M.prod(xs) == S.lprod(xs) : Nat}:
  Equal.trans(Nat, M.prod(xs), Nat.mul(1n, S.lprod(xs)), S.lprod(xs), prod_go(xs, 1n), LC.one_mul(S.lprod(xs)))

# ---- gcd_all ----

def nth0(+xs: List<&2, Nat>, +i: Nat, +d: Nat) -> Nat:
  match xs i:
    case Nil{} i0:
      d
    case Con{x, t} 0n:
      x
    case Con{x, t} 1n+j:
      nth0(t, j, d)

# d divides every element: xs[i] == ks[i] d
def dvd_with(+d: Nat, +xs: List<&2, Nat>, +ks: List<&2, Nat>) -> Type:
  match xs ks:
    case Nil{} Nil{}:
      Unit
    case Nil{} Con{k, kt}:
      Unit
    case Con{x, t} Nil{}:
      Empty
    case Con{+x, +t} Con{+k, +kt}:
      {x == Nat.mul(k, d) : Nat} & dvd_with(d, t, kt)

# m is a multiple of every element: m == ks[i] xs[i]
def mul_with(+m: Nat, +xs: List<&2, Nat>, +ks: List<&2, Nat>) -> Type:
  match xs ks:
    case Nil{} Nil{}:
      Unit
    case Nil{} Con{k, kt}:
      Unit
    case Con{x, t} Nil{}:
      Empty
    case Con{+x, +t} Con{+k, +kt}:
      {m == Nat.mul(k, x) : Nat} & mul_with(m, t, kt)

# (a == k1 b and b == k2 c) gives a == (k1 k2) c
def dvd_trans(+a: Nat, +b: Nat, +c: Nat, +k1: Nat, +k2: Nat, +e1: {a == Nat.mul(k1, b) : Nat}, +e2: {b == Nat.mul(k2, c) : Nat}) -> {a == Nat.mul(Nat.mul(k1, k2), c) : Nat}:
  Equal.trans(Nat, a, Nat.mul(k1, b), Nat.mul(Nat.mul(k1, k2), c), e1, Equal.trans(Nat, Nat.mul(k1, b), Nat.mul(k1, Nat.mul(k2, c)), Nat.mul(Nat.mul(k1, k2), c), Equal.cong(Nat, Nat, z => Nat.mul(k1, z), b, Nat.mul(k2, c), e2), Equal.sym(Nat, Nat.mul(Nat.mul(k1, k2), c), Nat.mul(k1, Nat.mul(k2, c)), A.mul_assoc(k1, k2, c))))

# the quotient acc / gcd_all_go(xs, acc)
def gw_acc(+xs: List<&2, Nat>, +acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      1n
    case Con{+x, +t}:
      Nat.mul(G.wl(G.ws(x, acc, x)), gw_acc(t, M.gcd(acc, x)))

def g_acc(+xs: List<&2, Nat>, +acc: Nat) -> {acc == Nat.mul(gw_acc(xs, acc), M.gcd_all_go(xs, acc)) : Nat}:
  match xs:
    case Nil{}:
      Equal.sym(Nat, Nat.mul(1n, acc), acc, LC.one_mul(acc))
    case Con{+x, +t}:
      dvd_trans(acc, M.gcd(acc, x), M.gcd_all_go(t, M.gcd(acc, x)), G.wl(G.ws(x, acc, x)), gw_acc(t, M.gcd(acc, x)), G.gcd_dvd_left(acc, x), g_acc(t, M.gcd(acc, x)))

# the quotient (xs[i]) / gcd_all_go(xs, acc)
def gw_nth(+xs: List<&2, Nat>, +acc: Nat, +i: Nat) -> Nat:
  match xs i:
    case Nil{} i0:
      0n
    case Con{+x, +t} 0n:
      Nat.mul(G.wr(G.ws(x, acc, x)), gw_acc(t, M.gcd(acc, x)))
    case Con{+x, +t} 1n+ +j:
      gw_nth(t, M.gcd(acc, x), j)

def g_nth(+xs: List<&2, Nat>, +acc: Nat, +i: Nat) -> {nth0(xs, i, 0n) == Nat.mul(gw_nth(xs, acc, i), M.gcd_all_go(xs, acc)) : Nat}:
  match xs i:
    case Nil{} i0:
      {==}
    case Con{+x, +t} 0n:
      dvd_trans(x, M.gcd(acc, x), M.gcd_all_go(t, M.gcd(acc, x)), G.wr(G.ws(x, acc, x)), gw_acc(t, M.gcd(acc, x)), G.gcd_dvd_right(acc, x), g_acc(t, M.gcd(acc, x)))
    case Con{+x, +t} 1n+ +j:
      g_nth(t, M.gcd(acc, x), j)

# gcd_all(xs) divides every element: xs[i] == k gcd_all(xs) (0 past the end)   (Mathlib Finset.gcd_dvd)
def gcd_all_dvd(+xs: List<&2, Nat>, +i: Nat) -> {nth0(xs, i, 0n) == Nat.mul(gw_nth(xs, 0n, i), M.gcd_all(xs)) : Nat}:
  g_nth(xs, 0n, i)

# the quotient gcd_all_go(xs, acc) / d for a common divisor d
def gw_dvd(+xs: List<&2, Nat>, +ks: List<&2, Nat>, +acc: Nat, +ka: Nat) -> Nat:
  match xs ks:
    case Nil{} Nil{}:
      ka
    case Nil{} Con{k, kt}:
      ka
    case Con{x, t} Nil{}:
      0n
    case Con{+x, +t} Con{+k, +kt}:
      gw_dvd(t, kt, M.gcd(acc, x), G.dw(x, acc, x, ka, k))

def g_dvd(+d: Nat, +xs: List<&2, Nat>, +ks: List<&2, Nat>, +acc: Nat, +ka: Nat, +ea: {acc == Nat.mul(ka, d) : Nat}, h: dvd_with(d, xs, ks)) -> {M.gcd_all_go(xs, acc) == Nat.mul(gw_dvd(xs, ks, acc, ka), d) : Nat}:
  match xs ks:
    case Nil{} Nil{}:
      ea
    case Nil{} Con{k, kt}:
      ea
    case Con{x, t} Nil{}:
      Empty.absurd({M.gcd_all_go(Con{x, t}, acc) == Nat.mul(gw_dvd(Con{x, t}, Nil{}, acc, ka), d) : Nat}, h)
    case Con{+x, +t} Con{+k, +kt}:
      (ex, ht) = h
      g_dvd(d, t, kt, M.gcd(acc, x), G.dw(x, acc, x, ka, k), G.dvd_gcd(acc, x, d, ka, k, ea, ex), ht)

# every common divisor of the elements divides gcd_all(xs)   (Mathlib Finset.dvd_gcd)
def dvd_gcd_all(+d: Nat, +xs: List<&2, Nat>, +ks: List<&2, Nat>, h: dvd_with(d, xs, ks)) -> {M.gcd_all(xs) == Nat.mul(gw_dvd(xs, ks, 0n, 0n), d) : Nat}:
  g_dvd(d, xs, ks, 0n, 0n, {==}, h)

# ---- lcm_all ----

def lw_acc(+xs: List<&2, Nat>, +acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      1n
    case Con{+x, +t}:
      Nat.mul(lw_acc(t, M.lcm(acc, x)), LC.lcm_wl(acc, x))

def l_acc(+xs: List<&2, Nat>, +acc: Nat) -> {M.lcm_all_go(xs, acc) == Nat.mul(lw_acc(xs, acc), acc) : Nat}:
  match xs:
    case Nil{}:
      Equal.sym(Nat, Nat.mul(1n, acc), acc, LC.one_mul(acc))
    case Con{+x, +t}:
      dvd_trans(M.lcm_all_go(t, M.lcm(acc, x)), M.lcm(acc, x), acc, lw_acc(t, M.lcm(acc, x)), LC.lcm_wl(acc, x), l_acc(t, M.lcm(acc, x)), LC.dvd_lcm_left(acc, x))

def lw_nth(+xs: List<&2, Nat>, +acc: Nat, +i: Nat) -> Nat:
  match xs i:
    case Nil{} i0:
      acc
    case Con{+x, +t} 0n:
      Nat.mul(lw_acc(t, M.lcm(acc, x)), LC.lcm_wr(acc, x))
    case Con{+x, +t} 1n+ +j:
      lw_nth(t, M.lcm(acc, x), j)

def l_nth(+xs: List<&2, Nat>, +acc: Nat, +i: Nat) -> {M.lcm_all_go(xs, acc) == Nat.mul(lw_nth(xs, acc, i), nth0(xs, i, 1n)) : Nat}:
  match xs i:
    case Nil{} i0:
      Equal.sym(Nat, Nat.mul(acc, 1n), acc, A.mul_one(acc))
    case Con{+x, +t} 0n:
      dvd_trans(M.lcm_all_go(t, M.lcm(acc, x)), M.lcm(acc, x), x, lw_acc(t, M.lcm(acc, x)), LC.lcm_wr(acc, x), l_acc(t, M.lcm(acc, x)), LC.dvd_lcm_right(acc, x))
    case Con{+x, +t} 1n+ +j:
      l_nth(t, M.lcm(acc, x), j)

# every element divides lcm_all(xs) (1 past the end)   (Mathlib Finset.dvd_lcm)
def dvd_lcm_all(+xs: List<&2, Nat>, +i: Nat) -> {M.lcm_all(xs) == Nat.mul(lw_nth(xs, 1n, i), nth0(xs, i, 1n)) : Nat}:
  l_nth(xs, 1n, i)

def lw_mul(+m: Nat, +xs: List<&2, Nat>, +ks: List<&2, Nat>, +acc: Nat, +ka: Nat) -> Nat:
  match xs ks:
    case Nil{} Nil{}:
      ka
    case Nil{} Con{k, kt}:
      ka
    case Con{x, t} Nil{}:
      0n
    case Con{+x, +t} Con{+k, +kt}:
      lw_mul(m, t, kt, M.lcm(acc, x), LC.lcm_dw(acc, x, m, ka, k))

def l_mul(+m: Nat, +xs: List<&2, Nat>, +ks: List<&2, Nat>, +acc: Nat, +ka: Nat, +ea: {m == Nat.mul(ka, acc) : Nat}, h: mul_with(m, xs, ks)) -> {m == Nat.mul(lw_mul(m, xs, ks, acc, ka), M.lcm_all_go(xs, acc)) : Nat}:
  match xs ks:
    case Nil{} Nil{}:
      ea
    case Nil{} Con{k, kt}:
      ea
    case Con{x, t} Nil{}:
      Empty.absurd({m == Nat.mul(lw_mul(m, Con{x, t}, Nil{}, acc, ka), M.lcm_all_go(Con{x, t}, acc)) : Nat}, h)
    case Con{+x, +t} Con{+k, +kt}:
      (ex, ht) = h
      l_mul(m, t, kt, M.lcm(acc, x), LC.lcm_dw(acc, x, m, ka, k), LC.lcm_dvd(acc, x, m, ka, k, ea, ex), ht)

# lcm_all(xs) divides every common multiple of the elements   (Mathlib Finset.lcm_dvd)
def lcm_all_dvd(+m: Nat, +xs: List<&2, Nat>, +ks: List<&2, Nat>, h: mul_with(m, xs, ks)) -> {m == Nat.mul(lw_mul(m, xs, ks, 1n, m), M.lcm_all(xs)) : Nat}:
  l_mul(m, xs, ks, 1n, m, Equal.sym(Nat, Nat.mul(m, 1n), m, A.mul_one(m)), h)
