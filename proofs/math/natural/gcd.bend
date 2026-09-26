import Base
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as A
import ../../../src/math/natural.bend as M
import ./arith.bend as R

# gcd is the greatest common divisor (Lean 4 Mathlib, Mathlib/Data/Nat/GCD:
# Nat.gcd_dvd_left, Nat.gcd_dvd_right, Nat.dvd_gcd; the Euclid step is
# Nat.gcd_rec). "d divides a" is a == k d with an explicit witness k, so
# every divisibility fact below names its quotient.

# ---- Euclid's step keeps the common divisors ----

# d | a and d | n give d | a mod n: a mod n == (ka - q kn) d, q = a / n
def dvd_mod(+bp: Nat, +a: Nat, +d: Nat, +ka: Nat, +kn: Nat, +ea: {a == Nat.mul(ka, d) : Nat}, +en: {1n+bp == Nat.mul(kn, d) : Nat}) -> {Nat.mod(a, 1n+bp) == Nat.mul(Nat.sub(ka, Nat.mul(Nat.div(a, 1n+bp), kn)), d) : Nat}:
  +q = Nat.div(a, 1n+bp)
  %Equal.sym(Nat, Nat.mul(Nat.sub(ka, Nat.mul(q, kn)), d), Nat.sub(Nat.mul(ka, d), Nat.mul(Nat.mul(q, kn), d)), R.mul_sub(ka, Nat.mul(q, kn), d)) : {Nat.mod(a, 1n+bp) == _ : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(q, kn), d), Nat.mul(q, Nat.mul(kn, d)), A.mul_assoc(q, kn, d)) : {Nat.mod(a, 1n+bp) == Nat.sub(Nat.mul(ka, d), _) : Nat}
  %Equal.sym(Nat, Nat.mul(kn, d), 1n+bp, Equal.sym(Nat, 1n+bp, Nat.mul(kn, d), en)) : {Nat.mod(a, 1n+bp) == Nat.sub(Nat.mul(ka, d), Nat.mul(q, _)) : Nat}
  %Equal.sym(Nat, Nat.mul(ka, d), a, Equal.sym(Nat, a, Nat.mul(ka, d), ea)) : {Nat.mod(a, 1n+bp) == Nat.sub(_, Nat.mul(q, 1n+bp)) : Nat}
  %Equal.sym(Nat, a, Nat.add(Nat.mul(q, 1n+bp), Nat.mod(a, 1n+bp)), R.dm_eq(bp, a)) : {Nat.mod(a, 1n+bp) == Nat.sub(_, Nat.mul(q, 1n+bp)) : Nat}
  Equal.sym(Nat, Nat.sub(Nat.add(Nat.mul(q, 1n+bp), Nat.mod(a, 1n+bp)), Nat.mul(q, 1n+bp)), Nat.mod(a, 1n+bp), N.add_sub_cancel(Nat.mul(q, 1n+bp), Nat.mod(a, 1n+bp)))

# d | n and d | a mod n give d | a: a == (q kn + kr) d
def dvd_of_mod(+bp: Nat, +a: Nat, +d: Nat, +kn: Nat, +kr: Nat, +en: {1n+bp == Nat.mul(kn, d) : Nat}, +er: {Nat.mod(a, 1n+bp) == Nat.mul(kr, d) : Nat}) -> {a == Nat.mul(Nat.add(Nat.mul(Nat.div(a, 1n+bp), kn), kr), d) : Nat}:
  +q = Nat.div(a, 1n+bp)
  %Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(q, kn), kr), d), Nat.add(Nat.mul(Nat.mul(q, kn), d), Nat.mul(kr, d)), A.mul_add_right(Nat.mul(q, kn), kr, d)) : {a == _ : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(q, kn), d), Nat.mul(q, Nat.mul(kn, d)), A.mul_assoc(q, kn, d)) : {a == Nat.add(_, Nat.mul(kr, d)) : Nat}
  %Equal.sym(Nat, Nat.mul(kn, d), 1n+bp, Equal.sym(Nat, 1n+bp, Nat.mul(kn, d), en)) : {a == Nat.add(Nat.mul(q, _), Nat.mul(kr, d)) : Nat}
  %Equal.sym(Nat, Nat.mul(kr, d), Nat.mod(a, 1n+bp), Equal.sym(Nat, Nat.mod(a, 1n+bp), Nat.mul(kr, d), er)) : {a == Nat.add(Nat.mul(q, 1n+bp), _) : Nat}
  R.dm_eq(bp, a)

# ---- gcd divides both arguments ----

# the quotients a / g and b / g, by Euclid's recursion
type Wit is Data:
  W{l: Nat, r: Nat}

def wl(w: Wit) -> Nat:
  match w:
    case W{l, r}:
      l

def wr(w: Wit) -> Nat:
  match w:
    case W{l, r}:
      r

# from n == l g and a mod n == r g: a == (q l + r) g and n == l g
def wstep(+q: Nat, w: Wit) -> Wit:
  match w:
    case W{+l, r}:
      W{Nat.add(Nat.mul(q, l), r), l}

def ws(fuel: Nat, +a: Nat, +b: Nat) -> Wit:
  match fuel b:
    case 0n _:
      W{1n, 0n}
    case 1n+f 0n:
      W{1n, 0n}
    case 1n+f 1n+ +bp:
      wstep(Nat.div(a, 1n+bp), ws(f, 1n+bp, Nat.mod(a, 1n+bp)))

def divides_both(+a: Nat, +b: Nat, +g: Nat, w: Wit) -> Type:
  {a == Nat.mul(wl(w), g) : Nat} & {b == Nat.mul(wr(w), g) : Nat}

def step_both(+bp: Nat, +a: Nat, +g: Nat, w: Wit, ih: divides_both(1n+bp, Nat.mod(a, 1n+bp), g, w)) -> divides_both(a, 1n+bp, g, wstep(Nat.div(a, 1n+bp), w)):
  match w:
    case W{+l, +r}:
      (en, er) = ih
      +en2 = {en : {1n+bp == Nat.mul(l, g) : Nat}}
      (dvd_of_mod(bp, a, g, l, r, en2, er), en2)

def gcd_both(fuel: Nat, +a: Nat, +b: Nat, +hb: {Nat.is_le(b, fuel) == True{} : Bool}) -> divides_both(a, b, M.gcd_go(fuel, a, b), ws(fuel, a, b)):
  match fuel b:
    case 0n 0n:
      (Equal.sym(Nat, Nat.add(a, 0n), a, A.add_zero(a)), {==})
    case 0n 1n+bp:
      Empty.absurd(divides_both(a, 1n+bp, M.gcd_go(0n, a, 1n+bp), ws(0n, a, 1n+bp)), L.false_true(hb))
    case 1n+f 0n:
      (Equal.sym(Nat, Nat.add(a, 0n), a, A.add_zero(a)), {==})
    case 1n+ +f 1n+ +bp:
      step_both(bp, a, M.gcd_go(f, 1n+bp, Nat.mod(a, 1n+bp)), ws(f, 1n+bp, Nat.mod(a, 1n+bp)), gcd_both(f, 1n+bp, Nat.mod(a, 1n+bp), N.le_trans(Nat.mod(a, 1n+bp), bp, f, N.lt_succ_le(Nat.mod(a, 1n+bp), bp, R.dm_lt(bp, a)), hb)))

# ---- every common divisor divides gcd ----

# the quotient g / d, for d | a (a == ka d) and d | b (b == kb d)
def dw(fuel: Nat, +a: Nat, +b: Nat, +ka: Nat, +kb: Nat) -> Nat:
  match fuel b:
    case 0n _:
      ka
    case 1n+f 0n:
      ka
    case 1n+f 1n+ +bp:
      dw(f, 1n+bp, Nat.mod(a, 1n+bp), kb, Nat.sub(ka, Nat.mul(Nat.div(a, 1n+bp), kb)))

def gcd_greatest(fuel: Nat, +a: Nat, +b: Nat, +hb: {Nat.is_le(b, fuel) == True{} : Bool}, +d: Nat, +ka: Nat, +kb: Nat, +ea: {a == Nat.mul(ka, d) : Nat}, +eb: {b == Nat.mul(kb, d) : Nat}) -> {M.gcd_go(fuel, a, b) == Nat.mul(dw(fuel, a, b, ka, kb), d) : Nat}:
  match fuel b:
    case 0n 0n:
      ea
    case 0n 1n+bp:
      Empty.absurd({M.gcd_go(0n, a, 1n+bp) == Nat.mul(dw(0n, a, 1n+bp, ka, kb), d) : Nat}, L.false_true(hb))
    case 1n+f 0n:
      ea
    case 1n+ +f 1n+ +bp:
      gcd_greatest(f, 1n+bp, Nat.mod(a, 1n+bp), N.le_trans(Nat.mod(a, 1n+bp), bp, f, N.lt_succ_le(Nat.mod(a, 1n+bp), bp, R.dm_lt(bp, a)), hb), d, kb, Nat.sub(ka, Nat.mul(Nat.div(a, 1n+bp), kb)), eb, dvd_mod(bp, a, d, ka, kb, ea, eb))

# ---- the theorems, on gcd(a, b) = gcd_go(b, a, b) ----

def both_l(+a: Nat, +b: Nat, +g: Nat, w: Wit, p: divides_both(a, b, g, w)) -> {a == Nat.mul(wl(w), g) : Nat}:
  (el, er) = p
  el

def both_r(+a: Nat, +b: Nat, +g: Nat, w: Wit, p: divides_both(a, b, g, w)) -> {b == Nat.mul(wr(w), g) : Nat}:
  (el, er) = p
  er

def gcd_dvd_left(+a: Nat, +b: Nat) -> {a == Nat.mul(wl(ws(b, a, b)), M.gcd(a, b)) : Nat}:
  both_l(a, b, M.gcd(a, b), ws(b, a, b), gcd_both(b, a, b, N.le_refl(b)))

def gcd_dvd_right(+a: Nat, +b: Nat) -> {b == Nat.mul(wr(ws(b, a, b)), M.gcd(a, b)) : Nat}:
  both_r(a, b, M.gcd(a, b), ws(b, a, b), gcd_both(b, a, b, N.le_refl(b)))

def dvd_gcd(+a: Nat, +b: Nat, +d: Nat, +ka: Nat, +kb: Nat, +ea: {a == Nat.mul(ka, d) : Nat}, +eb: {b == Nat.mul(kb, d) : Nat}) -> {M.gcd(a, b) == Nat.mul(dw(b, a, b, ka, kb), d) : Nat}:
  gcd_greatest(b, a, b, N.le_refl(b), d, ka, kb, ea, eb)
