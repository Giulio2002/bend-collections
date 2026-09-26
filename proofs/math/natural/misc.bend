import Base
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../../src/math/natural.bend as M
import ./arith.bend as R

# divmod and clamp. divmod(a, b) is (a // b, a % b) with a == q b + r and
# r < b (Mathlib Nat.div_add_mod, Nat.mod_lt; Python divmod), ZeroDivision
# for b == 0; clamp(x, lo, hi) lies in [lo, hi] and is x when x already
# does (C++ std::clamp, Rust Ord::clamp; the reference's clamp, section
# 10), Domain for hi < lo.

def divmod_done(+a: Nat, +bp: Nat) -> {M.divmod(a, 1n+bp) == Done{M.QR{Nat.div(a, 1n+bp), Nat.mod(a, 1n+bp)}} : Result<&2, &2, M.MathError, M.QuotRem>}:
  {==}

def divmod_eq(+a: Nat, +bp: Nat) -> {a == Nat.add(Nat.mul(Nat.div(a, 1n+bp), 1n+bp), Nat.mod(a, 1n+bp)) : Nat}:
  R.dm_eq(bp, a)

def divmod_lt(+a: Nat, +bp: Nat) -> {Nat.is_lt(Nat.mod(a, 1n+bp), 1n+bp) == True{} : Bool}:
  R.dm_lt(bp, a)

def divmod_zero(+a: Nat) -> {M.divmod(a, 0n) == Fail{M.ZeroDivision{}} : Result<&2, &2, M.MathError, M.QuotRem>}:
  {==}

# ---- max and min ----

def le_max_r(+x: Nat, +lo: Nat) -> {Nat.is_le(lo, Nat.max(x, lo)) == True{} : Bool}:
  match x lo:
    case 0n l0:
      N.le_refl(l0)
    case 1n+xp 0n:
      {==}
    case 1n+ +xp 1n+ +lp:
      le_max_r(xp, lp)

def max_eq_l(+x: Nat, +lo: Nat, +h: {Nat.is_le(lo, x) == True{} : Bool}) -> {Nat.max(x, lo) == x : Nat}:
  match x lo:
    case 0n 0n:
      {==}
    case 0n 1n+lp:
      Empty.absurd({Nat.max(0n, 1n+lp) == 0n : Nat}, L.false_true(h))
    case 1n+xp 0n:
      {==}
    case 1n+ +xp 1n+ +lp:
      N.succ_cong(Nat.max(xp, lp), xp, max_eq_l(xp, lp, h))

def min_le_r(+y: Nat, +hi: Nat) -> {Nat.is_le(Nat.min(y, hi), hi) == True{} : Bool}:
  match y hi:
    case 0n h0:
      N.zero_le(h0)
    case 1n+yp 0n:
      {==}
    case 1n+ +yp 1n+ +hp:
      min_le_r(yp, hp)

def le_min(+lo: Nat, +y: Nat, +hi: Nat, +h1: {Nat.is_le(lo, y) == True{} : Bool}, +h2: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Nat.is_le(lo, Nat.min(y, hi)) == True{} : Bool}:
  match lo y hi:
    case 0n y0 h0:
      N.zero_le(Nat.min(y0, h0))
    case 1n+lp 0n h0:
      Empty.absurd({Nat.is_le(1n+lp, Nat.min(0n, h0)) == True{} : Bool}, L.false_true(h1))
    case 1n+lp 1n+yp 0n:
      Empty.absurd({Nat.is_le(1n+lp, Nat.min(1n+yp, 0n)) == True{} : Bool}, L.false_true(h2))
    case 1n+ +lp 1n+ +yp 1n+ +hp:
      le_min(lp, yp, hp, h1, h2)

def min_eq_l(+y: Nat, +hi: Nat, +h: {Nat.is_le(y, hi) == True{} : Bool}) -> {Nat.min(y, hi) == y : Nat}:
  match y hi:
    case 0n h0:
      {==}
    case 1n+yp 0n:
      Empty.absurd({Nat.min(1n+yp, 0n) == 1n+yp : Nat}, L.false_true(h))
    case 1n+ +yp 1n+ +hp:
      N.succ_cong(Nat.min(yp, hp), yp, min_eq_l(yp, hp, h))

# ---- clamp ----

def clamp_done(+x: Nat, +lo: Nat, +hi: Nat, +h: {Nat.is_le(lo, hi) == True{} : Bool}) -> {M.clamp(x, lo, hi) == Done{Nat.min(Nat.max(x, lo), hi)} : Result<&2, &2, M.MathError, Nat>}:
  %Equal.sym(Bool, Nat.is_lt(hi, lo), False{}, N.le_not_lt(hi, lo, h)) : {M.clamp_ok(x, lo, hi, _) == Done{Nat.min(Nat.max(x, lo), hi)} : Result<&2, &2, M.MathError, Nat>}
  {==}

def clamp_domain(+x: Nat, +lo: Nat, +hi: Nat, +h: {Nat.is_lt(hi, lo) == True{} : Bool}) -> {M.clamp(x, lo, hi) == Fail{M.Domain{}} : Result<&2, &2, M.MathError, Nat>}:
  %Equal.sym(Bool, Nat.is_lt(hi, lo), True{}, h) : {M.clamp_ok(x, lo, hi, _) == Fail{M.Domain{}} : Result<&2, &2, M.MathError, Nat>}
  {==}

# lo <= clamp and clamp <= hi
def clamp_ge(+x: Nat, +lo: Nat, +hi: Nat, +h: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Nat.is_le(lo, Nat.min(Nat.max(x, lo), hi)) == True{} : Bool}:
  le_min(lo, Nat.max(x, lo), hi, le_max_r(x, lo), h)

def clamp_le(+x: Nat, +lo: Nat, +hi: Nat) -> {Nat.is_le(Nat.min(Nat.max(x, lo), hi), hi) == True{} : Bool}:
  min_le_r(Nat.max(x, lo), hi)

# x in [lo, hi] is left alone
def clamp_id(+x: Nat, +lo: Nat, +hi: Nat, +h1: {Nat.is_le(lo, x) == True{} : Bool}, +h2: {Nat.is_le(x, hi) == True{} : Bool}) -> {Nat.min(Nat.max(x, lo), hi) == x : Nat}:
  %Equal.sym(Nat, Nat.max(x, lo), x, max_eq_l(x, lo, h1)) : {Nat.min(_, hi) == x : Nat}
  min_eq_l(x, hi, h2)
