import Base
import ../lib/common.bend as C
import ../../src/math/num.bend as N
import ../../src/math/generic.bend as G
import ../../src/math/natural.bend as M
import ./natural.bend as NS
import ./w64.bend as SW
import ../../src/math/u64.bend as W

# Specification of src/math/generic.bend: every templated function at each
# instance of num.bend (U32, U64 from src/math/instances.bend; F32; the
# software F64 of src/math/f64.bend). A clause is stated once over an
# instance model and read at each type (docs/MATH_CONTRACTS.md has the
# function x type matrix).
#
# STATED AND TESTED; A FEW PROVED: the Nat functions of natural.bend are
# the proved reference (spec/math/natural.bend); these clauses relate each
# typed function to them and are exercised by tools/check_generic.py, which
# names the clause of every case it checks. At U32, Abs.identity,
# Min.agrees, Max.agrees, Sign.agrees and Clamp.agrees are proved for every
# input (proofs/math/typed/u32.bend); the other integer clauses are
# evaluated by the checker at concrete U32 inputs
# (proofs/math/typed/examples.bend). Semantics follow
# python_style_math_stdlib_design.pdf: errors are values (2.3); a fixed
# width reports Overflow instead of wrapping (2.6); Python's min/max keep
# the first argument on ties (3.1); float sum is a left fold (4.6 notes
# fsum is the compensated one); float pow is binary exponentiation with
# every product rounded (4.5).
#
# Integer instance model (U32: U32.to_nat / U32.from_nat, width 32;
# U64: spec/math/w64.bend's value / of_nat, width 64):
#   val: T -> Nat, the value;  of: Nat -> T, below 2^w;  w, the width.
#
#   function     integer clauses (U32, U64)     float clauses (F32, F64)
#   gcd          Gcd.agrees                      -
#   lcm          Lcm.checked                     -
#   gcd_all      GcdAll.agrees                   -
#   lcm_all      LcmAll.checked                  -
#   isqrt        Isqrt.agrees                    -
#   iroot        Iroot.agrees                    -
#   ilog         Ilog.agrees                     -
#   factorial    Factorial.checked               -
#   perm         Perm.checked                    -
#   comb         Comb.checked                    -
#   pow_mod      PowMod.agrees                   -
#   mod_inverse  ModInverse.agrees               -
#   divmod       DivMod.agrees                   -
#   bit_length   BitLength.agrees                -
#   clamp        Clamp.agrees                    FClamp.select
#   min, max     Min.agrees, Max.agrees          FMin.select, FMax.select
#   abs          Abs.identity                    FAbs.value
#   sign         Sign.agrees                     FSign.select
#   sum          Sum.checked                     FSum.fold
#   prod         Prod.checked                    FProd.fold
#   pow          Pow.checked                     FPow.binary

# ---- shared definitions ----

# n fits w bits: n < 2^w (spec/lib/common.bend states it without 2^w)
def fits(+w: Nat, +n: Nat) -> Bool:
  C.fits(w, n)

def checked_pick(~T: Data, ~of: Nat -> T, +n: Nat, ok: Bool) -> Result<&2, &2, N.NumError, T>:
  match ok:
    case True{}:
      Done{of(n)}
    case False{}:
      Fail{N.Overflow{}}

# n as a T, or Overflow when it needs more than w bits
def checked(~T: Data, ~of: Nat -> T, +w: Nat, +n: Nat) -> Result<&2, &2, N.NumError, T>:
  checked_pick(~T, ~of, n, fits(w, n))

def err(e: M.MathError) -> N.NumError:
  match e:
    case M.ZeroDivision{}:
      N.DivByZero{}
    case M.Domain{}:
      N.BadDomain{}
    case M.NotInvertible{}:
      N.NoInverse{}

# a Nat result carried to T (values that are no larger than an argument)
def lift(~T: Data, ~of: Nat -> T, r: Result<&2, &2, M.MathError, Nat>) -> Result<&2, &2, N.NumError, T>:
  match r:
    case Done{x}:
      Done{of(x)}
    case Fail{e}:
      Fail{err(e)}

def lift_nat(r: Result<&2, &2, M.MathError, Nat>) -> Result<&2, &2, N.NumError, Nat>:
  match r:
    case Done{x}:
      Done{x}
    case Fail{e}:
      Fail{err(e)}

def lift_qr(~T: Data, ~of: Nat -> T, r: Result<&2, &2, M.MathError, M.QuotRem>) -> Result<&2, &2, N.NumError, G.QuotRem<T>>:
  match r:
    case Done{M.QR{q, m}}:
      Done{G.TQR{of(q), of(m)}}
    case Fail{e}:
      Fail{err(e)}

def vals(~T: Data, ~val: T -> Nat, xs: List<&2, T>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{val(x), vals(~T, ~val, t)}

def pick(-T: Data, c: Bool, +a: T, +b: T) -> T:
  match c:
    case True{}:
      a
    case False{}:
      b

# a fold that stops at the first prefix of w bits or more (prod, lcm_all:
# a later 0 can shrink the value, the overflow already happened)
def prod_go(+w: Nat, xs: List<&2, Nat>, +acc: Nat, ok: Bool) -> Nat & Bool:
  match xs ok:
    case Nil{} _:
      (acc, ok)
    case Con{x, t} False{}:
      (acc, False{})
    case Con{+x, t} True{}:
      prod_go(w, t, Nat.mul(acc, x), fits(w, Nat.mul(acc, x)))

def lcm_go(+w: Nat, xs: List<&2, Nat>, +acc: Nat, ok: Bool) -> Nat & Bool:
  match xs ok:
    case Nil{} _:
      (acc, ok)
    case Con{x, t} False{}:
      (acc, False{})
    case Con{+x, t} True{}:
      lcm_go(w, t, M.lcm(acc, x), fits(w, M.lcm(acc, x)))

def prefix_fin(~T: Data, ~of: Nat -> T, r: Nat & Bool) -> Result<&2, &2, N.NumError, T>:
  (+n, ok) = r
  checked_pick(~T, ~of, n, ok)

# ---- integer instances (U32, U64) ----

def Gcd.agrees(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, ~of: Nat -> T, +a: T, +b: T) -> Type:
  {G.gcd(~T, ~op, ~test, a, b) == of(M.gcd(val(a), val(b))) : T}

def Lcm.checked(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, ~of: Nat -> T, +w: Nat, +a: T, +b: T) -> Type:
  {G.lcm(~T, ~op, ~test, a, b) == checked(~T, ~of, w, M.lcm(val(a), val(b))) : Result<&2, &2, N.NumError, T>}

def GcdAll.agrees(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, ~of: Nat -> T, xs: List<&2, T>) -> Type:
  {G.gcd_all(~T, ~op, ~test, xs) == of(M.gcd_all(vals(~T, ~val, xs))) : T}

def LcmAll.checked(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, ~of: Nat -> T, +w: Nat, xs: List<&2, T>) -> Type:
  {G.lcm_all(~T, ~op, ~test, xs) == prefix_fin(~T, ~of, lcm_go(w, vals(~T, ~val, xs), 1n, True{})) : Result<&2, &2, N.NumError, T>}

def Isqrt.agrees(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, ~of: Nat -> T, +n: T) -> Type:
  {G.isqrt(~T, ~op, ~test, n) == of(M.isqrt(val(n))) : T}

def Iroot.agrees(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, ~of: Nat -> T, +n: T, +k: Nat) -> Type:
  {G.iroot(~T, ~op, ~test, n, k) == lift(~T, ~of, M.iroot(val(n), k)) : Result<&2, &2, N.NumError, T>}

def Ilog.agrees(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, +n: T, +b: T) -> Type:
  {G.ilog(~T, ~op, ~test, n, b) == lift_nat(M.ilog(val(n), val(b))) : Result<&2, &2, N.NumError, Nat>}

def Factorial.checked(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, ~of: Nat -> T, +w: Nat, +n: T) -> Type:
  {G.factorial(~T, ~op, ~test, n) == checked(~T, ~of, w, M.factorial(val(n))) : Result<&2, &2, N.NumError, T>}

def Perm.checked(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, ~of: Nat -> T, +w: Nat, +n: T, +k: T) -> Type:
  {G.perm(~T, ~op, ~test, n, k) == checked(~T, ~of, w, M.perm(val(n), val(k))) : Result<&2, &2, N.NumError, T>}

def Comb.checked(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, ~of: Nat -> T, +w: Nat, +n: T, +k: T) -> Type:
  {G.comb(~T, ~op, ~test, n, k) == checked(~T, ~of, w, M.comb(val(n), val(k))) : Result<&2, &2, N.NumError, T>}

def PowMod.agrees(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, ~of: Nat -> T, +b: T, +e: T, +m: T) -> Type:
  {G.pow_mod(~T, ~op, ~test, b, e, m) == lift(~T, ~of, M.pow_mod(val(b), val(e), val(m))) : Result<&2, &2, N.NumError, T>}

def ModInverse.agrees(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, ~of: Nat -> T, +a: T, +m: T) -> Type:
  {G.mod_inverse(~T, ~op, ~test, a, m) == lift(~T, ~of, M.mod_inverse(val(a), val(m))) : Result<&2, &2, N.NumError, T>}

def DivMod.agrees(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, ~of: Nat -> T, +a: T, +b: T) -> Type:
  {G.divmod(~T, ~op, ~test, a, b) == lift_qr(~T, ~of, M.divmod(val(a), val(b))) : Result<&2, &2, N.NumError, G.QuotRem<T>>}

def BitLength.agrees(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, +n: T) -> Type:
  {G.bit_length(~T, ~op, ~test, n) == M.bit_length(val(n)) : Nat}

def Clamp.agrees(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, ~of: Nat -> T, +x: T, +lo: T, +hi: T) -> Type:
  {G.clamp(~T, ~op, ~test, x, lo, hi) == lift(~T, ~of, M.clamp(val(x), val(lo), val(hi))) : Result<&2, &2, N.NumError, T>}

def Min.agrees(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, ~of: Nat -> T, +a: T, +b: T) -> Type:
  {G.min(~T, ~op, ~test, a, b) == of(Nat.min(val(a), val(b))) : T}

def Max.agrees(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, ~of: Nat -> T, +a: T, +b: T) -> Type:
  {G.max(~T, ~op, ~test, a, b) == of(Nat.max(val(a), val(b))) : T}

# unsigned: |x| is x
def Abs.identity(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +x: T) -> Type:
  {G.abs(~T, ~op, ~test, x) == x : T}

# unsigned: 1 above zero, else 0
def Sign.agrees(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, ~of: Nat -> T, +x: T) -> Type:
  {G.sign(~T, ~op, ~test, x) == of(Nat.min(val(x), 1n)) : T}

# the partial sums only grow, so the sum overflows exactly when the total does
def Sum.checked(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, ~of: Nat -> T, +w: Nat, xs: List<&2, T>) -> Type:
  {G.sum(~T, ~op, ~test, xs) == checked(~T, ~of, w, NS.lsum(vals(~T, ~val, xs))) : Result<&2, &2, N.NumError, T>}

def Prod.checked(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, ~of: Nat -> T, +w: Nat, xs: List<&2, T>) -> Type:
  {G.prod(~T, ~op, ~test, xs) == prefix_fin(~T, ~of, prod_go(w, vals(~T, ~val, xs), 1n, True{})) : Result<&2, &2, N.NumError, T>}

def Pow.checked(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, ~of: Nat -> T, +w: Nat, +x: T, +k: Nat) -> Type:
  {G.pow(~T, ~op, ~test, x, k) == checked(~T, ~of, w, Nat.pow(val(x), k)) : Result<&2, &2, N.NumError, T>}

# ---- float instances (F32, F64): the instance's own IEEE operations ----
# (F32's are Base's primitives; F64's are src/math/f64.bend's, specified by
# spec/math/f64.bend)

def FMin.select(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +a: T, +b: T) -> Type:
  {G.min(~T, ~op, ~test, a, b) == pick(T, test(N.Lt{b, a}), b, a) : T}

def FMax.select(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +a: T, +b: T) -> Type:
  {G.max(~T, ~op, ~test, a, b) == pick(T, test(N.Lt{a, b}), b, a) : T}

def fclamp_pick(~T: Data, ~test: N.Test<T> -> Bool, +x: T, +lo: T, +hi: T, bad: Bool) -> Result<&2, &2, N.NumError, T>:
  match bad:
    case True{}:
      Fail{N.BadDomain{}}
    case False{}:
      Done{pick(T, test(N.Lt{hi, pick(T, test(N.Lt{x, lo}), lo, x)}), hi, pick(T, test(N.Lt{x, lo}), lo, x))}

# Domain when hi < lo; else min(max(x, lo), hi) by the two selections
def FClamp.select(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +x: T, +lo: T, +hi: T) -> Type:
  {G.clamp(~T, ~op, ~test, x, lo, hi) == fclamp_pick(~T, ~test, x, lo, hi, test(N.Lt{hi, lo})) : Result<&2, &2, N.NumError, T>}

def FAbs.value(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +x: T) -> Type:
  {G.abs(~T, ~op, ~test, x) == op(N.Abs{x}) : T}

# 1 above zero, -1 below, x itself otherwise (zeros keep their sign, NaN stays)
def FSign.select(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +x: T) -> Type:
  {G.sign(~T, ~op, ~test, x) == pick(T, test(N.Lt{op(N.ZeroOp{}), x}), op(N.One{}), pick(T, test(N.Lt{x, op(N.ZeroOp{})}), op(N.Neg{op(N.One{})}), x)) : T}

def fold_add(~T: Data, ~op: N.Op<T> -> T, xs: List<&2, T>, +acc: T) -> T:
  match xs:
    case Nil{}:
      acc
    case Con{+x, t}:
      fold_add(~T, ~op, t, op(N.Add{acc, x}))

def fold_mul(~T: Data, ~op: N.Op<T> -> T, xs: List<&2, T>, +acc: T) -> T:
  match xs:
    case Nil{}:
      acc
    case Con{+x, t}:
      fold_mul(~T, ~op, t, op(N.Mul{acc, x}))

# ((0 + x0) + x1) + ..., every addition rounded
def FSum.fold(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, xs: List<&2, T>) -> Type:
  {G.sum(~T, ~op, ~test, xs) == Done{fold_add(~T, ~op, xs, op(N.ZeroOp{}))} : Result<&2, &2, N.NumError, T>}

def FProd.fold(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, xs: List<&2, T>) -> Type:
  {G.prod(~T, ~op, ~test, xs) == Done{fold_mul(~T, ~op, xs, op(N.One{}))} : Result<&2, &2, N.NumError, T>}

# right-to-left binary exponentiation: acc *= base on a 1 bit, base *= base
# while bits remain, each product rounded (k = 0 is a fixed point, so any
# fuel past k's bit length gives the same result)
def binpow(~T: Data, ~op: N.Op<T> -> T, fuel: Nat, +k: Nat, +base: T, +acc: T) -> T:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      binpow(~T, ~op, f, Nat.div(k, 2n), pick(T, Nat.is_lt(1n, k), op(N.Mul{base, base}), base), pick(T, Nat.is_eq(Nat.mod(k, 2n), 1n), op(N.Mul{acc, base}), acc))

def FPow.binary(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +x: T, +k: Nat) -> Type:
  {G.pow(~T, ~op, ~test, x, k) == Done{binpow(~T, ~op, 1n+k, k, x, op(N.One{}))} : Result<&2, &2, N.NumError, T>}

# ---- instance models ----
# U32: the value and the U32 of a value below 2^32 (width 32)
def u32_val(x: U32) -> Nat:
  U32.to_nat(x)

def u32_of(n: Nat) -> U32:
  U32.from_nat(n)

# U64: the two-limb value and the U64 of a value below 2^64 (width 64)
def u64_val(x: W.U64) -> Nat:
  SW.value(x)

def u64_of(n: Nat) -> W.U64:
  SW.of_nat(n)
