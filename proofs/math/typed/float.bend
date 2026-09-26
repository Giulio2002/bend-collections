import Base
import ../../../spec/math/generic.bend as SG
import ../../../src/math/generic.bend as G
import ../../../src/math/num.bend as N
import ../../../src/math/instances.bend as I
import ../../../src/math/f64.bend as F

# The float clauses of spec/math/generic.bend (FMin.select, FMax.select,
# FClamp.select, FAbs.value, FSign.select, FSum.fold, FProd.fold,
# FPow.binary), proved once for every instance whose over-tests are False
# and then read at F32 (Base's primitives) and F64 (src/math/f64.bend).
#
# The clauses say how each generic function combines the instance's own
# operations (which operation, on which arguments, in which order); they do
# not depend on what the operations compute, so they hold for any
# operations, IEEE's included. This is the parametric style of Mathlib's
# lemmas over a structure (Mathlib.Algebra.Order.*: statements over any
# LinearOrder / ring, instantiated per type), and of the "free theorems"
# of parametric polymorphism (Wadler, Theorems for free!, 1989).

# the instance never reports an overflow (floats round instead)
def NoAddOver(~T: Data, ~test: N.Test<T> -> Bool) -> Type:
  @+a: T -> @+b: T -> {test(N.AddOver{a, b}) == False{} : Bool}

def NoMulOver(~T: Data, ~test: N.Test<T> -> Bool) -> Type:
  @+a: T -> @+b: T -> {test(N.MulOver{a, b}) == False{} : Bool}

# ---- selections: the two picks agree ----

def pick_eq(-T: Data, +c: Bool, +a: T, +b: T) -> {G.pick(T, c, a, b) == SG.pick(T, c, a, b) : T}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def fmin_select(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +a: T, +b: T) -> SG.FMin.select(~T, ~op, ~test, a, b):
  pick_eq(T, test(N.Lt{b, a}), b, a)

def fmax_select(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +a: T, +b: T) -> SG.FMax.select(~T, ~op, ~test, a, b):
  pick_eq(T, test(N.Lt{a, b}), b, a)

def fclamp_c(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +x: T, +lo: T, +hi: T, +c: Bool) -> {G.clamp_ok(~T, ~op, ~test, x, lo, hi, c) == SG.fclamp_pick(~T, ~test, x, lo, hi, c) : Result<&2, &2, N.NumError, T>}:
  match c:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(T, G.pick(T, test(N.Lt{x, lo}), lo, x), SG.pick(T, test(N.Lt{x, lo}), lo, x), pick_eq(T, test(N.Lt{x, lo}), lo, x)) : {Done{G.pick(T, test(N.Lt{hi, _}), hi, _)} == Done{SG.pick(T, test(N.Lt{hi, SG.pick(T, test(N.Lt{x, lo}), lo, x)}), hi, SG.pick(T, test(N.Lt{x, lo}), lo, x))} : Result<&2, &2, N.NumError, T>}
      %Equal.sym(T, G.pick(T, test(N.Lt{hi, SG.pick(T, test(N.Lt{x, lo}), lo, x)}), hi, SG.pick(T, test(N.Lt{x, lo}), lo, x)), SG.pick(T, test(N.Lt{hi, SG.pick(T, test(N.Lt{x, lo}), lo, x)}), hi, SG.pick(T, test(N.Lt{x, lo}), lo, x)), pick_eq(T, test(N.Lt{hi, SG.pick(T, test(N.Lt{x, lo}), lo, x)}), hi, SG.pick(T, test(N.Lt{x, lo}), lo, x))) : {Done{_} == Done{SG.pick(T, test(N.Lt{hi, SG.pick(T, test(N.Lt{x, lo}), lo, x)}), hi, SG.pick(T, test(N.Lt{x, lo}), lo, x))} : Result<&2, &2, N.NumError, T>}
      {==}

def fclamp_select(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +x: T, +lo: T, +hi: T) -> SG.FClamp.select(~T, ~op, ~test, x, lo, hi):
  fclamp_c(~T, ~op, ~test, x, lo, hi, test(N.Lt{hi, lo}))

def fabs_value(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +x: T) -> SG.FAbs.value(~T, ~op, ~test, x):
  {==}

def sign_b(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +x: T, +c: Bool) -> {G.sign_below(~T, ~op, ~test, x, c) == SG.pick(T, c, op(N.Neg{op(N.One{})}), x) : T}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def sign_a(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +x: T, +c: Bool) -> {G.sign_above(~T, ~op, ~test, x, c) == SG.pick(T, c, op(N.One{}), SG.pick(T, test(N.Lt{x, op(N.ZeroOp{})}), op(N.Neg{op(N.One{})}), x)) : T}:
  match c:
    case True{}:
      {==}
    case False{}:
      sign_b(~T, ~op, ~test, x, test(N.Lt{x, op(N.ZeroOp{})}))

def fsign_select(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +x: T) -> SG.FSign.select(~T, ~op, ~test, x):
  sign_a(~T, ~op, ~test, x, test(N.Lt{op(N.ZeroOp{}), x}))

# ---- folds: with no overflow the checked fold is the plain fold ----

def sum_fold(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~ao: NoAddOver(~T, ~test), xs: List<&2, T>, +acc: T) -> {G.sum_go(~T, ~op, ~test, xs, Some{acc}) == Some{SG.fold_add(~T, ~op, xs, acc)} : Maybe<&2, T>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      %Equal.sym(Bool, test(N.AddOver{acc, x}), False{}, ao(acc, x)) : {G.sum_go(~T, ~op, ~test, t, G.fits(T, _, op(N.Add{acc, x}))) == Some{SG.fold_add(~T, ~op, t, op(N.Add{acc, x}))} : Maybe<&2, T>}
      sum_fold(~T, ~op, ~test, ~ao, t, op(N.Add{acc, x}))

def fsum_fold(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~ao: NoAddOver(~T, ~test), xs: List<&2, T>) -> SG.FSum.fold(~T, ~op, ~test, xs):
  %Equal.sym(Maybe<&2, T>, G.sum_go(~T, ~op, ~test, xs, Some{op(N.ZeroOp{})}), Some{SG.fold_add(~T, ~op, xs, op(N.ZeroOp{}))}, sum_fold(~T, ~op, ~test, ~ao, xs, op(N.ZeroOp{}))) : {G.ok(T, _) == Done{SG.fold_add(~T, ~op, xs, op(N.ZeroOp{}))} : Result<&2, &2, N.NumError, T>}
  {==}

def prod_fold(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~mo: NoMulOver(~T, ~test), xs: List<&2, T>, +acc: T) -> {G.prod_go(~T, ~op, ~test, xs, Some{acc}) == Some{SG.fold_mul(~T, ~op, xs, acc)} : Maybe<&2, T>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      %Equal.sym(Bool, test(N.MulOver{acc, x}), False{}, mo(acc, x)) : {G.prod_go(~T, ~op, ~test, t, G.fits(T, _, op(N.Mul{acc, x}))) == Some{SG.fold_mul(~T, ~op, t, op(N.Mul{acc, x}))} : Maybe<&2, T>}
      prod_fold(~T, ~op, ~test, ~mo, t, op(N.Mul{acc, x}))

def fprod_fold(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~mo: NoMulOver(~T, ~test), xs: List<&2, T>) -> SG.FProd.fold(~T, ~op, ~test, xs):
  %Equal.sym(Maybe<&2, T>, G.prod_go(~T, ~op, ~test, xs, Some{op(N.One{})}), Some{SG.fold_mul(~T, ~op, xs, op(N.One{}))}, prod_fold(~T, ~op, ~test, ~mo, xs, op(N.One{}))) : {G.ok(T, _) == Done{SG.fold_mul(~T, ~op, xs, op(N.One{}))} : Result<&2, &2, N.NumError, T>}
  {==}

# ---- pow: square-and-multiply is the specification's binary exponentiation ----

# k = 0 is a fixed point of the specification's loop
def binpow_zero(~T: Data, ~op: N.Op<T> -> T, fuel: Nat, +b: T, +a: T) -> {SG.binpow(~T, ~op, fuel, 0n, b, a) == a : T}:
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      binpow_zero(~T, ~op, f, b, a)

def sq_val_eq(~T: Data, ~op: N.Op<T> -> T, +c: Bool, +b: T) -> {G.sq_val(~T, ~op, c, b) == SG.pick(T, c, op(N.Mul{b, b}), b) : T}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def sq_ok_eq(~T: Data, ~test: N.Test<T> -> Bool, ~mo: NoMulOver(~T, ~test), +c: Bool, +b: T) -> {G.sq_ok(~T, ~test, c, b, True{}) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, test(N.MulOver{b, b}), False{}, mo(b, b)) : {Bool.and(True{}, Bool.not(_)) == True{} : Bool}
      {==}
    case False{}:
      {==}

def mul_st_eq(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~mo: NoMulOver(~T, ~test), +d: Bool, +b: T, +a: T) -> {G.mul_st(~T, ~op, ~test, d, b, True{}, (a, True{})) == (SG.pick(T, d, op(N.Mul{a, b}), a), True{}) : T & Bool}:
  match d:
    case True{}:
      %Equal.sym(Bool, test(N.MulOver{a, b}), False{}, mo(a, b)) : {(op(N.Mul{a, b}), Bool.and(Bool.and(True{}, True{}), Bool.not(_))) == (op(N.Mul{a, b}), True{}) : T & Bool}
      {==}
    case False{}:
      {==}

def pow_bin(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~mo: NoMulOver(~T, ~test), +fuel: Nat, +k: Nat, +b: T, +a: T) -> {G.pow_go(~T, ~op, ~test, fuel, k, b, True{}, (a, True{})) == Some{SG.binpow(~T, ~op, fuel, k, b, a)} : Maybe<&2, T>}:
  match fuel k:
    case 0n _:
      {==}
    case 1n+ +f 0n:
      %Equal.sym(T, SG.binpow(~T, ~op, f, 0n, b, a), a, binpow_zero(~T, ~op, f, b, a)) : {Some{a} == Some{_} : Maybe<&2, T>}
      {==}
    case 1n+ +f 1n+ +j:
      %Equal.sym(T & Bool, G.mul_st(~T, ~op, ~test, Nat.is_eq(Nat.mod(1n+j, 2n), 1n), b, True{}, (a, True{})), (SG.pick(T, Nat.is_eq(Nat.mod(1n+j, 2n), 1n), op(N.Mul{a, b}), a), True{}), mul_st_eq(~T, ~op, ~test, ~mo, Nat.is_eq(Nat.mod(1n+j, 2n), 1n), b, a)) : {G.pow_go(~T, ~op, ~test, f, Nat.div(1n+j, 2n), G.sq_val(~T, ~op, Nat.is_lt(1n, 1n+j), b), G.sq_ok(~T, ~test, Nat.is_lt(1n, 1n+j), b, True{}), _) == Some{SG.binpow(~T, ~op, f, Nat.div(1n+j, 2n), SG.pick(T, Nat.is_lt(1n, 1n+j), op(N.Mul{b, b}), b), SG.pick(T, Nat.is_eq(Nat.mod(1n+j, 2n), 1n), op(N.Mul{a, b}), a))} : Maybe<&2, T>}
      %Equal.sym(Bool, G.sq_ok(~T, ~test, Nat.is_lt(1n, 1n+j), b, True{}), True{}, sq_ok_eq(~T, ~test, ~mo, Nat.is_lt(1n, 1n+j), b)) : {G.pow_go(~T, ~op, ~test, f, Nat.div(1n+j, 2n), G.sq_val(~T, ~op, Nat.is_lt(1n, 1n+j), b), _, (SG.pick(T, Nat.is_eq(Nat.mod(1n+j, 2n), 1n), op(N.Mul{a, b}), a), True{})) == Some{SG.binpow(~T, ~op, f, Nat.div(1n+j, 2n), SG.pick(T, Nat.is_lt(1n, 1n+j), op(N.Mul{b, b}), b), SG.pick(T, Nat.is_eq(Nat.mod(1n+j, 2n), 1n), op(N.Mul{a, b}), a))} : Maybe<&2, T>}
      %Equal.sym(T, G.sq_val(~T, ~op, Nat.is_lt(1n, 1n+j), b), SG.pick(T, Nat.is_lt(1n, 1n+j), op(N.Mul{b, b}), b), sq_val_eq(~T, ~op, Nat.is_lt(1n, 1n+j), b)) : {G.pow_go(~T, ~op, ~test, f, Nat.div(1n+j, 2n), _, True{}, (SG.pick(T, Nat.is_eq(Nat.mod(1n+j, 2n), 1n), op(N.Mul{a, b}), a), True{})) == Some{SG.binpow(~T, ~op, f, Nat.div(1n+j, 2n), SG.pick(T, Nat.is_lt(1n, 1n+j), op(N.Mul{b, b}), b), SG.pick(T, Nat.is_eq(Nat.mod(1n+j, 2n), 1n), op(N.Mul{a, b}), a))} : Maybe<&2, T>}
      pow_bin(~T, ~op, ~test, ~mo, f, Nat.div(1n+j, 2n), SG.pick(T, Nat.is_lt(1n, 1n+j), op(N.Mul{b, b}), b), SG.pick(T, Nat.is_eq(Nat.mod(1n+j, 2n), 1n), op(N.Mul{a, b}), a))

def fpow_binary(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~mo: NoMulOver(~T, ~test), +x: T, +k: Nat) -> SG.FPow.binary(~T, ~op, ~test, x, k):
  %Equal.sym(Maybe<&2, T>, G.pow_go(~T, ~op, ~test, 1n+k, k, x, True{}, (op(N.One{}), True{})), Some{SG.binpow(~T, ~op, 1n+k, k, x, op(N.One{}))}, pow_bin(~T, ~op, ~test, ~mo, 1n+k, k, x, op(N.One{}))) : {G.ok(T, _) == Done{SG.binpow(~T, ~op, 1n+k, k, x, op(N.One{}))} : Result<&2, &2, N.NumError, T>}
  {==}

# ---- F32 and F64: the over-tests are False ----

def f32_ao(+a: F32, +b: F32) -> {I.f32_is(N.AddOver{a, b}) == False{} : Bool}:
  {==}

def f32_mo(+a: F32, +b: F32) -> {I.f32_is(N.MulOver{a, b}) == False{} : Bool}:
  {==}

def f64_ao(+a: F.F64, +b: F.F64) -> {F.f64_is(N.AddOver{a, b}) == False{} : Bool}:
  {==}

def f64_mo(+a: F.F64, +b: F.F64) -> {F.f64_is(N.MulOver{a, b}) == False{} : Bool}:
  {==}

def f32_min(+a: F32, +b: F32) -> SG.FMin.select(~F32, ~I.f32_op, ~I.f32_is, a, b):
  fmin_select(~F32, ~I.f32_op, ~I.f32_is, a, b)

def f32_max(+a: F32, +b: F32) -> SG.FMax.select(~F32, ~I.f32_op, ~I.f32_is, a, b):
  fmax_select(~F32, ~I.f32_op, ~I.f32_is, a, b)

def f32_clamp(+x: F32, +lo: F32, +hi: F32) -> SG.FClamp.select(~F32, ~I.f32_op, ~I.f32_is, x, lo, hi):
  fclamp_select(~F32, ~I.f32_op, ~I.f32_is, x, lo, hi)

def f32_abs(+x: F32) -> SG.FAbs.value(~F32, ~I.f32_op, ~I.f32_is, x):
  fabs_value(~F32, ~I.f32_op, ~I.f32_is, x)

def f32_sign(+x: F32) -> SG.FSign.select(~F32, ~I.f32_op, ~I.f32_is, x):
  fsign_select(~F32, ~I.f32_op, ~I.f32_is, x)

def f32_sum(xs: List<&2, F32>) -> SG.FSum.fold(~F32, ~I.f32_op, ~I.f32_is, xs):
  fsum_fold(~F32, ~I.f32_op, ~I.f32_is, ~(a => b => f32_ao(a, b)), xs)

def f32_prod(xs: List<&2, F32>) -> SG.FProd.fold(~F32, ~I.f32_op, ~I.f32_is, xs):
  fprod_fold(~F32, ~I.f32_op, ~I.f32_is, ~(a => b => f32_mo(a, b)), xs)

def f32_pow(+x: F32, +k: Nat) -> SG.FPow.binary(~F32, ~I.f32_op, ~I.f32_is, x, k):
  fpow_binary(~F32, ~I.f32_op, ~I.f32_is, ~(a => b => f32_mo(a, b)), x, k)

def f64_min(+a: F.F64, +b: F.F64) -> SG.FMin.select(~F.F64, ~F.f64_op, ~F.f64_is, a, b):
  fmin_select(~F.F64, ~F.f64_op, ~F.f64_is, a, b)

def f64_max(+a: F.F64, +b: F.F64) -> SG.FMax.select(~F.F64, ~F.f64_op, ~F.f64_is, a, b):
  fmax_select(~F.F64, ~F.f64_op, ~F.f64_is, a, b)

def f64_clamp(+x: F.F64, +lo: F.F64, +hi: F.F64) -> SG.FClamp.select(~F.F64, ~F.f64_op, ~F.f64_is, x, lo, hi):
  fclamp_select(~F.F64, ~F.f64_op, ~F.f64_is, x, lo, hi)

def f64_abs(+x: F.F64) -> SG.FAbs.value(~F.F64, ~F.f64_op, ~F.f64_is, x):
  fabs_value(~F.F64, ~F.f64_op, ~F.f64_is, x)

def f64_sign(+x: F.F64) -> SG.FSign.select(~F.F64, ~F.f64_op, ~F.f64_is, x):
  fsign_select(~F.F64, ~F.f64_op, ~F.f64_is, x)

def f64_sum(xs: List<&2, F.F64>) -> SG.FSum.fold(~F.F64, ~F.f64_op, ~F.f64_is, xs):
  fsum_fold(~F.F64, ~F.f64_op, ~F.f64_is, ~(a => b => f64_ao(a, b)), xs)

def f64_prod(xs: List<&2, F.F64>) -> SG.FProd.fold(~F.F64, ~F.f64_op, ~F.f64_is, xs):
  fprod_fold(~F.F64, ~F.f64_op, ~F.f64_is, ~(a => b => f64_mo(a, b)), xs)

def f64_pow(+x: F.F64, +k: Nat) -> SG.FPow.binary(~F.F64, ~F.f64_op, ~F.f64_is, x, k):
  fpow_binary(~F.F64, ~F.f64_op, ~F.f64_is, ~(a => b => f64_mo(a, b)), x, k)
