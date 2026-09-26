import Base
import ../lib/common.bend as C
import ../../src/math/num.bend as N
import ../../src/math/natural.bend as M

# Specification of src/math/num.bend's interface and of the instances in
# src/math/instances.bend (and f64.bend's): what each Op and Test must
# compute for the generic functions (spec/math/generic.bend) to meet their
# contracts. num.bend itself is the interface's types; its laws are these.
#
# Integer instances (U32 with width 32, U64 with width 64; val as in
# spec/math/generic.bend): every operation is the Nat operation on the
# values, formed only where it fits (generic.bend asks AddOver or MulOver
# first, and forms Sub, Quot, Rem, MulMod under their preconditions).
#
# Float instances (F32: Base's F32 primitives, F64: src/math/f64.bend's,
# specified by spec/math/f64.bend): Add, Sub, Mul, Quot, Neg, Abs are the
# IEEE operations of the type, Lt the IEEE order (false on NaN), and the
# over-tests are False (floats round instead of overflowing).
#
# STATED, TESTED, NOT PROVED: exercised through every generic function by
# tools/check_generic.py and at U32 by the checker-evaluated examples of
# proofs/math/typed/examples.bend.
#
#   Op / Test    clauses
#   Zero, One    Ops.zero, Ops.one
#   Add          Ops.add, Tests.add_over
#   Sub          Ops.sub
#   Mul          Ops.mul, Tests.mul_over
#   Quot, Rem    Ops.quot, Ops.rem
#   Half         Ops.half
#   MulMod       Ops.mulmod
#   Pow2         Ops.pow2
#   Sqrt         Ops.sqrt
#   Abs          Ops.abs
#   Lt, Odd,     Tests.lt, Tests.odd, Tests.is_zero
#   IsZero

def Ops.zero(~T: Data, ~op: N.Op<T> -> T, ~val: T -> Nat) -> Type:
  {val(op(N.ZeroOp{})) == 0n : Nat}

def Ops.one(~T: Data, ~op: N.Op<T> -> T, ~val: T -> Nat) -> Type:
  {val(op(N.One{})) == 1n : Nat}

def Ops.add(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, +a: T, +b: T, +h: {test(N.AddOver{a, b}) == False{} : Bool}) -> Type:
  {val(op(N.Add{a, b})) == Nat.add(val(a), val(b)) : Nat}

def Tests.add_over(~T: Data, ~test: N.Test<T> -> Bool, ~val: T -> Nat, +w: Nat, +a: T, +b: T) -> Type:
  {test(N.AddOver{a, b}) == Bool.not(C.fits(w, Nat.add(val(a), val(b)))) : Bool}

def Ops.sub(~T: Data, ~op: N.Op<T> -> T, ~val: T -> Nat, +a: T, +b: T, +h: {Nat.is_le(val(b), val(a)) == True{} : Bool}) -> Type:
  {val(op(N.Sub{a, b})) == Nat.sub(val(a), val(b)) : Nat}

def Ops.mul(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~val: T -> Nat, +a: T, +b: T, +h: {test(N.MulOver{a, b}) == False{} : Bool}) -> Type:
  {val(op(N.Mul{a, b})) == Nat.mul(val(a), val(b)) : Nat}

def Tests.mul_over(~T: Data, ~test: N.Test<T> -> Bool, ~val: T -> Nat, +w: Nat, +a: T, +b: T) -> Type:
  {test(N.MulOver{a, b}) == Bool.not(C.fits(w, Nat.mul(val(a), val(b)))) : Bool}

def Ops.quot(~T: Data, ~op: N.Op<T> -> T, ~val: T -> Nat, +a: T, +b: T, +h: {Nat.is_eq(val(b), 0n) == False{} : Bool}) -> Type:
  {val(op(N.Quot{a, b})) == Nat.div(val(a), val(b)) : Nat}

def Ops.rem(~T: Data, ~op: N.Op<T> -> T, ~val: T -> Nat, +a: T, +b: T, +h: {Nat.is_eq(val(b), 0n) == False{} : Bool}) -> Type:
  {val(op(N.Rem{a, b})) == Nat.mod(val(a), val(b)) : Nat}

def Ops.half(~T: Data, ~op: N.Op<T> -> T, ~val: T -> Nat, +a: T) -> Type:
  {val(op(N.Half{a})) == Nat.div(val(a), 2n) : Nat}

def Ops.mulmod(~T: Data, ~op: N.Op<T> -> T, ~val: T -> Nat, +a: T, +b: T, +m: T, +ha: {Nat.is_lt(val(a), val(m)) == True{} : Bool}, +hb: {Nat.is_lt(val(b), val(m)) == True{} : Bool}) -> Type:
  {val(op(N.MulMod{a, b, m})) == Nat.mod(Nat.mul(val(a), val(b)), val(m)) : Nat}

def Ops.pow2(~T: Data, ~op: N.Op<T> -> T, ~val: T -> Nat, +w: Nat, +k: Nat, +hk: {Nat.is_lt(k, w) == True{} : Bool}) -> Type:
  {val(op(N.Pow2{k})) == C.pow2(k) : Nat}

def Ops.sqrt(~T: Data, ~op: N.Op<T> -> T, ~val: T -> Nat, +a: T) -> Type:
  {val(op(N.Sqrt{a})) == M.isqrt(val(a)) : Nat}

# unsigned: |a| is a
def Ops.abs(~T: Data, ~op: N.Op<T> -> T, +a: T) -> Type:
  {op(N.Abs{a}) == a : T}

def Tests.lt(~T: Data, ~test: N.Test<T> -> Bool, ~val: T -> Nat, +a: T, +b: T) -> Type:
  {test(N.Lt{a, b}) == Nat.is_lt(val(a), val(b)) : Bool}

def Tests.odd(~T: Data, ~test: N.Test<T> -> Bool, ~val: T -> Nat, +a: T) -> Type:
  {test(N.Odd{a}) == Nat.is_eq(Nat.mod(val(a), 2n), 1n) : Bool}

def Tests.is_zero(~T: Data, ~test: N.Test<T> -> Bool, ~val: T -> Nat, +a: T) -> Type:
  {test(N.IsZero{a}) == Nat.is_eq(val(a), 0n) : Bool}
