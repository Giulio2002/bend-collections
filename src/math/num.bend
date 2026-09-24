import Base

# Numeric interfaces for the generic math of generic.bend. A generic
# function takes its type and interface as templates (~T, ~num), so each
# instance compiles to its own copy with the operations inlined.
#
#   Arith<T>     an ordered set with ring-like arithmetic: add, sub, mul and
#                neg return None when the result does not fit (fixed-width
#                integers) and never fail for floats; lt is the order (for
#                floats IEEE <, false on NaN); abs is the type's absolute
#                value (floats clear the sign bit, so abs(-0.0) == 0.0).
#   Integer<T>   Arith plus Euclidean division (divmod(a, b) for b != 0),
#                from_nat (None past the width), the bit width, which
#                bounds every loop (fuel), halving and parity (shr1, odd)
#                and mulmod(a, b, m) = a * b mod m for a, b < m, which
#                never overflows (instances compute it exactly).
#
# Errors are values, as in natural.bend, with Overflow for results that do
# not fit a fixed width (design reference section 2.6: checked results).

type NumError is Data:
  ZeroDivision{}
  Domain{}
  NotInvertible{}
  Overflow{}

type Arith<-T: Data> is Type:
  Arith{zero: T, one: T, add: T -> T -> Maybe<&2, T>, sub: T -> T -> Maybe<&2, T>, mul: T -> T -> Maybe<&2, T>, neg: T -> Maybe<&2, T>, lt: T -> T -> Bool, abs: T -> T}

type Integer<-T: Data> is Type:
  Integer{ar: Arith<T>, divmod: T -> T -> T & T, from_nat: Nat -> Maybe<&2, T>, width: Nat, shr1: T -> T, odd: T -> Bool, mulmod: T -> T -> T -> T}

# ---- accessors ----

def zero(-T: Data, a: Arith<T>) -> T:
  match a:
    case Arith{z, o, ad, sb, ml, ng, lt, ab}:
      z

def one(-T: Data, a: Arith<T>) -> T:
  match a:
    case Arith{z, o, ad, sb, ml, ng, lt, ab}:
      o

def add(-T: Data, a: Arith<T>, x: T, y: T) -> Maybe<&2, T>:
  match a:
    case Arith{z, o, ad, sb, ml, ng, lt, ab}:
      ad(x, y)

def sub(-T: Data, a: Arith<T>, x: T, y: T) -> Maybe<&2, T>:
  match a:
    case Arith{z, o, ad, sb, ml, ng, lt, ab}:
      sb(x, y)

def mul(-T: Data, a: Arith<T>, x: T, y: T) -> Maybe<&2, T>:
  match a:
    case Arith{z, o, ad, sb, ml, ng, lt, ab}:
      ml(x, y)

def neg(-T: Data, a: Arith<T>, x: T) -> Maybe<&2, T>:
  match a:
    case Arith{z, o, ad, sb, ml, ng, lt, ab}:
      ng(x)

def lt(-T: Data, a: Arith<T>, x: T, y: T) -> Bool:
  match a:
    case Arith{z, o, ad, sb, ml, ng, lt, ab}:
      lt(x, y)

def abs(-T: Data, a: Arith<T>, x: T) -> T:
  match a:
    case Arith{z, o, ad, sb, ml, ng, lt, ab}:
      ab(x)

def ar(-T: Data, i: Integer<T>) -> Arith<T>:
  match i:
    case Integer{a, dm, fn, w, h, o, mm}:
      a

def divmod(-T: Data, i: Integer<T>, x: T, y: T) -> T & T:
  match i:
    case Integer{a, dm, fn, w, h, o, mm}:
      dm(x, y)

def from_nat(-T: Data, i: Integer<T>, n: Nat) -> Maybe<&2, T>:
  match i:
    case Integer{a, dm, fn, w, h, o, mm}:
      fn(n)

def width(-T: Data, i: Integer<T>) -> Nat:
  match i:
    case Integer{a, dm, fn, w, h, o, mm}:
      w

def shr1(-T: Data, i: Integer<T>, x: T) -> T:
  match i:
    case Integer{a, dm, fn, w, h, o, mm}:
      h(x)

def odd(-T: Data, i: Integer<T>, x: T) -> Bool:
  match i:
    case Integer{a, dm, fn, w, h, o, mm}:
      o(x)

def mulmod(-T: Data, i: Integer<T>, x: T, y: T, m: T) -> T:
  match i:
    case Integer{a, dm, fn, w, h, o, mm}:
      mm(x, y, m)
