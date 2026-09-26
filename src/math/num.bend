import Base

# The numeric interface of the generic math (generic.bend). A type T takes
# part through two functions, passed as templates next to T:
#
#   ~op: Op<T> -> T      its arithmetic, one constructor per operation
#   ~test: Test<T> -> Bool its comparisons and overflow tests
#
#   G.gcd(~U32, ~I.u32_op, ~I.u32_is, a, b)
#
# Templates are substituted at compile time and the match on the operation's
# constructor is resolved there, so every call compiles to the instance's
# native code (a record of functions would be called through closures at run
# time, about 5x slower).
#
# Fixed widths are checked: Add, Sub and Mul are only formed after the
# matching test (AddOver, Lt, MulOver) said the result fits. For floats the
# over-tests are False and the operations are IEEE's.
#
#   Zero, One          constants
#   Add, Sub, Mul      a + b, a - b (b <= a for unsigned), a * b
#   Neg, Abs           -a (floats), |a|
#   Quot, Rem          a / b, a mod b (unsigned, b != 0)
#   Half               a / 2
#   MulMod             a * b mod m for a, b < m (never overflows)
#   Pow2               2^k, for 2^k below the width
#   Sqrt               the integer square root (instances may use hardware)
#   Lt, AddOver, MulOver, Odd, IsZero
#
# Errors are values, as in natural.bend, with Overflow for results that do
# not fit a fixed width (design reference section 2.6: checked results).

type NumError is Data:
  DivByZero{}
  BadDomain{}
  NoInverse{}
  Overflow{}

type Op<-T: Data> is Data:
  ZeroOp{}
  One{}
  Add{a: T, b: T}
  Sub{a: T, b: T}
  Mul{a: T, b: T}
  Neg{a: T}
  Abs{a: T}
  Quot{a: T, b: T}
  Rem{a: T, b: T}
  Half{a: T}
  MulMod{a: T, b: T, m: T}
  Pow2{k: Nat}
  Sqrt{a: T}

type Test<-T: Data> is Data:
  Lt{a: T, b: T}
  AddOver{a: T, b: T}
  MulOver{a: T, b: T}
  Odd{a: T}
  IsZero{a: T}
