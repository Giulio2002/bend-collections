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
#   PowMod             a^e mod m for a < m, only formed when Mont{m} holds
#   GcdSmall           gcd(a, b), only formed when Small{a, b} holds
#   Lt, AddOver, MulOver, Odd, IsZero
#   FastDiv            True when Quot/Rem are native machine divisions, so
#                      gcd runs Euclid's algorithm; False (U64: division is
#                      software long division) picks the binary gcd, which
#                      only halves, subtracts and compares
#   Mont{m}            True when the instance computes PowMod mod m itself
#                      (U64: Montgomery multiplication for odd m in
#                      [2^32, 2^63)); False keeps the generic MulMod loop
#   Small{a, b}        True when the binary gcd should hand (a, b) to GcdSmall
#                      (U64: both below 2^48, a at least 2^16: Euclid on Nat)
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
  PowMod{a: T, e: T, m: T}
  GcdSmall{a: T, b: T}

type Test<-T: Data> is Data:
  Lt{a: T, b: T}
  AddOver{a: T, b: T}
  MulOver{a: T, b: T}
  Odd{a: T}
  IsZero{a: T}
  FastDiv{}
  Mont{m: T}
  Small{a: T, b: T}
