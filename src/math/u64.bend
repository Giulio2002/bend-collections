import Base

# 64-bit integers as two native U32 limbs (Bend 2 has no native 64-bit word).
# The same bits read as unsigned or as two's-complement signed, as in C.
#
#   zero(), of_u32(x)          construction
#   is_zero(a)                 a == 0
#   add(a, b), neg(a)          wrapping addition and negation
#   le_signed(a, b)            a <= b as signed 64-bit integers
#   div_small(a, d)            unsigned a / d, for 0 < d <= 2^20
#   div_small_signed(a, d)     signed a / d truncated toward zero, 0 < d <= 2^20

type U64 is Data:
  U64{lo: U32, hi: U32}

def zero() -> U64:
  U64{0, 0}

def of_u32(+x: U32) -> U64:
  U64{x, 0}

def is_zero(a: U64) -> Bool:
  U64{lo, hi} = a
  Bool.and(U32.is_zero(lo), U32.is_zero(hi))

def carry(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

def add_fin(+lo: U32, +alo: U32, +ahi: U32, +bhi: U32) -> U64:
  U64{lo, U32.add(U32.add(ahi, bhi), carry(U32.is_lt(lo, alo)))}

# Wrapping 64-bit addition.
def add(a: U64, b: U64) -> U64:
  U64{+alo, +ahi} = a
  U64{+blo, +bhi} = b
  add_fin(U32.add(alo, blo), alo, ahi, bhi)

def neg_fin(+lo2: U32, +hi: U32) -> U64:
  U64{lo2, U32.add(U32.not(hi), carry(U32.is_zero(lo2)))}

# Two's-complement negation.
def neg(a: U64) -> U64:
  U64{+lo, +hi} = a
  neg_fin(U32.inc(U32.not(lo)), hi)

def order(high: Cmp, low: Cmp) -> Cmp:
  match high:
    case EQ{}:
      low
    case LT{}:
      LT{}
    case GT{}:
      GT{}

def le_sign(+alo: U32, +ahi: U32, +blo: U32, +bhi: U32, negative_a: Bool, negative_b: Bool) -> Bool:
  match negative_a negative_b:
    case True{} False{}:
      True{}
    case False{} True{}:
      False{}
    case _ _:
      Cmp.is_le(order(U32.cmp(ahi, bhi), U32.cmp(alo, blo)))

# a <= b as signed 64-bit integers.
def le_signed(a: U64, b: U64) -> Bool:
  U64{alo, +ahi} = a
  U64{blo, +bhi} = b
  le_sign(alo, ahi, blo, bhi, U32.is_ge(ahi, 2147483648), U32.is_ge(bhi, 2147483648))

# Long division in 32/12/12/8-bit digits: every partial remainder is below
# d <= 2^20, so each candidate r * 2^12 + digit stays below 2^32.
def div_fin(+lo: U32, +hi: U32, +d: U32, +t1: U32, +t2: U32, +t3: U32) -> U64:
  U64{U32.add(U32.add(U32.mul(U32.div(t1, d), 1048576), U32.mul(U32.div(t2, d), 256)), U32.div(t3, d)), U32.div(hi, d)}

def div_t3(+lo: U32, +hi: U32, +d: U32, +t1: U32, +t2: U32) -> U64:
  div_fin(lo, hi, d, t1, t2, U32.add(U32.mul(U32.mod(t2, d), 256), U32.and(lo, 255)))

def div_t2(+lo: U32, +hi: U32, +d: U32, +t1: U32) -> U64:
  div_t3(lo, hi, d, t1, U32.add(U32.mul(U32.mod(t1, d), 4096), U32.and(U32.div(lo, 256), 4095)))

# Unsigned a / d, for 0 < d <= 2^20.
def div_small(a: U64, +d: U32) -> U64:
  U64{+lo, +hi} = a
  div_t2(lo, hi, d, U32.add(U32.mul(U32.mod(hi, d), 4096), U32.div(lo, 1048576)))

def div_sign(a: U64, +d: U32, negative: Bool) -> U64:
  match negative:
    case False{}:
      div_small(a, d)
    case True{}:
      neg(div_small(neg(a), d))

# Signed a / d truncated toward zero (C semantics), for 0 < d <= 2^20.
def div_small_signed(a: U64, +d: U32) -> U64:
  U64{lo, +hi} = a
  div_sign(U64{lo, hi}, d, U32.is_ge(hi, 2147483648))
