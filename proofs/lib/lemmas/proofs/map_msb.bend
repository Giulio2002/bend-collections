import Base
import ./native_map.bend as Native
import ./map_bits.bend as B
import ./numeric.bend as Numeric
import ./map_routing.bend as Logic
import ../src/wide.bend as W

law zero_bits:
  for +n: Nat
  for w: Word(n)
  for index: Nat
  for zero: {W.is_zero(n, w) == True{} : Bool}
  {B.nth(n, w, index) == False{} : Bool}
def zero_bits(n, w, index, zero):
  match n:
    case 0n: {==}
    case 1n+p:
      match w:
        case WCon{False{}, tail}:
          match index:
            case 0n: {==}
            case 1n+k: zero_bits(p, tail, k, zero)
        case WCon{True{}, tail}:
          Empty.absurd({B.nth(1n+p, WCon{True{}, tail}, index) == False{} : Bool}, Logic.false_true(zero))

law zero_u32_bits:
  for x: U32
  for index: Nat
  for zero: {U32.is_zero(x) == True{} : Bool}
  {B.at(x, index) == False{} : Bool}
def zero_u32_bits(x, index, zero):
  U32{+w} = x
  zero_bits(32n, w, index, Equal.trans(Bool, W.is_zero(32n, w), Cmp.is_eq(Word.cmp(32n, w, Word.zero(32n))), True{}, Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, w, Word.zero(32n))), W.is_zero(32n, w), Numeric.zero_comparison_correspondence(32n, w)), zero))

law beyond:
  for +n: Nat
  for w: Word(n)
  for index: Nat
  {B.nth(n, w, Nat.add(n, index)) == False{} : Bool}
def beyond(n, w, index):
  match n:
    case 0n: {==}
    case 1n+p:
      match w:
        case WCon{bit, tail}: beyond(p, tail, index)

law above_branch:
  for +fuel: Nat
  for +x: U32
  for +index: Nat
  for zero: Bool
  for +e: {U32.is_zero(x) == zero : Bool}
  for exhausted: {B.at(x, Nat.add(1n+fuel, index)) == False{} : Bool}
  for recur: {B.at(U32.shr(x), Nat.add(fuel, index)) == False{} : Bool} -> {B.at(U32.shr(x), Nat.add(Map.msb.u(fuel, U32.shr(x)), index)) == False{} : Bool}
  {B.at(x, Nat.add(Map.msb.u(1n+fuel, x), index)) == False{} : Bool}
def above_branch(fuel, x, index, zero, e, exhausted, recur):
  match zero:
    case True{}:
      %Equal.sym(Bool, U32.is_zero(x), True{}, e) : {B.at(x, Nat.add(Map.msb.u.if(fuel, x, _), index)) == False{} : Bool}
      zero_u32_bits(x, index, e)
    case False{}:
      %Equal.sym(Bool, U32.is_zero(x), False{}, e) : {B.at(x, Nat.add(Map.msb.u.if(fuel, x, _), index)) == False{} : Bool}
      Equal.trans(Bool, B.at(x, 1n+Nat.add(Map.msb.u(fuel, U32.shr(x)), index)), B.at(U32.shr(x), Nat.add(Map.msb.u(fuel, U32.shr(x)), index)), False{}, Equal.sym(Bool, B.at(U32.shr(x), Nat.add(Map.msb.u(fuel, U32.shr(x)), index)), B.at(x, 1n+Nat.add(Map.msb.u(fuel, U32.shr(x)), index)), B.shifted_u32(x, Nat.add(Map.msb.u(fuel, U32.shr(x)), index))), recur(Equal.trans(Bool, B.at(U32.shr(x), Nat.add(fuel, index)), B.at(x, 1n+Nat.add(fuel, index)), False{}, B.shifted_u32(x, Nat.add(fuel, index)), exhausted)))

law above_with_fuel:
  for +fuel: Nat
  for +x: U32
  for +index: Nat
  for exhausted: {B.at(x, Nat.add(fuel, index)) == False{} : Bool}
  {B.at(x, Nat.add(Map.msb.u(fuel, x), index)) == False{} : Bool}
def above_with_fuel(fuel, x, index, exhausted):
  match fuel:
    case 0n: exhausted
    case 1n+ +p:
      above_branch(p, x, index, U32.is_zero(x), {==}, exhausted, e => above_with_fuel(p, U32.shr(x), index, e))

# The artificial scan-fuel premise is discharged for the actual native 32-bit
# scan. Every bit at or above its returned length is zero, for every U32.
law above_native_msb:
  for x: U32
  for +index: Nat
  {Map.bit.u(x, Nat.add(Map.msb.u(32n, x), index)) == False{} : Bool}
def above_native_msb(x, index):
  U32{+w} = x
  Equal.trans(Bool, Map.bit.u(U32{w}, Nat.add(Map.msb.u(32n, U32{w}), index)), B.at(U32{w}, Nat.add(Map.msb.u(32n, U32{w}), index)), False{}, B.native_bit(U32{w}, Nat.add(Map.msb.u(32n, U32{w}), index)), above_with_fuel(32n, U32{w}, index, beyond(32n, w, index)))

# A single structural decomposition quantifies all 32 independent input bits;
# this is definitional shift evaluation, not enumeration of U32 values.
law shift_width_zero:
  for x: U32
  {U32.shrn(x, 32n) == 0 : U32}
def shift_width_zero(x):
  match x:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

law padded_zero:
  for +n: Nat
  for w: Word(n)
  {W.is_zero(1n+n, Word.shr.pad(n, w)) == W.is_zero(n, w) : Bool}
def padded_zero(n, w):
  match n:
    case 0n: {==}
    case 1n+p:
      match w:
        case WCon{+b, +tail}:
          Equal.cong(Bool, Bool, z => Bool.not(b) && z, W.is_zero(1n+p, Word.shr.pad(p, tail)), W.is_zero(p, tail), padded_zero(p, tail))

law shr_zero_tail:
  for +b: Bool
  for +tail: Word(31n)
  for zero: {U32.is_zero(U32.shr(U32{WCon{b, tail}})) == True{} : Bool}
  {W.is_zero(31n, tail) == True{} : Bool}
def shr_zero_tail(b, tail, zero):
  Equal.trans(Bool, W.is_zero(31n, tail), W.is_zero(32n, Word.shr.pad(31n, tail)), True{}, Equal.sym(Bool, W.is_zero(32n, Word.shr.pad(31n, tail)), W.is_zero(31n, tail), padded_zero(31n, tail)), Equal.trans(Bool, W.is_zero(32n, Word.shr.pad(31n, tail)), U32.is_zero(U32.shr(U32{WCon{b, tail}})), True{}, Equal.sym(Bool, U32.is_zero(U32.shr(U32{WCon{b, tail}})), W.is_zero(32n, Word.shr.pad(31n, tail)), Numeric.zero_comparison_correspondence(32n, Word.shr.pad(31n, tail))), zero))

law last_nonzero_low:
  for x: U32
  for nonzero: {U32.is_zero(x) == False{} : Bool}
  for shifted_zero: {U32.is_zero(U32.shr(x)) == True{} : Bool}
  {B.at(x, 0n) == True{} : Bool}
def last_nonzero_low(x, nonzero, shifted_zero):
  match x:
    case U32{WCon{True{}, tail}}: {==}
    case U32{WCon{False{}, +tail}}:
      Empty.absurd({False{} == True{} : Bool}, Logic.false_true(Equal.trans(Bool, False{}, U32.is_zero(U32{WCon{False{}, tail}}), True{}, Equal.sym(Bool, U32.is_zero(U32{WCon{False{}, tail}}), False{}, nonzero), Equal.trans(Bool, U32.is_zero(U32{WCon{False{}, tail}}), W.is_zero(31n, tail), True{}, Numeric.zero_comparison_correspondence(32n, WCon{False{}, tail}), shr_zero_tail(False{}, tail, shifted_zero)))))

law zero_msb:
  for fuel: Nat
  for +x: U32
  for zero: {U32.is_zero(x) == True{} : Bool}
  {Map.msb.u(fuel, x) == 0n : Nat}
def zero_msb(fuel, x, zero):
  match fuel:
    case 0n: {==}
    case 1n+p:
      Equal.cong(Bool, Nat, z => Map.msb.u.if(p, x, z), U32.is_zero(x), True{}, zero)

def Peak(fuel: Nat, +x: U32) -> Type:
  Sigma<&2, &1, Nat, position => {Map.msb.u(fuel, x) == 1n+position : Nat} & {B.at(x, position) == True{} : Bool}>

law lift_peak:
  for +fuel: Nat
  for +x: U32
  for nonzero: {U32.is_zero(x) == False{} : Bool}
  for peak: Peak(fuel, U32.shr(x))
  Peak(1n+fuel, x)
def lift_peak(fuel, x, nonzero, peak):
  match peak:
    case Tuple{+position, Tuple{length, bit}}:
      (1n+position, (Equal.trans(Nat, Map.msb.u(1n+fuel, x), 1n+Map.msb.u(fuel, U32.shr(x)), 2n+position, Equal.cong(Bool, Nat, z => Map.msb.u.if(fuel, x, z), U32.is_zero(x), False{}, nonzero), Equal.cong(Nat, Nat, n => 1n+n, Map.msb.u(fuel, U32.shr(x)), 1n+position, length)), Equal.trans(Bool, B.at(x, 1n+position), B.at(U32.shr(x), position), True{}, Equal.sym(Bool, B.at(U32.shr(x), position), B.at(x, 1n+position), B.shifted_u32(x, position)), bit)))

law peak_branch:
  for +fuel: Nat
  for +x: U32
  for zero: Bool
  for +e: {U32.is_zero(U32.shr(x)) == zero : Bool}
  for +nonzero: {U32.is_zero(x) == False{} : Bool}
  for recur: {U32.is_zero(U32.shr(x)) == False{} : Bool} -> Peak(fuel, U32.shr(x))
  Peak(1n+fuel, x)
def peak_branch(fuel, x, zero, e, nonzero, recur):
  match zero:
    case True{}:
      (0n, (Equal.trans(Nat, Map.msb.u(1n+fuel, x), 1n+Map.msb.u(fuel, U32.shr(x)), 1n, Equal.cong(Bool, Nat, z => Map.msb.u.if(fuel, x, z), U32.is_zero(x), False{}, nonzero), Equal.cong(Nat, Nat, n => 1n+n, Map.msb.u(fuel, U32.shr(x)), 0n, zero_msb(fuel, U32.shr(x), e))), last_nonzero_low(x, nonzero, e)))
    case False{}:
      lift_peak(fuel, x, nonzero, recur(e))

law peak_with_fuel:
  for +fuel: Nat
  for +x: U32
  for exhausted: {U32.is_zero(U32.shrn(x, fuel)) == True{} : Bool}
  for nonzero: {U32.is_zero(x) == False{} : Bool}
  Peak(fuel, x)
def peak_with_fuel(fuel, x, exhausted, nonzero):
  match fuel:
    case 0n:
      Empty.absurd(Peak(0n, x), Logic.false_true(Equal.trans(Bool, False{}, U32.is_zero(x), True{}, Equal.sym(Bool, U32.is_zero(x), False{}, nonzero), exhausted)))
    case 1n+ +p:
      peak_branch(p, x, U32.is_zero(U32.shr(x)), {==}, nonzero, e => peak_with_fuel(p, U32.shr(x), Equal.trans(Bool, U32.is_zero(U32.shrn(U32.shr(x), p)), U32.is_zero(U32.shrn(x, 1n+p)), True{}, Equal.cong(U32, Bool, U32.is_zero, U32.shrn(U32.shr(x), p), U32.shrn(x, 1n+p), Equal.sym(U32, U32.shrn(x, 1n+p), U32.shrn(U32.shr(x), p), B.shift_front(x, p))), exhausted), e))

# For every nonzero U32, the native scan identifies an actual set bit. The
# public theorem discharges termination at 32 shifts, not an assumed oracle.
law native_peak:
  for +x: U32
  for nonzero: {U32.is_zero(x) == False{} : Bool}
  Peak(32n, x)
def native_peak(x, nonzero):
  peak_with_fuel(32n, x, Equal.cong(U32, Bool, U32.is_zero, U32.shrn(x, 32n), 0, shift_width_zero(x)), nonzero)

law xor_zero_equal:
  for +n: Nat
  for a: Word(n)
  for b: Word(n)
  for zero: {W.is_zero(n, Word.xor(n, a, b)) == True{} : Bool}
  {a == b : Word(n)}
def xor_zero_equal(n, a, b, zero):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}: {==}
    case 1n+p:
      match a b:
        case WCon{False{}, +left_tail} WCon{False{}, +right_tail}:
          Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t}, left_tail, right_tail, xor_zero_equal(p, left_tail, right_tail, zero))
        case WCon{True{}, +left_tail} WCon{True{}, +right_tail}:
          Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t}, left_tail, right_tail, xor_zero_equal(p, left_tail, right_tail, zero))
        case WCon{False{}, left_tail} WCon{True{}, right_tail}:
          Empty.absurd({WCon{False{}, left_tail} == WCon{True{}, right_tail} : Word(1n+p)}, Logic.false_true(zero))
        case WCon{True{}, left_tail} WCon{False{}, right_tail}:
          Empty.absurd({WCon{True{}, left_tail} == WCon{False{}, right_tail} : Word(1n+p)}, Logic.false_true(zero))

law xor_zero_u32_equal:
  for a: U32
  for b: U32
  for zero: {U32.is_zero(U32.xor(a, b)) == True{} : Bool}
  {a == b : U32}
def xor_zero_u32_equal(a, b, zero):
  match a b:
    case U32{+x} U32{+y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, xor_zero_equal(32n, x, y, Equal.trans(Bool, W.is_zero(32n, Word.xor(32n, x, y)), U32.is_zero(U32.xor(U32{x}, U32{y})), True{}, Equal.sym(Bool, U32.is_zero(U32.xor(U32{x}, U32{y})), W.is_zero(32n, Word.xor(32n, x, y)), Numeric.zero_comparison_correspondence(32n, Word.xor(32n, x, y))), zero)))

law equal_u32_comparison:
  for +a: U32
  for b: U32
  for eq: {a == b : U32}
  {U32.is_eq(a, b) == True{} : Bool}
def equal_u32_comparison(a, b, eq):
  U32{+x} = a
  %eq : {U32.is_eq(U32{x}, _) == True{} : Bool}
  Equal.cong(Cmp, Bool, Cmp.is_eq, Word.cmp(32n, x, x), EQ{}, Native.word_compare_self(32n, x))

law xor_nonzero_case:
  for +a: U32
  for +b: U32
  for unequal: {U32.is_eq(a, b) == False{} : Bool}
  for z: Bool
  for e: {U32.is_zero(U32.xor(a, b)) == z : Bool}
  {U32.is_zero(U32.xor(a, b)) == False{} : Bool}
def xor_nonzero_case(a, b, unequal, z, e):
  match z:
    case False{}: e
    case True{}:
      Empty.absurd({U32.is_zero(U32.xor(a, b)) == False{} : Bool}, Logic.false_true(Equal.trans(Bool, False{}, U32.is_eq(a, b), True{}, Equal.sym(Bool, U32.is_eq(a, b), False{}, unequal), equal_u32_comparison(a, b, xor_zero_u32_equal(a, b, e)))))

law unequal_xor_nonzero:
  for +a: U32
  for +b: U32
  for unequal: {U32.is_eq(a, b) == False{} : Bool}
  {U32.is_zero(U32.xor(a, b)) == False{} : Bool}
def unequal_xor_nonzero(a, b, unequal):
  xor_nonzero_case(a, b, unequal, U32.is_zero(U32.xor(a, b)), {==})

# Native Map.diff.step uses precisely this XOR and equality branch. The returned
# position really distinguishes the character words, not an injective hash.
def Difference(+a: U32, +b: U32) -> Type:
  Sigma<&2, &1, Nat, p => {Map.msb.u(32n, U32.xor(a, b)) == 1n+p : Nat} & {Bool.xor(Map.bit.u(a, p), Map.bit.u(b, p)) == True{} : Bool}>

law difference_from_peak:
  for +a: U32
  for +b: U32
  for peak: Peak(32n, U32.xor(a, b))
  Difference(a, b)
def difference_from_peak(a, b, peak):
  match peak:
    case Tuple{+p, Tuple{length, bit}}:
      (p, (length, Equal.trans(Bool, Bool.xor(Map.bit.u(a, p), Map.bit.u(b, p)), Map.bit.u(U32.xor(a, b), p), True{}, Equal.sym(Bool, Map.bit.u(U32.xor(a, b), p), Bool.xor(Map.bit.u(a, p), Map.bit.u(b, p)), B.native_xor(a, b, p)), Equal.trans(Bool, Map.bit.u(U32.xor(a, b), p), B.at(U32.xor(a, b), p), True{}, B.native_bit(U32.xor(a, b), p), bit))))

law unequal_character_difference:
  for +a: U32
  for +b: U32
  for unequal: {U32.is_eq(a, b) == False{} : Bool}
  Difference(a, b)
def unequal_character_difference(a, b, unequal):
  difference_from_peak(a, b, native_peak(U32.xor(a, b), unequal_xor_nonzero(a, b, unequal)))

law bound_branch:
  for +fuel: Nat
  for +x: U32
  for zero: Bool
  for bound: {Nat.is_le(Map.msb.u(fuel, U32.shr(x)), fuel) == True{} : Bool}
  {Nat.is_le(Map.msb.u.if(fuel, x, zero), 1n+fuel) == True{} : Bool}
def bound_branch(fuel, x, zero, bound):
  match zero:
    case True{}: {==}
    case False{}: bound

law native_bound:
  for +fuel: Nat
  for +x: U32
  {Nat.is_le(Map.msb.u(fuel, x), fuel) == True{} : Bool}
def native_bound(fuel, x):
  match fuel:
    case 0n: {==}
    case 1n+ +p:
      bound_branch(p, x, U32.is_zero(x), native_bound(p, U32.shr(x)))
