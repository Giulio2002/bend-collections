import Base
import ../src/wide.bend as W
import ../spec/numeric.bend as S
import ./division_no_overflow.bend as Overflow
import ./division_bounds.bend as Bounds
import ./word_comparison.bend as Compare

def lt_le(c: Cmp, e: {Cmp.is_lt(c) == True{} : Bool}) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: e

def smaller_high(r: U32, d: U32, high: {W.last(32n, Overflow.bits(d)) == False{} : Bool}, less: {U32.is_lt(r, d) == True{} : Bool}) -> {W.last(32n, Overflow.bits(r)) == False{} : Bool}:
  match r d:
    case U32{+a} U32{+b}:
      Overflow.high_monotone(31n, a, b, high, lt_le(Word.cmp(32n, a, b), less))

def native(+r: U32, +d: U32, +bit: Bool, +high: {W.last(32n, Overflow.bits(d)) == False{} : Bool}, +less: {U32.is_lt(r, d) == True{} : Bool}) -> {U32.is_lt(U32.add(U32.mul(r, 2), W.bit_u32(bit)), U32.shl(d)) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(U32.add(U32.mul(r, 2), W.bit_u32(bit)), U32.shl(d)), Nat.is_lt(U32.to_nat(U32.add(U32.mul(r, 2), W.bit_u32(bit))), U32.to_nat(U32.shl(d))), True{}, Compare.u32_lt(U32.add(U32.mul(r, 2), W.bit_u32(bit)), U32.shl(d)), Equal.trans(Bool, Nat.is_lt(U32.to_nat(U32.add(U32.mul(r, 2), W.bit_u32(bit))), U32.to_nat(U32.shl(d))), Nat.is_lt(Nat.add(S.bit_value(bit), Nat.double(U32.to_nat(r))), U32.to_nat(U32.shl(d))), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(x, U32.to_nat(U32.shl(d))), U32.to_nat(U32.add(U32.mul(r, 2), W.bit_u32(bit))), Nat.add(S.bit_value(bit), Nat.double(U32.to_nat(r))), Overflow.high_candidate(r, bit, smaller_high(r, d, high, less))), Equal.trans(Bool, Nat.is_lt(Nat.add(S.bit_value(bit), Nat.double(U32.to_nat(r))), U32.to_nat(U32.shl(d))), Nat.is_lt(Nat.add(S.bit_value(bit), Nat.double(U32.to_nat(r))), Nat.double(U32.to_nat(d))), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(Nat.add(S.bit_value(bit), Nat.double(U32.to_nat(r))), x), U32.to_nat(U32.shl(d)), Nat.double(U32.to_nat(d)), Overflow.double_value(d, high)), Bounds.candidate(U32.to_nat(r), U32.to_nat(d), bit, Equal.trans(Bool, Nat.is_lt(U32.to_nat(r), U32.to_nat(d)), U32.is_lt(r, d), True{}, Equal.sym(Bool, U32.is_lt(r, d), Nat.is_lt(U32.to_nat(r), U32.to_nat(d)), Compare.u32_lt(r, d)), less)))))

def million(+r: U32, +bit: Bool, less: {U32.is_lt(r, 1000000) == True{} : Bool}) -> {U32.is_lt(U32.add(U32.mul(r, 2), W.bit_u32(bit)), 2000000) == True{} : Bool}:
  native(r, 1000000, bit, {==}, less)
