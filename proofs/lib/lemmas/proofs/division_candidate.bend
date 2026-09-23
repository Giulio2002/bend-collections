import Base
import ./word_comparison.bend as Comparison
import ../src/wide.bend as W
import ../spec/numeric.bend as S
import ./word_multiplication.bend as Mul
import ./word_shift.bend as Shift
import ./numeric.bend as N

def times_two(a: Nat) -> {Nat.mul(a, 2n) == Nat.double(a) : Nat}:
  match a:
    case 0n: {==}
    case 1n+ +p:
      Equal.cong(Nat, Nat, x => 2n+x, Nat.mul(p, 2n), Nat.double(p), times_two(p))

# The actual U32 multiplication in wide.digit computes low bits of 2*r.
def doubling(+r: U32) -> {U32.mul(r, 2) == U32{S.from_nat(32n, Nat.double(U32.to_nat(r)))} : U32}:
  Equal.trans(U32, U32.mul(r, 2), U32{S.from_nat(32n, Nat.mul(U32.to_nat(r), 2n))}, U32{S.from_nat(32n, Nat.double(U32.to_nat(r)))}, Mul.u32_refines(r, 2), Equal.cong(Nat, U32, x => U32{S.from_nat(32n, x)}, Nat.mul(U32.to_nat(r), 2n), Nat.double(U32.to_nat(r)), times_two(U32.to_nat(r))))

def shift_value(r: U32) -> {U32.shl(r) == U32{S.from_nat(32n, Nat.double(U32.to_nat(r)))} : U32}:
  U32{+bits} = r
  %Equal.sym(Nat, Word.to_nat(32n, bits), S.unsigned(32n, bits), N.primitive_word_interpretation(32n, bits)) : {U32.shl(U32{bits}) == U32{S.from_nat(32n, Nat.double(_))} : U32}
  Equal.cong(Word(32n), U32, w => U32{w}, Word.shl(32n, bits), S.from_nat(32n, Nat.double(S.unsigned(32n, bits))), Shift.refines(32n, bits))

def multiplication_is_shift(+r: U32) -> {U32.mul(r, 2) == U32.shl(r) : U32}:
  Equal.trans(U32, U32.mul(r, 2), U32{S.from_nat(32n, Nat.double(U32.to_nat(r)))}, U32.shl(r), doubling(r), Equal.sym(U32, U32.shl(r), U32{S.from_nat(32n, Nat.double(U32.to_nat(r)))}, shift_value(r)))

# Link directly to the recurrence used by actual div_million. This equation is
# still modular; the reachable remainder range must be discharged separately.
def digit(+p: Nat, +bit: Bool, +q: Word(p), +r: U32) -> {W.digit(p, bit, W.Div{q, r}) == W.digit_compare(p, q, U32.add(U32.shl(r), W.bit_u32(bit))) : W.Division<1n+p>}:
  Equal.cong(U32, W.Division<1n+p>, x => W.digit_compare(p, q, U32.add(x, W.bit_u32(bit))), U32.mul(r, 2), U32.shl(r), multiplication_is_shift(r))
