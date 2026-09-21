import Base
# Ported from reference/lru/proofs/word_addition.bend (unchanged proof text; imports retargeted to
# the natively compilable copies src/lru/{wide,time}.bend, types/lru_model.bend
# and spec/lru_{numeric,unsigned_division}.bend).
import ../../../spec/lru_numeric.bend as S
import ./addition.bend as Add
import ./modular_addition.bend as M
import ./numeric.bend as N

# Actual Base ripple addition, at any width, with exact modulo interpretation.
def refines(+n: Nat, +a: Word(n), +b: Word(n)) -> {Word.add(n, a, b) == S.from_nat(n, Nat.add(S.unsigned(n, a), S.unsigned(n, b))) : Word(n)}:
  %Add.adc_conservation(n, a, b, False{}) : {Word.add(n, a, b) == S.from_nat(n, _) : Word(n)}
  Equal.sym(Word(n), S.from_nat(n, Nat.add(S.unsigned(n, Word.add(n, a, b)), S.scale_binary(n, S.bit_value(Add.carry_out(n, a, b, False{}))))), Word.add(n, a, b), M.reconstruct(n, Word.add(n, a, b), S.bit_value(Add.carry_out(n, a, b, False{}))))

# Primitive U32 decoding is connected to that same independent interpretation.
def u32_refines(a: U32, b: U32) -> {U32.add(a, b) == U32{S.from_nat(32n, Nat.add(U32.to_nat(a), U32.to_nat(b)))} : U32}:
  match a b:
    case U32{+x} U32{+y}:
      %Equal.sym(Nat, Word.to_nat(32n, x), S.unsigned(32n, x), N.primitive_word_interpretation(32n, x)) : {U32.add(U32{x}, U32{y}) == U32{S.from_nat(32n, Nat.add(_, Word.to_nat(32n, y)))} : U32}
      %Equal.sym(Nat, Word.to_nat(32n, y), S.unsigned(32n, y), N.primitive_word_interpretation(32n, y)) : {U32.add(U32{x}, U32{y}) == U32{S.from_nat(32n, Nat.add(S.unsigned(32n, x), _))} : U32}
      Equal.cong(Word(32n), U32, w => U32{w}, Word.add(32n, x, y), S.from_nat(32n, Nat.add(S.unsigned(32n, x), S.unsigned(32n, y))), refines(32n, x, y))

def with_carry(+n: Nat, +a: Word(n), +b: Word(n), +carry: Bool) -> {Word.adc(n, a, b, False{}, carry) == S.from_nat(n, Nat.add(S.bit_value(carry), Nat.add(S.unsigned(n, a), S.unsigned(n, b)))) : Word(n)}:
  %Add.adc_conservation(n, a, b, carry) : {Word.adc(n, a, b, False{}, carry) == S.from_nat(n, _) : Word(n)}
  Equal.sym(Word(n), S.from_nat(n, Nat.add(S.unsigned(n, Word.adc(n, a, b, False{}, carry)), S.scale_binary(n, S.bit_value(Add.carry_out(n, a, b, carry))))), Word.adc(n, a, b, False{}, carry), M.reconstruct(n, Word.adc(n, a, b, False{}, carry), S.bit_value(Add.carry_out(n, a, b, carry))))
