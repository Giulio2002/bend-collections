import Base
import ../spec/numeric.bend as S
import ./addition.bend as Add
import ./addition_bounds.bend as Bounds
import ./modular_addition.bend as M
import ./native_map.bend as Natural

def carry(n: Nat, input: Bool, word: Word(n)) -> Bool:
  match n:
    case 0n: input
    case 1n+p:
      match word:
        case WCon{bit, tail}: carry(p, bit, tail)

# Integer conservation for actual Base.shl.put, retaining the discarded bit.
def conservation(+n: Nat, +input: Bool, word: Word(n)) -> {Nat.add(S.unsigned(n, Word.shl.put(n, input, word)), S.scale_binary(n, S.bit_value(carry(n, input, word)))) == Nat.add(S.bit_value(input), Nat.double(S.unsigned(n, word))) : Nat}:
  match n:
    case 0n:
      match word:
        case WNil{}:
          Equal.sym(Nat, Nat.add(S.bit_value(input), 0n), S.bit_value(input), Natural.natural_add_right_zero(S.bit_value(input)))
    case 1n+ +p:
      match word:
        case WCon{+bit, +tail}:
          Add.lift_conservation(input, S.unsigned(p, Word.shl.put(p, bit, tail)), S.scale_binary(p, S.bit_value(carry(p, bit, tail))), Nat.add(S.bit_value(bit), Nat.double(S.unsigned(p, tail))), conservation(p, bit, tail))

def same_as_put(+n: Nat, word: Word(n)) -> {Word.shl(n, word) == Word.shl.put(n, False{}, word) : Word(n)}:
  match n:
    case 0n: {==}
    case 1n+p:
      match word:
        case WCon{bit, tail}: {==}

def shift_conservation(+n: Nat, +word: Word(n)) -> {Nat.add(S.unsigned(n, Word.shl(n, word)), S.scale_binary(n, S.bit_value(carry(n, False{}, word)))) == Nat.double(S.unsigned(n, word)) : Nat}:
  %Equal.sym(Word(n), Word.shl(n, word), Word.shl.put(n, False{}, word), same_as_put(n, word)) : {Nat.add(S.unsigned(n, _), S.scale_binary(n, S.bit_value(carry(n, False{}, word)))) == Nat.double(S.unsigned(n, word)) : Nat}
  conservation(n, False{}, word)

def refines(+n: Nat, +word: Word(n)) -> {Word.shl(n, word) == S.from_nat(n, Nat.double(S.unsigned(n, word))) : Word(n)}:
  %shift_conservation(n, word) : {Word.shl(n, word) == S.from_nat(n, _) : Word(n)}
  Equal.sym(Word(n), S.from_nat(n, Nat.add(S.unsigned(n, Word.shl(n, word)), S.scale_binary(n, S.bit_value(carry(n, False{}, word))))), Word.shl(n, word), M.reconstruct(n, Word.shl(n, word), S.bit_value(carry(n, False{}, word))))

def exact(+n: Nat, +word: Word(n), bound: {Nat.is_lt(Nat.double(S.unsigned(n, word)), S.scale_binary(n, 1n)) == True{} : Bool}) -> {S.unsigned(n, Word.shl(n, word)) == Nat.double(S.unsigned(n, word)) : Nat}:
  Bounds.no_wrap(n, S.unsigned(n, Word.shl(n, word)), Nat.double(S.unsigned(n, word)), carry(n, False{}, word), shift_conservation(n, word), bound)
