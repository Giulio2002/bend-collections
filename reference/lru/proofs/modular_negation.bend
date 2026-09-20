import Base
import ../src/wide.bend as W
import ../spec/numeric.bend as S
import ./modular_addition.bend as M

# Arithmetic cancellation against actual Base Nat.sub, with no bounds premise.
def subtract_sum(a: Nat, b: Nat) -> {Nat.sub(Nat.add(a, b), a) == b : Nat}:
  match a:
    case 0n:
      match b:
        case 0n: {==}
        case 1n+p: {==}
    case 1n+p:
      subtract_sum(p, b)

def complementary_digits(a: Nat, b: Nat, bit: Bool) -> {Nat.add(Nat.add(S.bit_value(bit), Nat.double(a)), 1n+Nat.add(S.bit_value(Bool.not(bit)), Nat.double(b))) == Nat.double(Nat.add(a, 1n+b)) : Nat}:
  match a:
    case 0n:
      match bit:
        case False{}: {==}
        case True{}: {==}
    case 1n+ +p:
      match bit:
        case False{}:
          Equal.cong(Nat, Nat, x => 2n+x, Nat.add(Nat.add(S.bit_value(False{}), Nat.double(p)), 1n+Nat.add(S.bit_value(Bool.not(False{})), Nat.double(b))), Nat.double(Nat.add(p, 1n+b)), complementary_digits(p, b, False{}))
        case True{}:
          Equal.cong(Nat, Nat, x => 2n+x, Nat.add(Nat.add(S.bit_value(True{}), Nat.double(p)), 1n+Nat.add(S.bit_value(Bool.not(True{})), Nat.double(b))), Nat.double(Nat.add(p, 1n+b)), complementary_digits(p, b, True{}))

# Complement and original together, plus one, are exactly 2^width.
def complement_sum(+n: Nat, word: Word(n)) -> {Nat.add(S.unsigned(n, word), 1n+S.unsigned(n, Word.not(n, word))) == S.scale_binary(n, 1n) : Nat}:
  match n:
    case 0n:
      match word:
        case WNil{}: {==}
    case 1n+ +p:
      match word:
        case WCon{+bit, +tail}:
          Equal.trans(Nat, Nat.add(Nat.add(S.bit_value(bit), Nat.double(S.unsigned(p, tail))), 1n+Nat.add(S.bit_value(Bool.not(bit)), Nat.double(S.unsigned(p, Word.not(p, tail))))), Nat.double(Nat.add(S.unsigned(p, tail), 1n+S.unsigned(p, Word.not(p, tail)))), Nat.double(S.scale_binary(p, 1n)), complementary_digits(S.unsigned(p, tail), S.unsigned(p, Word.not(p, tail)), bit), Equal.cong(Nat, Nat, Nat.double, Nat.add(S.unsigned(p, tail), 1n+S.unsigned(p, Word.not(p, tail))), S.scale_binary(p, 1n), complement_sum(p, tail)))

def complement_distance(+n: Nat, +word: Word(n)) -> {Nat.sub(S.scale_binary(n, 1n), S.unsigned(n, word)) == 1n+S.unsigned(n, Word.not(n, word)) : Nat}:
  %complement_sum(n, word) : {Nat.sub(_, S.unsigned(n, word)) == 1n+S.unsigned(n, Word.not(n, word)) : Nat}
  subtract_sum(S.unsigned(n, word), 1n+S.unsigned(n, Word.not(n, word)))

# Actual two's-complement negation refines mathematical modular subtraction at
# every width, including zero and the signed minimum pattern. Signed division
# and JavaScript conversions remain separate obligations.
def negation_refines(+n: Nat, +word: Word(n)) -> {Word.inc(n, Word.not(n, word)) == S.from_nat(n, Nat.sub(S.scale_binary(n, 1n), S.unsigned(n, word))) : Word(n)}:
  %Equal.sym(Nat, Nat.sub(S.scale_binary(n, 1n), S.unsigned(n, word)), 1n+S.unsigned(n, Word.not(n, word)), complement_distance(n, word)) : {Word.inc(n, Word.not(n, word)) == S.from_nat(n, _) : Word(n)}
  M.increment_refines(n, Word.not(n, word))

# This concrete theorem reaches the actual fixed-width implementation without
# normalizing a 2^64 unary Nat literal in the checker.
def native_negation_refines(+word: Word(64n)) -> {W.neg(word) == S.from_nat(64n, 1n+S.unsigned(64n, Word.not(64n, word))) : Word(64n)}:
  M.increment_refines(64n, Word.not(64n, word))
