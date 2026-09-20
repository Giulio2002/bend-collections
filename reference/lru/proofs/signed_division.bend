import Base
import ../src/wide.bend as W
import ../spec/numeric.bend as S
import ./division_quotient.bend as Q
import ./modular_negation.bend as Neg
import ./negation_magnitude.bend as Magnitude

def negate(+n: Nat, word: Word(n)) -> Word(n):
  Word.inc(n, Word.not(n, word))

def specification_equation(+n: Nat, word: Word(n), +d: U32) -> {S.negative_quotient(n, word, d) == S.from_nat(n, Nat.sub(Nat.pow(2n, n), Nat.div(Nat.sub(Nat.pow(2n, n), S.unsigned(n, word)), U32.to_nat(d)))) : Word(n)}:
  match n:
    case 0n: {==}
    case 1n+p:
      match word:
        case WCon{bit, tail}: {==}

# Truncation toward zero: divide the positive magnitude, then negate modulo 2^n.
# Nonzero is discharged from the selected negative sign at the native boundary.
def negative(+n: Nat, +word: Word(n), +d: U32, same: {d == 1000000 : U32}, nonzero: {W.is_zero(n, word) == False{} : Bool}) -> {negate(n, Q.quotient(n, W.div_million(n, negate(n, word)))) == S.negative_quotient(n, word, d) : Word(n)}:
  Equal.trans(Word(n), negate(n, Q.quotient(n, W.div_million(n, negate(n, word)))), S.from_nat(n, Nat.sub(S.scale_binary(n, 1n), S.unsigned(n, Q.quotient(n, W.div_million(n, negate(n, word)))))), S.negative_quotient(n, word, d), Neg.negation_refines(n, Q.quotient(n, W.div_million(n, negate(n, word)))), Equal.trans(Word(n), S.from_nat(n, Nat.sub(S.scale_binary(n, 1n), S.unsigned(n, Q.quotient(n, W.div_million(n, negate(n, word)))))), S.from_nat(n, Nat.sub(S.scale_binary(n, 1n), Nat.div(S.unsigned(n, negate(n, word)), U32.to_nat(d)))), S.negative_quotient(n, word, d), Equal.cong(Nat, Word(n), x => S.from_nat(n, Nat.sub(S.scale_binary(n, 1n), x)), S.unsigned(n, Q.quotient(n, W.div_million(n, negate(n, word)))), Nat.div(S.unsigned(n, negate(n, word)), U32.to_nat(d)), Equal.sym(Nat, Nat.div(S.unsigned(n, negate(n, word)), U32.to_nat(d)), S.unsigned(n, Q.quotient(n, W.div_million(n, negate(n, word)))), Q.natural_quotient(n, negate(n, word), d, same))), Equal.trans(Word(n), S.from_nat(n, Nat.sub(S.scale_binary(n, 1n), Nat.div(S.unsigned(n, negate(n, word)), U32.to_nat(d)))), S.from_nat(n, Nat.sub(S.scale_binary(n, 1n), Nat.div(Nat.sub(S.scale_binary(n, 1n), S.unsigned(n, word)), U32.to_nat(d)))), S.negative_quotient(n, word, d), Equal.cong(Nat, Word(n), x => S.from_nat(n, Nat.sub(S.scale_binary(n, 1n), Nat.div(x, U32.to_nat(d)))), S.unsigned(n, negate(n, word)), Nat.sub(S.scale_binary(n, 1n), S.unsigned(n, word)), Magnitude.magnitude(n, word, nonzero)), Equal.trans(Word(n), S.from_nat(n, Nat.sub(S.scale_binary(n, 1n), Nat.div(Nat.sub(S.scale_binary(n, 1n), S.unsigned(n, word)), U32.to_nat(d)))), S.from_nat(n, Nat.sub(Nat.pow(2n, n), Nat.div(Nat.sub(Nat.pow(2n, n), S.unsigned(n, word)), U32.to_nat(d)))), S.negative_quotient(n, word, d), Equal.cong(Nat, Word(n), x => S.from_nat(n, Nat.sub(x, Nat.div(Nat.sub(x, S.unsigned(n, word)), U32.to_nat(d)))), S.scale_binary(n, 1n), Nat.pow(2n, n), Magnitude.scale_power(n)), Equal.sym(Word(n), S.negative_quotient(n, word, d), S.from_nat(n, Nat.sub(Nat.pow(2n, n), Nat.div(Nat.sub(Nat.pow(2n, n), S.unsigned(n, word)), U32.to_nat(d)))), specification_equation(n, word, d))))))

def actual_negative(+word: Word(64n), sign: {W.last(64n, word) == True{} : Bool}) -> {W.signed_milliseconds(word, True{}) == S.quotient_signed(word, True{}) : Word(64n)}:
  Equal.trans(Word(64n), W.signed_milliseconds(word, True{}), negate(64n, Q.quotient(64n, W.div_million(64n, W.neg(word)))), S.quotient_signed(word, True{}), Equal.cong(Word(64n), Word(64n), W.neg, W.quotient(W.div_million(64n, W.neg(word))), Q.quotient(64n, W.div_million(64n, W.neg(word))), Q.native_projection(W.div_million(64n, W.neg(word)))), negative(64n, word, 1000000, {==}, Magnitude.sign_nonzero(63n, word, sign)))

def branch(word: Word(64n), sign: Bool, chosen: {W.last(64n, word) == sign : Bool}) -> {W.signed_milliseconds(word, sign) == S.quotient_signed(word, sign) : Word(64n)}:
  match sign:
    case False{}: Q.unsigned_milliseconds(word)
    case True{}: actual_negative(word, chosen)
