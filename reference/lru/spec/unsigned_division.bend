import Base
import ./numeric.bend as N

# Mathematical division of the interpreted input. Matching the word before
# interpreting it avoids eager unary expansion of fixed denominator constants;
# this is not a binary-division algorithm or an implementation import.
def quotient(n: Nat, word: Word(n), d: U32) -> Word(n):
  N.unsigned_quotient(n, word, d)
