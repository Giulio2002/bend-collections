import Base
import ../lib/numeric.bend as N
import ../../src/math/u64.bend as U

# Specification of src/math/u64.bend: a U64 denotes the 64-bit word whose
# low 32 bits are lo and high 32 bits hi (bits below), and each operation is
# the word operation of spec/lib/numeric.bend: modular addition, two's
# complement negation, signed order, unsigned and signed quotients by small
# divisors.
#
#   function          clauses                                   proved in
#   is_zero           IsZero.value                              proofs/math/proof.bend
#   le_signed         LeSigned.value                            (u64_*, via u64/u64.bend
#   add               Add.bits, Add.modular                      and u64/u64div.bend)
#   neg               Neg.bits
#   div_small         DivSmall.quotient
#   div_small_signed  DivSmallSigned.quotient

def bits(a: U.U64) -> Word(64n):
  match a:
    case U.U64{lo, hi}:
      N.pack(lo, hi)

# the quotient of a signed word: rounded toward zero, as the magnitude's
def signed_quotient(w: Word(64n), neg: Bool, +d: U32) -> Word(64n):
  match neg:
    case False{}:
      N.unsigned_quotient(64n, w, d)
    case True{}:
      N.negative_quotient(64n, w, d)

def IsZero.value(+a: U.U64) -> Type:
  {U.is_zero(a) == N.zero(bits(a)) : Bool}

def LeSigned.value(+a: U.U64, +b: U.U64) -> Type:
  {U.le_signed(a, b) == N.order(bits(a), bits(b), N.negative(bits(a)), N.negative(bits(b))) : Bool}

def Add.bits(+a: U.U64, +b: U.U64) -> Type:
  {bits(U.add(a, b)) == Word.add(64n, bits(a), bits(b)) : Word(64n)}

# addition modulo 2^64
def Add.modular(+a: U.U64, +b: U.U64) -> Type:
  {bits(U.add(a, b)) == N.from_nat(64n, Nat.add(N.unsigned(64n, bits(a)), N.unsigned(64n, bits(b)))) : Word(64n)}

def Neg.bits(+a: U.U64) -> Type:
  {bits(U.neg(a)) == Word.inc(64n, Word.not(64n, bits(a))) : Word(64n)}

# divisors 1 .. 2^20 (the limb division stays inside 32 bits)
def DivSmall.quotient(+a: U.U64, +d: U32, +hd0: {U32.is_zero(d) == False{} : Bool}, +hle: {U32.is_le(d, 1048576) == True{} : Bool}) -> Type:
  {bits(U.div_small(a, d)) == N.unsigned_quotient(64n, bits(a), d) : Word(64n)}

def DivSmallSigned.quotient(+a: U.U64, +d: U32, +hd0: {U32.is_zero(d) == False{} : Bool}, +hle: {U32.is_le(d, 1048576) == True{} : Bool}) -> Type:
  {bits(U.div_small_signed(a, d)) == signed_quotient(bits(a), N.negative(bits(a)), d) : Word(64n)}
