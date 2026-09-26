import Base
import ../types/model.bend as T
import ../../../../spec/lib/numeric.bend as W

# The word model lives in spec/lib/numeric.bend; its names are kept here as
# one-line aliases for the proofs that use them, next to the cache model's
# Int64 interpretation (expiry, deadlines).

def bit_value(b: Bool) -> Nat:
  W.bit_value(b)

def unsigned(n: Nat, w: Word(n)) -> Nat:
  W.unsigned(n, w)

def sign_threshold(n: Nat) -> Word(1n+n):
  W.sign_threshold(n)

def negative(+w: Word(64n)) -> Bool:
  W.negative(w)

def zero(w: Word(64n)) -> Bool:
  W.zero(w)

def order(a: Word(64n), b: Word(64n), sign_a: Bool, sign_b: Bool) -> Bool:
  W.order(a, b, sign_a, sign_b)

def expired(deadline: T.Int64, now: T.Int64) -> Bool:
  match deadline now:
    case T.I64{+a} T.I64{+b}:
      Bool.not(zero(a)) && order(a, b, negative(a), negative(b))

def from_nat(n: Nat, +value: Nat) -> Word(n):
  W.from_nat(n, value)

def modulus() -> Nat:
  W.modulus()

def unsigned_quotient(n: Nat, word: Word(n), d: U32) -> Word(n):
  W.unsigned_quotient(n, word, d)

def negative_quotient(n: Nat, word: Word(n), d: U32) -> Word(n):
  W.negative_quotient(n, word, d)

def quotient_signed(bits: Word(64n), negative: Bool) -> Word(64n):
  W.quotient_signed(bits, negative)

def milliseconds(duration: T.Int64) -> T.Int64:
  T.I64{+bits} = duration
  T.I64{quotient_signed(bits, negative(bits))}

def add(a: T.Int64, b: T.Int64) -> T.Int64:
  match a b:
    case T.I64{x} T.I64{y}:
      T.I64{from_nat(64n, Nat.add(unsigned(64n, x), unsigned(64n, y)))}

def expiry_choose(now: T.Int64, duration: T.Int64, forever: Bool) -> T.Int64:
  match forever:
    case True{}:
      T.I64{Word.zero(64n)}
    case False{}:
      add(now, milliseconds(duration))

def deadline(now: T.Int64, duration: T.Int64) -> T.Int64:
  T.I64{+bits} = duration
  expiry_choose(now, T.I64{bits}, zero(bits))

def scale_binary(places: Nat, value: Nat) -> Nat:
  W.scale_binary(places, value)
