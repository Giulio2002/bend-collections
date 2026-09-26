import Base

# The 64-bit word model: a Word(n) denotes the natural number of its bits
# (least significant first), and machine operations are specified through
# Nat arithmetic (modulo 2^n, unsigned and signed quotients). Shared by the
# src/math specs (u64, w64, hash) and by the proofs about words and U32s.

# Independent mathematical interpretation. Nat here is a specification value;
# no public executable conversion of a 64-bit number through Nat is required.
def bit_value(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

def unsigned(n: Nat, w: Word(n)) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match w:
        case WCon{b, tail}:
          Nat.add(bit_value(b), Nat.double(unsigned(p, tail)))

def sign_threshold(n: Nat) -> Word(1n+n):
  match n:
    case 0n:
      WCon{True{}, WNil{}}
    case 1n+p:
      WCon{False{}, sign_threshold(p)}

def negative(+w: Word(64n)) -> Bool:
  Cmp.is_ge(Word.cmp(64n, w, sign_threshold(63n)))

def zero(w: Word(64n)) -> Bool:
  Cmp.is_eq(Word.cmp(64n, w, Word.zero(64n)))

def order(a: Word(64n), b: Word(64n), sign_a: Bool, sign_b: Bool) -> Bool:
  match sign_a sign_b:
    case False{} True{}:
      False{}
    case True{} False{}:
      True{}
    case x y:
      Cmp.is_le(Word.cmp(64n, a, b))

# These mathematical definitions specify modulo arithmetic through Nat values,
# independently of the implementation's ripple addition and binary long division.
def from_nat(n: Nat, +value: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{Nat.is_eq(Nat.mod(value, 2n), 1n), from_nat(p, Nat.div(value, 2n))}

def modulus() -> Nat:
  Nat.pow(2n, 64n)

# Observe the input constructor before evaluating mathematical division. This
# has the same from_nat(unsigned(input) / divisor) meaning; the structural guard
# keeps fixed large denominators from being expanded while input is unknown.
def unsigned_quotient(n: Nat, word: Word(n), d: U32) -> Word(n):
  match n:
    case 0n: WNil{}
    case 1n+ +p:
      match word:
        case WCon{bit, tail}:
          from_nat(1n+p, Nat.div(unsigned(1n+p, WCon{bit, tail}), U32.to_nat(d)))

def negative_quotient(n: Nat, word: Word(n), d: U32) -> Word(n):
  match n:
    case 0n: WNil{}
    case 1n+ +p:
      match word:
        case WCon{bit, tail}:
          from_nat(1n+p, Nat.sub(Nat.pow(2n, 1n+p), Nat.div(Nat.sub(Nat.pow(2n, 1n+p), unsigned(1n+p, WCon{bit, tail})), U32.to_nat(d))))

def quotient_signed(bits: Word(64n), negative: Bool) -> Word(64n):
  match negative:
    case False{}:
      unsigned_quotient(64n, bits, 1000000)
    case True{}:
      negative_quotient(64n, bits, 1000000)

# Mathematical multiplication by 2^places, specified without machine shifts.
def scale_binary(places: Nat, value: Nat) -> Nat:
  match places:
    case 0n:
      value
    case 1n+p:
      Nat.double(scale_binary(p, value))

# A 64-bit word from two 32-bit limbs (low first).
def join(n: Nat, +m: Nat, a: Word(n), b: Word(m)) -> Word(Nat.add(n, m)):
  match n:
    case 0n:
      b
    case 1n+p:
      match a:
        case WCon{h, tail}:
          WCon{h, join(p, m, tail, b)}

def pack(low: U32, high: U32) -> Word(64n):
  match low high:
    case U32{lo} U32{hi}:
      join(32n, 32n, lo, hi)

# The low k bits set, the rest clear.
def mask(+n: Nat, +k: Nat) -> Word(n):
  match n k:
    case 0n _:
      WNil{}
    case 1n+p 0n:
      WCon{False{}, mask(p, 0n)}
    case 1n+p 1n+j:
      WCon{True{}, mask(p, j)}
