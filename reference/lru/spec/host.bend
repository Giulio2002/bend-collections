import Base
import ./numeric.bend as N

# Independent meaning of the host values crossing the adapter boundary. The
# host passes integers as their decimal text (JS String(bigint)) and reads
# signed results back from decimal text (JS BigInt(string)); naturals cross as
# Nat, which the Bend runtime represents as a JS BigInt. No implementation or
# proof module is imported.

type Signed is Data:
  Signed{negative: Bool, magnitude: Nat}

def digit_pick(found: Bool, i: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match found:
    case True{}: Some{i}
    case False{}: rest

def digit_in(+c: Char, ds: String, +i: Nat) -> Maybe<&2, Nat>:
  match ds:
    case SNil{}: None{}
    case SCon{d, t}: digit_pick(Char.is_eq(c, d), i, digit_in(c, t, 1n+i))

# The value of a decimal digit character.
def digit_value(c: Char) -> Maybe<&2, Nat>:
  digit_in(c, "0123456789", 0n)

def place(d: Maybe<&2, Nat>, +len: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match d rest:
    case Some{x} Some{v}: Some{Nat.add(Nat.mul(x, Nat.pow(10n, len)), v)}
    case x y: None{}

# Positional value: each digit weighs 10 to the number of digits after it.
def positional(s: String) -> Maybe<&2, Nat>:
  match s:
    case SNil{}: Some{0n}
    case SCon{c, +t}: place(digit_value(c), String.length(t), positional(t))

# A natural numeral is a nonempty digit string.
def natural(s: String) -> Maybe<&2, Nat>:
  match s:
    case SNil{}: None{}
    case SCon{c, t}: positional(SCon{c, t})

def sign(negative: Bool, m: Maybe<&2, Nat>) -> Maybe<&2, Signed>:
  match m:
    case None{}: None{}
    case Some{v}: Some{Signed{negative, v}}

def signed(minus: Bool, c: Char, t: String) -> Maybe<&2, Signed>:
  match minus:
    case True{}: sign(True{}, natural(t))
    case False{}: sign(False{}, natural(SCon{c, t}))

# An integer numeral is an optional '-' followed by a natural numeral.
def integer(s: String) -> Maybe<&2, Signed>:
  match s:
    case SNil{}: None{}
    case SCon{+c, t}: signed(Char.is_eq(c, '-'), c, t)

# v < 2^width, stated without large constants: v survives the width-bit
# round trip (proofs/host_numeric.bend proves this equals v < 2^width).
def fits(+width: Nat, +v: Nat) -> Bool:
  Nat.is_eq(N.unsigned(width, N.from_nat(width, v)), v)

def fits_if(+width: Nat, v: Nat, ok: Bool) -> Maybe<&2, Word(width)>:
  match ok:
    case True{}: Some{N.from_nat(width, v)}
    case False{}: None{}

def bounded(+width: Nat, m: Maybe<&2, Nat>) -> Maybe<&2, Word(width)>:
  match m:
    case None{}: None{}
    case Some{+v}: fits_if(width, v, fits(width, v))

# An unsigned width-bit value: a natural numeral below 2^width.
def unsigned_text(+width: Nat, s: String) -> Maybe<&2, Word(width)>:
  bounded(width, natural(s))

# Two's complement of width 1+n. The sign bit is set exactly from 2^n on.
def sign_bit(+n: Nat, w: Word(1n+n)) -> Bool:
  Cmp.is_ge(Word.cmp(1n+n, w, N.sign_threshold(n)))

# 0 <= v < 2^n.
def half(+n: Nat, +v: Nat) -> Bool:
  Bool.and(fits(1n+n, v), Bool.not(sign_bit(n, N.from_nat(1n+n, v))))

def nonnegative_if(+n: Nat, v: Nat, ok: Bool) -> Maybe<&2, Word(1n+n)>:
  match ok:
    case True{}: Some{N.from_nat(1n+n, v)}
    case False{}: None{}

# -(k+1) is represented by the bitwise complement of k, for 0 <= k < 2^n.
def complement_if(+n: Nat, k: Nat, ok: Bool) -> Maybe<&2, Word(1n+n)>:
  match ok:
    case True{}: Some{Word.not(1n+n, N.from_nat(1n+n, k))}
    case False{}: None{}

def negative_of(+n: Nat, v: Nat) -> Maybe<&2, Word(1n+n)>:
  match v:
    case 0n: Some{N.from_nat(1n+n, 0n)}
    case 1n+ +k: complement_if(n, k, half(n, k))

def signed_of(+n: Nat, m: Maybe<&2, Signed>) -> Maybe<&2, Word(1n+n)>:
  match m:
    case None{}: None{}
    case Some{Signed{False{}, +v}}: nonnegative_if(n, v, half(n, v))
    case Some{Signed{True{}, v}}: negative_of(n, v)

# A signed (1+n)-bit value in [-2^n, 2^n): the integer numeral's word.
def signed_text(+n: Nat, s: String) -> Maybe<&2, Word(1n+n)>:
  signed_of(n, integer(s))

# int64: [-2^63, 2^63).
def int64_text(s: String) -> Maybe<&2, Word(64n)>:
  signed_text(63n, s)

def surrogate(+x: U32) -> Bool:
  Bool.and(U32.is_le(55296, x), U32.is_le(x, 57343))

# JS strings of Unicode scalar values: no unpaired surrogate code point.
def scalar(s: String) -> Bool:
  match s:
    case SNil{}: True{}
    case SCon{Chr{x}, t}: Bool.and(Bool.not(surrogate(x)), scalar(t))
