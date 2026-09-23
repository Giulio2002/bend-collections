import Base

# All bits are represented explicitly: no Nat holds a full-width integer.
def zero() -> Word(64n):
  Word.zero(64n)

def inc(w: Word(64n)) -> Word(64n):
  Word.inc(64n, w)

def add(a: Word(64n), b: Word(64n)) -> Word(64n):
  Word.add(64n, a, b)

def neg(w: Word(64n)) -> Word(64n):
  Word.inc(64n, Word.not(64n, w))

def last(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+0n:
      match w:
        case WCon{b, tail}:
          b
    case 1n+1n+p:
      match w:
        case WCon{b, tail}:
          last(1n+p, tail)

def is_zero(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{b, tail}:
          Bool.not(b) && is_zero(p, tail)

def signed_order(a: Word(64n), b: Word(64n), sa: Bool, sb: Bool) -> Bool:
  match sa sb:
    case True{} False{}:
      True{}
    case False{} True{}:
      False{}
    case x y:
      Cmp.is_le(Word.cmp(64n, a, b))

def le(+a: Word(64n), +b: Word(64n)) -> Bool:
  signed_order(a, b, last(64n, a), last(64n, b))

def bit_u32(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1

type Division<-n: Nat> is Data:
  Div{quotient: Word(n), remainder: U32}

def digit_result(p: Nat, q: Word(p), r: U32, subtract: Bool) -> Division<1n+p>:
  match subtract:
    case False{}:
      Div{WCon{False{}, q}, r}
    case True{}:
      Div{WCon{True{}, q}, U32.sub(r, 1000000)}

def digit_compare(p: Nat, q: Word(p), +r: U32) -> Division<1n+p>:
  digit_result(p, q, r, U32.is_ge(r, 1000000))

def digit(p: Nat, b: Bool, prior: Division<p>) -> Division<1n+p>:
  Div{q, r} = prior
  digit_compare(p, q, U32.add(U32.mul(r, 2), bit_u32(b)))

# Binary long division, processing the most significant bit first. The partial
# remainder stays below 1,000,000; the next candidate fits in U32 (<2,000,000).
def div_million(+n: Nat, w: Word(n)) -> Division<n>:
  match n:
    case 0n:
      Div{WNil{}, 0}
    case 1n+p:
      match w:
        case WCon{b, tail}:
          digit(p, b, div_million(p, tail))

def quotient(r: Division<64n>) -> Word(64n):
  Div{q, rem} = r
  q

def unsigned_milliseconds(w: Word(64n)) -> Word(64n):
  quotient(div_million(64n, w))

def signed_milliseconds(w: Word(64n), negative: Bool) -> Word(64n):
  match negative:
    case False{}:
      unsigned_milliseconds(w)
    case True{}:
      neg(unsigned_milliseconds(neg(w)))

def milliseconds(+w: Word(64n)) -> Word(64n):
  signed_milliseconds(w, last(64n, w))

# Exact limb boundary used by the host bridge; limbs themselves are primitive U32.
def join(n: Nat, +m: Nat, a: Word(n), b: Word(m)) -> Word(Nat.add(n, m)):
  match n:
    case 0n:
      b
    case 1n+p:
      match a:
        case WCon{h, tail}:
          WCon{h, join(p, m, tail, b)}

type Parts<-n: Nat, -m: Nat> is Data:
  Split{low: Word(n), high: Word(m)}

def split_cons(-n: Nat, -m: Nat, h: Bool, parts: Parts<n, m>) -> Parts<1n+n, m>:
  Split{low, high} = parts
  Split{WCon{h, low}, high}

def split(n: Nat, +m: Nat, w: Word(Nat.add(n, m))) -> Parts<n, m>:
  match n:
    case 0n:
      Split{WNil{}, w}
    case 1n+p:
      match w:
        case WCon{h, tail}:
          split_cons(p, m, h, split(p, m, tail))

def pack(low: U32, high: U32) -> Word(64n):
  match low high:
    case U32{lo} U32{hi}:
      join(32n, 32n, lo, hi)

def limbs(parts: Parts<32n, 32n>) -> U32 & U32:
  Split{lo, hi} = parts
  (U32{lo}, U32{hi})

def unpack(w: Word(64n)) -> U32 & U32:
  limbs(split(32n, 32n, w))
