import Base
import ../types/model.bend as T
import ../spec/clock.bend as Clock
import ./cache.bend as C
import ./public.bend as Pub
import ./driver.bend as D
import ./wide.bend as W
import ./entry_ops.bend as Entry

# Host boundary in Bend. src/adapter.ts passes integers as decimal text
# (JS String(bigint)), naturals as Nat (a JS BigInt at runtime) and strings
# unchanged; every range check, sign mapping, limb split and rendering below is
# Bend code proved against spec/host.bend and spec/numeric.bend
# (proofs/host_numeric.bend). The host step functions begin/answer are the
# only transitions the adapter's loop invokes (proofs/host_loop.bend).

# ---------------------------------------------------------------------------
# Decimal input. Integers arrive as decimal text; no runtime Nat can hold a
# 64-bit value (compiled Nat is limited to 2^48), so digits stay symbolic and
# the binary word is obtained by exact halving of the decimal digit list.
type Digit is Data:
  D0{}
  D1{}
  D2{}
  D3{}
  D4{}
  D5{}
  D6{}
  D7{}
  D8{}
  D9{}

def pick(found: Bool, d: Digit, rest: Maybe<&2, Digit>) -> Maybe<&2, Digit>:
  match found:
    case True{}: Some{d}
    case False{}: rest

def search(+c: Char, cs: String, ds: List<&2, Digit>) -> Maybe<&2, Digit>:
  match cs ds:
    case SCon{x, ct} Con{d, dt}: pick(Char.is_eq(c, x), d, search(c, ct, dt))
    case x y: None{}

def all_digits() -> List<&2, Digit>:
  [D0{}, D1{}, D2{}, D3{}, D4{}, D5{}, D6{}, D7{}, D8{}, D9{}]

def digit(c: Char) -> Maybe<&2, Digit>:
  search(c, "0123456789", all_digits())

def cons(d: Maybe<&2, Digit>, rest: Maybe<&2, List<&2, Digit>>) -> Maybe<&2, List<&2, Digit>>:
  match d rest:
    case Some{x} Some{xs}: Some{Con{x, xs}}
    case x y: None{}

# All characters are digits: the big-endian digit list.
def digits(s: String) -> Maybe<&2, List<&2, Digit>>:
  match s:
    case SNil{}: Some{Nil{}}
    case SCon{c, t}: cons(digit(c), digits(t))

# A natural numeral: nonempty digit string.
def numeral(s: String) -> Maybe<&2, List<&2, Digit>>:
  match s:
    case SNil{}: None{}
    case SCon{c, t}: digits(SCon{c, t})

type Parsed is Data:
  Parsed{negative: Bool, magnitude: List<&2, Digit>}

def sign(negative: Bool, m: Maybe<&2, List<&2, Digit>>) -> Maybe<&2, Parsed>:
  match m:
    case None{}: None{}
    case Some{v}: Some{Parsed{negative, v}}

def signed(minus: Bool, c: Char, t: String) -> Maybe<&2, Parsed>:
  match minus:
    case True{}: sign(True{}, numeral(t))
    case False{}: sign(False{}, numeral(SCon{c, t}))

def integer(s: String) -> Maybe<&2, Parsed>:
  match s:
    case SNil{}: None{}
    case SCon{+c, t}: signed(Char.is_eq(c, '-'), c, t)

type Half is Data:
  Half{quotient: List<&2, Digit>, bit: Bool}

def prepend(d: Digit, h: Half) -> Half:
  Half{q, b} = h
  Half{Con{d, q}, b}

# Long division of a big-endian digit list by two with incoming remainder r:
# quotient digits and the final remainder bit.
def halve(ds: List<&2, Digit>, r: Bool) -> Half:
  match ds r:
    case Nil{} r0: Half{Nil{}, r0}
    case Con{D0{}, t} False{}: prepend(D0{}, halve(t, False{}))
    case Con{D1{}, t} False{}: prepend(D0{}, halve(t, True{}))
    case Con{D2{}, t} False{}: prepend(D1{}, halve(t, False{}))
    case Con{D3{}, t} False{}: prepend(D1{}, halve(t, True{}))
    case Con{D4{}, t} False{}: prepend(D2{}, halve(t, False{}))
    case Con{D5{}, t} False{}: prepend(D2{}, halve(t, True{}))
    case Con{D6{}, t} False{}: prepend(D3{}, halve(t, False{}))
    case Con{D7{}, t} False{}: prepend(D3{}, halve(t, True{}))
    case Con{D8{}, t} False{}: prepend(D4{}, halve(t, False{}))
    case Con{D9{}, t} False{}: prepend(D4{}, halve(t, True{}))
    case Con{D0{}, t} True{}: prepend(D5{}, halve(t, False{}))
    case Con{D1{}, t} True{}: prepend(D5{}, halve(t, True{}))
    case Con{D2{}, t} True{}: prepend(D6{}, halve(t, False{}))
    case Con{D3{}, t} True{}: prepend(D6{}, halve(t, True{}))
    case Con{D4{}, t} True{}: prepend(D7{}, halve(t, False{}))
    case Con{D5{}, t} True{}: prepend(D7{}, halve(t, True{}))
    case Con{D6{}, t} True{}: prepend(D8{}, halve(t, False{}))
    case Con{D7{}, t} True{}: prepend(D8{}, halve(t, True{}))
    case Con{D8{}, t} True{}: prepend(D9{}, halve(t, False{}))
    case Con{D9{}, t} True{}: prepend(D9{}, halve(t, True{}))

def split(-p: Nat, h: Half, f: List<&2, Digit> -> Bool -> Word(1n+p) & List<&2, Digit>) -> Word(1n+p) & List<&2, Digit>:
  Half{q, b} = h
  f(q)(b)

def attach(b: Bool, -p: Nat, r: Word(p) & List<&2, Digit>) -> Word(1n+p) & List<&2, Digit>:
  (w, left) = r
  (WCon{b, w}, left)

# n bits of the value (least significant first) and the leftover quotient.
def binary(n: Nat, ds: List<&2, Digit>) -> Word(n) & List<&2, Digit>:
  match n:
    case 0n: (WNil{}, ds)
    case 1n+p: split(p, halve(ds, False{}), q => b => attach(b, p, binary(p, q)))

def zeros(ds: List<&2, Digit>) -> Bool:
  match ds:
    case Nil{}: True{}
    case Con{D0{}, t}: zeros(t)
    case Con{d, t}: False{}

def fit(-n: Nat, msg: String, w: Word(n), ok: Bool) -> Result<&2, &2, String, Word(n)>:
  match ok:
    case True{}: Done{w}
    case False{}: Fail{msg}

def fit_pair(-n: Nat, msg: String, r: Word(n) & List<&2, Digit>) -> Result<&2, &2, String, Word(n)>:
  (w, left) = r
  fit(n, msg, w, zeros(left))

def fit_digits(+n: Nat, msg: String, m: Maybe<&2, List<&2, Digit>>) -> Result<&2, &2, String, Word(n)>:
  match m:
    case None{}: Fail{msg}
    case Some{ds}: fit_pair(n, msg, binary(n, ds))

# An unsigned width-bit value from a natural numeral below 2^width.
def unsigned_word(+n: Nat, msg: String, s: String) -> Result<&2, &2, String, Word(n)>:
  fit_digits(n, msg, numeral(s))

def threshold(n: Nat) -> Word(1n+n):
  match n:
    case 0n: WCon{True{}, WNil{}}
    case 1n+p: WCon{False{}, threshold(p)}

# Sign bit of a (1+n)-bit two's-complement word: the value is at least 2^n.
def sign_bit(+n: Nat, w: Word(1n+n)) -> Bool:
  Cmp.is_ge(Word.cmp(1n+n, w, threshold(n)))

def is_zero(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n: True{}
    case 1n+p:
      match w:
        case WCon{b, t}: Bool.and(Bool.not(b), is_zero(p, t))

def unit(n: Nat) -> Word(1n+n):
  WCon{True{}, Word.zero(n)}

def nonnegative_word(+n: Nat, msg: String, r: Result<&2, &2, String, Word(1n+n)>) -> Result<&2, &2, String, Word(1n+n)>:
  match r:
    case Fail{e}: Fail{e}
    case Done{+w}: fit(1n+n, msg, w, Bool.not(sign_bit(n, w)))

# -(k+1) is the complement of k, where k is one less than the magnitude.
def negative_nonzero(+n: Nat, msg: String, +k: Word(1n+n)) -> Result<&2, &2, String, Word(1n+n)>:
  fit(1n+n, msg, Word.not(1n+n, k), Bool.not(sign_bit(n, k)))

def negative_zero(+n: Nat, msg: String, +w: Word(1n+n), zero: Bool) -> Result<&2, &2, String, Word(1n+n)>:
  match zero:
    case True{}: Done{w}
    case False{}: negative_nonzero(n, msg, Word.sub(1n+n, w, unit(n)))

def negative_word(+n: Nat, msg: String, r: Result<&2, &2, String, Word(1n+n)>) -> Result<&2, &2, String, Word(1n+n)>:
  match r:
    case Fail{e}: Fail{e}
    case Done{+w}: negative_zero(n, msg, w, is_zero(1n+n, w))

def signed_fit(+n: Nat, +msg: String, m: Maybe<&2, Parsed>) -> Result<&2, &2, String, Word(1n+n)>:
  match m:
    case None{}: Fail{msg}
    case Some{Parsed{True{}, ds}}: negative_word(n, msg, fit_pair(1n+n, msg, binary(1n+n, ds)))
    case Some{Parsed{False{}, ds}}: nonnegative_word(n, msg, fit_pair(1n+n, msg, binary(1n+n, ds)))

# A signed (1+n)-bit value in [-2^n, 2^n) as its two's-complement word.
def signed_word(+n: Nat, +msg: String, s: String) -> Result<&2, &2, String, Word(1n+n)>:
  signed_fit(n, msg, integer(s))

def int64_word(+msg: String, s: String) -> Result<&2, &2, String, Word(64n)>:
  signed_word(63n, msg, s)

def uint64_key(s: String) -> Result<&2, &2, String, Word(64n)>:
  unsigned_word(64n, "uint64 key", s)

def int64_key(s: String) -> Result<&2, &2, String, Word(64n)>:
  int64_word("int64 key", s)

def time_of(r: Result<&2, &2, String, Word(64n)>) -> Result<&2, &2, String, T.Int64>:
  match r:
    case Fail{e}: Fail{e}
    case Done{w}: Done{T.I64{w}}

# Durations and clock samples: signed int64.
def time(s: String) -> Result<&2, &2, String, T.Int64>:
  time_of(int64_word("int64 value", s))

def sample_of(r: Result<&2, &2, String, T.Int64>) -> Clock.Event:
  match r:
    case Fail{e}: Clock.InvalidSample{e}
    case Done{t}: Clock.Sample{t}

# One clock sample as a provider event: in-range samples are accepted, every
# other value is an invalid sample (an execution failure, never a success).
def sample(s: String) -> Clock.Event:
  sample_of(time(s))

# A provider that threw.
def thrown() -> Clock.Event:
  Clock.ProviderException{"clock provider threw"}

def surrogate(+x: U32) -> Bool:
  Bool.and(U32.is_le(55296, x), U32.is_le(x, 57343))

def scalar(s: String) -> Bool:
  match s:
    case SNil{}: True{}
    case SCon{Chr{x}, t}: Bool.and(Bool.not(surrogate(x)), scalar(t))

def string_if(s: String, ok: Bool) -> Result<&2, &2, String, String>:
  match ok:
    case True{}: Done{s}
    case False{}: Fail{"unpaired surrogate"}

def string_key(+s: String) -> Result<&2, &2, String, String>:
  string_if(s, scalar(s))

def u32_of(r: Result<&2, &2, String, Word(32n)>) -> Result<&2, &2, String, U32>:
  match r:
    case Fail{e}: Fail{e}
    case Done{w}: Done{U32{w}}

def uint32(msg: String, s: String) -> Result<&2, &2, String, U32>:
  u32_of(unsigned_word(32n, msg, s))

def create_of(-K: Data, -V: Data, capacity: Result<&2, &2, String, U32>, size: Result<&2, &2, String, U32>) -> Result<&2, &2, String, C.Cache<K, V>>:
  match capacity size:
    case Fail{e} s: Fail{e}
    case Done{c} Fail{e}: Fail{e}
    case Done{+c} Done{+s}: C.new_with_size(K, V, c, s)

# Construction from host capacity/size text; out-of-range inputs are rejected
# before the upstream validation of C.new_with_size.
def create(-K: Data, -V: Data, capacity: String, size: String) -> Result<&2, &2, String, C.Cache<K, V>>:
  create_of(K, V, uint32("uint32 capacity/size", capacity), uint32("uint32 capacity/size", size))

# ---------------------------------------------------------------------------
# Output: words as decimal text (JS BigInt(text)).
# Doubling a little-endian decimal digit list and adding a carry bit.
def double_digits(ds: List<&2, Digit>, carry: Bool) -> List<&2, Digit>:
  match ds carry:
    case Nil{} True{}: Con{D1{}, Nil{}}
    case Nil{} False{}: Nil{}
    case Con{D0{}, rest} True{}: Con{D1{}, double_digits(rest, False{})}
    case Con{D1{}, rest} True{}: Con{D3{}, double_digits(rest, False{})}
    case Con{D2{}, rest} True{}: Con{D5{}, double_digits(rest, False{})}
    case Con{D3{}, rest} True{}: Con{D7{}, double_digits(rest, False{})}
    case Con{D4{}, rest} True{}: Con{D9{}, double_digits(rest, False{})}
    case Con{D5{}, rest} True{}: Con{D1{}, double_digits(rest, True{})}
    case Con{D6{}, rest} True{}: Con{D3{}, double_digits(rest, True{})}
    case Con{D7{}, rest} True{}: Con{D5{}, double_digits(rest, True{})}
    case Con{D8{}, rest} True{}: Con{D7{}, double_digits(rest, True{})}
    case Con{D9{}, rest} True{}: Con{D9{}, double_digits(rest, True{})}
    case Con{D0{}, rest} False{}: Con{D0{}, double_digits(rest, False{})}
    case Con{D1{}, rest} False{}: Con{D2{}, double_digits(rest, False{})}
    case Con{D2{}, rest} False{}: Con{D4{}, double_digits(rest, False{})}
    case Con{D3{}, rest} False{}: Con{D6{}, double_digits(rest, False{})}
    case Con{D4{}, rest} False{}: Con{D8{}, double_digits(rest, False{})}
    case Con{D5{}, rest} False{}: Con{D0{}, double_digits(rest, True{})}
    case Con{D6{}, rest} False{}: Con{D2{}, double_digits(rest, True{})}
    case Con{D7{}, rest} False{}: Con{D4{}, double_digits(rest, True{})}
    case Con{D8{}, rest} False{}: Con{D6{}, double_digits(rest, True{})}
    case Con{D9{}, rest} False{}: Con{D8{}, double_digits(rest, True{})}

# Decimal digits (least significant first) of a word, most significant bit
# processed last: value(WCon{b, t}) = b + 2 * value(t).
def decimal(n: Nat, w: Word(n)) -> List<&2, Digit>:
  match n:
    case 0n: Nil{}
    case 1n+p:
      match w:
        case WCon{b, t}: double_digits(decimal(p, t), b)

def digit_char(d: Digit) -> Char:
  match d:
    case D0{}: '0'
    case D1{}: '1'
    case D2{}: '2'
    case D3{}: '3'
    case D4{}: '4'
    case D5{}: '5'
    case D6{}: '6'
    case D7{}: '7'
    case D8{}: '8'
    case D9{}: '9'

def render(ds: List<&2, Digit>, acc: String) -> String:
  match ds:
    case Nil{}: acc
    case Con{d, rest}: render(rest, SCon{digit_char(d), acc})

def render_all(ds: List<&2, Digit>) -> String:
  match ds:
    case Nil{}: "0"
    case Con{d, rest}: render(Con{d, rest}, SNil{})

# Unsigned decimal text of a width-bit word.
def unsigned_text(n: Nat, w: Word(n)) -> String:
  render_all(decimal(n, w))

def signed_text(+n: Nat, +w: Word(1n+n), negative: Bool) -> String:
  match negative:
    case False{}: unsigned_text(1n+n, w)
    case True{}: SCon{'-', unsigned_text(1n+n, Word.inc(1n+n, Word.not(1n+n, w)))}

# Signed decimal text of a two's-complement word: int64 keys returned to JS.
def int64_text(+w: Word(64n)) -> String:
  signed_text(63n, w, sign_bit(63n, w))

# Unsigned decimal text of a 64-bit word: counters and uint64 keys.
def uint64_text(w: Word(64n)) -> String:
  unsigned_text(64n, w)

# ---------------------------------------------------------------------------
# Host step machine. The adapter calls begin once, then answer once per Ask
# with the provider's event, and adopts Return/Raise unchanged.
type Action<-K: Data, -V: Data> is Data:
  Return{cache: C.Cache<K, V>, answer: Pub.Answer<K, V>}
  Raise{cache: C.Cache<K, V>, error: Clock.Error}
  Ask{pending: Pub.Pending<K, V>}

def act(-K: Data, -V: Data, progress: Pub.Progress<K, V>) -> Action<K, V>:
  match progress:
    case Pub.Finished{c, a}: Return{c, a}
    case Pub.Waiting{p}: Ask{p}

def begin(-K: Data, -V: Data, encode: K -> String, zero_key: K, zero_value: V, +c: C.Cache<K, V>, request: Pub.Request<K, V>) -> Action<K, V>:
  act(K, V, Pub.start(K, V, encode, zero_key, zero_value, c, request))

def continued(-K: Data, -V: Data, step: D.Step<K, V>) -> Action<K, V>:
  match step:
    case D.Continue{p}: act(K, V, p)
    case D.Stopped{c, e}: Raise{c, e}

def answer(-K: Data, -V: Data, zero_value: V, pending: Pub.Pending<K, V>, event: Clock.Event) -> Action<K, V>:
  continued(K, V, D.advance(K, V, zero_value, pending, event))

# ---------------------------------------------------------------------------
# Runtime self-check used by tests (CheckInvariants): bounded, consistent,
# duplicate-free recency. It is a test oracle, not part of any public
# operation; the adapter also compares the stored keys' codes with the order.
def member(+x: String, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}: False{}
    case Con{+y, t}: Bool.or(String.eq(x, y), member(x, t))

def unique(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}: True{}
    case Con{+x, +t}: Bool.and(Bool.not(member(x, t)), unique(t))

def consistent(-K: Data, -V: Data, +c: C.Cache<K, V>) -> Bool:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  Bool.and(Bool.and(Nat.is_le(List.length(&2, String, order), cap), Nat.is_eq(C.map_size(K, V, C.State{cap, table, order, life, counts, cb}), List.length(&2, String, order))), Bool.and(unique(order), Nat.is_eq(List.length(&2, T.Entry<K, V>, C.entries(K, V, C.State{cap, table, order, life, counts, cb})), List.length(&2, String, order))))

# Original keys of the stored entries, oldest first.
def keys(-K: Data, -V: Data, c: C.Cache<K, V>) -> List<&2, K>:
  Entry.keys_of(K, V, C.entries(K, V, c))
