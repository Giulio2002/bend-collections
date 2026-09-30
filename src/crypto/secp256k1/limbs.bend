import Base

# Arithmetic modulo m = 2^256 - c on little-endian lists of natural-number
# limbs in radix 2^16 (secp256k1's p and n are both of this form, with
# c = 2^32 + 977 and c < 2^129). A list [l0, l1, ...] stands for
# l0 + 2^16 l1 + 2^32 l2 + ... ; a reduced element is 16 limbs, each below
# 2^16, with value below m.
#
# Bend's native runtime holds a Nat in one machine word and checks it stays
# below 2^48 (it aborts otherwise, it never wraps). The products of two
# limbs are below 2^32, a column of the schoolbook product below 2^36, and
# every other intermediate below 2^40, so no operation here comes near the
# bound (proofs/crypto/secp256k1/ proves the values; the bounds are shown in
# docs/CRYPTO_CONTRACTS.md).
#
# Only the constants 2, 255 and 256 appear: a 16-bit limb is split into two
# bytes with div/mod 256 (which compile to shifts and masks), so the proof
# checker, which keeps natural numbers in unary, never meets 2^16 as a
# literal.
#
# The reduction follows the folding reductions of libsecp256k1
# (secp256k1_fe_mul_inner, secp256k1_scalar_reduce_512) and of Fiat-Crypto's
# "solinas" reduction: with 2^256 = m + c, the high part hi of
# x = lo + 2^256 hi is folded as x == lo + c hi (mod m); a fixed number of
# folds (3 for p, 4 for n) brings any product of two reduced elements below
# 2^256, and one conditional subtraction of m (computed branch-free as
# "add c and look at bit 256") gives the representative below m.
#
# No function branches on a limb value: selection is arithmetic
# (b * x + (1 - b) * y with b in {0, 1}), every list has a fixed length,
# and loops run over public counts. Bend has no timing model, so this is a
# property of the code's shape, not a proved fact.

# ---- 16-bit limbs from bytes ----

# s mod 2^16 and s div 2^16
def lo16(+s: Nat) -> Nat:
  Nat.add(Nat.mod(s, 256n), Nat.mul(Nat.mod(Nat.div(s, 256n), 256n), 256n))

def hi16(+s: Nat) -> Nat:
  Nat.div(Nat.div(s, 256n), 256n)

# 2^16 - 1 - x for x below 2^16
def comp1(+x: Nat) -> Nat:
  Nat.add(Nat.sub(255n, Nat.mod(x, 256n)), Nat.mul(Nat.sub(255n, Nat.div(x, 256n)), 256n))

# ---- limb lists ----

def hd0(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}: 0n
    case x <> t: x

def tl(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}: Nil{}
    case x <> t: t

# limb-wise sum; the longer tail is kept
def add(xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs ys:
    case Nil{} _: ys
    case x <> xt Nil{}: x <> xt
    case x <> xt y <> yt: Nat.add(x, y) <> add(xt, yt)

# every limb times a
def scal(+a: Nat, ys: List<&2, Nat>) -> List<&2, Nat>:
  match ys:
    case Nil{}: Nil{}
    case y <> yt: Nat.mul(y, a) <> scal(a, yt)

# the schoolbook product without carries: conv(x :: xs, ys) = x ys + 2^16 conv(xs, ys)
def conv(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}: Nil{}
    case x <> xt: add(scal(x, ys), 0n <> conv(xt, ys))

def take(n: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match n xs:
    case 0n _: Nil{}
    case 1n+k Nil{}: Nil{}
    case 1n+k x <> t: x <> take(k, t)

def drop(n: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match n xs:
    case 0n _: xs
    case 1n+k Nil{}: Nil{}
    case 1n+k x <> t: drop(k, t)

# the value of the limbs (only ever of an empty list at run time: see carry)
def horner(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}: 0n
    case x <> t: Nat.add(Nat.mul(Nat.mul(horner(t), 256n), 256n), x)

# A carry pass: n limbs, each below 2^16, then one limb holding the carry u
# out of them plus the value of whatever is left of xs past n limbs (on
# every call below xs has at most n limbs, so that is the carry alone).
# Every function here looks at its list before producing anything, so that
# on a symbolic argument the proof checker stops at once.
def carry(n: Nat, xs: List<&2, Nat>, u: Nat) -> List<&2, Nat>:
  match n xs:
    case 0n Nil{}: [u]
    case 0n x <> t: [Nat.add(u, horner(x <> t))]
    case 1n+k Nil{}:
      +s = Nat.add(u, 0n)
      lo16(s) <> carry(k, Nil{}, hi16(s))
    case 1n+k x <> t:
      +s = Nat.add(u, x)
      lo16(s) <> carry(k, t, hi16(s))

# every limb x becomes 2^16 - 1 - x
def comp(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}: Nil{}
    case x <> t: comp1(x) <> comp(t)

# b x + (1 - b) y, limb-wise, for b in {0, 1}
def pick1(+b: Nat, +x: Nat, +y: Nat) -> Nat:
  Nat.add(Nat.mul(x, b), Nat.mul(y, Nat.sub(1n, b)))

def select(+b: Nat, xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs ys:
    case x <> xt y <> yt: pick1(b, x, y) <> select(b, xt, yt)
    case _ _: Nil{}

# ---- reduction modulo m = 2^256 - c ----

# the normalized form of a value below 2^256: exactly 16 limbs below 2^16
def norm16(xs: List<&2, Nat>) -> List<&2, Nat>:
  take(16n, carry(32n, xs, 0n))

# lo + c hi, for x = lo + 2^256 hi: congruent to x modulo m
def fold(+c: List<&2, Nat>, +xs: List<&2, Nat>) -> List<&2, Nat>:
  add(take(16n, xs), conv(drop(16n, xs), c))

def rounds(k: Nat, +c: List<&2, Nat>, xs: List<&2, Nat>) -> List<&2, Nat>:
  match k:
    case 0n: xs
    case 1n+j: rounds(j, c, carry(32n, fold(c, xs), 0n))

# the part of a carried value above 2^256 (0 or 1 below)
def top(xs: List<&2, Nat>) -> Nat:
  horner(drop(16n, xs))

# t (16 limbs, value below 2^256) mod m: t + c has bit 256 set exactly when
# t >= m, and then its low 256 bits are t - m
def canon(+c: List<&2, Nat>, +t: List<&2, Nat>) -> List<&2, Nat>:
  +u = carry(32n, add(t, c), 0n)
  select(top(u), take(16n, u), t)

def reduce_go(+c: List<&2, Nat>, k: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  canon(c, take(16n, rounds(k, c, carry(32n, xs, 0n))))

# x mod m for x below 2^512, in k folds (x is looked at first, so that the
# proof checker keeps an unknown reduction folded)
def reduce(+c: List<&2, Nat>, k: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}: reduce_go(c, k, Nil{})
    case x <> t: reduce_go(c, k, x <> t)

# ---- negation and comparison modulo m, from c ----

# m - b = (2^256 - 1 - (b + c)) + 1, for b < m (so b + c < 2^256); no
# constant but c is ever formed
def neg_raw(+c: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  add(comp(norm16(add(b, c))), [1n])

# x < m, i.e. x + c < 2^256, for x of 16 limbs below 2^16
def ltm(+c: List<&2, Nat>, x: List<&2, Nat>) -> Bool:
  Nat.is_eq(top(carry(32n, add(x, c), 0n)), 0n)

# ---- comparisons and bits ----

def b2n(b: Bool) -> Nat:
  match b:
    case True{}: 1n
    case False{}: 0n

# 1 when the value of xs is below the value of ys plus br, else 0 (the
# borrow out of xs - ys - br), for lists of the same length
def borrow(xs: List<&2, Nat>, ys: List<&2, Nat>, br: Nat) -> Nat:
  match xs ys:
    case x <> xt y <> yt: borrow(xt, yt, b2n(Nat.is_lt(x, Nat.add(br, y))))
    case _ _: br

def lt(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  Nat.is_eq(borrow(xs, ys, 0n), 1n)

# OR of all limbs being nonzero, without an early exit
def nonzero(xs: List<&2, Nat>, acc: Nat) -> Nat:
  match xs:
    case Nil{}: acc
    case x <> t: nonzero(t, Nat.add(acc, x))

def is_zero(xs: List<&2, Nat>) -> Bool:
  Nat.is_eq(nonzero(xs, 0n), 0n)

def diff(xs: List<&2, Nat>, ys: List<&2, Nat>, acc: Nat) -> Nat:
  match xs ys:
    case +x <> xt +y <> yt: diff(xt, yt, Nat.add(acc, Nat.add(Nat.sub(x, y), Nat.sub(y, x))))
    case _ _: acc

def eq(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  Nat.is_eq(diff(xs, ys, 0n), 0n)

# the k low bits of x, most significant first
def bits_of(k: Nat, +x: Nat) -> List<&2, Nat>:
  match k:
    case 0n: Nil{}
    case 1n+j: List.append(&2, Nat, bits_of(j, Nat.div(x, 2n)), [Nat.mod(x, 2n)])

# every bit flipped: the bits of 2^k - 1 - x from those of x
def cbits(bs: List<&2, Nat>) -> List<&2, Nat>:
  match bs:
    case Nil{}: Nil{}
    case b <> t: Nat.sub(1n, b) <> cbits(t)

# all bits of a limb list, most significant first (16 per limb)
def bits(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}: Nil{}
    case x <> t: List.append(&2, Nat, bits(t), bits_of(16n, x))

# the same in linear time, as the scalar multiplications read them:
# bits_of(k, x) ++ acc, and bits(xs) ++ acc (proofs: pmul.bend bitsf_is)
def bits_acc(k: Nat, +x: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match k:
    case 0n: acc
    case 1n+j: bits_acc(j, Nat.div(x, 2n), Nat.mod(x, 2n) <> acc)

def bits_go(xs: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}: acc
    case x <> t: bits_go(t, bits_acc(16n, x, acc))

def bitsf(xs: List<&2, Nat>) -> List<&2, Nat>:
  bits_go(xs, Nil{})
