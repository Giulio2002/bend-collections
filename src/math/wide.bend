import Base

# Wide naturals for the software float (f64.bend): little-endian lists of
# 24-bit limbs, so every limb product and carry stays below 2^48 (Bend's
# runtime Nat bound). Values are kept normalized (no zero top limb), so zero
# is Nil and comparison can go by length.

def base() -> Nat:
  16777216n

def norm_last(+h: Nat) -> List<&2, Nat>:
  match h:
    case 0n:
      Nil{}
    case 1n+p:
      Con{1n+p, Nil{}}

def norm_cons(+h: Nat, t: List<&2, Nat>) -> List<&2, Nat>:
  match t:
    case Nil{}:
      norm_last(h)
    case Con{a, b}:
      Con{h, Con{a, b}}

def norm_go(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      norm_cons(h, norm_go(t))

def norm(xs: List<&2, Nat>) -> List<&2, Nat>:
  norm_go(xs)

# n < 2^48
def of_nat(+n: Nat) -> List<&2, Nat>:
  norm(Con{Nat.mod(n, base()), Con{Nat.div(n, base()), Nil{}}})

def is_zero(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

# the low 48 bits as a Nat
def low(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, Nil{}}:
      h
    case Con{+h, Con{g, t}}:
      Nat.add(h, Nat.mul(g, base()))

def length(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+length(t)

def bitn(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def pow2(k: Nat) -> Nat:
  match k:
    case 0n:
      1n
    case 1n+p:
      Nat.mul(pow2(p), 2n)

# ---- addition and subtraction ----

def add_go(xs: List<&2, Nat>, ys: List<&2, Nat>, +c: Nat) -> List<&2, Nat>:
  match xs ys:
    case Nil{} Nil{}:
      norm_last(c)
    case Nil{} Con{+y, yt}:
      Con{Nat.mod(Nat.add(y, c), base()), add_go(Nil{}, yt, Nat.div(Nat.add(y, c), base()))}
    case Con{+x, xt} Nil{}:
      Con{Nat.mod(Nat.add(x, c), base()), add_go(xt, Nil{}, Nat.div(Nat.add(x, c), base()))}
    case Con{+x, xt} Con{+y, yt}:
      Con{Nat.mod(Nat.add(Nat.add(x, y), c), base()), add_go(xt, yt, Nat.div(Nat.add(Nat.add(x, y), c), base()))}

def add(xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  add_go(xs, ys, 0n)

# xs - ys for ys <= xs
def sub_go(xs: List<&2, Nat>, ys: List<&2, Nat>, +b: Nat) -> List<&2, Nat>:
  match xs ys:
    case Nil{} _:
      Nil{}
    case Con{+x, xt} Nil{}:
      Con{Nat.mod(Nat.sub(Nat.add(x, base()), b), base()), sub_go(xt, Nil{}, bitn(Nat.is_lt(x, b)))}
    case Con{+x, xt} Con{+y, yt}:
      Con{Nat.mod(Nat.sub(Nat.add(x, base()), Nat.add(y, b)), base()), sub_go(xt, yt, bitn(Nat.is_lt(x, Nat.add(y, b))))}

def sub(xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  norm(sub_go(xs, ys, 0n))

def cmp_keep(c: Cmp, acc: Cmp) -> Cmp:
  match c:
    case EQ{}:
      acc
    case LT{}:
      LT{}
    case GT{}:
      GT{}

# ---- comparison ----

def cmp_pick(+x: Nat, +y: Nat, acc: Cmp) -> Cmp:
  cmp_keep(Nat.cmp(x, y), acc)

def cmp_go(xs: List<&2, Nat>, ys: List<&2, Nat>, acc: Cmp) -> Cmp:
  match xs ys:
    case Nil{} Nil{}:
      acc
    case Nil{} Con{y, yt}:
      LT{}
    case Con{x, xt} Nil{}:
      GT{}
    case Con{+x, xt} Con{+y, yt}:
      cmp_go(xt, yt, cmp_pick(x, y, acc))

def cmp(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Cmp:
  cmp_go(xs, ys, EQ{})

def lt(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  Cmp.is_lt(cmp(xs, ys))

# ---- multiplication ----

# ys * x + c for x < 2^24 (each limb step stays below 2^48)
def mul_limb(ys: List<&2, Nat>, +x: Nat, +c: Nat) -> List<&2, Nat>:
  match ys:
    case Nil{}:
      norm_last(c)
    case Con{+y, yt}:
      Con{Nat.mod(Nat.add(Nat.mul(y, x), c), base()), mul_limb(yt, x, Nat.div(Nat.add(Nat.mul(y, x), c), base()))}

def shift_limb(zs: List<&2, Nat>) -> List<&2, Nat>:
  match zs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{0n, Con{h, t}}

def mul(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, xt}:
      add(norm(mul_limb(ys, x, 0n)), shift_limb(mul(xt, ys)))

# ---- shifts ----

def shl_limbs(k: Nat, zs: List<&2, Nat>) -> List<&2, Nat>:
  match k:
    case 0n:
      zs
    case 1n+j:
      shift_limb(shl_limbs(j, zs))

# xs * 2^k
def shl(xs: List<&2, Nat>, +k: Nat) -> List<&2, Nat>:
  shl_limbs(Nat.div(k, 24n), norm(mul_limb(xs, pow2(Nat.mod(k, 24n)), 0n)))

def any_nonzero(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+h, t}:
      Bool.or(Nat.is_lt(0n, h), any_nonzero(t))

def drop_limbs(k: Nat, xs: List<&2, Nat>, +sticky: Bool) -> List<&2, Nat> & Bool:
  match k xs:
    case 0n _:
      (xs, sticky)
    case 1n+j Nil{}:
      (Nil{}, sticky)
    case 1n+j Con{+h, t}:
      drop_limbs(j, t, Bool.or(sticky, Nat.is_lt(0n, h)))

def head0(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      h

# every limb shifted right by r < 24, taking the low r bits of the next one
def shr_bits(xs: List<&2, Nat>, +r: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      Con{Nat.add(Nat.div(x, pow2(r)), Nat.mul(Nat.mod(head0(t), pow2(r)), pow2(Nat.sub(24n, r)))), shr_bits(t, r)}

def shr_fin(+r: Nat, p: List<&2, Nat> & Bool) -> List<&2, Nat> & Bool:
  (+xs, +sticky) = p
  (norm(shr_bits(xs, r)), Bool.or(sticky, Nat.is_lt(0n, Nat.mod(head0(xs), pow2(r)))))

# (xs / 2^k, whether any bit shifted out was set)
def shr_sticky(xs: List<&2, Nat>, +k: Nat) -> List<&2, Nat> & Bool:
  shr_fin(Nat.mod(k, 24n), drop_limbs(Nat.div(k, 24n), xs, False{}))

# the bit length of n < 2^48 plus k (the fuel bounds the halvings)
def nat_bits_go(f: Nat, n: Nat, +k: Nat) -> Nat:
  match f n:
    case 0n _:
      k
    case 1n+g 0n:
      k
    case 1n+g 1n+ +p:
      nat_bits_go(g, Nat.div(1n+p, 2n), 1n+k)

def nat_bits(n: Nat, +k: Nat) -> Nat:
  nat_bits_go(50n, n, k)

def top(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, Nil{}}:
      h
    case Con{h, Con{a, b}}:
      top(Con{a, b})

def bit_length_len(len: Nat, +t: Nat) -> Nat:
  match len:
    case 0n:
      0n
    case 1n+j:
      Nat.add(Nat.mul(24n, j), nat_bits(t, 0n))

# the number of significant bits (0 for zero)
def bit_length(+xs: List<&2, Nat>) -> Nat:
  bit_length_len(length(xs), top(xs))

def nth(xs: List<&2, Nat>, i: Nat) -> Nat:
  match xs i:
    case Nil{} _:
      0n
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      nth(t, j)

def bit(xs: List<&2, Nat>, +i: Nat) -> Nat:
  Nat.mod(Nat.div(nth(xs, Nat.div(i, 24n)), pow2(Nat.mod(i, 24n))), 2n)

# ---- division and square root ----

def div_pick(+ys: List<&2, Nat>, +q: List<&2, Nat>, +r: List<&2, Nat>, below: Bool) -> List<&2, Nat> & List<&2, Nat>:
  match below:
    case True{}:
      (shl(q, 1n), r)
    case False{}:
      (add(shl(q, 1n), of_nat(1n)), sub(r, ys))

def div_next(+ys: List<&2, Nat>, +q: List<&2, Nat>, +r: List<&2, Nat>) -> List<&2, Nat> & List<&2, Nat>:
  div_pick(ys, q, r, lt(r, ys))

# restoring division over the bits of xs, high to low: (quotient, remainder)
def div_go(k: Nat, +xs: List<&2, Nat>, +ys: List<&2, Nat>, st: List<&2, Nat> & List<&2, Nat>) -> List<&2, Nat> & List<&2, Nat>:
  match k st:
    case 0n _:
      st
    case 1n+ +j Tuple{+q, +r}:
      div_go(j, xs, ys, div_next(ys, q, add(shl(r, 1n), of_nat(bit(xs, j)))))

# (xs / ys, xs mod ys) for ys > 0
def divmod(+xs: List<&2, Nat>, +ys: List<&2, Nat>) -> List<&2, Nat> & List<&2, Nat>:
  div_go(bit_length(xs), xs, ys, (Nil{}, Nil{}))

def sqrt_pick(+r: List<&2, Nat>, +t: List<&2, Nat>, take: Bool) -> List<&2, Nat>:
  match take:
    case True{}:
      t
    case False{}:
      r

def sqrt_try(+n: List<&2, Nat>, +r: List<&2, Nat>, +t: List<&2, Nat>) -> List<&2, Nat>:
  sqrt_pick(r, t, Bool.not(lt(n, mul(t, t))))

# floor(sqrt n), bit by bit from 2^i with i = bit_length(n) / 2
def sqrt_go(k: Nat, +n: List<&2, Nat>, +r: List<&2, Nat>) -> List<&2, Nat>:
  match k:
    case 0n:
      r
    case 1n+ +j:
      sqrt_go(j, n, sqrt_try(n, r, add(r, shl(of_nat(1n), j))))

def isqrt(+n: List<&2, Nat>) -> List<&2, Nat>:
  sqrt_go(1n+Nat.div(bit_length(n), 2n), n, Nil{})

# xs / 2
def shr1(xs: List<&2, Nat>) -> List<&2, Nat>:
  norm(shr_bits(xs, 1n))

def frac_pick(+d: List<&2, Nat>, +q: List<&2, Nat>, +r2: List<&2, Nat>, below: Bool) -> List<&2, Nat> & List<&2, Nat>:
  match below:
    case True{}:
      (shl(q, 1n), r2)
    case False{}:
      (add(shl(q, 1n), Con{1n, Nil{}}), sub(r2, d))

# ---- fraction digits for the float's division and square root ----

# q, r after k steps of q := 2q + [2r >= d], r := 2r - [2r >= d] d, from a
# remainder r < d: q = floor(r0 2^k / d) and r its remainder
def frac_step(+d: List<&2, Nat>, st: List<&2, Nat> & List<&2, Nat>) -> List<&2, Nat> & List<&2, Nat>:
  (+q, +r) = st
  frac_pick(d, q, shl(r, 1n), lt(shl(r, 1n), d))

def frac_go(k: Nat, +d: List<&2, Nat>, st: List<&2, Nat> & List<&2, Nat>) -> List<&2, Nat> & List<&2, Nat>:
  match k:
    case 0n:
      st
    case 1n+j:
      frac_go(j, d, frac_step(d, st))

# floor(n 2^k / d) and its remainder, for d <= n < 2 d (one leading 1 bit)
def div_frac(+n: List<&2, Nat>, +d: List<&2, Nat>, +k: Nat) -> List<&2, Nat> & List<&2, Nat>:
  frac_go(k, d, (Con{1n, Nil{}}, sub(n, d)))

def bit_at_ge(+m: List<&2, Nat>, +s: Nat, +i: Nat, ge: Bool) -> Nat:
  match ge:
    case True{}:
      bit(m, Nat.sub(i, s))
    case False{}:
      0n

def bit_at(+m: List<&2, Nat>, +s: Nat, +i: Nat) -> Nat:
  bit_at_ge(m, s, i, Nat.is_le(s, i))

# digit-by-digit square root of N = m 2^s over the pairs of bits of N from
# position 2i + 1 down: rem := 4 rem + pair, t := 4 root + 1, and root gets
# a 1 when t fits (rem >= t). Ends with root = isqrt(N), rem = N - root^2.
def pair_at(+m: List<&2, Nat>, +s: Nat, +i: Nat) -> Nat:
  Nat.add(Nat.mul(bit_at(m, s, Nat.add(Nat.mul(i, 2n), 1n)), 2n), bit_at(m, s, Nat.mul(i, 2n)))

def root_pick(+root: List<&2, Nat>, +rem: List<&2, Nat>, +t: List<&2, Nat>, below: Bool) -> List<&2, Nat> & List<&2, Nat>:
  match below:
    case True{}:
      (shl(root, 1n), rem)
    case False{}:
      (add(shl(root, 1n), Con{1n, Nil{}}), sub(rem, t))

def root_try(+root: List<&2, Nat>, +rem: List<&2, Nat>, +t: List<&2, Nat>) -> List<&2, Nat> & List<&2, Nat>:
  root_pick(root, rem, t, lt(rem, t))

def root_step(+m: List<&2, Nat>, +s: Nat, +i: Nat, st: List<&2, Nat> & List<&2, Nat>) -> List<&2, Nat> & List<&2, Nat>:
  (+root, +rem) = st
  root_try(root, add(shl(rem, 2n), of_nat(pair_at(m, s, i))), add(shl(root, 2n), Con{1n, Nil{}}))

def root_go(k: Nat, +m: List<&2, Nat>, +s: Nat, st: List<&2, Nat> & List<&2, Nat>) -> List<&2, Nat> & List<&2, Nat>:
  match k:
    case 0n:
      st
    case 1n+ +j:
      root_go(j, m, s, root_step(m, s, j, st))

# (isqrt(m 2^s), m 2^s - isqrt^2) for m 2^s of at most 2k bits
def sqrt_rem(+m: List<&2, Nat>, +s: Nat, +k: Nat) -> List<&2, Nat> & List<&2, Nat>:
  root_go(k, m, s, (Nil{}, Nil{}))

def nat_pick(c: Bool, +a: Nat, +b: Nat) -> Nat:
  match c:
    case True{}:
      a
    case False{}:
      b
