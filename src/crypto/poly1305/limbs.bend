import Base

# Arithmetic modulo p = 2^130 - 5 on little-endian lists of U32 limbs of
# radix 2^8 (TweetNaCl's representation): a list [l0, l1, ...] stands for
# l0 + 2^8 l1 + 2^16 l2 + ... . Limbs may exceed 8 bits between carry
# passes; every operation below keeps them under 2^31 on the Poly1305 path
# (proofs/crypto/poly1305/ bounds each step), so no U32 operation wraps.
#
# Constant time: every loop runs over public lengths; the only data-dependent
# choice (the final conditional subtraction of p) is a mask select, with no
# branch and no secret-dependent memory access. Bend has no timing model, so
# this is a property of the code's shape, not a proved fact.

# The first limb (0 for the empty list) and the rest.
def hd0(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}: 0
    case x <> t: x

def tl(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}: Nil{}
    case x <> t: t

# Limb-wise sum (the shorter list is padded with zeros), no carries.
def add(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  match a b:
    case Nil{} _: b
    case x <> at Nil{}: x <> at
    case x <> at y <> bt: U32.add(x, y) <> add(at, bt)

# Every limb times c, no carries.
def scale(+c: U32, a: List<&2, U32>) -> List<&2, U32>:
  match a:
    case Nil{}: Nil{}
    case x <> t: U32.mul(x, c) <> scale(c, t)

# Schoolbook product, no carries: x r0 + 2^8 (x r1 + 2^8 (...)).
def mul(+x: List<&2, U32>, r: List<&2, U32>) -> List<&2, U32>:
  match r:
    case Nil{}: Nil{}
    case r0 <> rs: add(scale(r0, x), 0 <> mul(x, rs))

def take(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n xs:
    case 0n _: Nil{}
    case 1n+k Nil{}: Nil{}
    case 1n+k x <> rest: x <> take(k, rest)

def skip(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n xs:
    case 0n _: xs
    case 1n+k Nil{}: Nil{}
    case 1n+k x <> rest: skip(k, rest)

# The first n limbs, padded with zeros to exactly n.
def fit(n: Nat, +xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n: Nil{}
    case 1n+k: hd0(xs) <> fit(k, tl(xs))

# 2^136 = 64 p + 320: limbs 17.. are folded onto limbs 0.. times 320.
def fold(+z: List<&2, U32>) -> List<&2, U32>:
  add(take(17n, z), scale(320, skip(17n, z)))

# A carry pass over n limbs, each kept to 8 bits; the carry u and all limbs
# from n on (one, on the Poly1305 path) are summed into the top limb.
def carry(n: Nat, +ds: List<&2, U32>, u: U32) -> List<&2, U32>:
  match n:
    case 0n: [U32.add(u, hd0(ds))]
    case 1n+k:
      +s = U32.add(u, hd0(ds))
      U32.and(s, 255) <> carry(k, tl(ds), U32.shrn(s, 8n))

# Limb n (the top one) reduced to its low 2 bits, i.e. the value below 2^130
# when n = 16; quot is the rest of limb n, the multiple of 2^130.
def split(n: Nat, +xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n: [U32.and(hd0(xs), 3)]
    case 1n+k: hd0(xs) <> split(k, tl(xs))

def quot(n: Nat, +xs: List<&2, U32>) -> U32:
  match n:
    case 0n: U32.shrn(hd0(xs), 2n)
    case 1n+k: quot(k, tl(xs))

# Partial reduction of 17 limbs: carry, then 2^130 q = p q + 5 q, so q is
# folded back as 5 q on limb 0 and carried again. The result has limbs 0..15
# below 2^8 and a value below 5 * 2^128 < 2p.
def reduce(+d: List<&2, U32>) -> List<&2, U32>:
  +t = carry(16n, d, 0)
  carry(16n, add([U32.mul(quot(16n, t), 5)], split(16n, t)), 0)

# One Poly1305 block: h = (h + c) r, partially reduced mod p.
def block(+r: List<&2, U32>, h: List<&2, U32>, c: List<&2, U32>) -> List<&2, U32>:
  reduce(fold(mul(add(h, c), r)))

# 2^136 - p = 5 + 252 * 2^128.
def minus_p() -> List<&2, U32>:
  [5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 252]

# a when m is all zeros, b when m is all ones.
def pick(+m: U32, +a: U32, b: U32) -> U32:
  U32.xor(a, U32.and(m, U32.xor(a, b)))

def select(+m: U32, a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  match a b:
    case x <> at y <> bt: pick(m, x, y) <> select(m, at, bt)
    case _ _: Nil{}

# The low 16 limbs of h mod p, for h below 2p: e = h + 2^136 - p has bit 136
# set exactly when h >= p, and then its low limbs are those of h - p.
def freeze(+h: List<&2, U32>) -> List<&2, U32>:
  +e = carry(16n, add(h, minus_p()), 0)
  +b = U32.shrn(hd0(skip(16n, e)), 8n)
  select(U32.sub(0, b), take(16n, h), take(16n, e))

# n bytes of the value of ds + u (mod 2^(8n)).
def bytes(n: Nat, +ds: List<&2, U32>, u: U32) -> List<&2, U32>:
  match n:
    case 0n: Nil{}
    case 1n+k:
      +s = U32.add(u, hd0(ds))
      U32.and(s, 255) <> bytes(k, tl(ds), U32.shrn(s, 8n))
