import Base

# Limb lists over Nat for the fast field of fe.bend: the reference algorithms
# whose unrolled forms are the straight-line field operations of fe.bend
# (tools/gen_fe.py writes those by evaluating these definitions on 15
# symbolic limbs; the proofs check each unrolled operation against its
# reference form by evaluation, then reason about the reference form by
# induction), and the rarely used conversions (bits, bytes, the canonical
# form), which run in this list form.
#
# Radix R = 2^17 (a parameter: the callers compute it once from their
# symbolic one, see fe.bend); every Nat stays below 2^48, the native
# backend's Nat bound (proved: spec/crypto/curve25519/fe.bend, Mul.fits,
# Sq.fits, Carry.fits).

# ---- polynomial operations ----

# limbwise sum; the longer tail is kept
def addl(xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      ys
    case Con{x, xt}:
      match ys:
        case Nil{}:
          Con{x, xt}
        case Con{y, yt}:
          Con{Nat.add(x, y), addl(xt, yt)}

# every limb times a (a on the left)
def scal(+a: Nat, ys: List<&2, Nat>) -> List<&2, Nat>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{y, yt}:
      Con{Nat.mul(a, y), scal(a, yt)}

# every limb times k (k on the right: the checker never unfolds a constant k)
def scal_r(ys: List<&2, Nat>, +k: Nat) -> List<&2, Nat>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{y, yt}:
      Con{Nat.mul(y, k), scal_r(yt, k)}

# the schoolbook product: conv(x :: xs, y :: ys) = x y :: (x ys + conv(xs, y :: ys))
def conv(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, xt}:
      match ys:
        case Nil{}:
          Nil{}
        case Con{+y, +yt}:
          Con{Nat.mul(x, y), addl(scal(x, yt), conv(xt, Con{y, yt}))}

# a b through the native 32-bit multiplier (exact when a b < 2^32): a Nat
# product checks the 48-bit bound with a division, a U32 product does not
def pu(+a: Nat, +b: Nat) -> Nat:
  U32.to_nat(U32.mul(U32.from_nat(a), U32.from_nat(b)))

# a b for a, b < 2^19: b split at bit 9, both half products below 2^29
def pm(+a: Nat, +b: Nat) -> Nat:
  Nat.add(pu(a, Nat.mod(b, 512n)), Nat.mul(pu(a, Nat.div(b, 512n)), 512n))

# scal and conv with pm
def scalp(+a: Nat, ys: List<&2, Nat>) -> List<&2, Nat>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{y, yt}:
      Con{pm(a, y), scalp(a, yt)}

def convp(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, xt}:
      match ys:
        case Nil{}:
          Nil{}
        case Con{+y, +yt}:
          Con{pm(x, y), addl(scalp(x, yt), convp(xt, Con{y, yt}))}

# every limb doubled
def dbl(ys: List<&2, Nat>) -> List<&2, Nat>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{+y, yt}:
      Con{Nat.add(y, y), dbl(yt)}

# the square: (x + R t)^2 = x^2 + R (2 x t0) + R^2 (2 x tt + t^2), each
# cross product once (with the other factor doubled)
def sqp(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +xt}:
      match xt:
        case Nil{}:
          Con{pm(x, x), Nil{}}
        case Con{+t0, +tt}:
          Con{pm(x, x), Con{pm(x, Nat.add(t0, t0)), addl(scalp(x, dbl(tt)), sqp(xt))}}

def take(n: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      match xs:
        case Nil{}:
          Nil{}
        case Con{x, xt}:
          Con{x, take(m, xt)}

def drop(n: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      xs
    case 1n+m:
      match xs:
        case Nil{}:
          Nil{}
        case Con{x, xt}:
          drop(m, xt)

# the product's limbs 15.. folded down by 19: 2^255 == 19 (mod p)
def fold(+zs: List<&2, Nat>) -> List<&2, Nat>:
  addl(take(15n, zs), scal_r(drop(15n, zs), 19n))

# x + k - y limbwise (k a multiple of p with every limb above y's)
def subl(xs: List<&2, Nat>, ys: List<&2, Nat>, ks: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, xt}:
      match ys:
        case Nil{}:
          Nil{}
        case Con{y, yt}:
          match ks:
            case Nil{}:
              Nil{}
            case Con{k, kt}:
              Con{Nat.sub(Nat.add(x, k), y), subl(xt, yt, kt)}

# n copies of k after h
def rep(n: Nat, +k: Nat, t: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      t
    case 1n+m:
      Con{k, rep(m, k, t)}

# 8 p = 2^258 - 152 in 15 limbs, each at least 2^19:
# [8 R - 152, 8 R - 8, ..., 8 R - 8]
def kp8(+R: Nat) -> List<&2, Nat>:
  Con{Nat.sub(Nat.mul(R, 8n), 152n), rep(14n, Nat.sub(Nat.mul(R, 8n), 8n), Nil{})}

# s == 0: xs; s == 1: ys; limbwise x (1 - s) + y s
def sel(+s: Nat, xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, xt}:
      match ys:
        case Nil{}:
          Nil{}
        case Con{y, yt}:
          Con{Nat.add(Nat.mul(x, Nat.sub(1n, s)), Nat.mul(y, s)), sel(s, xt, yt)}

# ---- carries ----

type Cr is Data:
  Cr{limbs: List<&2, Nat>, out: Nat}

def cr_limbs(r: Cr) -> List<&2, Nat>:
  match r:
    case Cr{a, c}:
      a

def cr_out(r: Cr) -> Nat:
  match r:
    case Cr{a, c}:
      c

def cr_con(l: Nat, r: Cr) -> Cr:
  match r:
    case Cr{a, c}:
      Cr{Con{l, a}, c}

# one carry pass with a carry in: limbs below R and the carry out
def carry(+R: Nat, xs: List<&2, Nat>, c: Nat) -> Cr:
  match xs:
    case Nil{}:
      Cr{Nil{}, c}
    case Con{h, t}:
      +s = Nat.add(h, c)
      cr_con(Nat.mod(s, R), carry(R, t, Nat.div(s, R)))

# the same with no carry in
def carry0(+R: Nat, xs: List<&2, Nat>) -> Cr:
  match xs:
    case Nil{}:
      Cr{Nil{}, 0n}
    case Con{+h, t}:
      cr_con(Nat.mod(h, R), carry(R, t, Nat.div(h, R)))

# the carry out c of the top limb re-enters as 19 c (2^255 == 19 mod p):
# limb 0 takes t = r0 + 19 c mod R, limb 1 the rest of t
def pass_fin(+R: Nat, r: Cr) -> List<&2, Nat>:
  match r:
    case Cr{ls, c}:
      match ls:
        case Nil{}:
          Nil{}
        case Con{r0, rt}:
          match rt:
            case Nil{}:
              Nil{}
            case Con{r1, rs}:
              +t = Nat.add(r0, Nat.mul(c, 19n))
              Con{Nat.mod(t, R), Con{Nat.add(r1, Nat.div(t, R)), rs}}

def pass(+R: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  pass_fin(R, carry0(R, xs))

# every carry moved one limb up at once, with no chain (for sums below
# 2^21, whose carries are below 2^4): limb i keeps x_i mod R and takes
# x_(i-1) div R; the top limb's carry re-enters limb 0 times 19
def pcs(+R: Nat, xs: List<&2, Nat>, +c: Nat) -> Cr:
  match xs:
    case Nil{}:
      Cr{Nil{}, c}
    case Con{+x, xt}:
      cr_con(Nat.add(Nat.mod(x, R), c), pcs(R, xt, Nat.div(x, R)))

def pc_fin(+m: Nat, r: Cr) -> List<&2, Nat>:
  match r:
    case Cr{ls, q}:
      Con{Nat.add(m, Nat.mul(q, 19n)), ls}

def pc(+R: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, xt}:
      pc_fin(Nat.mod(x, R), pcs(R, xt, Nat.div(x, R)))

# the operations of fe.bend on limb lists
def add_l(+R: Nat, xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  pc(R, addl(xs, ys))

def sub_l(+R: Nat, xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  pc(R, subl(xs, ys, kp8(R)))

def mul_l(+R: Nat, xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  pass(R, fold(convp(xs, ys)))

def sq_l(+R: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  pass(R, fold(sqp(xs)))

# two rounds of pc (limbs below 2^36: the first round leaves limbs below
# 2^20, the second below 2^19)
def mul_small_l(+R: Nat, xs: List<&2, Nat>, +k: Nat) -> List<&2, Nat>:
  pc(R, pc(R, scal_r(xs, k)))

# ---- the canonical representative ----

# x - p when x >= p, else x, for limbs below R and x < 2^255: x + 19
# carries out of 2^255 exactly when x >= p, and then its limbs hold x - p
def csub_fin(r: Cr, xs: List<&2, Nat>) -> List<&2, Nat>:
  match r:
    case Cr{ys, q}:
      sel(q, xs, ys)

def csub(+R: Nat, +xs: List<&2, Nat>) -> List<&2, Nat>:
  csub_fin(carry(R, xs, 19n), xs)

# two passes take limbs below 2^19 to limbs below R with a value below
# 2^255; then one conditional subtraction
def freeze_l(+R: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  csub(R, pass(R, pass(R, xs)))

# ---- bits and bytes ----

# the low w bits of x, least significant first
def bits(w: Nat, +x: Nat) -> List<&2, Nat>:
  match w:
    case 0n:
      Nil{}
    case 1n+m:
      Con{Nat.mod(x, 2n), bits(m, Nat.div(x, 2n))}

def app(xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      ys
    case Con{x, xt}:
      Con{x, app(xt, ys)}

# the low w bits of every limb, in order
def bits_all(+w: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, xt}:
      app(bits(w, x), bits_all(w, xt))

# the number whose bits (least significant first) are the first w of bs
def unbits(w: Nat, bs: List<&2, Nat>) -> Nat:
  match w:
    case 0n:
      0n
    case 1n+m:
      match bs:
        case Nil{}:
          0n
        case Con{b, bt}:
          Nat.add(b, Nat.double(unbits(m, bt)))

# n limbs of w bits each from the bit list (missing bits are 0)
def group(+w: Nat, n: Nat, +bs: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{unbits(w, bs), group(w, m, drop(w, bs))}

def nat_of(xs: List<&2, U32>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, xt}:
      Con{U32.to_nat(x), nat_of(xt)}

def u32_of(xs: List<&2, Nat>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, xt}:
      Con{U32.from_nat(x), u32_of(xt)}

# 15 limbs of 17 bits from 32 bytes, bit 255 dropped (RFC 7748 decodeUCoordinate)
def of_bytes_l(bs: List<&2, U32>) -> List<&2, Nat>:
  group(17n, 15n, take(255n, bits_all(8n, nat_of(bs))))

# 32 bytes from 15 limbs of 17 bits (a value below 2^255)
def to_bytes_l(xs: List<&2, Nat>) -> List<&2, U32>:
  u32_of(group(8n, 32n, bits_all(17n, xs)))

def sum(xs: List<&2, Nat>, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{x, xt}:
      sum(xt, Nat.add(acc, x))

def head(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, xt}:
      x
