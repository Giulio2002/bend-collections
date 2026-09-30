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

# ---- lists and bytes ----

def app(xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      ys
    case Con{x, xt}:
      Con{x, app(xt, ys)}

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

# ---- bytes and 17-bit limbs, regrouped through a bit buffer ----
# ---- GEN-PACK begin (tools/gen_pack.py) ----

# 2^n x
def shl(n: Nat, +x: Nat) -> Nat:
  match n:
    case 0n:
      x
    case 1n+m:
      Nat.double(shl(m, x))

# a byte as a Nat (below 256 whatever the U32 holds)
def b8(b: U32) -> Nat:
  Nat.mod(U32.to_nat(b), 256n)

# the 17-bit limbs of a byte string, least significant first: acc holds
# the nb low bits not yet written (nb <= 16). A byte enters above them;
# once 17 bits are there, a limb leaves (the buffer and the byte's low
# 17 - nb bits) and the byte's other bits stay. The last limb holds the
# bits left over.
def pk(bs: List<&2, U32>, acc: Nat, +nb: Nat) -> List<&2, Nat>:
  match bs:
    case Nil{}:
      Con{acc, Nil{}}
    case Con{b, bt}:
      match nb:
        case 0n:
          pk(bt, Nat.add(acc, shl(0n, b8(b))), 8n)
        case 1n:
          pk(bt, Nat.add(acc, shl(1n, b8(b))), 9n)
        case 2n:
          pk(bt, Nat.add(acc, shl(2n, b8(b))), 10n)
        case 3n:
          pk(bt, Nat.add(acc, shl(3n, b8(b))), 11n)
        case 4n:
          pk(bt, Nat.add(acc, shl(4n, b8(b))), 12n)
        case 5n:
          pk(bt, Nat.add(acc, shl(5n, b8(b))), 13n)
        case 6n:
          pk(bt, Nat.add(acc, shl(6n, b8(b))), 14n)
        case 7n:
          pk(bt, Nat.add(acc, shl(7n, b8(b))), 15n)
        case 8n:
          pk(bt, Nat.add(acc, shl(8n, b8(b))), 16n)
        case 9n:
          +B = b8(b)
          Con{Nat.add(acc, shl(9n, Nat.mod(B, 256n))), pk(bt, Nat.div(B, 256n), 0n)}
        case 10n:
          +B = b8(b)
          Con{Nat.add(acc, shl(10n, Nat.mod(B, 128n))), pk(bt, Nat.div(B, 128n), 1n)}
        case 11n:
          +B = b8(b)
          Con{Nat.add(acc, shl(11n, Nat.mod(B, 64n))), pk(bt, Nat.div(B, 64n), 2n)}
        case 12n:
          +B = b8(b)
          Con{Nat.add(acc, shl(12n, Nat.mod(B, 32n))), pk(bt, Nat.div(B, 32n), 3n)}
        case 13n:
          +B = b8(b)
          Con{Nat.add(acc, shl(13n, Nat.mod(B, 16n))), pk(bt, Nat.div(B, 16n), 4n)}
        case 14n:
          +B = b8(b)
          Con{Nat.add(acc, shl(14n, Nat.mod(B, 8n))), pk(bt, Nat.div(B, 8n), 5n)}
        case 15n:
          +B = b8(b)
          Con{Nat.add(acc, shl(15n, Nat.mod(B, 4n))), pk(bt, Nat.div(B, 4n), 6n)}
        case 16n:
          +B = b8(b)
          Con{Nat.add(acc, shl(16n, Nat.mod(B, 2n))), pk(bt, Nat.div(B, 2n), 7n)}
        case 17n+m:
          Con{acc, pk(bt, b8(b), 8n)}

def byte(+a: Nat) -> U32:
  U32.from_nat(Nat.mod(a, 256n))

# the bytes of 17-bit limbs, least significant first: acc holds the nb low
# bits not yet written (nb <= 7). The limb's low 8 - nb bits complete a
# byte, its next 8 bits are a byte, and the rest stays (nb + 1 bits; at
# nb = 7 they are a third byte). The last byte holds the bits left over.
def up(xs: List<&2, Nat>, acc: Nat, +nb: Nat) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Con{byte(acc), Nil{}}
    case Con{+x, xt}:
      match nb:
        case 0n:
          +x1 = Nat.div(x, 256n)
          Con{byte(Nat.add(acc, shl(0n, Nat.mod(x, 256n)))), Con{byte(x1), up(xt, Nat.div(x1, 256n), 1n)}}
        case 1n:
          +x1 = Nat.div(x, 128n)
          Con{byte(Nat.add(acc, shl(1n, Nat.mod(x, 128n)))), Con{byte(x1), up(xt, Nat.div(x1, 256n), 2n)}}
        case 2n:
          +x1 = Nat.div(x, 64n)
          Con{byte(Nat.add(acc, shl(2n, Nat.mod(x, 64n)))), Con{byte(x1), up(xt, Nat.div(x1, 256n), 3n)}}
        case 3n:
          +x1 = Nat.div(x, 32n)
          Con{byte(Nat.add(acc, shl(3n, Nat.mod(x, 32n)))), Con{byte(x1), up(xt, Nat.div(x1, 256n), 4n)}}
        case 4n:
          +x1 = Nat.div(x, 16n)
          Con{byte(Nat.add(acc, shl(4n, Nat.mod(x, 16n)))), Con{byte(x1), up(xt, Nat.div(x1, 256n), 5n)}}
        case 5n:
          +x1 = Nat.div(x, 8n)
          Con{byte(Nat.add(acc, shl(5n, Nat.mod(x, 8n)))), Con{byte(x1), up(xt, Nat.div(x1, 256n), 6n)}}
        case 6n:
          +x1 = Nat.div(x, 4n)
          Con{byte(Nat.add(acc, shl(6n, Nat.mod(x, 4n)))), Con{byte(x1), up(xt, Nat.div(x1, 256n), 7n)}}
        case 7n:
          +x1 = Nat.div(x, 2n)
          Con{byte(Nat.add(acc, shl(7n, Nat.mod(x, 2n)))), Con{byte(x1), Con{byte(Nat.div(x1, 256n)), up(xt, 0n, 0n)}}}
        case 8n+m:
          Con{byte(acc), up(xt, x, 0n)}

# ---- GEN-PACK end ----
# every 17-bit limb of a byte string: ceil(8 n / 17) of them for the
# lengths used here (32 and 64 bytes: 16 and 31 limbs)
def limbs17(bs: List<&2, U32>) -> List<&2, Nat>:
  pk(bs, 0n, 0n)

def head(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, xt}:
      x

def ltl(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, xt}:
      xt

# the first n limbs (missing limbs are 0); n alone decides the shape, so
# the result of fit(15n, xs) is 15 limbs whatever xs is
def fit(n: Nat, +xs: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{head(xs), fit(m, ltl(xs))}

# 15 limbs of 17 bits from 32 bytes, bit 255 dropped (RFC 7748 decodeUCoordinate)
def of_bytes_l(bs: List<&2, U32>) -> List<&2, Nat>:
  fit(15n, limbs17(bs))

# 32 bytes from 15 limbs of 17 bits (a value below 2^255)
def to_bytes_l(xs: List<&2, Nat>) -> List<&2, U32>:
  up(xs, 0n, 0n)

def sum(xs: List<&2, Nat>, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{x, xt}:
      sum(xt, Nat.add(acc, x))
