import Base
import ../curve25519/field.bend as F
import ../curve25519/fe.bend as FE
import ../curve25519/limbs.bend as LS
import ../curve25519/x25519.bend as X
import ./step.bend as ST

# Scalars mod L = 2^252 + 27742317777372353535851937790883648493 (RFC 8032
# section 5.1). Byte strings in and out (32 bytes, every value below L);
# inside, 17-bit Nat limbs (the radix of ../curve25519/fe.bend) and Horner's
# rule from the most significant limb:
#
#   step(acc, d)        (d + 2^17 acc) mod L for acc < L: the quotient
#                       estimate q = floor(t / 2^252) is the true quotient
#                       or one more (L - 2^252 < 2^125), so t - (q - 1) L
#                       is in [0, 2 L), and one borrow-checked subtraction
#                       of L finishes (Barrett-style, HAC 14.42)
#   reduce(bs)          value(bs) mod L (a 64-byte SHA-512 digest, say)
#   mul_add(k, s, r)    (r + k s) mod L: the schoolbook product, then reduce
#   lt_l(x)             x < L
#
# Every step is the same for every value (the subtraction is kept or not
# by selection, limb counts come from the input's length): branch-free by
# construction.

# L, little-endian bytes
def ell() -> List<&2, U32>:
  [237, 211, 245, 92, 26, 99, 18, 88, 214, 156, 247, 162, 222, 249, 222, 20,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16]

# 2^256 - L
def comp_l() -> List<&2, U32>:
  [19, 44, 10, 163, 229, 156, 237, 167, 41, 99, 8, 93, 33, 6, 33, 235,
   255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 239]

# ---- subtraction with borrows ----

type Sb is Data:
  Sb{limbs: List<&2, Nat>, out: Nat}

def sb_limbs(r: Sb) -> List<&2, Nat>:
  match r:
    case Sb{a, b}:
      a

def sb_out(r: Sb) -> Nat:
  match r:
    case Sb{a, b}:
      b

def sb_con(l: Nat, r: Sb) -> Sb:
  match r:
    case Sb{a, b}:
      Sb{Con{l, a}, b}

# x - y - b limb by limb (limbs below R, b a bit): the digits and the
# borrow out
def subb(+R: Nat, xs: List<&2, Nat>, ys: List<&2, Nat>, b: Nat) -> Sb:
  match xs:
    case Nil{}:
      Sb{Nil{}, b}
    case Con{x, xt}:
      match ys:
        case Nil{}:
          Sb{Nil{}, b}
        case Con{y, yt}:
          +d = Nat.sub(Nat.add(x, R), Nat.add(y, b))
          sb_con(Nat.mod(d, R), subb(R, xt, yt, Nat.sub(1n, Nat.div(d, R))))

# limb n (0 when missing)
def nth(n: Nat, xs: List<&2, Nat>) -> Nat:
  match n xs:
    case _ Nil{}:
      0n
    case 0n Con{x, xt}:
      x
    case 1n+m Con{x, xt}:
      nth(m, xt)

# ---- Horner's rule mod L ----

# L in 15 limbs of 17 bits; taking an input list xs keeps the proof checker
# from evaluating the limbs while xs is unknown
def ell_of(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      ell()
    case Con{h, t}:
      ell()

def l15(+xs: List<&2, U32>) -> List<&2, Nat>:
  LS.of_bytes_l(ell_of(xs))

def zeros() -> List<&2, Nat>:
  [0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n]

# (d + R acc) mod L for acc < L in 15 limbs below R and d < R
def step_fin(+R: Nat, +l: List<&2, Nat>, +t: List<&2, Nat>, +ml: LS.Cr) -> List<&2, Nat>:
  +u = sb_limbs(subb(R, t, LS.app(LS.cr_limbs(ml), [LS.cr_out(ml)]), 0n))
  +w = subb(R, u, LS.app(l, [0n]), 0n)
  LS.take(15n, LS.sel(sb_out(w), sb_limbs(w), u))

def step(+R: Nat, +l: List<&2, Nat>, +acc: List<&2, Nat>, +d: Nat) -> List<&2, Nat>:
  +x = Nat.add(nth(13n, acc), Nat.mul(nth(14n, acc), R))
  +m = Nat.sub(Nat.div(x, Nat.div(R, 8n)), 1n)
  step_fin(R, l, Con{d, acc}, LS.carry(R, LS.scal(m, l), 0n))

# the limbs, most significant first, folded by step
def hr(+R: Nat, +l: List<&2, Nat>, xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      zeros()
    case Con{x, xt}:
      step(R, l, hr(R, l, xt), x)

# the same on 15-limb tuples (ST.step15 is step as straight-line code)
def hr15(+R: Nat, +l: FE.Fe, xs: List<&2, Nat>) -> FE.Fe:
  match xs:
    case Nil{}:
      FE.zero()
    case Con{x, xt}:
      ST.step15(R, l, hr15(R, l, xt), x)

def hrf(+R: Nat, +l: List<&2, Nat>, xs: List<&2, Nat>) -> List<&2, Nat>:
  FE.to_list(hr15(R, FE.of_list(l), xs))

# value(bs) mod L, 32 bytes
def reduce(+bs: List<&2, U32>) -> List<&2, U32>:
  LS.to_bytes_l(hrf(FE.radix(X.one_of(bs)), l15(bs), LS.limbs17(bs)))

# (r + k s) mod L for s, r < L: the product in 17-bit limbs, carried
def mul_add_l(+R: Nat, +k: List<&2, U32>, +s: List<&2, U32>, +r: List<&2, U32>) -> List<&2, Nat>:
  +pr = LS.carry(R, LS.addl(LS.conv(LS.limbs17(k), LS.of_bytes_l(s)), LS.of_bytes_l(r)), 0n)
  hrf(R, l15(k), LS.app(LS.cr_limbs(pr), [LS.cr_out(pr)]))

def mul_add(+k: List<&2, U32>, +s: List<&2, U32>, +r: List<&2, U32>) -> List<&2, U32>:
  LS.to_bytes_l(mul_add_l(FE.radix(X.one_of(k)), k, s, r))

# x < L: the carry of x + 2^256 - L is 0
def lt_l(+x: List<&2, U32>) -> Bool:
  U32.is_eq(F.cr_out(F.carry(F.addl(x, comp_l()), 0)), 0)
