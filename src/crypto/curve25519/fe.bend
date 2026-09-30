import Base
import ./limbs.bend as LS

# GF(p), p = 2^255 - 19, for X25519 and Ed25519: 15 limbs of 17 bits,
# value(x) = l0 + 2^17 l1 + ... + 2^238 l14 (spec/crypto/curve25519/fe.bend).
# The limbs are Nat: the native backend keeps a Nat below 2^48 in one
# machine word, and every intermediate here stays below 2^47 (proved: an
# element is "ok" when its limbs are below 2^19; the schoolbook product of
# two ok elements has columns below 15 * 2^38, the fold by 19 keeps them
# below 2^47, and a carry pass brings them back to ok). This is the
# unsaturated-limb field of Fiat-Crypto (Erbsen et al. 2019) and HACL*'s
# Field51, with 17-bit limbs so that products and sums fit the 48-bit Nat.
#
# add, sub, mul, mul_small and select are straight-line code, written by
# tools/gen_fe.py from the list algorithms of limbs.bend (do not edit them
# by hand; rerun the script). Every operation takes the radix R = 2^17,
# which the callers compute once from their symbolic one (radix(one)), so
# the proofs never meet a closed 2^17.
#
# No operation branches on a limb: selection is arithmetic, the exponents
# of inv and pow_p58 are public, and freeze's subtraction is a selection.
# Bend has no timing model, so constant time is by construction, not
# proved.

type Fe is Data:
  Fe{l0: Nat, l1: Nat, l2: Nat, l3: Nat, l4: Nat, l5: Nat, l6: Nat, l7: Nat, l8: Nat, l9: Nat, l10: Nat, l11: Nat, l12: Nat, l13: Nat, l14: Nat}

def to_list(x: Fe) -> List<&2, Nat>:
  match x:
    case Fe{l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14}:
      [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14]

# the first 15 limbs of a list (missing limbs are 0)
def lhd(xs: List<&2, Nat>) -> Nat:
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

def of_list(xs: List<&2, Nat>) -> Fe:
  match xs:
    case Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Con{x12, Con{x13, Con{x14, t}}}}}}}}}}}}}}}:
      Fe{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14}
    case _:
      Fe{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

# 2^n x
def pow2(n: Nat, +x: Nat) -> Nat:
  match n:
    case 0n:
      x
    case 1n+m:
      Nat.double(pow2(m, x))

# the radix 2^17, from the symbolic one (1n at run time)
def radix(+one: Nat) -> Nat:
  pow2(17n, one)

# ---- constants ----

def zero() -> Fe:
  Fe{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

def one() -> Fe:
  Fe{1n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

# a constant k < 2^17
def small(k: Nat) -> Fe:
  Fe{k, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

# ---- straight-line operations (tools/gen_fe.py) ----

# a + b: LS.add_l
def add(+R: Nat, a: Fe, b: Fe) -> Fe:
  match a b:
    case Fe{+a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7, +a8, +a9, +a10, +a11, +a12, +a13, +a14} Fe{+b0, +b1, +b2, +b3, +b4, +b5, +b6, +b7, +b8, +b9, +b10, +b11, +b12, +b13, +b14}:
      +w0 = Nat.add(a0, b0)
      +w1 = Nat.add(Nat.add(a1, b1), Nat.div(w0, R))
      +w2 = Nat.add(Nat.add(a2, b2), Nat.div(w1, R))
      +w3 = Nat.add(Nat.add(a3, b3), Nat.div(w2, R))
      +w4 = Nat.add(Nat.add(a4, b4), Nat.div(w3, R))
      +w5 = Nat.add(Nat.add(a5, b5), Nat.div(w4, R))
      +w6 = Nat.add(Nat.add(a6, b6), Nat.div(w5, R))
      +w7 = Nat.add(Nat.add(a7, b7), Nat.div(w6, R))
      +w8 = Nat.add(Nat.add(a8, b8), Nat.div(w7, R))
      +w9 = Nat.add(Nat.add(a9, b9), Nat.div(w8, R))
      +w10 = Nat.add(Nat.add(a10, b10), Nat.div(w9, R))
      +w11 = Nat.add(Nat.add(a11, b11), Nat.div(w10, R))
      +w12 = Nat.add(Nat.add(a12, b12), Nat.div(w11, R))
      +w13 = Nat.add(Nat.add(a13, b13), Nat.div(w12, R))
      +w14 = Nat.add(Nat.add(a14, b14), Nat.div(w13, R))
      +w15 = Nat.add(Nat.mod(w0, R), Nat.mul(Nat.div(w14, R), 19n))
      Fe{Nat.mod(w15, R), Nat.add(Nat.mod(w1, R), Nat.div(w15, R)), Nat.mod(w2, R), Nat.mod(w3, R), Nat.mod(w4, R), Nat.mod(w5, R), Nat.mod(w6, R), Nat.mod(w7, R), Nat.mod(w8, R), Nat.mod(w9, R), Nat.mod(w10, R), Nat.mod(w11, R), Nat.mod(w12, R), Nat.mod(w13, R), Nat.mod(w14, R)}

# a + 8 p - b: LS.sub_l
def sub(+R: Nat, a: Fe, b: Fe) -> Fe:
  match a b:
    case Fe{+a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7, +a8, +a9, +a10, +a11, +a12, +a13, +a14} Fe{+b0, +b1, +b2, +b3, +b4, +b5, +b6, +b7, +b8, +b9, +b10, +b11, +b12, +b13, +b14}:
      +w0 = Nat.mul(R, 8n)
      +w1 = Nat.sub(Nat.add(a0, Nat.sub(w0, 152n)), b0)
      +w2 = Nat.sub(w0, 8n)
      +w3 = Nat.add(Nat.sub(Nat.add(a1, w2), b1), Nat.div(w1, R))
      +w4 = Nat.add(Nat.sub(Nat.add(a2, w2), b2), Nat.div(w3, R))
      +w5 = Nat.add(Nat.sub(Nat.add(a3, w2), b3), Nat.div(w4, R))
      +w6 = Nat.add(Nat.sub(Nat.add(a4, w2), b4), Nat.div(w5, R))
      +w7 = Nat.add(Nat.sub(Nat.add(a5, w2), b5), Nat.div(w6, R))
      +w8 = Nat.add(Nat.sub(Nat.add(a6, w2), b6), Nat.div(w7, R))
      +w9 = Nat.add(Nat.sub(Nat.add(a7, w2), b7), Nat.div(w8, R))
      +w10 = Nat.add(Nat.sub(Nat.add(a8, w2), b8), Nat.div(w9, R))
      +w11 = Nat.add(Nat.sub(Nat.add(a9, w2), b9), Nat.div(w10, R))
      +w12 = Nat.add(Nat.sub(Nat.add(a10, w2), b10), Nat.div(w11, R))
      +w13 = Nat.add(Nat.sub(Nat.add(a11, w2), b11), Nat.div(w12, R))
      +w14 = Nat.add(Nat.sub(Nat.add(a12, w2), b12), Nat.div(w13, R))
      +w15 = Nat.add(Nat.sub(Nat.add(a13, w2), b13), Nat.div(w14, R))
      +w16 = Nat.add(Nat.sub(Nat.add(a14, w2), b14), Nat.div(w15, R))
      +w17 = Nat.add(Nat.mod(w1, R), Nat.mul(Nat.div(w16, R), 19n))
      Fe{Nat.mod(w17, R), Nat.add(Nat.mod(w3, R), Nat.div(w17, R)), Nat.mod(w4, R), Nat.mod(w5, R), Nat.mod(w6, R), Nat.mod(w7, R), Nat.mod(w8, R), Nat.mod(w9, R), Nat.mod(w10, R), Nat.mod(w11, R), Nat.mod(w12, R), Nat.mod(w13, R), Nat.mod(w14, R), Nat.mod(w15, R), Nat.mod(w16, R)}

# a b: LS.mul_l
def mul(+R: Nat, a: Fe, b: Fe) -> Fe:
  match a b:
    case Fe{+a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7, +a8, +a9, +a10, +a11, +a12, +a13, +a14} Fe{+b0, +b1, +b2, +b3, +b4, +b5, +b6, +b7, +b8, +b9, +b10, +b11, +b12, +b13, +b14}:
      +w0 = Nat.add(Nat.mul(a0, b0), Nat.mul(Nat.add(Nat.mul(a1, b14), Nat.add(Nat.mul(a2, b13), Nat.add(Nat.mul(a3, b12), Nat.add(Nat.mul(a4, b11), Nat.add(Nat.mul(a5, b10), Nat.add(Nat.mul(a6, b9), Nat.add(Nat.mul(a7, b8), Nat.add(Nat.mul(a8, b7), Nat.add(Nat.mul(a9, b6), Nat.add(Nat.mul(a10, b5), Nat.add(Nat.mul(a11, b4), Nat.add(Nat.mul(a12, b3), Nat.add(Nat.mul(a13, b2), Nat.mul(a14, b1)))))))))))))), 19n))
      +w1 = Nat.add(Nat.add(Nat.add(Nat.mul(a0, b1), Nat.mul(a1, b0)), Nat.mul(Nat.add(Nat.mul(a2, b14), Nat.add(Nat.mul(a3, b13), Nat.add(Nat.mul(a4, b12), Nat.add(Nat.mul(a5, b11), Nat.add(Nat.mul(a6, b10), Nat.add(Nat.mul(a7, b9), Nat.add(Nat.mul(a8, b8), Nat.add(Nat.mul(a9, b7), Nat.add(Nat.mul(a10, b6), Nat.add(Nat.mul(a11, b5), Nat.add(Nat.mul(a12, b4), Nat.add(Nat.mul(a13, b3), Nat.mul(a14, b2))))))))))))), 19n)), Nat.div(w0, R))
      +w2 = Nat.add(Nat.add(Nat.add(Nat.mul(a0, b2), Nat.add(Nat.mul(a1, b1), Nat.mul(a2, b0))), Nat.mul(Nat.add(Nat.mul(a3, b14), Nat.add(Nat.mul(a4, b13), Nat.add(Nat.mul(a5, b12), Nat.add(Nat.mul(a6, b11), Nat.add(Nat.mul(a7, b10), Nat.add(Nat.mul(a8, b9), Nat.add(Nat.mul(a9, b8), Nat.add(Nat.mul(a10, b7), Nat.add(Nat.mul(a11, b6), Nat.add(Nat.mul(a12, b5), Nat.add(Nat.mul(a13, b4), Nat.mul(a14, b3)))))))))))), 19n)), Nat.div(w1, R))
      +w3 = Nat.add(Nat.add(Nat.add(Nat.mul(a0, b3), Nat.add(Nat.mul(a1, b2), Nat.add(Nat.mul(a2, b1), Nat.mul(a3, b0)))), Nat.mul(Nat.add(Nat.mul(a4, b14), Nat.add(Nat.mul(a5, b13), Nat.add(Nat.mul(a6, b12), Nat.add(Nat.mul(a7, b11), Nat.add(Nat.mul(a8, b10), Nat.add(Nat.mul(a9, b9), Nat.add(Nat.mul(a10, b8), Nat.add(Nat.mul(a11, b7), Nat.add(Nat.mul(a12, b6), Nat.add(Nat.mul(a13, b5), Nat.mul(a14, b4))))))))))), 19n)), Nat.div(w2, R))
      +w4 = Nat.add(Nat.add(Nat.add(Nat.mul(a0, b4), Nat.add(Nat.mul(a1, b3), Nat.add(Nat.mul(a2, b2), Nat.add(Nat.mul(a3, b1), Nat.mul(a4, b0))))), Nat.mul(Nat.add(Nat.mul(a5, b14), Nat.add(Nat.mul(a6, b13), Nat.add(Nat.mul(a7, b12), Nat.add(Nat.mul(a8, b11), Nat.add(Nat.mul(a9, b10), Nat.add(Nat.mul(a10, b9), Nat.add(Nat.mul(a11, b8), Nat.add(Nat.mul(a12, b7), Nat.add(Nat.mul(a13, b6), Nat.mul(a14, b5)))))))))), 19n)), Nat.div(w3, R))
      +w5 = Nat.add(Nat.add(Nat.add(Nat.mul(a0, b5), Nat.add(Nat.mul(a1, b4), Nat.add(Nat.mul(a2, b3), Nat.add(Nat.mul(a3, b2), Nat.add(Nat.mul(a4, b1), Nat.mul(a5, b0)))))), Nat.mul(Nat.add(Nat.mul(a6, b14), Nat.add(Nat.mul(a7, b13), Nat.add(Nat.mul(a8, b12), Nat.add(Nat.mul(a9, b11), Nat.add(Nat.mul(a10, b10), Nat.add(Nat.mul(a11, b9), Nat.add(Nat.mul(a12, b8), Nat.add(Nat.mul(a13, b7), Nat.mul(a14, b6))))))))), 19n)), Nat.div(w4, R))
      +w6 = Nat.add(Nat.add(Nat.add(Nat.mul(a0, b6), Nat.add(Nat.mul(a1, b5), Nat.add(Nat.mul(a2, b4), Nat.add(Nat.mul(a3, b3), Nat.add(Nat.mul(a4, b2), Nat.add(Nat.mul(a5, b1), Nat.mul(a6, b0))))))), Nat.mul(Nat.add(Nat.mul(a7, b14), Nat.add(Nat.mul(a8, b13), Nat.add(Nat.mul(a9, b12), Nat.add(Nat.mul(a10, b11), Nat.add(Nat.mul(a11, b10), Nat.add(Nat.mul(a12, b9), Nat.add(Nat.mul(a13, b8), Nat.mul(a14, b7)))))))), 19n)), Nat.div(w5, R))
      +w7 = Nat.add(Nat.add(Nat.add(Nat.mul(a0, b7), Nat.add(Nat.mul(a1, b6), Nat.add(Nat.mul(a2, b5), Nat.add(Nat.mul(a3, b4), Nat.add(Nat.mul(a4, b3), Nat.add(Nat.mul(a5, b2), Nat.add(Nat.mul(a6, b1), Nat.mul(a7, b0)))))))), Nat.mul(Nat.add(Nat.mul(a8, b14), Nat.add(Nat.mul(a9, b13), Nat.add(Nat.mul(a10, b12), Nat.add(Nat.mul(a11, b11), Nat.add(Nat.mul(a12, b10), Nat.add(Nat.mul(a13, b9), Nat.mul(a14, b8))))))), 19n)), Nat.div(w6, R))
      +w8 = Nat.add(Nat.add(Nat.add(Nat.mul(a0, b8), Nat.add(Nat.mul(a1, b7), Nat.add(Nat.mul(a2, b6), Nat.add(Nat.mul(a3, b5), Nat.add(Nat.mul(a4, b4), Nat.add(Nat.mul(a5, b3), Nat.add(Nat.mul(a6, b2), Nat.add(Nat.mul(a7, b1), Nat.mul(a8, b0))))))))), Nat.mul(Nat.add(Nat.mul(a9, b14), Nat.add(Nat.mul(a10, b13), Nat.add(Nat.mul(a11, b12), Nat.add(Nat.mul(a12, b11), Nat.add(Nat.mul(a13, b10), Nat.mul(a14, b9)))))), 19n)), Nat.div(w7, R))
      +w9 = Nat.add(Nat.add(Nat.add(Nat.mul(a0, b9), Nat.add(Nat.mul(a1, b8), Nat.add(Nat.mul(a2, b7), Nat.add(Nat.mul(a3, b6), Nat.add(Nat.mul(a4, b5), Nat.add(Nat.mul(a5, b4), Nat.add(Nat.mul(a6, b3), Nat.add(Nat.mul(a7, b2), Nat.add(Nat.mul(a8, b1), Nat.mul(a9, b0)))))))))), Nat.mul(Nat.add(Nat.mul(a10, b14), Nat.add(Nat.mul(a11, b13), Nat.add(Nat.mul(a12, b12), Nat.add(Nat.mul(a13, b11), Nat.mul(a14, b10))))), 19n)), Nat.div(w8, R))
      +w10 = Nat.add(Nat.add(Nat.add(Nat.mul(a0, b10), Nat.add(Nat.mul(a1, b9), Nat.add(Nat.mul(a2, b8), Nat.add(Nat.mul(a3, b7), Nat.add(Nat.mul(a4, b6), Nat.add(Nat.mul(a5, b5), Nat.add(Nat.mul(a6, b4), Nat.add(Nat.mul(a7, b3), Nat.add(Nat.mul(a8, b2), Nat.add(Nat.mul(a9, b1), Nat.mul(a10, b0))))))))))), Nat.mul(Nat.add(Nat.mul(a11, b14), Nat.add(Nat.mul(a12, b13), Nat.add(Nat.mul(a13, b12), Nat.mul(a14, b11)))), 19n)), Nat.div(w9, R))
      +w11 = Nat.add(Nat.add(Nat.add(Nat.mul(a0, b11), Nat.add(Nat.mul(a1, b10), Nat.add(Nat.mul(a2, b9), Nat.add(Nat.mul(a3, b8), Nat.add(Nat.mul(a4, b7), Nat.add(Nat.mul(a5, b6), Nat.add(Nat.mul(a6, b5), Nat.add(Nat.mul(a7, b4), Nat.add(Nat.mul(a8, b3), Nat.add(Nat.mul(a9, b2), Nat.add(Nat.mul(a10, b1), Nat.mul(a11, b0)))))))))))), Nat.mul(Nat.add(Nat.mul(a12, b14), Nat.add(Nat.mul(a13, b13), Nat.mul(a14, b12))), 19n)), Nat.div(w10, R))
      +w12 = Nat.add(Nat.add(Nat.add(Nat.mul(a0, b12), Nat.add(Nat.mul(a1, b11), Nat.add(Nat.mul(a2, b10), Nat.add(Nat.mul(a3, b9), Nat.add(Nat.mul(a4, b8), Nat.add(Nat.mul(a5, b7), Nat.add(Nat.mul(a6, b6), Nat.add(Nat.mul(a7, b5), Nat.add(Nat.mul(a8, b4), Nat.add(Nat.mul(a9, b3), Nat.add(Nat.mul(a10, b2), Nat.add(Nat.mul(a11, b1), Nat.mul(a12, b0))))))))))))), Nat.mul(Nat.add(Nat.mul(a13, b14), Nat.mul(a14, b13)), 19n)), Nat.div(w11, R))
      +w13 = Nat.add(Nat.add(Nat.add(Nat.mul(a0, b13), Nat.add(Nat.mul(a1, b12), Nat.add(Nat.mul(a2, b11), Nat.add(Nat.mul(a3, b10), Nat.add(Nat.mul(a4, b9), Nat.add(Nat.mul(a5, b8), Nat.add(Nat.mul(a6, b7), Nat.add(Nat.mul(a7, b6), Nat.add(Nat.mul(a8, b5), Nat.add(Nat.mul(a9, b4), Nat.add(Nat.mul(a10, b3), Nat.add(Nat.mul(a11, b2), Nat.add(Nat.mul(a12, b1), Nat.mul(a13, b0)))))))))))))), Nat.mul(Nat.mul(a14, b14), 19n)), Nat.div(w12, R))
      +w14 = Nat.add(Nat.add(Nat.mul(a0, b14), Nat.add(Nat.mul(a1, b13), Nat.add(Nat.mul(a2, b12), Nat.add(Nat.mul(a3, b11), Nat.add(Nat.mul(a4, b10), Nat.add(Nat.mul(a5, b9), Nat.add(Nat.mul(a6, b8), Nat.add(Nat.mul(a7, b7), Nat.add(Nat.mul(a8, b6), Nat.add(Nat.mul(a9, b5), Nat.add(Nat.mul(a10, b4), Nat.add(Nat.mul(a11, b3), Nat.add(Nat.mul(a12, b2), Nat.add(Nat.mul(a13, b1), Nat.mul(a14, b0))))))))))))))), Nat.div(w13, R))
      +w15 = Nat.add(Nat.mod(w0, R), Nat.mul(Nat.div(w14, R), 19n))
      Fe{Nat.mod(w15, R), Nat.add(Nat.mod(w1, R), Nat.div(w15, R)), Nat.mod(w2, R), Nat.mod(w3, R), Nat.mod(w4, R), Nat.mod(w5, R), Nat.mod(w6, R), Nat.mod(w7, R), Nat.mod(w8, R), Nat.mod(w9, R), Nat.mod(w10, R), Nat.mod(w11, R), Nat.mod(w12, R), Nat.mod(w13, R), Nat.mod(w14, R)}

# a k for k < 2^17: LS.mul_small_l
def mul_small(+R: Nat, a: Fe, +k: Nat) -> Fe:
  match a:
    case Fe{+a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7, +a8, +a9, +a10, +a11, +a12, +a13, +a14}:
      +w0 = Nat.mul(a0, k)
      +w1 = Nat.add(Nat.mul(a1, k), Nat.div(w0, R))
      +w2 = Nat.add(Nat.mul(a2, k), Nat.div(w1, R))
      +w3 = Nat.add(Nat.mul(a3, k), Nat.div(w2, R))
      +w4 = Nat.add(Nat.mul(a4, k), Nat.div(w3, R))
      +w5 = Nat.add(Nat.mul(a5, k), Nat.div(w4, R))
      +w6 = Nat.add(Nat.mul(a6, k), Nat.div(w5, R))
      +w7 = Nat.add(Nat.mul(a7, k), Nat.div(w6, R))
      +w8 = Nat.add(Nat.mul(a8, k), Nat.div(w7, R))
      +w9 = Nat.add(Nat.mul(a9, k), Nat.div(w8, R))
      +w10 = Nat.add(Nat.mul(a10, k), Nat.div(w9, R))
      +w11 = Nat.add(Nat.mul(a11, k), Nat.div(w10, R))
      +w12 = Nat.add(Nat.mul(a12, k), Nat.div(w11, R))
      +w13 = Nat.add(Nat.mul(a13, k), Nat.div(w12, R))
      +w14 = Nat.add(Nat.mul(a14, k), Nat.div(w13, R))
      +w15 = Nat.add(Nat.mod(w0, R), Nat.mul(Nat.div(w14, R), 19n))
      Fe{Nat.mod(w15, R), Nat.add(Nat.mod(w1, R), Nat.div(w15, R)), Nat.mod(w2, R), Nat.mod(w3, R), Nat.mod(w4, R), Nat.mod(w5, R), Nat.mod(w6, R), Nat.mod(w7, R), Nat.mod(w8, R), Nat.mod(w9, R), Nat.mod(w10, R), Nat.mod(w11, R), Nat.mod(w12, R), Nat.mod(w13, R), Nat.mod(w14, R)}

# s == 0: a; s == 1: b (LS.sel on U32.to_nat(s))
def select(+s: U32, a: Fe, b: Fe) -> Fe:
  match a b:
    case Fe{+a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7, +a8, +a9, +a10, +a11, +a12, +a13, +a14} Fe{+b0, +b1, +b2, +b3, +b4, +b5, +b6, +b7, +b8, +b9, +b10, +b11, +b12, +b13, +b14}:
      +sn = U32.to_nat(s)
      +w0 = Nat.sub(1n, sn)
      Fe{Nat.add(Nat.mul(a0, w0), Nat.mul(b0, sn)), Nat.add(Nat.mul(a1, w0), Nat.mul(b1, sn)), Nat.add(Nat.mul(a2, w0), Nat.mul(b2, sn)), Nat.add(Nat.mul(a3, w0), Nat.mul(b3, sn)), Nat.add(Nat.mul(a4, w0), Nat.mul(b4, sn)), Nat.add(Nat.mul(a5, w0), Nat.mul(b5, sn)), Nat.add(Nat.mul(a6, w0), Nat.mul(b6, sn)), Nat.add(Nat.mul(a7, w0), Nat.mul(b7, sn)), Nat.add(Nat.mul(a8, w0), Nat.mul(b8, sn)), Nat.add(Nat.mul(a9, w0), Nat.mul(b9, sn)), Nat.add(Nat.mul(a10, w0), Nat.mul(b10, sn)), Nat.add(Nat.mul(a11, w0), Nat.mul(b11, sn)), Nat.add(Nat.mul(a12, w0), Nat.mul(b12, sn)), Nat.add(Nat.mul(a13, w0), Nat.mul(b13, sn)), Nat.add(Nat.mul(a14, w0), Nat.mul(b14, sn))}

def sq(+R: Nat, +a: Fe) -> Fe:
  mul(R, a, a)

def neg(+R: Nat, a: Fe) -> Fe:
  sub(R, zero(), a)

# ---- powers (public exponents) ----
#
# The loops take the base x first and inspect it before their counter, so
# the proof checker never unfolds a fixed-count loop over an unknown base.

# acc^(2^n) * x^(2^n - 1): n steps of acc = acc^2 * x
def pow_ones(+R: Nat, +x: Fe, n: Nat, acc: Fe) -> Fe:
  match x:
    case Fe{l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14}:
      match n:
        case 0n:
          acc
        case 1n+m:
          pow_ones(R, x, m, mul(R, sq(R, acc), x))

# one bit of a public exponent, most significant first: acc^2 (* x)
def pow_bit(+R: Nat, b: Bool, +x: Fe, acc: Fe) -> Fe:
  match b:
    case True{}:
      mul(R, sq(R, acc), x)
    case False{}:
      sq(R, acc)

def pow_bits(+R: Nat, +x: Fe, bs: List<&2, Bool>, acc: Fe) -> Fe:
  match x:
    case Fe{l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14}:
      match bs:
        case Nil{}:
          acc
        case Con{b, bt}:
          pow_bits(R, x, bt, pow_bit(R, b, x, acc))

# x^(p - 2) = x^(2^255 - 21): 250 one bits (x, then 249 steps), then 0 1 0 1 1
def inv(+R: Nat, +x: Fe) -> Fe:
  pow_bits(R, x, [False{}, True{}, False{}, True{}, True{}], pow_ones(R, x, 249n, x))

# x^((p - 5) / 8) = x^(2^252 - 3): 250 one bits, then 0 1
def pow_p58(+R: Nat, +x: Fe) -> Fe:
  pow_bits(R, x, [False{}, True{}], pow_ones(R, x, 249n, x))

# ---- canonical form and bytes (list form, limbs.bend) ----

# the canonical representative: limbs below R, value below p
def freeze(+R: Nat, x: Fe) -> Fe:
  of_list(LS.freeze_l(R, to_list(x)))

# the 32-byte little-endian encoding of the canonical representative
def to_bytes(+R: Nat, x: Fe) -> List<&2, U32>:
  LS.to_bytes_l(LS.freeze_l(R, to_list(x)))

# 32 bytes to an element, bit 255 ignored (RFC 7748 decodeUCoordinate)
def of_bytes(bs: List<&2, U32>) -> Fe:
  of_list(LS.of_bytes_l(bs))

# x == 0 in the field: every limb of the canonical form is 0
def is_zero(+R: Nat, x: Fe) -> Bool:
  Nat.is_eq(LS.sum(LS.freeze_l(R, to_list(x)), 0n), 0n)

# a == b in the field
def eq(+R: Nat, a: Fe, b: Fe) -> Bool:
  is_zero(R, sub(R, a, b))

# the parity of the canonical representative (RFC 8032 x_0)
def parity(+R: Nat, x: Fe) -> U32:
  U32.from_nat(Nat.mod(LS.head(LS.freeze_l(R, to_list(x))), 2n))
