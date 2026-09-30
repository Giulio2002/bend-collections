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

# a + b: LS.add_l (carries moved at once)
def add(+R: Nat, a: Fe, b: Fe) -> Fe:
  match a b:
    case Fe{+a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7, +a8, +a9, +a10, +a11, +a12, +a13, +a14} Fe{+b0, +b1, +b2, +b3, +b4, +b5, +b6, +b7, +b8, +b9, +b10, +b11, +b12, +b13, +b14}:
      +w0 = Nat.add(a0, b0)
      +w1 = Nat.add(a14, b14)
      +w2 = Nat.add(a1, b1)
      +w3 = Nat.add(a2, b2)
      +w4 = Nat.add(a3, b3)
      +w5 = Nat.add(a4, b4)
      +w6 = Nat.add(a5, b5)
      +w7 = Nat.add(a6, b6)
      +w8 = Nat.add(a7, b7)
      +w9 = Nat.add(a8, b8)
      +w10 = Nat.add(a9, b9)
      +w11 = Nat.add(a10, b10)
      +w12 = Nat.add(a11, b11)
      +w13 = Nat.add(a12, b12)
      +w14 = Nat.add(a13, b13)
      Fe{Nat.add(Nat.mod(w0, R), Nat.mul(Nat.div(w1, R), 19n)), Nat.add(Nat.mod(w2, R), Nat.div(w0, R)), Nat.add(Nat.mod(w3, R), Nat.div(w2, R)), Nat.add(Nat.mod(w4, R), Nat.div(w3, R)), Nat.add(Nat.mod(w5, R), Nat.div(w4, R)), Nat.add(Nat.mod(w6, R), Nat.div(w5, R)), Nat.add(Nat.mod(w7, R), Nat.div(w6, R)), Nat.add(Nat.mod(w8, R), Nat.div(w7, R)), Nat.add(Nat.mod(w9, R), Nat.div(w8, R)), Nat.add(Nat.mod(w10, R), Nat.div(w9, R)), Nat.add(Nat.mod(w11, R), Nat.div(w10, R)), Nat.add(Nat.mod(w12, R), Nat.div(w11, R)), Nat.add(Nat.mod(w13, R), Nat.div(w12, R)), Nat.add(Nat.mod(w14, R), Nat.div(w13, R)), Nat.add(Nat.mod(w1, R), Nat.div(w14, R))}

# a + 8 p - b: LS.sub_l (carries moved at once)
def sub(+R: Nat, a: Fe, b: Fe) -> Fe:
  match a b:
    case Fe{+a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7, +a8, +a9, +a10, +a11, +a12, +a13, +a14} Fe{+b0, +b1, +b2, +b3, +b4, +b5, +b6, +b7, +b8, +b9, +b10, +b11, +b12, +b13, +b14}:
      +w0 = Nat.mul(R, 8n)
      +w1 = Nat.sub(Nat.add(a0, Nat.sub(w0, 152n)), b0)
      +w2 = Nat.sub(w0, 8n)
      +w3 = Nat.sub(Nat.add(a14, w2), b14)
      +w4 = Nat.sub(Nat.add(a1, w2), b1)
      +w5 = Nat.sub(Nat.add(a2, w2), b2)
      +w6 = Nat.sub(Nat.add(a3, w2), b3)
      +w7 = Nat.sub(Nat.add(a4, w2), b4)
      +w8 = Nat.sub(Nat.add(a5, w2), b5)
      +w9 = Nat.sub(Nat.add(a6, w2), b6)
      +w10 = Nat.sub(Nat.add(a7, w2), b7)
      +w11 = Nat.sub(Nat.add(a8, w2), b8)
      +w12 = Nat.sub(Nat.add(a9, w2), b9)
      +w13 = Nat.sub(Nat.add(a10, w2), b10)
      +w14 = Nat.sub(Nat.add(a11, w2), b11)
      +w15 = Nat.sub(Nat.add(a12, w2), b12)
      +w16 = Nat.sub(Nat.add(a13, w2), b13)
      Fe{Nat.add(Nat.mod(w1, R), Nat.mul(Nat.div(w3, R), 19n)), Nat.add(Nat.mod(w4, R), Nat.div(w1, R)), Nat.add(Nat.mod(w5, R), Nat.div(w4, R)), Nat.add(Nat.mod(w6, R), Nat.div(w5, R)), Nat.add(Nat.mod(w7, R), Nat.div(w6, R)), Nat.add(Nat.mod(w8, R), Nat.div(w7, R)), Nat.add(Nat.mod(w9, R), Nat.div(w8, R)), Nat.add(Nat.mod(w10, R), Nat.div(w9, R)), Nat.add(Nat.mod(w11, R), Nat.div(w10, R)), Nat.add(Nat.mod(w12, R), Nat.div(w11, R)), Nat.add(Nat.mod(w13, R), Nat.div(w12, R)), Nat.add(Nat.mod(w14, R), Nat.div(w13, R)), Nat.add(Nat.mod(w15, R), Nat.div(w14, R)), Nat.add(Nat.mod(w16, R), Nat.div(w15, R)), Nat.add(Nat.mod(w3, R), Nat.div(w16, R))}

# a b: LS.mul_l
def mul(+R: Nat, a: Fe, b: Fe) -> Fe:
  match a b:
    case Fe{+a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7, +a8, +a9, +a10, +a11, +a12, +a13, +a14} Fe{+b0, +b1, +b2, +b3, +b4, +b5, +b6, +b7, +b8, +b9, +b10, +b11, +b12, +b13, +b14}:
      +w0 = U32.from_nat(a0)
      +w1 = U32.from_nat(Nat.mod(b0, 512n))
      +w2 = U32.from_nat(Nat.div(b0, 512n))
      +w3 = U32.from_nat(a1)
      +w4 = U32.from_nat(Nat.mod(b14, 512n))
      +w5 = U32.from_nat(Nat.div(b14, 512n))
      +w6 = U32.from_nat(a2)
      +w7 = U32.from_nat(Nat.mod(b13, 512n))
      +w8 = U32.from_nat(Nat.div(b13, 512n))
      +w9 = U32.from_nat(a3)
      +w10 = U32.from_nat(Nat.mod(b12, 512n))
      +w11 = U32.from_nat(Nat.div(b12, 512n))
      +w12 = U32.from_nat(a4)
      +w13 = U32.from_nat(Nat.mod(b11, 512n))
      +w14 = U32.from_nat(Nat.div(b11, 512n))
      +w15 = U32.from_nat(a5)
      +w16 = U32.from_nat(Nat.mod(b10, 512n))
      +w17 = U32.from_nat(Nat.div(b10, 512n))
      +w18 = U32.from_nat(a6)
      +w19 = U32.from_nat(Nat.mod(b9, 512n))
      +w20 = U32.from_nat(Nat.div(b9, 512n))
      +w21 = U32.from_nat(a7)
      +w22 = U32.from_nat(Nat.mod(b8, 512n))
      +w23 = U32.from_nat(Nat.div(b8, 512n))
      +w24 = U32.from_nat(a8)
      +w25 = U32.from_nat(Nat.mod(b7, 512n))
      +w26 = U32.from_nat(Nat.div(b7, 512n))
      +w27 = U32.from_nat(a9)
      +w28 = U32.from_nat(Nat.mod(b6, 512n))
      +w29 = U32.from_nat(Nat.div(b6, 512n))
      +w30 = U32.from_nat(a10)
      +w31 = U32.from_nat(Nat.mod(b5, 512n))
      +w32 = U32.from_nat(Nat.div(b5, 512n))
      +w33 = U32.from_nat(a11)
      +w34 = U32.from_nat(Nat.mod(b4, 512n))
      +w35 = U32.from_nat(Nat.div(b4, 512n))
      +w36 = U32.from_nat(a12)
      +w37 = U32.from_nat(Nat.mod(b3, 512n))
      +w38 = U32.from_nat(Nat.div(b3, 512n))
      +w39 = U32.from_nat(a13)
      +w40 = U32.from_nat(Nat.mod(b2, 512n))
      +w41 = U32.from_nat(Nat.div(b2, 512n))
      +w42 = U32.from_nat(a14)
      +w43 = U32.from_nat(Nat.mod(b1, 512n))
      +w44 = U32.from_nat(Nat.div(b1, 512n))
      +w45 = Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w1)), Nat.mul(U32.to_nat(U32.mul(w0, w2)), 512n)), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w3, w4)), Nat.mul(U32.to_nat(U32.mul(w3, w5)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w6, w7)), Nat.mul(U32.to_nat(U32.mul(w6, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w10)), Nat.mul(U32.to_nat(U32.mul(w9, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w13)), Nat.mul(U32.to_nat(U32.mul(w12, w14)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w15, w16)), Nat.mul(U32.to_nat(U32.mul(w15, w17)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w18, w19)), Nat.mul(U32.to_nat(U32.mul(w18, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w22)), Nat.mul(U32.to_nat(U32.mul(w21, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w25)), Nat.mul(U32.to_nat(U32.mul(w24, w26)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w27, w28)), Nat.mul(U32.to_nat(U32.mul(w27, w29)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w30, w31)), Nat.mul(U32.to_nat(U32.mul(w30, w32)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w33, w34)), Nat.mul(U32.to_nat(U32.mul(w33, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w37)), Nat.mul(U32.to_nat(U32.mul(w36, w38)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w39, w40)), Nat.mul(U32.to_nat(U32.mul(w39, w41)), 512n)), Nat.add(U32.to_nat(U32.mul(w42, w43)), Nat.mul(U32.to_nat(U32.mul(w42, w44)), 512n))))))))))))))), 19n))
      +w46 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w43)), Nat.mul(U32.to_nat(U32.mul(w0, w44)), 512n)), Nat.add(U32.to_nat(U32.mul(w3, w1)), Nat.mul(U32.to_nat(U32.mul(w3, w2)), 512n))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w6, w4)), Nat.mul(U32.to_nat(U32.mul(w6, w5)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w7)), Nat.mul(U32.to_nat(U32.mul(w9, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w10)), Nat.mul(U32.to_nat(U32.mul(w12, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w15, w13)), Nat.mul(U32.to_nat(U32.mul(w15, w14)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w18, w16)), Nat.mul(U32.to_nat(U32.mul(w18, w17)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w19)), Nat.mul(U32.to_nat(U32.mul(w21, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w22)), Nat.mul(U32.to_nat(U32.mul(w24, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w27, w25)), Nat.mul(U32.to_nat(U32.mul(w27, w26)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w30, w28)), Nat.mul(U32.to_nat(U32.mul(w30, w29)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w33, w31)), Nat.mul(U32.to_nat(U32.mul(w33, w32)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w34)), Nat.mul(U32.to_nat(U32.mul(w36, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w39, w37)), Nat.mul(U32.to_nat(U32.mul(w39, w38)), 512n)), Nat.add(U32.to_nat(U32.mul(w42, w40)), Nat.mul(U32.to_nat(U32.mul(w42, w41)), 512n)))))))))))))), 19n)), Nat.div(w45, R))
      +w47 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w40)), Nat.mul(U32.to_nat(U32.mul(w0, w41)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w3, w43)), Nat.mul(U32.to_nat(U32.mul(w3, w44)), 512n)), Nat.add(U32.to_nat(U32.mul(w6, w1)), Nat.mul(U32.to_nat(U32.mul(w6, w2)), 512n)))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w4)), Nat.mul(U32.to_nat(U32.mul(w9, w5)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w7)), Nat.mul(U32.to_nat(U32.mul(w12, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w15, w10)), Nat.mul(U32.to_nat(U32.mul(w15, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w18, w13)), Nat.mul(U32.to_nat(U32.mul(w18, w14)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w16)), Nat.mul(U32.to_nat(U32.mul(w21, w17)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w19)), Nat.mul(U32.to_nat(U32.mul(w24, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w27, w22)), Nat.mul(U32.to_nat(U32.mul(w27, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w30, w25)), Nat.mul(U32.to_nat(U32.mul(w30, w26)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w33, w28)), Nat.mul(U32.to_nat(U32.mul(w33, w29)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w31)), Nat.mul(U32.to_nat(U32.mul(w36, w32)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w39, w34)), Nat.mul(U32.to_nat(U32.mul(w39, w35)), 512n)), Nat.add(U32.to_nat(U32.mul(w42, w37)), Nat.mul(U32.to_nat(U32.mul(w42, w38)), 512n))))))))))))), 19n)), Nat.div(w46, R))
      +w48 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w37)), Nat.mul(U32.to_nat(U32.mul(w0, w38)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w3, w40)), Nat.mul(U32.to_nat(U32.mul(w3, w41)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w6, w43)), Nat.mul(U32.to_nat(U32.mul(w6, w44)), 512n)), Nat.add(U32.to_nat(U32.mul(w9, w1)), Nat.mul(U32.to_nat(U32.mul(w9, w2)), 512n))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w4)), Nat.mul(U32.to_nat(U32.mul(w12, w5)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w15, w7)), Nat.mul(U32.to_nat(U32.mul(w15, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w18, w10)), Nat.mul(U32.to_nat(U32.mul(w18, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w13)), Nat.mul(U32.to_nat(U32.mul(w21, w14)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w16)), Nat.mul(U32.to_nat(U32.mul(w24, w17)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w27, w19)), Nat.mul(U32.to_nat(U32.mul(w27, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w30, w22)), Nat.mul(U32.to_nat(U32.mul(w30, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w33, w25)), Nat.mul(U32.to_nat(U32.mul(w33, w26)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w28)), Nat.mul(U32.to_nat(U32.mul(w36, w29)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w39, w31)), Nat.mul(U32.to_nat(U32.mul(w39, w32)), 512n)), Nat.add(U32.to_nat(U32.mul(w42, w34)), Nat.mul(U32.to_nat(U32.mul(w42, w35)), 512n)))))))))))), 19n)), Nat.div(w47, R))
      +w49 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w34)), Nat.mul(U32.to_nat(U32.mul(w0, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w3, w37)), Nat.mul(U32.to_nat(U32.mul(w3, w38)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w6, w40)), Nat.mul(U32.to_nat(U32.mul(w6, w41)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w43)), Nat.mul(U32.to_nat(U32.mul(w9, w44)), 512n)), Nat.add(U32.to_nat(U32.mul(w12, w1)), Nat.mul(U32.to_nat(U32.mul(w12, w2)), 512n)))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w15, w4)), Nat.mul(U32.to_nat(U32.mul(w15, w5)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w18, w7)), Nat.mul(U32.to_nat(U32.mul(w18, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w10)), Nat.mul(U32.to_nat(U32.mul(w21, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w13)), Nat.mul(U32.to_nat(U32.mul(w24, w14)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w27, w16)), Nat.mul(U32.to_nat(U32.mul(w27, w17)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w30, w19)), Nat.mul(U32.to_nat(U32.mul(w30, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w33, w22)), Nat.mul(U32.to_nat(U32.mul(w33, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w25)), Nat.mul(U32.to_nat(U32.mul(w36, w26)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w39, w28)), Nat.mul(U32.to_nat(U32.mul(w39, w29)), 512n)), Nat.add(U32.to_nat(U32.mul(w42, w31)), Nat.mul(U32.to_nat(U32.mul(w42, w32)), 512n))))))))))), 19n)), Nat.div(w48, R))
      +w50 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w31)), Nat.mul(U32.to_nat(U32.mul(w0, w32)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w3, w34)), Nat.mul(U32.to_nat(U32.mul(w3, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w6, w37)), Nat.mul(U32.to_nat(U32.mul(w6, w38)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w40)), Nat.mul(U32.to_nat(U32.mul(w9, w41)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w43)), Nat.mul(U32.to_nat(U32.mul(w12, w44)), 512n)), Nat.add(U32.to_nat(U32.mul(w15, w1)), Nat.mul(U32.to_nat(U32.mul(w15, w2)), 512n))))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w18, w4)), Nat.mul(U32.to_nat(U32.mul(w18, w5)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w7)), Nat.mul(U32.to_nat(U32.mul(w21, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w10)), Nat.mul(U32.to_nat(U32.mul(w24, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w27, w13)), Nat.mul(U32.to_nat(U32.mul(w27, w14)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w30, w16)), Nat.mul(U32.to_nat(U32.mul(w30, w17)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w33, w19)), Nat.mul(U32.to_nat(U32.mul(w33, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w22)), Nat.mul(U32.to_nat(U32.mul(w36, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w39, w25)), Nat.mul(U32.to_nat(U32.mul(w39, w26)), 512n)), Nat.add(U32.to_nat(U32.mul(w42, w28)), Nat.mul(U32.to_nat(U32.mul(w42, w29)), 512n)))))))))), 19n)), Nat.div(w49, R))
      +w51 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w28)), Nat.mul(U32.to_nat(U32.mul(w0, w29)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w3, w31)), Nat.mul(U32.to_nat(U32.mul(w3, w32)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w6, w34)), Nat.mul(U32.to_nat(U32.mul(w6, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w37)), Nat.mul(U32.to_nat(U32.mul(w9, w38)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w40)), Nat.mul(U32.to_nat(U32.mul(w12, w41)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w15, w43)), Nat.mul(U32.to_nat(U32.mul(w15, w44)), 512n)), Nat.add(U32.to_nat(U32.mul(w18, w1)), Nat.mul(U32.to_nat(U32.mul(w18, w2)), 512n)))))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w4)), Nat.mul(U32.to_nat(U32.mul(w21, w5)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w7)), Nat.mul(U32.to_nat(U32.mul(w24, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w27, w10)), Nat.mul(U32.to_nat(U32.mul(w27, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w30, w13)), Nat.mul(U32.to_nat(U32.mul(w30, w14)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w33, w16)), Nat.mul(U32.to_nat(U32.mul(w33, w17)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w19)), Nat.mul(U32.to_nat(U32.mul(w36, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w39, w22)), Nat.mul(U32.to_nat(U32.mul(w39, w23)), 512n)), Nat.add(U32.to_nat(U32.mul(w42, w25)), Nat.mul(U32.to_nat(U32.mul(w42, w26)), 512n))))))))), 19n)), Nat.div(w50, R))
      +w52 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w25)), Nat.mul(U32.to_nat(U32.mul(w0, w26)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w3, w28)), Nat.mul(U32.to_nat(U32.mul(w3, w29)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w6, w31)), Nat.mul(U32.to_nat(U32.mul(w6, w32)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w34)), Nat.mul(U32.to_nat(U32.mul(w9, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w37)), Nat.mul(U32.to_nat(U32.mul(w12, w38)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w15, w40)), Nat.mul(U32.to_nat(U32.mul(w15, w41)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w18, w43)), Nat.mul(U32.to_nat(U32.mul(w18, w44)), 512n)), Nat.add(U32.to_nat(U32.mul(w21, w1)), Nat.mul(U32.to_nat(U32.mul(w21, w2)), 512n))))))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w4)), Nat.mul(U32.to_nat(U32.mul(w24, w5)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w27, w7)), Nat.mul(U32.to_nat(U32.mul(w27, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w30, w10)), Nat.mul(U32.to_nat(U32.mul(w30, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w33, w13)), Nat.mul(U32.to_nat(U32.mul(w33, w14)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w16)), Nat.mul(U32.to_nat(U32.mul(w36, w17)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w39, w19)), Nat.mul(U32.to_nat(U32.mul(w39, w20)), 512n)), Nat.add(U32.to_nat(U32.mul(w42, w22)), Nat.mul(U32.to_nat(U32.mul(w42, w23)), 512n)))))))), 19n)), Nat.div(w51, R))
      +w53 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w22)), Nat.mul(U32.to_nat(U32.mul(w0, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w3, w25)), Nat.mul(U32.to_nat(U32.mul(w3, w26)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w6, w28)), Nat.mul(U32.to_nat(U32.mul(w6, w29)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w31)), Nat.mul(U32.to_nat(U32.mul(w9, w32)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w34)), Nat.mul(U32.to_nat(U32.mul(w12, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w15, w37)), Nat.mul(U32.to_nat(U32.mul(w15, w38)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w18, w40)), Nat.mul(U32.to_nat(U32.mul(w18, w41)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w43)), Nat.mul(U32.to_nat(U32.mul(w21, w44)), 512n)), Nat.add(U32.to_nat(U32.mul(w24, w1)), Nat.mul(U32.to_nat(U32.mul(w24, w2)), 512n)))))))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w27, w4)), Nat.mul(U32.to_nat(U32.mul(w27, w5)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w30, w7)), Nat.mul(U32.to_nat(U32.mul(w30, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w33, w10)), Nat.mul(U32.to_nat(U32.mul(w33, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w13)), Nat.mul(U32.to_nat(U32.mul(w36, w14)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w39, w16)), Nat.mul(U32.to_nat(U32.mul(w39, w17)), 512n)), Nat.add(U32.to_nat(U32.mul(w42, w19)), Nat.mul(U32.to_nat(U32.mul(w42, w20)), 512n))))))), 19n)), Nat.div(w52, R))
      +w54 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w19)), Nat.mul(U32.to_nat(U32.mul(w0, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w3, w22)), Nat.mul(U32.to_nat(U32.mul(w3, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w6, w25)), Nat.mul(U32.to_nat(U32.mul(w6, w26)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w28)), Nat.mul(U32.to_nat(U32.mul(w9, w29)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w31)), Nat.mul(U32.to_nat(U32.mul(w12, w32)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w15, w34)), Nat.mul(U32.to_nat(U32.mul(w15, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w18, w37)), Nat.mul(U32.to_nat(U32.mul(w18, w38)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w40)), Nat.mul(U32.to_nat(U32.mul(w21, w41)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w43)), Nat.mul(U32.to_nat(U32.mul(w24, w44)), 512n)), Nat.add(U32.to_nat(U32.mul(w27, w1)), Nat.mul(U32.to_nat(U32.mul(w27, w2)), 512n))))))))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w30, w4)), Nat.mul(U32.to_nat(U32.mul(w30, w5)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w33, w7)), Nat.mul(U32.to_nat(U32.mul(w33, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w10)), Nat.mul(U32.to_nat(U32.mul(w36, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w39, w13)), Nat.mul(U32.to_nat(U32.mul(w39, w14)), 512n)), Nat.add(U32.to_nat(U32.mul(w42, w16)), Nat.mul(U32.to_nat(U32.mul(w42, w17)), 512n)))))), 19n)), Nat.div(w53, R))
      +w55 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w16)), Nat.mul(U32.to_nat(U32.mul(w0, w17)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w3, w19)), Nat.mul(U32.to_nat(U32.mul(w3, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w6, w22)), Nat.mul(U32.to_nat(U32.mul(w6, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w25)), Nat.mul(U32.to_nat(U32.mul(w9, w26)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w28)), Nat.mul(U32.to_nat(U32.mul(w12, w29)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w15, w31)), Nat.mul(U32.to_nat(U32.mul(w15, w32)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w18, w34)), Nat.mul(U32.to_nat(U32.mul(w18, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w37)), Nat.mul(U32.to_nat(U32.mul(w21, w38)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w40)), Nat.mul(U32.to_nat(U32.mul(w24, w41)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w27, w43)), Nat.mul(U32.to_nat(U32.mul(w27, w44)), 512n)), Nat.add(U32.to_nat(U32.mul(w30, w1)), Nat.mul(U32.to_nat(U32.mul(w30, w2)), 512n)))))))))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w33, w4)), Nat.mul(U32.to_nat(U32.mul(w33, w5)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w7)), Nat.mul(U32.to_nat(U32.mul(w36, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w39, w10)), Nat.mul(U32.to_nat(U32.mul(w39, w11)), 512n)), Nat.add(U32.to_nat(U32.mul(w42, w13)), Nat.mul(U32.to_nat(U32.mul(w42, w14)), 512n))))), 19n)), Nat.div(w54, R))
      +w56 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w13)), Nat.mul(U32.to_nat(U32.mul(w0, w14)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w3, w16)), Nat.mul(U32.to_nat(U32.mul(w3, w17)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w6, w19)), Nat.mul(U32.to_nat(U32.mul(w6, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w22)), Nat.mul(U32.to_nat(U32.mul(w9, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w25)), Nat.mul(U32.to_nat(U32.mul(w12, w26)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w15, w28)), Nat.mul(U32.to_nat(U32.mul(w15, w29)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w18, w31)), Nat.mul(U32.to_nat(U32.mul(w18, w32)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w34)), Nat.mul(U32.to_nat(U32.mul(w21, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w37)), Nat.mul(U32.to_nat(U32.mul(w24, w38)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w27, w40)), Nat.mul(U32.to_nat(U32.mul(w27, w41)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w30, w43)), Nat.mul(U32.to_nat(U32.mul(w30, w44)), 512n)), Nat.add(U32.to_nat(U32.mul(w33, w1)), Nat.mul(U32.to_nat(U32.mul(w33, w2)), 512n))))))))))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w4)), Nat.mul(U32.to_nat(U32.mul(w36, w5)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w39, w7)), Nat.mul(U32.to_nat(U32.mul(w39, w8)), 512n)), Nat.add(U32.to_nat(U32.mul(w42, w10)), Nat.mul(U32.to_nat(U32.mul(w42, w11)), 512n)))), 19n)), Nat.div(w55, R))
      +w57 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w10)), Nat.mul(U32.to_nat(U32.mul(w0, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w3, w13)), Nat.mul(U32.to_nat(U32.mul(w3, w14)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w6, w16)), Nat.mul(U32.to_nat(U32.mul(w6, w17)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w19)), Nat.mul(U32.to_nat(U32.mul(w9, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w22)), Nat.mul(U32.to_nat(U32.mul(w12, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w15, w25)), Nat.mul(U32.to_nat(U32.mul(w15, w26)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w18, w28)), Nat.mul(U32.to_nat(U32.mul(w18, w29)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w31)), Nat.mul(U32.to_nat(U32.mul(w21, w32)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w34)), Nat.mul(U32.to_nat(U32.mul(w24, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w27, w37)), Nat.mul(U32.to_nat(U32.mul(w27, w38)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w30, w40)), Nat.mul(U32.to_nat(U32.mul(w30, w41)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w33, w43)), Nat.mul(U32.to_nat(U32.mul(w33, w44)), 512n)), Nat.add(U32.to_nat(U32.mul(w36, w1)), Nat.mul(U32.to_nat(U32.mul(w36, w2)), 512n)))))))))))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w39, w4)), Nat.mul(U32.to_nat(U32.mul(w39, w5)), 512n)), Nat.add(U32.to_nat(U32.mul(w42, w7)), Nat.mul(U32.to_nat(U32.mul(w42, w8)), 512n))), 19n)), Nat.div(w56, R))
      +w58 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w7)), Nat.mul(U32.to_nat(U32.mul(w0, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w3, w10)), Nat.mul(U32.to_nat(U32.mul(w3, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w6, w13)), Nat.mul(U32.to_nat(U32.mul(w6, w14)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w16)), Nat.mul(U32.to_nat(U32.mul(w9, w17)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w19)), Nat.mul(U32.to_nat(U32.mul(w12, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w15, w22)), Nat.mul(U32.to_nat(U32.mul(w15, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w18, w25)), Nat.mul(U32.to_nat(U32.mul(w18, w26)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w28)), Nat.mul(U32.to_nat(U32.mul(w21, w29)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w31)), Nat.mul(U32.to_nat(U32.mul(w24, w32)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w27, w34)), Nat.mul(U32.to_nat(U32.mul(w27, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w30, w37)), Nat.mul(U32.to_nat(U32.mul(w30, w38)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w33, w40)), Nat.mul(U32.to_nat(U32.mul(w33, w41)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w43)), Nat.mul(U32.to_nat(U32.mul(w36, w44)), 512n)), Nat.add(U32.to_nat(U32.mul(w39, w1)), Nat.mul(U32.to_nat(U32.mul(w39, w2)), 512n))))))))))))))), Nat.mul(Nat.add(U32.to_nat(U32.mul(w42, w4)), Nat.mul(U32.to_nat(U32.mul(w42, w5)), 512n)), 19n)), Nat.div(w57, R))
      +w59 = Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w4)), Nat.mul(U32.to_nat(U32.mul(w0, w5)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w3, w7)), Nat.mul(U32.to_nat(U32.mul(w3, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w6, w10)), Nat.mul(U32.to_nat(U32.mul(w6, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w13)), Nat.mul(U32.to_nat(U32.mul(w9, w14)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w16)), Nat.mul(U32.to_nat(U32.mul(w12, w17)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w15, w19)), Nat.mul(U32.to_nat(U32.mul(w15, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w18, w22)), Nat.mul(U32.to_nat(U32.mul(w18, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w25)), Nat.mul(U32.to_nat(U32.mul(w21, w26)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w28)), Nat.mul(U32.to_nat(U32.mul(w24, w29)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w27, w31)), Nat.mul(U32.to_nat(U32.mul(w27, w32)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w30, w34)), Nat.mul(U32.to_nat(U32.mul(w30, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w33, w37)), Nat.mul(U32.to_nat(U32.mul(w33, w38)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w40)), Nat.mul(U32.to_nat(U32.mul(w36, w41)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w39, w43)), Nat.mul(U32.to_nat(U32.mul(w39, w44)), 512n)), Nat.add(U32.to_nat(U32.mul(w42, w1)), Nat.mul(U32.to_nat(U32.mul(w42, w2)), 512n)))))))))))))))), Nat.div(w58, R))
      +w60 = Nat.add(Nat.mod(w45, R), Nat.mul(Nat.div(w59, R), 19n))
      Fe{Nat.mod(w60, R), Nat.add(Nat.mod(w46, R), Nat.div(w60, R)), Nat.mod(w47, R), Nat.mod(w48, R), Nat.mod(w49, R), Nat.mod(w50, R), Nat.mod(w51, R), Nat.mod(w52, R), Nat.mod(w53, R), Nat.mod(w54, R), Nat.mod(w55, R), Nat.mod(w56, R), Nat.mod(w57, R), Nat.mod(w58, R), Nat.mod(w59, R)}

# a^2, each cross product once: LS.sq_l
def sq(+R: Nat, a: Fe) -> Fe:
  match a:
    case Fe{+a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7, +a8, +a9, +a10, +a11, +a12, +a13, +a14}:
      +w0 = U32.from_nat(a0)
      +w1 = U32.from_nat(a1)
      +w2 = Nat.add(a14, a14)
      +w3 = U32.from_nat(Nat.mod(w2, 512n))
      +w4 = U32.from_nat(Nat.div(w2, 512n))
      +w5 = U32.from_nat(a2)
      +w6 = Nat.add(a13, a13)
      +w7 = U32.from_nat(Nat.mod(w6, 512n))
      +w8 = U32.from_nat(Nat.div(w6, 512n))
      +w9 = U32.from_nat(a3)
      +w10 = Nat.add(a12, a12)
      +w11 = U32.from_nat(Nat.mod(w10, 512n))
      +w12 = U32.from_nat(Nat.div(w10, 512n))
      +w13 = U32.from_nat(a4)
      +w14 = Nat.add(a11, a11)
      +w15 = U32.from_nat(Nat.mod(w14, 512n))
      +w16 = U32.from_nat(Nat.div(w14, 512n))
      +w17 = U32.from_nat(a5)
      +w18 = Nat.add(a10, a10)
      +w19 = U32.from_nat(Nat.mod(w18, 512n))
      +w20 = U32.from_nat(Nat.div(w18, 512n))
      +w21 = U32.from_nat(a6)
      +w22 = Nat.add(a9, a9)
      +w23 = U32.from_nat(Nat.mod(w22, 512n))
      +w24 = U32.from_nat(Nat.div(w22, 512n))
      +w25 = U32.from_nat(a7)
      +w26 = Nat.add(a8, a8)
      +w27 = U32.from_nat(Nat.mod(w26, 512n))
      +w28 = U32.from_nat(Nat.div(w26, 512n))
      +w29 = Nat.add(Nat.add(U32.to_nat(U32.mul(w0, U32.from_nat(Nat.mod(a0, 512n)))), Nat.mul(U32.to_nat(U32.mul(w0, U32.from_nat(Nat.div(a0, 512n)))), 512n)), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w3)), Nat.mul(U32.to_nat(U32.mul(w1, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w7)), Nat.mul(U32.to_nat(U32.mul(w5, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w11)), Nat.mul(U32.to_nat(U32.mul(w9, w12)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w13, w15)), Nat.mul(U32.to_nat(U32.mul(w13, w16)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w17, w19)), Nat.mul(U32.to_nat(U32.mul(w17, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w23)), Nat.mul(U32.to_nat(U32.mul(w21, w24)), 512n)), Nat.add(U32.to_nat(U32.mul(w25, w27)), Nat.mul(U32.to_nat(U32.mul(w25, w28)), 512n)))))))), 19n))
      +w30 = Nat.add(a7, a7)
      +w31 = U32.from_nat(Nat.mod(w30, 512n))
      +w32 = U32.from_nat(Nat.div(w30, 512n))
      +w33 = U32.from_nat(a14)
      +w34 = U32.from_nat(a13)
      +w35 = Nat.add(a6, a6)
      +w36 = U32.from_nat(Nat.mod(w35, 512n))
      +w37 = U32.from_nat(Nat.div(w35, 512n))
      +w38 = U32.from_nat(a12)
      +w39 = U32.from_nat(a11)
      +w40 = Nat.add(a5, a5)
      +w41 = U32.from_nat(Nat.mod(w40, 512n))
      +w42 = U32.from_nat(Nat.div(w40, 512n))
      +w43 = U32.from_nat(a10)
      +w44 = U32.from_nat(a9)
      +w45 = Nat.add(a4, a4)
      +w46 = U32.from_nat(Nat.mod(w45, 512n))
      +w47 = U32.from_nat(Nat.div(w45, 512n))
      +w48 = U32.from_nat(a8)
      +w49 = Nat.add(a3, a3)
      +w50 = U32.from_nat(Nat.mod(w49, 512n))
      +w51 = U32.from_nat(Nat.div(w49, 512n))
      +w52 = Nat.add(a2, a2)
      +w53 = U32.from_nat(Nat.mod(w52, 512n))
      +w54 = U32.from_nat(Nat.div(w52, 512n))
      +w55 = Nat.add(a1, a1)
      +w56 = Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, U32.from_nat(Nat.mod(w55, 512n)))), Nat.mul(U32.to_nat(U32.mul(w0, U32.from_nat(Nat.div(w55, 512n)))), 512n)), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w3)), Nat.mul(U32.to_nat(U32.mul(w5, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w7)), Nat.mul(U32.to_nat(U32.mul(w9, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w13, w11)), Nat.mul(U32.to_nat(U32.mul(w13, w12)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w17, w15)), Nat.mul(U32.to_nat(U32.mul(w17, w16)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w19)), Nat.mul(U32.to_nat(U32.mul(w21, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w25, w23)), Nat.mul(U32.to_nat(U32.mul(w25, w24)), 512n)), Nat.add(U32.to_nat(U32.mul(w48, U32.from_nat(Nat.mod(a8, 512n)))), Nat.mul(U32.to_nat(U32.mul(w48, U32.from_nat(Nat.div(a8, 512n)))), 512n)))))))), 19n)), Nat.div(w29, R))
      +w57 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w53)), Nat.mul(U32.to_nat(U32.mul(w0, w54)), 512n)), Nat.add(U32.to_nat(U32.mul(w1, U32.from_nat(Nat.mod(a1, 512n)))), Nat.mul(U32.to_nat(U32.mul(w1, U32.from_nat(Nat.div(a1, 512n)))), 512n))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w3)), Nat.mul(U32.to_nat(U32.mul(w9, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w13, w7)), Nat.mul(U32.to_nat(U32.mul(w13, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w17, w11)), Nat.mul(U32.to_nat(U32.mul(w17, w12)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w15)), Nat.mul(U32.to_nat(U32.mul(w21, w16)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w25, w19)), Nat.mul(U32.to_nat(U32.mul(w25, w20)), 512n)), Nat.add(U32.to_nat(U32.mul(w48, w23)), Nat.mul(U32.to_nat(U32.mul(w48, w24)), 512n))))))), 19n)), Nat.div(w56, R))
      +w58 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w50)), Nat.mul(U32.to_nat(U32.mul(w0, w51)), 512n)), Nat.add(U32.to_nat(U32.mul(w1, w53)), Nat.mul(U32.to_nat(U32.mul(w1, w54)), 512n))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w13, w3)), Nat.mul(U32.to_nat(U32.mul(w13, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w17, w7)), Nat.mul(U32.to_nat(U32.mul(w17, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w11)), Nat.mul(U32.to_nat(U32.mul(w21, w12)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w25, w15)), Nat.mul(U32.to_nat(U32.mul(w25, w16)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w19)), Nat.mul(U32.to_nat(U32.mul(w48, w20)), 512n)), Nat.add(U32.to_nat(U32.mul(w44, U32.from_nat(Nat.mod(a9, 512n)))), Nat.mul(U32.to_nat(U32.mul(w44, U32.from_nat(Nat.div(a9, 512n)))), 512n))))))), 19n)), Nat.div(w57, R))
      +w59 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w46)), Nat.mul(U32.to_nat(U32.mul(w0, w47)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w50)), Nat.mul(U32.to_nat(U32.mul(w1, w51)), 512n)), Nat.add(U32.to_nat(U32.mul(w5, U32.from_nat(Nat.mod(a2, 512n)))), Nat.mul(U32.to_nat(U32.mul(w5, U32.from_nat(Nat.div(a2, 512n)))), 512n)))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w17, w3)), Nat.mul(U32.to_nat(U32.mul(w17, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w7)), Nat.mul(U32.to_nat(U32.mul(w21, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w25, w11)), Nat.mul(U32.to_nat(U32.mul(w25, w12)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w15)), Nat.mul(U32.to_nat(U32.mul(w48, w16)), 512n)), Nat.add(U32.to_nat(U32.mul(w44, w19)), Nat.mul(U32.to_nat(U32.mul(w44, w20)), 512n)))))), 19n)), Nat.div(w58, R))
      +w60 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w41)), Nat.mul(U32.to_nat(U32.mul(w0, w42)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w46)), Nat.mul(U32.to_nat(U32.mul(w1, w47)), 512n)), Nat.add(U32.to_nat(U32.mul(w5, w50)), Nat.mul(U32.to_nat(U32.mul(w5, w51)), 512n)))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w3)), Nat.mul(U32.to_nat(U32.mul(w21, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w25, w7)), Nat.mul(U32.to_nat(U32.mul(w25, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w11)), Nat.mul(U32.to_nat(U32.mul(w48, w12)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w15)), Nat.mul(U32.to_nat(U32.mul(w44, w16)), 512n)), Nat.add(U32.to_nat(U32.mul(w43, U32.from_nat(Nat.mod(a10, 512n)))), Nat.mul(U32.to_nat(U32.mul(w43, U32.from_nat(Nat.div(a10, 512n)))), 512n)))))), 19n)), Nat.div(w59, R))
      +w61 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w36)), Nat.mul(U32.to_nat(U32.mul(w0, w37)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w41)), Nat.mul(U32.to_nat(U32.mul(w1, w42)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w46)), Nat.mul(U32.to_nat(U32.mul(w5, w47)), 512n)), Nat.add(U32.to_nat(U32.mul(w9, U32.from_nat(Nat.mod(a3, 512n)))), Nat.mul(U32.to_nat(U32.mul(w9, U32.from_nat(Nat.div(a3, 512n)))), 512n))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w25, w3)), Nat.mul(U32.to_nat(U32.mul(w25, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w7)), Nat.mul(U32.to_nat(U32.mul(w48, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w11)), Nat.mul(U32.to_nat(U32.mul(w44, w12)), 512n)), Nat.add(U32.to_nat(U32.mul(w43, w15)), Nat.mul(U32.to_nat(U32.mul(w43, w16)), 512n))))), 19n)), Nat.div(w60, R))
      +w62 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w31)), Nat.mul(U32.to_nat(U32.mul(w0, w32)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w36)), Nat.mul(U32.to_nat(U32.mul(w1, w37)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w41)), Nat.mul(U32.to_nat(U32.mul(w5, w42)), 512n)), Nat.add(U32.to_nat(U32.mul(w9, w46)), Nat.mul(U32.to_nat(U32.mul(w9, w47)), 512n))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w3)), Nat.mul(U32.to_nat(U32.mul(w48, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w7)), Nat.mul(U32.to_nat(U32.mul(w44, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w43, w11)), Nat.mul(U32.to_nat(U32.mul(w43, w12)), 512n)), Nat.add(U32.to_nat(U32.mul(w39, U32.from_nat(Nat.mod(a11, 512n)))), Nat.mul(U32.to_nat(U32.mul(w39, U32.from_nat(Nat.div(a11, 512n)))), 512n))))), 19n)), Nat.div(w61, R))
      +w63 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w27)), Nat.mul(U32.to_nat(U32.mul(w0, w28)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w31)), Nat.mul(U32.to_nat(U32.mul(w1, w32)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w36)), Nat.mul(U32.to_nat(U32.mul(w5, w37)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w41)), Nat.mul(U32.to_nat(U32.mul(w9, w42)), 512n)), Nat.add(U32.to_nat(U32.mul(w13, U32.from_nat(Nat.mod(a4, 512n)))), Nat.mul(U32.to_nat(U32.mul(w13, U32.from_nat(Nat.div(a4, 512n)))), 512n)))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w3)), Nat.mul(U32.to_nat(U32.mul(w44, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w43, w7)), Nat.mul(U32.to_nat(U32.mul(w43, w8)), 512n)), Nat.add(U32.to_nat(U32.mul(w39, w11)), Nat.mul(U32.to_nat(U32.mul(w39, w12)), 512n)))), 19n)), Nat.div(w62, R))
      +w64 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w23)), Nat.mul(U32.to_nat(U32.mul(w0, w24)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w27)), Nat.mul(U32.to_nat(U32.mul(w1, w28)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w31)), Nat.mul(U32.to_nat(U32.mul(w5, w32)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w36)), Nat.mul(U32.to_nat(U32.mul(w9, w37)), 512n)), Nat.add(U32.to_nat(U32.mul(w13, w41)), Nat.mul(U32.to_nat(U32.mul(w13, w42)), 512n)))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w43, w3)), Nat.mul(U32.to_nat(U32.mul(w43, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w39, w7)), Nat.mul(U32.to_nat(U32.mul(w39, w8)), 512n)), Nat.add(U32.to_nat(U32.mul(w38, U32.from_nat(Nat.mod(a12, 512n)))), Nat.mul(U32.to_nat(U32.mul(w38, U32.from_nat(Nat.div(a12, 512n)))), 512n)))), 19n)), Nat.div(w63, R))
      +w65 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w19)), Nat.mul(U32.to_nat(U32.mul(w0, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w23)), Nat.mul(U32.to_nat(U32.mul(w1, w24)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w27)), Nat.mul(U32.to_nat(U32.mul(w5, w28)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w31)), Nat.mul(U32.to_nat(U32.mul(w9, w32)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w13, w36)), Nat.mul(U32.to_nat(U32.mul(w13, w37)), 512n)), Nat.add(U32.to_nat(U32.mul(w17, U32.from_nat(Nat.mod(a5, 512n)))), Nat.mul(U32.to_nat(U32.mul(w17, U32.from_nat(Nat.div(a5, 512n)))), 512n))))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w39, w3)), Nat.mul(U32.to_nat(U32.mul(w39, w4)), 512n)), Nat.add(U32.to_nat(U32.mul(w38, w7)), Nat.mul(U32.to_nat(U32.mul(w38, w8)), 512n))), 19n)), Nat.div(w64, R))
      +w66 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w15)), Nat.mul(U32.to_nat(U32.mul(w0, w16)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w19)), Nat.mul(U32.to_nat(U32.mul(w1, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w23)), Nat.mul(U32.to_nat(U32.mul(w5, w24)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w27)), Nat.mul(U32.to_nat(U32.mul(w9, w28)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w13, w31)), Nat.mul(U32.to_nat(U32.mul(w13, w32)), 512n)), Nat.add(U32.to_nat(U32.mul(w17, w36)), Nat.mul(U32.to_nat(U32.mul(w17, w37)), 512n))))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w38, w3)), Nat.mul(U32.to_nat(U32.mul(w38, w4)), 512n)), Nat.add(U32.to_nat(U32.mul(w34, U32.from_nat(Nat.mod(a13, 512n)))), Nat.mul(U32.to_nat(U32.mul(w34, U32.from_nat(Nat.div(a13, 512n)))), 512n))), 19n)), Nat.div(w65, R))
      +w67 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w11)), Nat.mul(U32.to_nat(U32.mul(w0, w12)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w15)), Nat.mul(U32.to_nat(U32.mul(w1, w16)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w19)), Nat.mul(U32.to_nat(U32.mul(w5, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w23)), Nat.mul(U32.to_nat(U32.mul(w9, w24)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w13, w27)), Nat.mul(U32.to_nat(U32.mul(w13, w28)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w17, w31)), Nat.mul(U32.to_nat(U32.mul(w17, w32)), 512n)), Nat.add(U32.to_nat(U32.mul(w21, U32.from_nat(Nat.mod(a6, 512n)))), Nat.mul(U32.to_nat(U32.mul(w21, U32.from_nat(Nat.div(a6, 512n)))), 512n)))))))), Nat.mul(Nat.add(U32.to_nat(U32.mul(w34, w3)), Nat.mul(U32.to_nat(U32.mul(w34, w4)), 512n)), 19n)), Nat.div(w66, R))
      +w68 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w7)), Nat.mul(U32.to_nat(U32.mul(w0, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w11)), Nat.mul(U32.to_nat(U32.mul(w1, w12)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w15)), Nat.mul(U32.to_nat(U32.mul(w5, w16)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w19)), Nat.mul(U32.to_nat(U32.mul(w9, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w13, w23)), Nat.mul(U32.to_nat(U32.mul(w13, w24)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w17, w27)), Nat.mul(U32.to_nat(U32.mul(w17, w28)), 512n)), Nat.add(U32.to_nat(U32.mul(w21, w31)), Nat.mul(U32.to_nat(U32.mul(w21, w32)), 512n)))))))), Nat.mul(Nat.add(U32.to_nat(U32.mul(w33, U32.from_nat(Nat.mod(a14, 512n)))), Nat.mul(U32.to_nat(U32.mul(w33, U32.from_nat(Nat.div(a14, 512n)))), 512n)), 19n)), Nat.div(w67, R))
      +w69 = Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w3)), Nat.mul(U32.to_nat(U32.mul(w0, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w7)), Nat.mul(U32.to_nat(U32.mul(w1, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w11)), Nat.mul(U32.to_nat(U32.mul(w5, w12)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w15)), Nat.mul(U32.to_nat(U32.mul(w9, w16)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w13, w19)), Nat.mul(U32.to_nat(U32.mul(w13, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w17, w23)), Nat.mul(U32.to_nat(U32.mul(w17, w24)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w27)), Nat.mul(U32.to_nat(U32.mul(w21, w28)), 512n)), Nat.add(U32.to_nat(U32.mul(w25, U32.from_nat(Nat.mod(a7, 512n)))), Nat.mul(U32.to_nat(U32.mul(w25, U32.from_nat(Nat.div(a7, 512n)))), 512n))))))))), Nat.div(w68, R))
      +w70 = Nat.add(Nat.mod(w29, R), Nat.mul(Nat.div(w69, R), 19n))
      Fe{Nat.mod(w70, R), Nat.add(Nat.mod(w56, R), Nat.div(w70, R)), Nat.mod(w57, R), Nat.mod(w58, R), Nat.mod(w59, R), Nat.mod(w60, R), Nat.mod(w61, R), Nat.mod(w62, R), Nat.mod(w63, R), Nat.mod(w64, R), Nat.mod(w65, R), Nat.mod(w66, R), Nat.mod(w67, R), Nat.mod(w68, R), Nat.mod(w69, R)}

# a k for k < 2^17: LS.mul_small_l
def mul_small(+R: Nat, a: Fe, +k: Nat) -> Fe:
  match a:
    case Fe{+a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7, +a8, +a9, +a10, +a11, +a12, +a13, +a14}:
      +w0 = Nat.mul(a0, k)
      +w1 = Nat.mul(a14, k)
      +w2 = Nat.add(Nat.mod(w0, R), Nat.mul(Nat.div(w1, R), 19n))
      +w3 = Nat.mul(a13, k)
      +w4 = Nat.add(Nat.mod(w1, R), Nat.div(w3, R))
      +w5 = Nat.mul(a1, k)
      +w6 = Nat.add(Nat.mod(w5, R), Nat.div(w0, R))
      +w7 = Nat.mul(a2, k)
      +w8 = Nat.add(Nat.mod(w7, R), Nat.div(w5, R))
      +w9 = Nat.mul(a3, k)
      +w10 = Nat.add(Nat.mod(w9, R), Nat.div(w7, R))
      +w11 = Nat.mul(a4, k)
      +w12 = Nat.add(Nat.mod(w11, R), Nat.div(w9, R))
      +w13 = Nat.mul(a5, k)
      +w14 = Nat.add(Nat.mod(w13, R), Nat.div(w11, R))
      +w15 = Nat.mul(a6, k)
      +w16 = Nat.add(Nat.mod(w15, R), Nat.div(w13, R))
      +w17 = Nat.mul(a7, k)
      +w18 = Nat.add(Nat.mod(w17, R), Nat.div(w15, R))
      +w19 = Nat.mul(a8, k)
      +w20 = Nat.add(Nat.mod(w19, R), Nat.div(w17, R))
      +w21 = Nat.mul(a9, k)
      +w22 = Nat.add(Nat.mod(w21, R), Nat.div(w19, R))
      +w23 = Nat.mul(a10, k)
      +w24 = Nat.add(Nat.mod(w23, R), Nat.div(w21, R))
      +w25 = Nat.mul(a11, k)
      +w26 = Nat.add(Nat.mod(w25, R), Nat.div(w23, R))
      +w27 = Nat.mul(a12, k)
      +w28 = Nat.add(Nat.mod(w27, R), Nat.div(w25, R))
      +w29 = Nat.add(Nat.mod(w3, R), Nat.div(w27, R))
      Fe{Nat.add(Nat.mod(w2, R), Nat.mul(Nat.div(w4, R), 19n)), Nat.add(Nat.mod(w6, R), Nat.div(w2, R)), Nat.add(Nat.mod(w8, R), Nat.div(w6, R)), Nat.add(Nat.mod(w10, R), Nat.div(w8, R)), Nat.add(Nat.mod(w12, R), Nat.div(w10, R)), Nat.add(Nat.mod(w14, R), Nat.div(w12, R)), Nat.add(Nat.mod(w16, R), Nat.div(w14, R)), Nat.add(Nat.mod(w18, R), Nat.div(w16, R)), Nat.add(Nat.mod(w20, R), Nat.div(w18, R)), Nat.add(Nat.mod(w22, R), Nat.div(w20, R)), Nat.add(Nat.mod(w24, R), Nat.div(w22, R)), Nat.add(Nat.mod(w26, R), Nat.div(w24, R)), Nat.add(Nat.mod(w28, R), Nat.div(w26, R)), Nat.add(Nat.mod(w29, R), Nat.div(w28, R)), Nat.add(Nat.mod(w4, R), Nat.div(w29, R))}

# s == 0: a; s == 1: b (LS.sel on U32.to_nat(s))
def select(+s: U32, a: Fe, b: Fe) -> Fe:
  match a b:
    case Fe{+a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7, +a8, +a9, +a10, +a11, +a12, +a13, +a14} Fe{+b0, +b1, +b2, +b3, +b4, +b5, +b6, +b7, +b8, +b9, +b10, +b11, +b12, +b13, +b14}:
      +sn = U32.to_nat(s)
      +w0 = Nat.sub(1n, sn)
      Fe{Nat.add(Nat.mul(a0, w0), Nat.mul(b0, sn)), Nat.add(Nat.mul(a1, w0), Nat.mul(b1, sn)), Nat.add(Nat.mul(a2, w0), Nat.mul(b2, sn)), Nat.add(Nat.mul(a3, w0), Nat.mul(b3, sn)), Nat.add(Nat.mul(a4, w0), Nat.mul(b4, sn)), Nat.add(Nat.mul(a5, w0), Nat.mul(b5, sn)), Nat.add(Nat.mul(a6, w0), Nat.mul(b6, sn)), Nat.add(Nat.mul(a7, w0), Nat.mul(b7, sn)), Nat.add(Nat.mul(a8, w0), Nat.mul(b8, sn)), Nat.add(Nat.mul(a9, w0), Nat.mul(b9, sn)), Nat.add(Nat.mul(a10, w0), Nat.mul(b10, sn)), Nat.add(Nat.mul(a11, w0), Nat.mul(b11, sn)), Nat.add(Nat.mul(a12, w0), Nat.mul(b12, sn)), Nat.add(Nat.mul(a13, w0), Nat.mul(b13, sn)), Nat.add(Nat.mul(a14, w0), Nat.mul(b14, sn))}

def neg(+R: Nat, a: Fe) -> Fe:
  sub(R, zero(), a)

# ---- powers (public exponents) ----
#
# The loops take the base x first and inspect it before their counter, so
# the proof checker never unfolds a fixed-count loop over an unknown base.

# y^(2^n): n squarings. g is the chain's base, passed unchanged and
# inspected first, so the proof checker never unfolds the loop over an
# unknown base.
def sqn(+R: Nat, +g: Fe, n: Nat, y: Fe) -> Fe:
  match g:
    case Fe{l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14}:
      match n:
        case 0n:
          y
        case 1n+m:
          sqn(R, g, m, sq(R, y))

# y^(2^m) z: with y = x^(2^n - 1) and z = x^(2^m - 1), x^(2^(n + m) - 1)
def cat(+R: Nat, +g: Fe, y: Fe, z: Fe, m: Nat) -> Fe:
  mul(R, sqn(R, g, m, y), z)

# x^(2^250 - 1): the addition chain of ref10's fe_invert (249 squarings,
# 10 multiplications)
def p250(+R: Nat, +x: Fe) -> Fe:
  +z2 = cat(R, x, x, x, 1n)
  +z4 = cat(R, x, z2, z2, 2n)
  +z5 = cat(R, x, z4, x, 1n)
  +z10 = cat(R, x, z5, z5, 5n)
  +z20 = cat(R, x, z10, z10, 10n)
  +z40 = cat(R, x, z20, z20, 20n)
  +z50 = cat(R, x, z40, z10, 10n)
  +z100 = cat(R, x, z50, z50, 50n)
  +z200 = cat(R, x, z100, z100, 100n)
  cat(R, x, z200, z50, 50n)

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

# x^(p - 2) = x^(2^255 - 21): 250 one bits, then 0 1 0 1 1
def inv(+R: Nat, +x: Fe) -> Fe:
  pow_bits(R, x, [False{}, True{}, False{}, True{}, True{}], p250(R, x))

# x^((p - 5) / 8) = x^(2^252 - 3): 250 one bits, then 0 1
def pow_p58(+R: Nat, +x: Fe) -> Fe:
  pow_bits(R, x, [False{}, True{}], p250(R, x))

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
