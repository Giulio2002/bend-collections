import Base
import ./limbs.bend as LS

# GF(p), p = 2^255 - 19, for X25519 and Ed25519: 15 limbs of 17 bits,
# value(x) = l0 + 2^17 l1 + ... + 2^238 l14 (spec/crypto/curve25519/fe.bend).
# The limbs are Nat: the native backend keeps a Nat below 2^48 in one
# machine word, and every intermediate here stays below 2^48 (proved: an
# element is "ok" when its limbs are below 2^19; the schoolbook product of
# two ok elements has columns below 15 * 2^38, the fold by 19 keeps them
# below 2^47, and a carry pass brings them back to ok). This is the
# unsaturated-limb field of Fiat-Crypto (Erbsen et al. 2019) and HACL*'s
# Field51, with 17-bit limbs so that products and sums fit the 48-bit Nat.
#
# Limb products run on the native 32-bit multiplier (LS.pm: one factor
# split at bit 9 by a mask and a shift of its 32-bit word, both half
# products below 2^29): a Nat product checks its 48-bit bound with a
# division. The square computes each cross product once
# (LS.sqp). add and sub move every carry one limb up at once, with no carry
# chain (LS.pc); mul and sq end with one chained carry pass, mul_small with
# two rounds of LS.pc.
#
# add, sub, mul, sq, mul_small and select are straight-line code, written
# by tools/gen_fe.py from the list algorithms of limbs.bend (do not edit
# them by hand; rerun the script). Every operation takes the radix
# R = 2^17, which the callers compute once from their symbolic one
# (radix(one)), so the proofs never meet a closed 2^17.
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
      +w1 = U32.from_nat(b0)
      +w2 = U32.and(w1, 511)
      +w3 = U32.shrn(w1, 9n)
      +w4 = U32.from_nat(a1)
      +w5 = U32.from_nat(b14)
      +w6 = U32.and(w5, 511)
      +w7 = U32.shrn(w5, 9n)
      +w8 = U32.from_nat(a2)
      +w9 = U32.from_nat(b13)
      +w10 = U32.and(w9, 511)
      +w11 = U32.shrn(w9, 9n)
      +w12 = U32.from_nat(a3)
      +w13 = U32.from_nat(b12)
      +w14 = U32.and(w13, 511)
      +w15 = U32.shrn(w13, 9n)
      +w16 = U32.from_nat(a4)
      +w17 = U32.from_nat(b11)
      +w18 = U32.and(w17, 511)
      +w19 = U32.shrn(w17, 9n)
      +w20 = U32.from_nat(a5)
      +w21 = U32.from_nat(b10)
      +w22 = U32.and(w21, 511)
      +w23 = U32.shrn(w21, 9n)
      +w24 = U32.from_nat(a6)
      +w25 = U32.from_nat(b9)
      +w26 = U32.and(w25, 511)
      +w27 = U32.shrn(w25, 9n)
      +w28 = U32.from_nat(a7)
      +w29 = U32.from_nat(b8)
      +w30 = U32.and(w29, 511)
      +w31 = U32.shrn(w29, 9n)
      +w32 = U32.from_nat(a8)
      +w33 = U32.from_nat(b7)
      +w34 = U32.and(w33, 511)
      +w35 = U32.shrn(w33, 9n)
      +w36 = U32.from_nat(a9)
      +w37 = U32.from_nat(b6)
      +w38 = U32.and(w37, 511)
      +w39 = U32.shrn(w37, 9n)
      +w40 = U32.from_nat(a10)
      +w41 = U32.from_nat(b5)
      +w42 = U32.and(w41, 511)
      +w43 = U32.shrn(w41, 9n)
      +w44 = U32.from_nat(a11)
      +w45 = U32.from_nat(b4)
      +w46 = U32.and(w45, 511)
      +w47 = U32.shrn(w45, 9n)
      +w48 = U32.from_nat(a12)
      +w49 = U32.from_nat(b3)
      +w50 = U32.and(w49, 511)
      +w51 = U32.shrn(w49, 9n)
      +w52 = U32.from_nat(a13)
      +w53 = U32.from_nat(b2)
      +w54 = U32.and(w53, 511)
      +w55 = U32.shrn(w53, 9n)
      +w56 = U32.from_nat(a14)
      +w57 = U32.from_nat(b1)
      +w58 = U32.and(w57, 511)
      +w59 = U32.shrn(w57, 9n)
      +w60 = Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w2)), Nat.mul(U32.to_nat(U32.mul(w0, w3)), 512n)), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w4, w6)), Nat.mul(U32.to_nat(U32.mul(w4, w7)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w8, w10)), Nat.mul(U32.to_nat(U32.mul(w8, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w14)), Nat.mul(U32.to_nat(U32.mul(w12, w15)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w16, w18)), Nat.mul(U32.to_nat(U32.mul(w16, w19)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w20, w22)), Nat.mul(U32.to_nat(U32.mul(w20, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w26)), Nat.mul(U32.to_nat(U32.mul(w24, w27)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w28, w30)), Nat.mul(U32.to_nat(U32.mul(w28, w31)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w32, w34)), Nat.mul(U32.to_nat(U32.mul(w32, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w38)), Nat.mul(U32.to_nat(U32.mul(w36, w39)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w40, w42)), Nat.mul(U32.to_nat(U32.mul(w40, w43)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w46)), Nat.mul(U32.to_nat(U32.mul(w44, w47)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w50)), Nat.mul(U32.to_nat(U32.mul(w48, w51)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w52, w54)), Nat.mul(U32.to_nat(U32.mul(w52, w55)), 512n)), Nat.add(U32.to_nat(U32.mul(w56, w58)), Nat.mul(U32.to_nat(U32.mul(w56, w59)), 512n))))))))))))))), 19n))
      +w61 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w58)), Nat.mul(U32.to_nat(U32.mul(w0, w59)), 512n)), Nat.add(U32.to_nat(U32.mul(w4, w2)), Nat.mul(U32.to_nat(U32.mul(w4, w3)), 512n))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w8, w6)), Nat.mul(U32.to_nat(U32.mul(w8, w7)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w10)), Nat.mul(U32.to_nat(U32.mul(w12, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w16, w14)), Nat.mul(U32.to_nat(U32.mul(w16, w15)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w20, w18)), Nat.mul(U32.to_nat(U32.mul(w20, w19)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w22)), Nat.mul(U32.to_nat(U32.mul(w24, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w28, w26)), Nat.mul(U32.to_nat(U32.mul(w28, w27)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w32, w30)), Nat.mul(U32.to_nat(U32.mul(w32, w31)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w34)), Nat.mul(U32.to_nat(U32.mul(w36, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w40, w38)), Nat.mul(U32.to_nat(U32.mul(w40, w39)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w42)), Nat.mul(U32.to_nat(U32.mul(w44, w43)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w46)), Nat.mul(U32.to_nat(U32.mul(w48, w47)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w52, w50)), Nat.mul(U32.to_nat(U32.mul(w52, w51)), 512n)), Nat.add(U32.to_nat(U32.mul(w56, w54)), Nat.mul(U32.to_nat(U32.mul(w56, w55)), 512n)))))))))))))), 19n)), Nat.div(w60, R))
      +w62 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w54)), Nat.mul(U32.to_nat(U32.mul(w0, w55)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w4, w58)), Nat.mul(U32.to_nat(U32.mul(w4, w59)), 512n)), Nat.add(U32.to_nat(U32.mul(w8, w2)), Nat.mul(U32.to_nat(U32.mul(w8, w3)), 512n)))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w6)), Nat.mul(U32.to_nat(U32.mul(w12, w7)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w16, w10)), Nat.mul(U32.to_nat(U32.mul(w16, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w20, w14)), Nat.mul(U32.to_nat(U32.mul(w20, w15)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w18)), Nat.mul(U32.to_nat(U32.mul(w24, w19)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w28, w22)), Nat.mul(U32.to_nat(U32.mul(w28, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w32, w26)), Nat.mul(U32.to_nat(U32.mul(w32, w27)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w30)), Nat.mul(U32.to_nat(U32.mul(w36, w31)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w40, w34)), Nat.mul(U32.to_nat(U32.mul(w40, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w38)), Nat.mul(U32.to_nat(U32.mul(w44, w39)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w42)), Nat.mul(U32.to_nat(U32.mul(w48, w43)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w52, w46)), Nat.mul(U32.to_nat(U32.mul(w52, w47)), 512n)), Nat.add(U32.to_nat(U32.mul(w56, w50)), Nat.mul(U32.to_nat(U32.mul(w56, w51)), 512n))))))))))))), 19n)), Nat.div(w61, R))
      +w63 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w50)), Nat.mul(U32.to_nat(U32.mul(w0, w51)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w4, w54)), Nat.mul(U32.to_nat(U32.mul(w4, w55)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w8, w58)), Nat.mul(U32.to_nat(U32.mul(w8, w59)), 512n)), Nat.add(U32.to_nat(U32.mul(w12, w2)), Nat.mul(U32.to_nat(U32.mul(w12, w3)), 512n))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w16, w6)), Nat.mul(U32.to_nat(U32.mul(w16, w7)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w20, w10)), Nat.mul(U32.to_nat(U32.mul(w20, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w14)), Nat.mul(U32.to_nat(U32.mul(w24, w15)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w28, w18)), Nat.mul(U32.to_nat(U32.mul(w28, w19)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w32, w22)), Nat.mul(U32.to_nat(U32.mul(w32, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w26)), Nat.mul(U32.to_nat(U32.mul(w36, w27)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w40, w30)), Nat.mul(U32.to_nat(U32.mul(w40, w31)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w34)), Nat.mul(U32.to_nat(U32.mul(w44, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w38)), Nat.mul(U32.to_nat(U32.mul(w48, w39)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w52, w42)), Nat.mul(U32.to_nat(U32.mul(w52, w43)), 512n)), Nat.add(U32.to_nat(U32.mul(w56, w46)), Nat.mul(U32.to_nat(U32.mul(w56, w47)), 512n)))))))))))), 19n)), Nat.div(w62, R))
      +w64 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w46)), Nat.mul(U32.to_nat(U32.mul(w0, w47)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w4, w50)), Nat.mul(U32.to_nat(U32.mul(w4, w51)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w8, w54)), Nat.mul(U32.to_nat(U32.mul(w8, w55)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w58)), Nat.mul(U32.to_nat(U32.mul(w12, w59)), 512n)), Nat.add(U32.to_nat(U32.mul(w16, w2)), Nat.mul(U32.to_nat(U32.mul(w16, w3)), 512n)))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w20, w6)), Nat.mul(U32.to_nat(U32.mul(w20, w7)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w10)), Nat.mul(U32.to_nat(U32.mul(w24, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w28, w14)), Nat.mul(U32.to_nat(U32.mul(w28, w15)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w32, w18)), Nat.mul(U32.to_nat(U32.mul(w32, w19)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w22)), Nat.mul(U32.to_nat(U32.mul(w36, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w40, w26)), Nat.mul(U32.to_nat(U32.mul(w40, w27)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w30)), Nat.mul(U32.to_nat(U32.mul(w44, w31)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w34)), Nat.mul(U32.to_nat(U32.mul(w48, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w52, w38)), Nat.mul(U32.to_nat(U32.mul(w52, w39)), 512n)), Nat.add(U32.to_nat(U32.mul(w56, w42)), Nat.mul(U32.to_nat(U32.mul(w56, w43)), 512n))))))))))), 19n)), Nat.div(w63, R))
      +w65 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w42)), Nat.mul(U32.to_nat(U32.mul(w0, w43)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w4, w46)), Nat.mul(U32.to_nat(U32.mul(w4, w47)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w8, w50)), Nat.mul(U32.to_nat(U32.mul(w8, w51)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w54)), Nat.mul(U32.to_nat(U32.mul(w12, w55)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w16, w58)), Nat.mul(U32.to_nat(U32.mul(w16, w59)), 512n)), Nat.add(U32.to_nat(U32.mul(w20, w2)), Nat.mul(U32.to_nat(U32.mul(w20, w3)), 512n))))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w6)), Nat.mul(U32.to_nat(U32.mul(w24, w7)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w28, w10)), Nat.mul(U32.to_nat(U32.mul(w28, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w32, w14)), Nat.mul(U32.to_nat(U32.mul(w32, w15)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w18)), Nat.mul(U32.to_nat(U32.mul(w36, w19)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w40, w22)), Nat.mul(U32.to_nat(U32.mul(w40, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w26)), Nat.mul(U32.to_nat(U32.mul(w44, w27)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w30)), Nat.mul(U32.to_nat(U32.mul(w48, w31)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w52, w34)), Nat.mul(U32.to_nat(U32.mul(w52, w35)), 512n)), Nat.add(U32.to_nat(U32.mul(w56, w38)), Nat.mul(U32.to_nat(U32.mul(w56, w39)), 512n)))))))))), 19n)), Nat.div(w64, R))
      +w66 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w38)), Nat.mul(U32.to_nat(U32.mul(w0, w39)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w4, w42)), Nat.mul(U32.to_nat(U32.mul(w4, w43)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w8, w46)), Nat.mul(U32.to_nat(U32.mul(w8, w47)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w50)), Nat.mul(U32.to_nat(U32.mul(w12, w51)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w16, w54)), Nat.mul(U32.to_nat(U32.mul(w16, w55)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w20, w58)), Nat.mul(U32.to_nat(U32.mul(w20, w59)), 512n)), Nat.add(U32.to_nat(U32.mul(w24, w2)), Nat.mul(U32.to_nat(U32.mul(w24, w3)), 512n)))))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w28, w6)), Nat.mul(U32.to_nat(U32.mul(w28, w7)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w32, w10)), Nat.mul(U32.to_nat(U32.mul(w32, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w14)), Nat.mul(U32.to_nat(U32.mul(w36, w15)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w40, w18)), Nat.mul(U32.to_nat(U32.mul(w40, w19)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w22)), Nat.mul(U32.to_nat(U32.mul(w44, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w26)), Nat.mul(U32.to_nat(U32.mul(w48, w27)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w52, w30)), Nat.mul(U32.to_nat(U32.mul(w52, w31)), 512n)), Nat.add(U32.to_nat(U32.mul(w56, w34)), Nat.mul(U32.to_nat(U32.mul(w56, w35)), 512n))))))))), 19n)), Nat.div(w65, R))
      +w67 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w34)), Nat.mul(U32.to_nat(U32.mul(w0, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w4, w38)), Nat.mul(U32.to_nat(U32.mul(w4, w39)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w8, w42)), Nat.mul(U32.to_nat(U32.mul(w8, w43)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w46)), Nat.mul(U32.to_nat(U32.mul(w12, w47)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w16, w50)), Nat.mul(U32.to_nat(U32.mul(w16, w51)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w20, w54)), Nat.mul(U32.to_nat(U32.mul(w20, w55)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w58)), Nat.mul(U32.to_nat(U32.mul(w24, w59)), 512n)), Nat.add(U32.to_nat(U32.mul(w28, w2)), Nat.mul(U32.to_nat(U32.mul(w28, w3)), 512n))))))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w32, w6)), Nat.mul(U32.to_nat(U32.mul(w32, w7)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w10)), Nat.mul(U32.to_nat(U32.mul(w36, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w40, w14)), Nat.mul(U32.to_nat(U32.mul(w40, w15)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w18)), Nat.mul(U32.to_nat(U32.mul(w44, w19)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w22)), Nat.mul(U32.to_nat(U32.mul(w48, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w52, w26)), Nat.mul(U32.to_nat(U32.mul(w52, w27)), 512n)), Nat.add(U32.to_nat(U32.mul(w56, w30)), Nat.mul(U32.to_nat(U32.mul(w56, w31)), 512n)))))))), 19n)), Nat.div(w66, R))
      +w68 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w30)), Nat.mul(U32.to_nat(U32.mul(w0, w31)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w4, w34)), Nat.mul(U32.to_nat(U32.mul(w4, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w8, w38)), Nat.mul(U32.to_nat(U32.mul(w8, w39)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w42)), Nat.mul(U32.to_nat(U32.mul(w12, w43)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w16, w46)), Nat.mul(U32.to_nat(U32.mul(w16, w47)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w20, w50)), Nat.mul(U32.to_nat(U32.mul(w20, w51)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w54)), Nat.mul(U32.to_nat(U32.mul(w24, w55)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w28, w58)), Nat.mul(U32.to_nat(U32.mul(w28, w59)), 512n)), Nat.add(U32.to_nat(U32.mul(w32, w2)), Nat.mul(U32.to_nat(U32.mul(w32, w3)), 512n)))))))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w6)), Nat.mul(U32.to_nat(U32.mul(w36, w7)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w40, w10)), Nat.mul(U32.to_nat(U32.mul(w40, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w14)), Nat.mul(U32.to_nat(U32.mul(w44, w15)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w18)), Nat.mul(U32.to_nat(U32.mul(w48, w19)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w52, w22)), Nat.mul(U32.to_nat(U32.mul(w52, w23)), 512n)), Nat.add(U32.to_nat(U32.mul(w56, w26)), Nat.mul(U32.to_nat(U32.mul(w56, w27)), 512n))))))), 19n)), Nat.div(w67, R))
      +w69 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w26)), Nat.mul(U32.to_nat(U32.mul(w0, w27)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w4, w30)), Nat.mul(U32.to_nat(U32.mul(w4, w31)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w8, w34)), Nat.mul(U32.to_nat(U32.mul(w8, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w38)), Nat.mul(U32.to_nat(U32.mul(w12, w39)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w16, w42)), Nat.mul(U32.to_nat(U32.mul(w16, w43)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w20, w46)), Nat.mul(U32.to_nat(U32.mul(w20, w47)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w50)), Nat.mul(U32.to_nat(U32.mul(w24, w51)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w28, w54)), Nat.mul(U32.to_nat(U32.mul(w28, w55)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w32, w58)), Nat.mul(U32.to_nat(U32.mul(w32, w59)), 512n)), Nat.add(U32.to_nat(U32.mul(w36, w2)), Nat.mul(U32.to_nat(U32.mul(w36, w3)), 512n))))))))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w40, w6)), Nat.mul(U32.to_nat(U32.mul(w40, w7)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w10)), Nat.mul(U32.to_nat(U32.mul(w44, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w14)), Nat.mul(U32.to_nat(U32.mul(w48, w15)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w52, w18)), Nat.mul(U32.to_nat(U32.mul(w52, w19)), 512n)), Nat.add(U32.to_nat(U32.mul(w56, w22)), Nat.mul(U32.to_nat(U32.mul(w56, w23)), 512n)))))), 19n)), Nat.div(w68, R))
      +w70 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w22)), Nat.mul(U32.to_nat(U32.mul(w0, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w4, w26)), Nat.mul(U32.to_nat(U32.mul(w4, w27)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w8, w30)), Nat.mul(U32.to_nat(U32.mul(w8, w31)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w34)), Nat.mul(U32.to_nat(U32.mul(w12, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w16, w38)), Nat.mul(U32.to_nat(U32.mul(w16, w39)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w20, w42)), Nat.mul(U32.to_nat(U32.mul(w20, w43)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w46)), Nat.mul(U32.to_nat(U32.mul(w24, w47)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w28, w50)), Nat.mul(U32.to_nat(U32.mul(w28, w51)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w32, w54)), Nat.mul(U32.to_nat(U32.mul(w32, w55)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w58)), Nat.mul(U32.to_nat(U32.mul(w36, w59)), 512n)), Nat.add(U32.to_nat(U32.mul(w40, w2)), Nat.mul(U32.to_nat(U32.mul(w40, w3)), 512n)))))))))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w6)), Nat.mul(U32.to_nat(U32.mul(w44, w7)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w10)), Nat.mul(U32.to_nat(U32.mul(w48, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w52, w14)), Nat.mul(U32.to_nat(U32.mul(w52, w15)), 512n)), Nat.add(U32.to_nat(U32.mul(w56, w18)), Nat.mul(U32.to_nat(U32.mul(w56, w19)), 512n))))), 19n)), Nat.div(w69, R))
      +w71 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w18)), Nat.mul(U32.to_nat(U32.mul(w0, w19)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w4, w22)), Nat.mul(U32.to_nat(U32.mul(w4, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w8, w26)), Nat.mul(U32.to_nat(U32.mul(w8, w27)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w30)), Nat.mul(U32.to_nat(U32.mul(w12, w31)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w16, w34)), Nat.mul(U32.to_nat(U32.mul(w16, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w20, w38)), Nat.mul(U32.to_nat(U32.mul(w20, w39)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w42)), Nat.mul(U32.to_nat(U32.mul(w24, w43)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w28, w46)), Nat.mul(U32.to_nat(U32.mul(w28, w47)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w32, w50)), Nat.mul(U32.to_nat(U32.mul(w32, w51)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w54)), Nat.mul(U32.to_nat(U32.mul(w36, w55)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w40, w58)), Nat.mul(U32.to_nat(U32.mul(w40, w59)), 512n)), Nat.add(U32.to_nat(U32.mul(w44, w2)), Nat.mul(U32.to_nat(U32.mul(w44, w3)), 512n))))))))))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w6)), Nat.mul(U32.to_nat(U32.mul(w48, w7)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w52, w10)), Nat.mul(U32.to_nat(U32.mul(w52, w11)), 512n)), Nat.add(U32.to_nat(U32.mul(w56, w14)), Nat.mul(U32.to_nat(U32.mul(w56, w15)), 512n)))), 19n)), Nat.div(w70, R))
      +w72 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w14)), Nat.mul(U32.to_nat(U32.mul(w0, w15)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w4, w18)), Nat.mul(U32.to_nat(U32.mul(w4, w19)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w8, w22)), Nat.mul(U32.to_nat(U32.mul(w8, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w26)), Nat.mul(U32.to_nat(U32.mul(w12, w27)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w16, w30)), Nat.mul(U32.to_nat(U32.mul(w16, w31)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w20, w34)), Nat.mul(U32.to_nat(U32.mul(w20, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w38)), Nat.mul(U32.to_nat(U32.mul(w24, w39)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w28, w42)), Nat.mul(U32.to_nat(U32.mul(w28, w43)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w32, w46)), Nat.mul(U32.to_nat(U32.mul(w32, w47)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w50)), Nat.mul(U32.to_nat(U32.mul(w36, w51)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w40, w54)), Nat.mul(U32.to_nat(U32.mul(w40, w55)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w58)), Nat.mul(U32.to_nat(U32.mul(w44, w59)), 512n)), Nat.add(U32.to_nat(U32.mul(w48, w2)), Nat.mul(U32.to_nat(U32.mul(w48, w3)), 512n)))))))))))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w52, w6)), Nat.mul(U32.to_nat(U32.mul(w52, w7)), 512n)), Nat.add(U32.to_nat(U32.mul(w56, w10)), Nat.mul(U32.to_nat(U32.mul(w56, w11)), 512n))), 19n)), Nat.div(w71, R))
      +w73 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w10)), Nat.mul(U32.to_nat(U32.mul(w0, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w4, w14)), Nat.mul(U32.to_nat(U32.mul(w4, w15)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w8, w18)), Nat.mul(U32.to_nat(U32.mul(w8, w19)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w22)), Nat.mul(U32.to_nat(U32.mul(w12, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w16, w26)), Nat.mul(U32.to_nat(U32.mul(w16, w27)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w20, w30)), Nat.mul(U32.to_nat(U32.mul(w20, w31)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w34)), Nat.mul(U32.to_nat(U32.mul(w24, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w28, w38)), Nat.mul(U32.to_nat(U32.mul(w28, w39)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w32, w42)), Nat.mul(U32.to_nat(U32.mul(w32, w43)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w46)), Nat.mul(U32.to_nat(U32.mul(w36, w47)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w40, w50)), Nat.mul(U32.to_nat(U32.mul(w40, w51)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w54)), Nat.mul(U32.to_nat(U32.mul(w44, w55)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w58)), Nat.mul(U32.to_nat(U32.mul(w48, w59)), 512n)), Nat.add(U32.to_nat(U32.mul(w52, w2)), Nat.mul(U32.to_nat(U32.mul(w52, w3)), 512n))))))))))))))), Nat.mul(Nat.add(U32.to_nat(U32.mul(w56, w6)), Nat.mul(U32.to_nat(U32.mul(w56, w7)), 512n)), 19n)), Nat.div(w72, R))
      +w74 = Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w6)), Nat.mul(U32.to_nat(U32.mul(w0, w7)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w4, w10)), Nat.mul(U32.to_nat(U32.mul(w4, w11)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w8, w14)), Nat.mul(U32.to_nat(U32.mul(w8, w15)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w12, w18)), Nat.mul(U32.to_nat(U32.mul(w12, w19)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w16, w22)), Nat.mul(U32.to_nat(U32.mul(w16, w23)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w20, w26)), Nat.mul(U32.to_nat(U32.mul(w20, w27)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w24, w30)), Nat.mul(U32.to_nat(U32.mul(w24, w31)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w28, w34)), Nat.mul(U32.to_nat(U32.mul(w28, w35)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w32, w38)), Nat.mul(U32.to_nat(U32.mul(w32, w39)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w36, w42)), Nat.mul(U32.to_nat(U32.mul(w36, w43)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w40, w46)), Nat.mul(U32.to_nat(U32.mul(w40, w47)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w50)), Nat.mul(U32.to_nat(U32.mul(w44, w51)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w54)), Nat.mul(U32.to_nat(U32.mul(w48, w55)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w52, w58)), Nat.mul(U32.to_nat(U32.mul(w52, w59)), 512n)), Nat.add(U32.to_nat(U32.mul(w56, w2)), Nat.mul(U32.to_nat(U32.mul(w56, w3)), 512n)))))))))))))))), Nat.div(w73, R))
      +w75 = Nat.add(Nat.mod(w60, R), Nat.mul(Nat.div(w74, R), 19n))
      Fe{Nat.mod(w75, R), Nat.add(Nat.mod(w61, R), Nat.div(w75, R)), Nat.mod(w62, R), Nat.mod(w63, R), Nat.mod(w64, R), Nat.mod(w65, R), Nat.mod(w66, R), Nat.mod(w67, R), Nat.mod(w68, R), Nat.mod(w69, R), Nat.mod(w70, R), Nat.mod(w71, R), Nat.mod(w72, R), Nat.mod(w73, R), Nat.mod(w74, R)}

# a^2, each cross product once: LS.sq_l
def sq(+R: Nat, a: Fe) -> Fe:
  match a:
    case Fe{+a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7, +a8, +a9, +a10, +a11, +a12, +a13, +a14}:
      +w0 = U32.from_nat(a0)
      +w1 = U32.from_nat(a1)
      +w2 = U32.from_nat(Nat.add(a14, a14))
      +w3 = U32.and(w2, 511)
      +w4 = U32.shrn(w2, 9n)
      +w5 = U32.from_nat(a2)
      +w6 = U32.from_nat(Nat.add(a13, a13))
      +w7 = U32.and(w6, 511)
      +w8 = U32.shrn(w6, 9n)
      +w9 = U32.from_nat(a3)
      +w10 = U32.from_nat(Nat.add(a12, a12))
      +w11 = U32.and(w10, 511)
      +w12 = U32.shrn(w10, 9n)
      +w13 = U32.from_nat(a4)
      +w14 = U32.from_nat(Nat.add(a11, a11))
      +w15 = U32.and(w14, 511)
      +w16 = U32.shrn(w14, 9n)
      +w17 = U32.from_nat(a5)
      +w18 = U32.from_nat(Nat.add(a10, a10))
      +w19 = U32.and(w18, 511)
      +w20 = U32.shrn(w18, 9n)
      +w21 = U32.from_nat(a6)
      +w22 = U32.from_nat(Nat.add(a9, a9))
      +w23 = U32.and(w22, 511)
      +w24 = U32.shrn(w22, 9n)
      +w25 = U32.from_nat(a7)
      +w26 = U32.from_nat(Nat.add(a8, a8))
      +w27 = U32.and(w26, 511)
      +w28 = U32.shrn(w26, 9n)
      +w29 = Nat.add(Nat.add(U32.to_nat(U32.mul(w0, U32.and(w0, 511))), Nat.mul(U32.to_nat(U32.mul(w0, U32.shrn(w0, 9n))), 512n)), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w3)), Nat.mul(U32.to_nat(U32.mul(w1, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w7)), Nat.mul(U32.to_nat(U32.mul(w5, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w11)), Nat.mul(U32.to_nat(U32.mul(w9, w12)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w13, w15)), Nat.mul(U32.to_nat(U32.mul(w13, w16)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w17, w19)), Nat.mul(U32.to_nat(U32.mul(w17, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w23)), Nat.mul(U32.to_nat(U32.mul(w21, w24)), 512n)), Nat.add(U32.to_nat(U32.mul(w25, w27)), Nat.mul(U32.to_nat(U32.mul(w25, w28)), 512n)))))))), 19n))
      +w30 = U32.from_nat(Nat.add(a7, a7))
      +w31 = U32.and(w30, 511)
      +w32 = U32.shrn(w30, 9n)
      +w33 = U32.from_nat(a14)
      +w34 = U32.from_nat(a13)
      +w35 = U32.from_nat(Nat.add(a6, a6))
      +w36 = U32.and(w35, 511)
      +w37 = U32.shrn(w35, 9n)
      +w38 = U32.from_nat(a12)
      +w39 = U32.from_nat(a11)
      +w40 = U32.from_nat(Nat.add(a5, a5))
      +w41 = U32.and(w40, 511)
      +w42 = U32.shrn(w40, 9n)
      +w43 = U32.from_nat(a10)
      +w44 = U32.from_nat(a9)
      +w45 = U32.from_nat(Nat.add(a4, a4))
      +w46 = U32.and(w45, 511)
      +w47 = U32.shrn(w45, 9n)
      +w48 = U32.from_nat(a8)
      +w49 = U32.from_nat(Nat.add(a3, a3))
      +w50 = U32.and(w49, 511)
      +w51 = U32.shrn(w49, 9n)
      +w52 = U32.from_nat(Nat.add(a2, a2))
      +w53 = U32.and(w52, 511)
      +w54 = U32.shrn(w52, 9n)
      +w55 = U32.from_nat(Nat.add(a1, a1))
      +w56 = Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, U32.and(w55, 511))), Nat.mul(U32.to_nat(U32.mul(w0, U32.shrn(w55, 9n))), 512n)), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w3)), Nat.mul(U32.to_nat(U32.mul(w5, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w7)), Nat.mul(U32.to_nat(U32.mul(w9, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w13, w11)), Nat.mul(U32.to_nat(U32.mul(w13, w12)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w17, w15)), Nat.mul(U32.to_nat(U32.mul(w17, w16)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w19)), Nat.mul(U32.to_nat(U32.mul(w21, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w25, w23)), Nat.mul(U32.to_nat(U32.mul(w25, w24)), 512n)), Nat.add(U32.to_nat(U32.mul(w48, U32.and(w48, 511))), Nat.mul(U32.to_nat(U32.mul(w48, U32.shrn(w48, 9n))), 512n)))))))), 19n)), Nat.div(w29, R))
      +w57 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w53)), Nat.mul(U32.to_nat(U32.mul(w0, w54)), 512n)), Nat.add(U32.to_nat(U32.mul(w1, U32.and(w1, 511))), Nat.mul(U32.to_nat(U32.mul(w1, U32.shrn(w1, 9n))), 512n))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w3)), Nat.mul(U32.to_nat(U32.mul(w9, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w13, w7)), Nat.mul(U32.to_nat(U32.mul(w13, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w17, w11)), Nat.mul(U32.to_nat(U32.mul(w17, w12)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w15)), Nat.mul(U32.to_nat(U32.mul(w21, w16)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w25, w19)), Nat.mul(U32.to_nat(U32.mul(w25, w20)), 512n)), Nat.add(U32.to_nat(U32.mul(w48, w23)), Nat.mul(U32.to_nat(U32.mul(w48, w24)), 512n))))))), 19n)), Nat.div(w56, R))
      +w58 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w50)), Nat.mul(U32.to_nat(U32.mul(w0, w51)), 512n)), Nat.add(U32.to_nat(U32.mul(w1, w53)), Nat.mul(U32.to_nat(U32.mul(w1, w54)), 512n))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w13, w3)), Nat.mul(U32.to_nat(U32.mul(w13, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w17, w7)), Nat.mul(U32.to_nat(U32.mul(w17, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w11)), Nat.mul(U32.to_nat(U32.mul(w21, w12)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w25, w15)), Nat.mul(U32.to_nat(U32.mul(w25, w16)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w19)), Nat.mul(U32.to_nat(U32.mul(w48, w20)), 512n)), Nat.add(U32.to_nat(U32.mul(w44, U32.and(w44, 511))), Nat.mul(U32.to_nat(U32.mul(w44, U32.shrn(w44, 9n))), 512n))))))), 19n)), Nat.div(w57, R))
      +w59 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w46)), Nat.mul(U32.to_nat(U32.mul(w0, w47)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w50)), Nat.mul(U32.to_nat(U32.mul(w1, w51)), 512n)), Nat.add(U32.to_nat(U32.mul(w5, U32.and(w5, 511))), Nat.mul(U32.to_nat(U32.mul(w5, U32.shrn(w5, 9n))), 512n)))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w17, w3)), Nat.mul(U32.to_nat(U32.mul(w17, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w7)), Nat.mul(U32.to_nat(U32.mul(w21, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w25, w11)), Nat.mul(U32.to_nat(U32.mul(w25, w12)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w15)), Nat.mul(U32.to_nat(U32.mul(w48, w16)), 512n)), Nat.add(U32.to_nat(U32.mul(w44, w19)), Nat.mul(U32.to_nat(U32.mul(w44, w20)), 512n)))))), 19n)), Nat.div(w58, R))
      +w60 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w41)), Nat.mul(U32.to_nat(U32.mul(w0, w42)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w46)), Nat.mul(U32.to_nat(U32.mul(w1, w47)), 512n)), Nat.add(U32.to_nat(U32.mul(w5, w50)), Nat.mul(U32.to_nat(U32.mul(w5, w51)), 512n)))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w3)), Nat.mul(U32.to_nat(U32.mul(w21, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w25, w7)), Nat.mul(U32.to_nat(U32.mul(w25, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w11)), Nat.mul(U32.to_nat(U32.mul(w48, w12)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w15)), Nat.mul(U32.to_nat(U32.mul(w44, w16)), 512n)), Nat.add(U32.to_nat(U32.mul(w43, U32.and(w43, 511))), Nat.mul(U32.to_nat(U32.mul(w43, U32.shrn(w43, 9n))), 512n)))))), 19n)), Nat.div(w59, R))
      +w61 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w36)), Nat.mul(U32.to_nat(U32.mul(w0, w37)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w41)), Nat.mul(U32.to_nat(U32.mul(w1, w42)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w46)), Nat.mul(U32.to_nat(U32.mul(w5, w47)), 512n)), Nat.add(U32.to_nat(U32.mul(w9, U32.and(w9, 511))), Nat.mul(U32.to_nat(U32.mul(w9, U32.shrn(w9, 9n))), 512n))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w25, w3)), Nat.mul(U32.to_nat(U32.mul(w25, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w7)), Nat.mul(U32.to_nat(U32.mul(w48, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w11)), Nat.mul(U32.to_nat(U32.mul(w44, w12)), 512n)), Nat.add(U32.to_nat(U32.mul(w43, w15)), Nat.mul(U32.to_nat(U32.mul(w43, w16)), 512n))))), 19n)), Nat.div(w60, R))
      +w62 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w31)), Nat.mul(U32.to_nat(U32.mul(w0, w32)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w36)), Nat.mul(U32.to_nat(U32.mul(w1, w37)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w41)), Nat.mul(U32.to_nat(U32.mul(w5, w42)), 512n)), Nat.add(U32.to_nat(U32.mul(w9, w46)), Nat.mul(U32.to_nat(U32.mul(w9, w47)), 512n))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w48, w3)), Nat.mul(U32.to_nat(U32.mul(w48, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w7)), Nat.mul(U32.to_nat(U32.mul(w44, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w43, w11)), Nat.mul(U32.to_nat(U32.mul(w43, w12)), 512n)), Nat.add(U32.to_nat(U32.mul(w39, U32.and(w39, 511))), Nat.mul(U32.to_nat(U32.mul(w39, U32.shrn(w39, 9n))), 512n))))), 19n)), Nat.div(w61, R))
      +w63 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w27)), Nat.mul(U32.to_nat(U32.mul(w0, w28)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w31)), Nat.mul(U32.to_nat(U32.mul(w1, w32)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w36)), Nat.mul(U32.to_nat(U32.mul(w5, w37)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w41)), Nat.mul(U32.to_nat(U32.mul(w9, w42)), 512n)), Nat.add(U32.to_nat(U32.mul(w13, U32.and(w13, 511))), Nat.mul(U32.to_nat(U32.mul(w13, U32.shrn(w13, 9n))), 512n)))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w44, w3)), Nat.mul(U32.to_nat(U32.mul(w44, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w43, w7)), Nat.mul(U32.to_nat(U32.mul(w43, w8)), 512n)), Nat.add(U32.to_nat(U32.mul(w39, w11)), Nat.mul(U32.to_nat(U32.mul(w39, w12)), 512n)))), 19n)), Nat.div(w62, R))
      +w64 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w23)), Nat.mul(U32.to_nat(U32.mul(w0, w24)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w27)), Nat.mul(U32.to_nat(U32.mul(w1, w28)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w31)), Nat.mul(U32.to_nat(U32.mul(w5, w32)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w36)), Nat.mul(U32.to_nat(U32.mul(w9, w37)), 512n)), Nat.add(U32.to_nat(U32.mul(w13, w41)), Nat.mul(U32.to_nat(U32.mul(w13, w42)), 512n)))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w43, w3)), Nat.mul(U32.to_nat(U32.mul(w43, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w39, w7)), Nat.mul(U32.to_nat(U32.mul(w39, w8)), 512n)), Nat.add(U32.to_nat(U32.mul(w38, U32.and(w38, 511))), Nat.mul(U32.to_nat(U32.mul(w38, U32.shrn(w38, 9n))), 512n)))), 19n)), Nat.div(w63, R))
      +w65 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w19)), Nat.mul(U32.to_nat(U32.mul(w0, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w23)), Nat.mul(U32.to_nat(U32.mul(w1, w24)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w27)), Nat.mul(U32.to_nat(U32.mul(w5, w28)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w31)), Nat.mul(U32.to_nat(U32.mul(w9, w32)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w13, w36)), Nat.mul(U32.to_nat(U32.mul(w13, w37)), 512n)), Nat.add(U32.to_nat(U32.mul(w17, U32.and(w17, 511))), Nat.mul(U32.to_nat(U32.mul(w17, U32.shrn(w17, 9n))), 512n))))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w39, w3)), Nat.mul(U32.to_nat(U32.mul(w39, w4)), 512n)), Nat.add(U32.to_nat(U32.mul(w38, w7)), Nat.mul(U32.to_nat(U32.mul(w38, w8)), 512n))), 19n)), Nat.div(w64, R))
      +w66 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w15)), Nat.mul(U32.to_nat(U32.mul(w0, w16)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w19)), Nat.mul(U32.to_nat(U32.mul(w1, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w23)), Nat.mul(U32.to_nat(U32.mul(w5, w24)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w27)), Nat.mul(U32.to_nat(U32.mul(w9, w28)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w13, w31)), Nat.mul(U32.to_nat(U32.mul(w13, w32)), 512n)), Nat.add(U32.to_nat(U32.mul(w17, w36)), Nat.mul(U32.to_nat(U32.mul(w17, w37)), 512n))))))), Nat.mul(Nat.add(Nat.add(U32.to_nat(U32.mul(w38, w3)), Nat.mul(U32.to_nat(U32.mul(w38, w4)), 512n)), Nat.add(U32.to_nat(U32.mul(w34, U32.and(w34, 511))), Nat.mul(U32.to_nat(U32.mul(w34, U32.shrn(w34, 9n))), 512n))), 19n)), Nat.div(w65, R))
      +w67 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w11)), Nat.mul(U32.to_nat(U32.mul(w0, w12)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w15)), Nat.mul(U32.to_nat(U32.mul(w1, w16)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w19)), Nat.mul(U32.to_nat(U32.mul(w5, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w23)), Nat.mul(U32.to_nat(U32.mul(w9, w24)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w13, w27)), Nat.mul(U32.to_nat(U32.mul(w13, w28)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w17, w31)), Nat.mul(U32.to_nat(U32.mul(w17, w32)), 512n)), Nat.add(U32.to_nat(U32.mul(w21, U32.and(w21, 511))), Nat.mul(U32.to_nat(U32.mul(w21, U32.shrn(w21, 9n))), 512n)))))))), Nat.mul(Nat.add(U32.to_nat(U32.mul(w34, w3)), Nat.mul(U32.to_nat(U32.mul(w34, w4)), 512n)), 19n)), Nat.div(w66, R))
      +w68 = Nat.add(Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w7)), Nat.mul(U32.to_nat(U32.mul(w0, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w11)), Nat.mul(U32.to_nat(U32.mul(w1, w12)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w15)), Nat.mul(U32.to_nat(U32.mul(w5, w16)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w19)), Nat.mul(U32.to_nat(U32.mul(w9, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w13, w23)), Nat.mul(U32.to_nat(U32.mul(w13, w24)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w17, w27)), Nat.mul(U32.to_nat(U32.mul(w17, w28)), 512n)), Nat.add(U32.to_nat(U32.mul(w21, w31)), Nat.mul(U32.to_nat(U32.mul(w21, w32)), 512n)))))))), Nat.mul(Nat.add(U32.to_nat(U32.mul(w33, U32.and(w33, 511))), Nat.mul(U32.to_nat(U32.mul(w33, U32.shrn(w33, 9n))), 512n)), 19n)), Nat.div(w67, R))
      +w69 = Nat.add(Nat.add(Nat.add(U32.to_nat(U32.mul(w0, w3)), Nat.mul(U32.to_nat(U32.mul(w0, w4)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w1, w7)), Nat.mul(U32.to_nat(U32.mul(w1, w8)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w5, w11)), Nat.mul(U32.to_nat(U32.mul(w5, w12)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w9, w15)), Nat.mul(U32.to_nat(U32.mul(w9, w16)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w13, w19)), Nat.mul(U32.to_nat(U32.mul(w13, w20)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w17, w23)), Nat.mul(U32.to_nat(U32.mul(w17, w24)), 512n)), Nat.add(Nat.add(U32.to_nat(U32.mul(w21, w27)), Nat.mul(U32.to_nat(U32.mul(w21, w28)), 512n)), Nat.add(U32.to_nat(U32.mul(w25, U32.and(w25, 511))), Nat.mul(U32.to_nat(U32.mul(w25, U32.shrn(w25, 9n))), 512n))))))))), Nat.div(w68, R))
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
