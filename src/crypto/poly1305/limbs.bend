import Base

# Arithmetic modulo p = 2^130 - 5 on five natural-number limbs in radix
# w = 2^26 (the representation of poly1305-donna-32 and of HACL*'s
# Hacl.Spec.Poly1305.Field32xN): F{l0, l1, l2, l3, l4} stands for
# l0 + w l1 + w^2 l2 + w^3 l3 + w^4 l4, and w^5 = 2^130 = p + 5, so a limb
# product that lands at w^(5+i) is folded back onto w^i times 5.
#
# Bend's native runtime keeps a Nat in one machine word and aborts (never
# wraps) past 2^48, so the product of two 26-bit limbs (2^52) is out of
# reach. The multiplier r is therefore split into 13-bit halves,
# r = e + 2^13 o (e and o are five limbs each, below 2^13): the block
# product (h + m) r is (h + m) e + 2^13 (h + m) o, two schoolbook products
# whose terms stay below 2^44 and whose five-term sums stay below 2^46
# (proofs/crypto/poly1305/sops.bend has the bound table).
#
# The only radix literal is 2^13 = 8192: x div 2^26 and x mod 2^26 are two
# steps of 2^13 (dw and mw below). A division by a literal power of two
# compiles to a shift and a mask, and the proof checker holds 8192 as a
# number (2^26 as a literal would be a unary numeral to it).
#
# What is proved (proofs/crypto/poly1305/): every function below computes
# its value exactly as a natural number, or congruent mod p where limbs at
# 2^130 fold back; between blocks every limb has at most 27 bits (bnd.bend),
# which the final reduction relies on; and every Nat computed stays below
# the runtime's 2^48, for every key and message (sops.bend per function,
# safe.bend for mac, poly1305 and mac_aead).
#
# Constant time: every loop runs over public lengths and no branch depends
# on a limb; the final conditional subtraction of p is arithmetic (a limb
# times c plus a limb times 1 - c, for the carry bit c). Bend has no timing
# model, so this is a property of the code's shape, not a proved fact.

type F is Data:
  F{l0: Nat, l1: Nat, l2: Nat, l3: Nat, l4: Nat}

# The multiplier r = e + 2^13 o in 13-bit halves: e0..e4 and o0..o4, and
# f_i = 5 e_i, g_i = 5 o_i for the folded products.
type K is Data:
  K{e0: Nat, e1: Nat, e2: Nat, e3: Nat, e4: Nat, f1: Nat, f2: Nat, f3: Nat, f4: Nat,
    o0: Nat, o1: Nat, o2: Nat, o3: Nat, o4: Nat, g1: Nat, g2: Nat, g3: Nat, g4: Nat}

# x div 2^26 and x mod 2^26, as two steps of 2^13 (a division by a literal
# power of two compiles to a shift; 2^13 is the only radix the proofs meet
# as a literal).
def dw(x: Nat) -> Nat:
  Nat.div(Nat.div(x, 8192n), 8192n)

def mw(+x: Nat) -> Nat:
  Nat.add(Nat.mod(x, 8192n), Nat.mul(Nat.mod(Nat.div(x, 8192n), 8192n), 8192n))

def zero() -> F:
  F{0n, 0n, 0n, 0n, 0n}

# A byte of the byte convention (the low 8 bits of a U32).
def byte(+x: U32) -> Nat:
  U32.to_nat(U32.and(x, 255))

# 16 bytes x0..x15 (little-endian) plus pb at 2^128, as five radix-2^26
# limbs: bytes 3, 6 and 9 straddle a limb boundary and are split by
# mod/div 4, 16 and 64.
def load(x0: Nat, x1: Nat, x2: Nat, +x3: Nat, x4: Nat, x5: Nat, +x6: Nat, x7: Nat, x8: Nat, +x9: Nat, x10: Nat, x11: Nat, x12: Nat, x13: Nat, x14: Nat, x15: Nat, pb: Nat) -> F:
  F{Nat.add(x0, Nat.mul(Nat.add(x1, Nat.mul(Nat.add(x2, Nat.mul(Nat.mod(x3, 4n), 256n)), 256n)), 256n)),
    Nat.add(Nat.div(x3, 4n), Nat.mul(Nat.add(x4, Nat.mul(Nat.add(x5, Nat.mul(Nat.mod(x6, 16n), 256n)), 256n)), 64n)),
    Nat.add(Nat.div(x6, 16n), Nat.mul(Nat.add(x7, Nat.mul(Nat.add(x8, Nat.mul(Nat.mod(x9, 64n), 256n)), 256n)), 16n)),
    Nat.add(Nat.div(x9, 64n), Nat.mul(Nat.add(x10, Nat.mul(Nat.add(x11, Nat.mul(x12, 256n)), 256n)), 4n)),
    Nat.add(x13, Nat.mul(Nat.add(x14, Nat.mul(Nat.add(x15, Nat.mul(pb, 256n)), 256n)), 256n))}

# The schoolbook product of a0..a4 and r0..r4 with the limbs from w^5 on
# folded back (s_i = 5 r_i): column k is a0 r_k + a1 r_(k-1) + ... with
# r_(-j) read as s_(5-j).
def mul(+a0: Nat, +a1: Nat, +a2: Nat, +a3: Nat, +a4: Nat, +r0: Nat, +r1: Nat, +r2: Nat, +r3: Nat, +r4: Nat, +s1: Nat, +s2: Nat, +s3: Nat, +s4: Nat) -> F:
  F{Nat.add(Nat.mul(a0, r0), Nat.add(Nat.mul(a1, s4), Nat.add(Nat.mul(a2, s3), Nat.add(Nat.mul(a3, s2), Nat.mul(a4, s1))))),
    Nat.add(Nat.mul(a0, r1), Nat.add(Nat.mul(a1, r0), Nat.add(Nat.mul(a2, s4), Nat.add(Nat.mul(a3, s3), Nat.mul(a4, s2))))),
    Nat.add(Nat.mul(a0, r2), Nat.add(Nat.mul(a1, r1), Nat.add(Nat.mul(a2, r0), Nat.add(Nat.mul(a3, s4), Nat.mul(a4, s3))))),
    Nat.add(Nat.mul(a0, r3), Nat.add(Nat.mul(a1, r2), Nat.add(Nat.mul(a2, r1), Nat.add(Nat.mul(a3, r0), Nat.mul(a4, s4))))),
    Nat.add(Nat.mul(a0, r4), Nat.add(Nat.mul(a1, r3), Nat.add(Nat.mul(a2, r2), Nat.add(Nat.mul(a3, r1), Nat.mul(a4, r0)))))}

# d + 2^13 e (mod p) with small limbs: e_i = lo_i + w hi_i, 2^13 lo_i stays
# at limb i, 2^13 hi_i moves to limb i + 1 (limb 0 for i = 4, times 5).
def comb(d: F, e: F) -> F:
  match d e:
    case F{d0, d1, d2, d3, d4} F{+e0, +e1, +e2, +e3, +e4}:
      F{Nat.add(d0, Nat.add(Nat.mul(mw(e0), 8192n), Nat.mul(Nat.mul(dw(e4), 8192n), 5n))),
        Nat.add(d1, Nat.add(Nat.mul(mw(e1), 8192n), Nat.mul(dw(e0), 8192n))),
        Nat.add(d2, Nat.add(Nat.mul(mw(e2), 8192n), Nat.mul(dw(e1), 8192n))),
        Nat.add(d3, Nat.add(Nat.mul(mw(e3), 8192n), Nat.mul(dw(e2), 8192n))),
        Nat.add(d4, Nat.add(Nat.mul(mw(e4), 8192n), Nat.mul(dw(e3), 8192n)))}

# The carries of limbs 0..3 into the next limb, the carry out of limb 4
# folded onto limb 0 times 5 (w^5 = p + 5): congruent mod p, limbs 1..4
# below w and limb 0 below w + 5 (carry out of limb 4).
def top(z: F) -> F:
  match z:
    case F{+z0, z1, z2, z3, z4}:
      +y1 = Nat.add(z1, dw(z0))
      +y2 = Nat.add(z2, dw(y1))
      +y3 = Nat.add(z3, dw(y2))
      +y4 = Nat.add(z4, dw(y3))
      F{Nat.add(mw(z0), Nat.mul(dw(y4), 5n)), mw(y1), mw(y2), mw(y3), mw(y4)}

# Limb 0's carry into limb 1.
def fix(t: F) -> F:
  match t:
    case F{+u0, t1, t2, t3, t4}:
      F{mw(u0), Nat.add(t1, dw(u0)), t2, t3, t4}

# One carry pass: top, then fix.
def carry(z: F) -> F:
  fix(top(z))

# One Poly1305 block: (h + m) r, partially reduced mod p.
def block(+k: K, h: F, m: F) -> F:
  match k h m:
    case K{+e0, +e1, +e2, +e3, +e4, +f1, +f2, +f3, +f4, +o0, +o1, +o2, +o3, +o4, +g1, +g2, +g3, +g4} F{h0, h1, h2, h3, h4} F{m0, m1, m2, m3, m4}:
      +a0 = Nat.add(h0, m0)
      +a1 = Nat.add(h1, m1)
      +a2 = Nat.add(h2, m2)
      +a3 = Nat.add(h3, m3)
      +a4 = Nat.add(h4, m4)
      carry(comb(mul(a0, a1, a2, a3, a4, e0, e1, e2, e3, e4, f1, f2, f3, f4), mul(a0, a1, a2, a3, a4, o0, o1, o2, o3, o4, g1, g2, g3, g4)))

# The multiplier of the limbs of r.
def key(r: F) -> K:
  match r:
    case F{+r0, +r1, +r2, +r3, +r4}:
      +e1 = Nat.mod(r1, 8192n)
      +e2 = Nat.mod(r2, 8192n)
      +e3 = Nat.mod(r3, 8192n)
      +e4 = Nat.mod(r4, 8192n)
      +o1 = Nat.div(r1, 8192n)
      +o2 = Nat.div(r2, 8192n)
      +o3 = Nat.div(r3, 8192n)
      +o4 = Nat.div(r4, 8192n)
      K{Nat.mod(r0, 8192n), e1, e2, e3, e4, Nat.mul(e1, 5n), Nat.mul(e2, 5n), Nat.mul(e3, 5n), Nat.mul(e4, 5n),
        Nat.div(r0, 8192n), o1, o2, o3, o4, Nat.mul(o1, 5n), Nat.mul(o2, 5n), Nat.mul(o3, 5n), Nat.mul(o4, 5n)}

# ---- the tag ----

# x when c is 0, y when c is 1.
def pick(+c: Nat, x: Nat, y: Nat) -> Nat:
  Nat.add(Nat.mul(x, Nat.sub(1n, c)), Nat.mul(y, c))

# The low byte of x.
def by(+x: Nat) -> U32:
  U32.from_nat(Nat.mod(x, 256n))

def d8(x: Nat) -> Nat:
  Nat.div(x, 256n)

# The 16 low bytes of l0 + w l1 + w^2 l2 + w^3 l3 + w^4 l4, streamed: three
# bytes of l0, the 2 bits left plus 4 l1 give three more, the 4 bits left
# plus 16 l2 three more, the 6 bits left plus 64 l3 four, the rest plus l4
# the last three.
def bytes(+l0: Nat, l1: Nat, l2: Nat, l3: Nat, l4: Nat) -> List<&2, U32>:
  +a1 = d8(l0)
  +a2 = d8(a1)
  +c0 = Nat.add(d8(a2), Nat.mul(l1, 4n))
  +c1 = d8(c0)
  +c2 = d8(c1)
  +q0 = Nat.add(d8(c2), Nat.mul(l2, 16n))
  +q1 = d8(q0)
  +q2 = d8(q1)
  +t0 = Nat.add(d8(q2), Nat.mul(l3, 64n))
  +t1 = d8(t0)
  +t2 = d8(t1)
  +t3 = d8(t2)
  +u0 = Nat.add(d8(t3), l4)
  +u1 = d8(u0)
  [by(l0), by(a1), by(a2), by(c0), by(c1), by(c2), by(q0), by(q1), by(q2), by(t0), by(t1), by(t2), by(t3), by(u0), by(u1), by(d8(u1))]

# (h mod p + s) mod 2^128 as 16 bytes, for h below 2^130 + 64 (top brings
# an accumulator of 27-bit limbs there): g = h + 5 with its carries
# has c = 1 at 2^130 exactly when h >= p, and then its low 130 bits are
# h - p; the selected limbs plus s are carried and serialized.
def frz(h: F, s: F) -> List<&2, U32>:
  match h s:
    case F{+h0, +h1, +h2, +h3, +h4} F{s0, s1, s2, s3, s4}:
      +g0 = Nat.add(h0, 5n)
      +g1 = Nat.add(h1, dw(g0))
      +g2 = Nat.add(h2, dw(g1))
      +g3 = Nat.add(h3, dw(g2))
      +g4 = Nat.add(h4, dw(g3))
      +c = dw(g4)
      +t0 = Nat.add(pick(c, h0, mw(g0)), s0)
      +t1 = Nat.add(Nat.add(pick(c, h1, mw(g1)), s1), dw(t0))
      +t2 = Nat.add(Nat.add(pick(c, h2, mw(g2)), s2), dw(t1))
      +t3 = Nat.add(Nat.add(pick(c, h3, mw(g3)), s3), dw(t2))
      +t4 = Nat.add(Nat.add(pick(c, h4, mw(g4)), s4), dw(t3))
      bytes(mw(t0), mw(t1), mw(t2), mw(t3), t4)

# The tag bytes of an accumulator (limbs below 2^27) and s.
def fin(h: F, s: F) -> List<&2, U32>:
  frz(top(h), s)
