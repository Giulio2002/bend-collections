import Base
import ../u64.bend as W
import ../w64.bend as X

# PCG: Go's math/rand/v2.PCG, bit for bit: a 128-bit linear congruential
# generator (O'Neill's PCG family) with the DXSM ("double xorshift
# multiply") output function.
#
#   new(seed1, seed2)  the state hi:lo = seed1:seed2 (Go's NewPCG)
#   next(p)            the next 64-bit output and the advanced generator
#                      (Go's (*PCG).Uint64); the Source interface of rand.bend
#
# One step is state = state * MUL + INC (mod 2^128) with Go's constants
# MUL = mulHi:mulLo, INC = incHi:incLo; the output is DXSM of the new state:
# hi ^= hi >> 32; hi *= 0xda942042e4dd58b5; hi ^= hi >> 48; hi *= lo | 1.
# The 64-bit words are src/math/u64.bend's two-limb U64 with the proved
# arithmetic of src/math/w64.bend.
#
# Proved equal to spec/math/random/pcg.bend (the step and the output on
# naturals) for every state (proofs/math/random/pcg.bend); tested against
# Go's vectors (tools/check_random.py). PCG is not a cryptographic generator:
# its state follows from a few outputs.

type PCG is Data:
  P{hi: W.U64, lo: W.U64}

def new(+seed1: W.U64, +seed2: W.U64) -> PCG:
  P{seed1, seed2}

# 2549297995355413924, 4865540595714422341
def mul_hi() -> W.U64:
  W.U64{533093796, 593554693}

def mul_lo() -> W.U64:
  W.U64{2681009733, 1132846948}

# 6364136223846793005, 1442695040888963407
def inc_hi() -> W.U64:
  W.U64{1284865837, 1481765933}

def inc_lo() -> W.U64:
  W.U64{4150755663, 335903614}

# 0xda942042e4dd58b5
def cheap_mul() -> W.U64:
  W.U64{3839711413, 3667140674}

def xor64(+a: W.U64, +b: W.U64) -> W.U64:
  W.U64{U32.xor(X.lo(a), X.lo(b)), U32.xor(X.hi(a), X.hi(b))}

# the new state from the product's low word l and high word h
def step_fin(+ih: W.U64, +il: W.U64, +l: W.U64, +h: W.U64) -> PCG:
  P{X.add(X.add(h, ih), W.U64{X.b32(X.add_over(l, il)), 0}), X.add(l, il)}

def step_mul(+mh: W.U64, +ml: W.U64, +ih: W.U64, +il: W.U64, +hi: W.U64, +lo: W.U64, p: W.U64 & W.U64) -> PCG:
  (+l, +h) = p
  step_fin(ih, il, l, X.add(h, X.add(X.mul(hi, ml), X.mul(lo, mh))))

# state * (mh:ml) + (ih:il) mod 2^128 (Go's (*PCG).next with its constants
# as parameters)
def step_with(+mh: W.U64, +ml: W.U64, +ih: W.U64, +il: W.U64, p: PCG) -> PCG:
  match p:
    case P{+hi, +lo}:
      step_mul(mh, ml, ih, il, hi, lo, X.mul128(lo, ml))

def step(p: PCG) -> PCG:
  step_with(mul_hi(), mul_lo(), inc_hi(), inc_lo(), p)

def dxsm2(+h: W.U64, +lo: W.U64) -> W.U64:
  X.mul(xor64(h, X.shr(h, 48n)), W.U64{U32.or(X.lo(lo), 1), X.hi(lo)})

# the DXSM output of a state hi:lo with the multiplier cm
def dxsm_with(+cm: W.U64, +hi: W.U64, +lo: W.U64) -> W.U64:
  dxsm2(X.mul(xor64(hi, X.shr(hi, 32n)), cm), lo)

def out(+p: PCG) -> W.U64 & PCG:
  match p:
    case P{+hi, +lo}:
      (dxsm_with(cheap_mul(), hi, lo), P{hi, lo})

def next(p: PCG) -> W.U64 & PCG:
  out(step(p))
