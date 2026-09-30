import Base

# Shared representation only; this module contains no algorithm or operations.

# A 64-bit word as its two 32-bit halves, most significant first.
type Lane is Data:
  W{hi: U32, lo: U32}

# The working variables a..h (and the chaining value H0..H7).
type State is Data:
  H{a: Lane, b: Lane, c: Lane, d: Lane, e: Lane, f: Lane, g: Lane, h: Lane}
