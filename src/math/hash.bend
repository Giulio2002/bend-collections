import Base

# 32-bit hashing primitives for open-addressing tables.
#
#   mix(h, c)          one step of a multiply-xor string hash: (h ^ c) * phi32
#   bucket(w, mask)    the home bucket of check word w in a table of mask + 1
#                      buckets: Fibonacci hashing, then the high half folded
#                      into the low bits before masking

def phi32() -> U32:
  2654435761

def mix(+h: U32, +c: U32) -> U32:
  U32.mul(U32.xor(h, c), phi32())

def fold(+x: U32, +mask: U32) -> U32:
  U32.and(U32.xor(x, U32.shrn(x, 16n)), mask)

def bucket(+w: U32, +mask: U32) -> U32:
  fold(U32.mul(w, phi32()), mask)
