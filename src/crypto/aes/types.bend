import Base

# Shared representation only; this module contains no algorithm or operations.
# FIPS 197 section 3: a word (Quad) is four bytes, and the 4x4 state is four columns,
# column c holding the bytes s[0,c], s[1,c], s[2,c], s[3,c]. A byte is a U32.
type Quad is Data:
  W{b0: U32, b1: U32, b2: U32, b3: U32}

type State is Data:
  S{c0: Quad, c1: Quad, c2: Quad, c3: Quad}
