import Base

# A chaining value: eight 32-bit words.
type CV is Data:
  CV{h0: U32, h1: U32, h2: U32, h3: U32, h4: U32, h5: U32, h6: U32, h7: U32}

# A 64-byte message block: sixteen little-endian 32-bit words.
type Block is Data:
  B{m0: U32, m1: U32, m2: U32, m3: U32, m4: U32, m5: U32, m6: U32, m7: U32, m8: U32, m9: U32, m10: U32, m11: U32, m12: U32, m13: U32, m14: U32, m15: U32}

# The compression state: sixteen 32-bit words.
type St is Data:
  St{v0: U32, v1: U32, v2: U32, v3: U32, v4: U32, v5: U32, v6: U32, v7: U32, v8: U32, v9: U32, v10: U32, v11: U32, v12: U32, v13: U32, v14: U32, v15: U32}

# A node whose compression is still pending: its input chaining value, block,
# counter, block length and flags. The root node is finalized with ROOT.
type Out is Data:
  Out{cv: CV, block: Block, counter: U32, len: U32, flags: U32}
