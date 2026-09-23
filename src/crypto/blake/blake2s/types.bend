import Base

# The chaining value h[0..7] of RFC 7693.
type State is Data:
  H{h0: U32, h1: U32, h2: U32, h3: U32, h4: U32, h5: U32, h6: U32, h7: U32}

# The local work vector v[0..15] of the compression function F.
type Vector is Data:
  V{v0: U32, v1: U32, v2: U32, v3: U32, v4: U32, v5: U32, v6: U32, v7: U32, v8: U32, v9: U32, v10: U32, v11: U32, v12: U32, v13: U32, v14: U32, v15: U32}
