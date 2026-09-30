import Base
import ./types.bend as T
import ./core.bend as Core
import ./stream.bend as Stream

# SHA-512 (FIPS 180-4). Bytes are U32 values, each < 256; the digest is the
# 64 bytes of H0..H7, most significant first. Proved equal to the executable
# specification spec/crypto/sha512.bend for every input:
# proofs/crypto/sha512/laws.bend. Streaming: each byte is read once
# (src/crypto/sha512/stream.bend).
def sha512(bytes: List<&2, U32>) -> List<&2, U32>:
  Stream.hash(bytes)

def ascii(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      c <> ascii(t)

def hex_digit_if(x: U32, small: Bool) -> Char:
  match small:
    case True{}:
      Chr{(48 + x : U32)}
    case False{}:
      Chr{(87 + x : U32)}

def hex_digit(+x: U32) -> Char:
  hex_digit_if(x, U32.is_lt(x, 10))

# Lowercase hex of a byte list.
def hex(bytes: List<&2, U32>) -> String:
  match bytes:
    case Nil{}:
      ""
    case +b <> t:
      SCon{hex_digit(U32.and(U32.shrn(b, 4n), 15)), SCon{hex_digit(U32.and(b, 15)), hex(t)}}
