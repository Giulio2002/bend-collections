import Base
import ./core.bend as Core

# The core refinement theorem quantifies over every constant table.
# Instantiate the verified core with the FIPS 180-4 constants.
def constants() -> List<&2, U32>:
  [1116352408, 1899447441, 3049323471, 3921009573,
   961987163, 1508970993, 2453635748, 2870763221,
   3624381080, 310598401, 607225278, 1426881987,
   1925078388, 2162078206, 2614888103, 3248222580,
   3835390401, 4022224774, 264347078, 604807628,
   770255983, 1249150122, 1555081692, 1996064986,
   2554220882, 2821834349, 2952996808, 3210313671,
   3336571891, 3584528711, 113926993, 338241895,
   666307205, 773529912, 1294757372, 1396182291,
   1695183700, 1986661051, 2177026350, 2456956037,
   2730485921, 2820302411, 3259730800, 3345764771,
   3516065817, 3600352804, 4094571909, 275423344,
   430227734, 506948616, 659060556, 883997877,
   958139571, 1322822218, 1537002063, 1747873779,
   1955562222, 2024104815, 2227730452, 2361852424,
   2428436474, 2756734187, 3204031479, 3329325298]

def sha256(bytes: List<&2, U32>) -> List<&2, U32>:
  Core.sha256(bytes)

def ascii(s: String) -> List<&2, U32>:
  Core.ascii(s)

def hex(ws: List<&2, U32>) -> String:
  Core.hex(ws)

# Big-endian octets, represented as U32 values in 0..255.
def digest_bytes(ws: List<&2, U32>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      Nil{}
    case +w <> tail:
      U32.and(U32.shrn(w, 24n), 255) <>
      U32.and(U32.shrn(w, 16n), 255) <>
      U32.and(U32.shrn(w, 8n), 255) <>
      U32.and(w, 255) <> digest_bytes(tail)

def sha256_bytes(bytes: List<&2, U32>) -> List<&2, U32>:
  digest_bytes(sha256(bytes))
