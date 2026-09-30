import Base
import ./sha/sha256.bend as SHA256
import ./sha/stream.bend as N256
import ./sha512/stream.bend as N512
import ./sha3/stream.bend as N3

# Hash functions: one-shot and incremental.
#
#   sha256(bytes), sha512(bytes), sha3_256(bytes)       the digest (32, 64, 32 bytes)
#   new_sha256(), new_sha512(), new_sha3_256()          an empty Hasher
#   update(h, bytes)                                    h with bytes appended
#   update_all(h, chunks)                               update with each chunk in turn
#   digest(h)                                           the digest of everything appended
#
# Bytes are U32 values, each < 256 (List<&2, U32>). A Hasher is a stream
# state (src/crypto/{sha,sha512,sha3}/stream.bend): the chaining value, the
# words read but not yet compressed, the bytes of an unfinished word and the
# number of bytes compressed. update reads each new byte once and compresses
# every block it completes; digest pads what is left with the total length.
# Proved (proofs/crypto/hash/laws.bend): each one-shot function equals its
# executable specification, and for every list of chunks,
# digest(update_all(new_X(), chunks)) == X(concat(chunks)).
# Hashers are values: update returns a new one, the old one is unchanged.

type Hasher is Data:
  Sha256H{st: N256.St}
  Sha512H{st: N512.St}
  Sha3H{st: N3.St}

# SHA-256 (FIPS 180-4), 32 bytes.
def sha256(bytes: List<&2, U32>) -> List<&2, U32>:
  SHA256.sha256_bytes(bytes)

# SHA-512 (FIPS 180-4), 64 bytes.
def sha512(bytes: List<&2, U32>) -> List<&2, U32>:
  N512.hash(bytes)

# SHA3-256 (FIPS 202), 32 bytes.
def sha3_256(bytes: List<&2, U32>) -> List<&2, U32>:
  N3.hash(bytes)

def new_sha256() -> Hasher:
  Sha256H{N256.new()}

def new_sha512() -> Hasher:
  Sha512H{N512.new()}

def new_sha3_256() -> Hasher:
  Sha3H{N3.new()}

def update(h: Hasher, bytes: List<&2, U32>) -> Hasher:
  match h:
    case Sha256H{st}:
      Sha256H{N256.update(st, bytes, 48n)}
    case Sha512H{st}:
      Sha512H{N512.update(st, bytes, 64n)}
    case Sha3H{st}:
      Sha3H{N3.update(st, bytes, 24n)}

def fold(chunks: List<&2, List<&2, U32>>, h: Hasher) -> Hasher:
  match chunks:
    case Nil{}:
      h
    case c <> rest:
      fold(rest, update(h, c))

def update_all(h: Hasher, chunks: List<&2, List<&2, U32>>) -> Hasher:
  fold(chunks, h)

def digest(h: Hasher) -> List<&2, U32>:
  match h:
    case Sha256H{st}:
      N256.finish(st, 48n)
    case Sha512H{st}:
      N512.finish(st, 64n)
    case Sha3H{st}:
      N3.finish(st, 24n)
