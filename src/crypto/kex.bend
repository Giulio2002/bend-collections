import Base
import ./curve25519/x25519.bend as X
import ./curve25519/field.bend as F

# Key exchange: X25519 (RFC 7748). Keys and secrets are 32-byte lists of U32
# values below 256; malformed input is rejected as a value (None).
#
#   generate_keypair(seed)   the secret is the 32-byte seed (clamped inside
#                            X25519), the public key X25519(secret, 9)
#   generate_keypair_os()    the same from 32 bytes of IO.random_u32
#   shared_secret(sk, pk)    X25519(sk, pk); None when either input is
#                            malformed or the result is all zero (a
#                            small-order peer key, RFC 7748 section 6.1)
#
# Correctness against RFC 7748 is proved (spec/crypto/kex.bend,
# proofs/crypto/curve25519). The ladder is branch-free on secrets; Bend
# has no timing model, so constant time is by construction, not proved.

type Keypair is Data:
  Keypair{secret: List<&2, U32>, public: List<&2, U32>}

def keypair_of(+seed: List<&2, U32>, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Keypair>:
  match m:
    case None{}:
      None{}
    case Some{pk}:
      Some{Keypair{seed, pk}}

def generate_keypair(+seed: List<&2, U32>) -> Maybe<&2, Keypair>:
  keypair_of(seed, X.x25519(seed, X.base()))

# 32 bytes from 8 words, little-endian
def word_bytes(+w: U32, rest: List<&2, U32>) -> List<&2, U32>:
  Con{U32.and(w, 255), Con{U32.and(U32.shrn(w, 8n), 255), Con{U32.and(U32.shrn(w, 16n), 255), Con{U32.shrn(w, 24n), rest}}}}

def random_bytes(n: Nat, acc: List<&2, U32>) -> IO(List<&2, U32>):
  match n:
    case 0n:
      IO.pure(List<&2, U32>, acc)
    case 1n+m:
      do IO<List<&2, U32>>:
        w : U32 <- IO.try(U32, IO.random_u32())
        rest : List<&2, U32> <- random_bytes(m, acc)
        return word_bytes(w, rest)

def generate_keypair_os() -> IO(Maybe<&2, Keypair>):
  do IO<Maybe<&2, Keypair>>:
    seed : List<&2, U32> <- random_bytes(8n, Nil{})
    return generate_keypair(seed)

def nonzero(ss: List<&2, U32>, z: Bool) -> Maybe<&2, List<&2, U32>>:
  match z:
    case True{}:
      None{}
    case False{}:
      Some{ss}

def shared_of(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{+ss}:
      nonzero(ss, U32.is_eq(F.sum_all(ss, 0), 0))

def shared_secret(+sk: List<&2, U32>, +pk: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  shared_of(X.x25519(sk, pk))
