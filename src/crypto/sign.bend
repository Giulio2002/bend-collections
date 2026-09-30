import Base
import ./curve25519/x25519.bend as X
import ./ed25519/ed25519.bend as E

# Signatures: Ed25519 (RFC 8032). Keys and signatures are byte lists (U32
# values below 256) of the RFC lengths; malformed ones are rejected as
# values.
#
#   generate_keypair(seed)   secret = the 32-byte seed, public = [s]B
#   generate_keypair_os()    the same from 32 bytes of IO.random_u32
#   sign(sk, msg)            the 64-byte signature, None for a bad key
#   verify(pk, msg, sig)     True iff sig is valid (cofactorless check,
#                            non-canonical S >= L rejected)
#
# Correctness against RFC 8032 is proved (spec/crypto/sign.bend,
# proofs/crypto/ed25519). Scalar multiplication and scalar arithmetic are
# branch-free on secrets; Bend has no timing model, so constant time is by
# construction, not proved.

type Keypair is Data:
  Keypair{secret: List<&2, U32>, public: List<&2, U32>}

def keypair_if(+seed: List<&2, U32>, ok: Bool) -> Maybe<&2, Keypair>:
  match ok:
    case True{}:
      Some{Keypair{seed, E.public_key(seed)}}
    case False{}:
      None{}

def generate_keypair(+seed: List<&2, U32>) -> Maybe<&2, Keypair>:
  keypair_if(seed, X.valid_bytes(32n, seed))

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

def sign_if(+sk: List<&2, U32>, +msg: List<&2, U32>, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{E.sign_raw(sk, msg)}
    case False{}:
      None{}

def sign(+sk: List<&2, U32>, +msg: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  sign_if(sk, msg, X.valid_bytes(32n, sk))

def verify_if(+pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>, ok: Bool) -> Bool:
  match ok:
    case True{}:
      E.verify_raw(pk, msg, sig)
    case False{}:
      False{}

def verify(+pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>) -> Bool:
  verify_if(pk, msg, sig, Bool.and(X.valid_bytes(32n, pk), X.valid_bytes(64n, sig)))
