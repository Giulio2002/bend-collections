import Base
import ./secp256k1/ecdsa.bend as E
import ./secp256k1/schnorr.bend as Sch

# secp256k1 signatures: ECDSA (SEC 1 v2 section 4.1) with RFC 6979
# deterministic nonces and low-S output, public key recovery (Ethereum's
# ecrecover), Ethereum addresses, and BIP-340 Schnorr signatures.
#
# Byte convention: bytes are U32 values below 256; keys, hashes and
# signatures are byte lists of their standard lengths, and a malformed one
# is rejected as a value (None / False), never a crash.
#
#   generate_keypair(seed)        secret = the 32-byte seed if 1 <= seed < n,
#                                 public = its 33-byte compressed SEC 1 key
#   generate_keypair_os()         the same from IO.random_u32 (drawn again
#                                 while the seed is not a valid key)
#   public_key(sk, compressed)    33-byte (02/03) or 65-byte (04) SEC 1 key
#   sign(sk, hash32)              Signature{r, s, v}: RFC 6979 nonce, low s,
#                                 v the recovery id 0..3
#   sign_compact(sk, hash32)      r || s || v, 65 bytes
#   verify(pk, hash32, sig64)     SEC 1 verification of r || s (high s allowed)
#   verify_strict(pk, h, sig64)   the same, high s rejected (BIP 146 LOW_S)
#   recover(hash32, sig65)        the 65-byte public key of r || s || id
#   eth_address(pk65)             the 20-byte Ethereum address
#   ecrecover(input)              Ethereum's precompile 0x01: 128 bytes
#                                 hash || v || r || s -> the address word
#   schnorr_pubkey(sk)            BIP-340 32-byte x-only public key
#   schnorr_sign(sk, msg, aux32)  BIP-340 64-byte signature
#   schnorr_verify(pk32, msg, sig64)
#
# Every function is proved equal to its specification
# (spec/crypto/secp256k1/, transcribed from SEC 1/SEC 2, RFC 6979 and
# BIP-340) for every input: proofs/crypto/secp256k1/, clauses in
# docs/CRYPTO_CONTRACTS.md. Scalar multiplication by secrets and all
# secret-dependent arithmetic are branch-free (masked selection over
# complete formulas); Bend has no timing model, so constant time is by
# construction, not proved.

type Keypair is Data:
  Keypair{secret: List<&2, U32>, public: List<&2, U32>}

def keypair_of(+seed: List<&2, U32>, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Keypair>:
  match m:
    case None{}: None{}
    case Some{pk}: Some{Keypair{seed, pk}}

def generate_keypair(+seed: List<&2, U32>) -> Maybe<&2, Keypair>:
  keypair_of(seed, E.public_key(seed, True{}))

def word_bytes(+w: U32, rest: List<&2, U32>) -> List<&2, U32>:
  U32.and(w, 255) <> U32.and(U32.shrn(w, 8n), 255) <> U32.and(U32.shrn(w, 16n), 255) <> U32.shrn(w, 24n) <> rest

def random_bytes(n: Nat, acc: List<&2, U32>) -> IO(List<&2, U32>):
  match n:
    case 0n:
      IO.pure(List<&2, U32>, acc)
    case 1n+m:
      do IO<List<&2, U32>>:
        w : U32 <- IO.try(U32, IO.random_u32())
        rest : List<&2, U32> <- random_bytes(m, acc)
        return word_bytes(w, rest)

def os_retry(fuel: Nat, m: Maybe<&2, Keypair>) -> IO(Maybe<&2, Keypair>):
  match fuel m:
    case _ Some{kp}:
      IO.pure(Maybe<&2, Keypair>, Some{kp})
    case 0n None{}:
      IO.pure(Maybe<&2, Keypair>, None{})
    case 1n+f None{}:
      do IO<Maybe<&2, Keypair>>:
        seed : List<&2, U32> <- random_bytes(8n, Nil{})
        kp : Maybe<&2, Keypair> <- os_retry(f, generate_keypair(seed))
        return kp

# 32 bytes of the operating system's random source (getrandom, arc4random,
# crypto.getRandomValues) as the seed; a seed outside [1, n - 1] (chance
# 2^-128) is drawn again, up to 8 times
def generate_keypair_os() -> IO(Maybe<&2, Keypair>):
  os_retry(8n, None{})

def public_key(+sk: List<&2, U32>, compressed: Bool) -> Maybe<&2, List<&2, U32>>:
  E.public_key(sk, compressed)

def sign(+sk: List<&2, U32>, +hash: List<&2, U32>) -> Maybe<&2, E.Signature>:
  E.sign(sk, hash)

def compact(m: Maybe<&2, E.Signature>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}: None{}
    case Some{E.Signature{r, s, v}}: Some{List.append(&2, U32, r, List.append(&2, U32, s, [v]))}

def sign_compact(+sk: List<&2, U32>, +hash: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  compact(E.sign(sk, hash))

def verify(+pk: List<&2, U32>, +hash: List<&2, U32>, +sig: List<&2, U32>) -> Bool:
  E.verify(pk, hash, sig)

def verify_strict(+pk: List<&2, U32>, +hash: List<&2, U32>, +sig: List<&2, U32>) -> Bool:
  E.verify_strict(pk, hash, sig)

def recover(+hash: List<&2, U32>, +sig: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  E.recover(hash, sig)

def eth_address(+pk: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  E.eth_address(pk)

def ecrecover(input: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  E.ecrecover(input)

def schnorr_pubkey(+sk: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  Sch.pubkey(sk)

def schnorr_sign(+sk: List<&2, U32>, +msg: List<&2, U32>, +aux: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  Sch.sign(sk, msg, aux)

def schnorr_verify(+pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>) -> Bool:
  Sch.verify(pk, msg, sig)
