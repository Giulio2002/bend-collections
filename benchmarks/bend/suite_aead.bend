import Base
import ./suite.bend as S
import ../../src/crypto/aead.bend as A

# The AEAD facade (src/crypto/aead.bend). BENCH_ALG: 0 ChaCha20-Poly1305,
# 1 XChaCha20-Poly1305, 2 AES-128-GCM, 3 AES-256-GCM; fixed key and nonce,
# empty associated data. BENCH_PARAM 0: encrypt every message (output
# ciphertext || tag); 1: decrypt ciphertexts sealed before the timed region
# (output the plaintext).

def alg_of(+a: Nat) -> A.Alg:
  match a:
    case 0n:
      A.CHACHA20_POLY1305{}
    case 1n+p:
      match p:
        case 0n:
          A.XCHACHA20_POLY1305{}
        case 1n+q:
          match q:
            case 0n:
              A.AES_128_GCM{}
            case 1n+r:
              A.AES_256_GCM{}

def seal(xs: List<&2, List<&2, U32>>, +alg: A.Alg, +key: List<&2, U32>, +nonce: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      seal(t, alg, key, nonce, S.unwrap(A.encrypt(alg, key, nonce, [], h)) <> acc)

def open(xs: List<&2, List<&2, U32>>, +alg: A.Alg, +key: List<&2, U32>, +nonce: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      open(t, alg, key, nonce, S.unwrap(A.decrypt(alg, key, nonce, [], h)) <> acc)

def go(+mode: Nat, inputs: List<&2, List<&2, U32>>, +alg: A.Alg, +key: List<&2, U32>, +nonce: List<&2, U32>) -> IO(Unit):
  match mode:
    case 0n:
      do IO<Unit>:
        start : Nat <- IO.now()
        outs : List<&2, List<&2, U32>> = seal(inputs, alg, key, nonce, Nil{})
        stop : Nat <- IO.now()
        S.report(start, stop, outs)
    case 1n+p:
      do IO<Unit>:
        sealed : List<&2, List<&2, U32>> = List.reverse(&2, List<&2, U32>, seal(inputs, alg, key, nonce, Nil{}))
        start : Nat <- IO.now()
        outs : List<&2, List<&2, U32>> = open(sealed, alg, key, nonce, Nil{})
        stop : Nat <- IO.now()
        S.report(start, stop, outs)

def main() -> IO(Unit):
  do IO<Unit>:
    inputs : List<&2, List<&2, U32>> <- S.messages()
    +a : Nat <- S.env_nat("BENCH_ALG")
    +mode : Nat <- S.env_nat("BENCH_PARAM")
    +alg : A.Alg = alg_of(a)
    +key : List<&2, U32> = S.pattern(A.key_size(alg), 7, 1)
    +nonce : List<&2, U32> = S.pattern(A.nonce_size(alg), 3, 5)
    go(mode, inputs, alg, key, nonce)
