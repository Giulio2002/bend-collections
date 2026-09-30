import Base
import ./suite.bend as S
import ../../src/crypto/hash.bend as H

# The incremental Hasher of src/crypto/hash.bend against the one-shot
# functions. BENCH_ALGO: 0 SHA-256, 1 SHA-512, 2 SHA3-256. BENCH_PARAM: 0
# hashes each message with the one-shot function; k > 0 feeds it to a Hasher
# in k-byte chunks (cut before the timed region) and takes the digest.

def fresh(+algo: Nat) -> H.Hasher:
  match algo:
    case 0n:
      H.new_sha256()
    case 1n+p:
      match p:
        case 0n:
          H.new_sha512()
        case 1n+q:
          H.new_sha3_256()

def oneshot(+algo: Nat, bytes: List<&2, U32>) -> List<&2, U32>:
  match algo:
    case 0n:
      H.sha256(bytes)
    case 1n+p:
      match p:
        case 0n:
          H.sha512(bytes)
        case 1n+q:
          H.sha3_256(bytes)

def hash(+chunk: Nat, +algo: Nat, parts: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match chunk parts:
    case 0n Nil{}:
      []
    case 0n h <> t:
      oneshot(algo, h)
    case 1n+c _:
      H.digest(H.update_all(fresh(algo), parts))

def cut(xs: List<&2, List<&2, U32>>, +chunk: Nat, acc: List<&2, List<&2, List<&2, U32>>>) -> List<&2, List<&2, List<&2, U32>>>:
  match xs chunk:
    case Nil{} _:
      List.reverse(&2, List<&2, List<&2, U32>>, acc)
    case h <> t 0n:
      cut(t, chunk, [h] <> acc)
    case h <> t 1n+c:
      cut(t, chunk, S.chunks(h, chunk, chunk, Nil{}, Nil{}) <> acc)

def run(xs: List<&2, List<&2, List<&2, U32>>>, +chunk: Nat, +algo: Nat, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      run(t, chunk, algo, hash(chunk, algo, h) <> acc)

def main() -> IO(Unit):
  do IO<Unit>:
    msgs : List<&2, List<&2, U32>> <- S.messages()
    +chunk : Nat <- S.env_nat("BENCH_PARAM")
    +algo : Nat <- S.env_nat("BENCH_ALGO")
    inputs : List<&2, List<&2, List<&2, U32>>> = cut(msgs, chunk, Nil{})
    start : Nat <- IO.now()
    outs : List<&2, List<&2, U32>> = run(inputs, chunk, algo, Nil{})
    stop : Nat <- IO.now()
    S.report(start, stop, outs)
