import Base
import ../../src/crypto/blake/blake3/blake3.bend as K
import ../../tests/crypto/blake/blake3/main.bend as V

# BLAKE3 benchmark driver; the same protocol as keccak256.bend. The input is
# 2^BLAKE_DEPTH words w_i = i*2654435761 + 42, hashed BLAKE_COUNT times over
# its first BLAKE_SIZE bytes (each hash gets a fresh clone of the array).
# Prints BENCH_MS=<ms>, then the sum mod 2^32 of the first little-endian digest
# word over all hashes.

def fold(r: Maybe<&1,Array<U32>>) -> U32:
  match r:
    case None{}: 0
    case Some{a}: Pair.snd(Array<U32>,U32,Array.get(U32,a,0))

def hashes(n: Nat, +size: Nat, pair: Array<U32> & Array<U32>, acc: U32) -> U32:
  match n pair:
    case 0n Tuple{a,b}: acc
    case 1n+p Tuple{a,b}: hashes(p,size,Array.clone(U32,a),U32.add(acc,fold(K.blake3(b,size))))

def number(r: Maybe<&2,Nat>) -> Nat:
  match r:
    case None{}: 0n
    case Some{n}: n

def main() -> IO(Unit):
  do IO<Unit>:
    st : String <- IO.try(String,IO.get_env("BLAKE_SIZE"))
    dt : String <- IO.try(String,IO.get_env("BLAKE_DEPTH"))
    nt : String <- IO.try(String,IO.get_env("BLAKE_COUNT"))
    +size : Nat = number(Nat.read(st))
    +depth : Nat = number(Nat.read(dt))
    +count : Nat = number(Nat.read(nt))
    a : Array<U32> = V.fill(Nat.pow(2n,depth),0,42,Array.new(U32,depth,0))
    pair : Array<U32> & Array<U32> = Array.clone(U32,a)
    start : Nat <- IO.now()
    result : U32 = hashes(count,size,pair,0)
    stop : Nat <- IO.now()
    IO.print("BENCH_MS=" ++ Nat.show(Nat.sub(stop,start)))
    IO.print(U32.show(result))
