import Base
import ./suite.bend as S
import ../../src/crypto/argon2/argon2.bend as A

# Argon2id (src/crypto/argon2/argon2.bend, RFC 9106): every 16-byte message
# is a password; fixed 16-byte salt (pattern(16, 11, 7)), no key or
# associated data, one lane, a 32-byte tag. BENCH_PARAM 0: m = 64 KiB, t = 3;
# 1: m = 19456 KiB (OWASP), t = 2. C: the official P-H-C reference (ref.c).

def passes(+param: Nat) -> Nat:
  match param:
    case 0n:
      3n
    case 1n+p:
      2n

def memory(+param: Nat) -> Nat:
  match param:
    case 0n:
      64n
    case 1n+p:
      19456n

def run(xs: List<&2, List<&2, U32>>, +salt: List<&2, U32>, +t: Nat, +m: Nat, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case h <> r:
      run(r, salt, t, m, S.unwrap(A.argon2id(h, salt, Nil{}, Nil{}, t, m, 1n, 32n)) <> acc)

def main() -> IO(Unit):
  do IO<Unit>:
    inputs : List<&2, List<&2, U32>> <- S.messages()
    +param : Nat <- S.env_nat("BENCH_PARAM")
    +salt : List<&2, U32> = S.pattern(16n, 11, 7)
    +t : Nat = passes(param)
    +m : Nat = memory(param)
    start : Nat <- IO.now()
    outs : List<&2, List<&2, U32>> = run(inputs, salt, t, m, Nil{})
    stop : Nat <- IO.now()
    S.report(start, stop, outs)
