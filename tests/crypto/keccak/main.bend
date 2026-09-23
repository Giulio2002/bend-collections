import Base
import ../../../src/crypto/keccak/keccak.bend as K
import ../../../src/crypto/keccak/hex.bend as H

def fill(n: Nat, +i: U32, +seed: U32, a: Array<U32>) -> Array<U32>:
  match n:
    case 0n: a
    case 1n+p: fill(p,U32.inc(i),seed,Array.set(U32,a,i,U32.add(U32.mul(i,2654435761),seed)))

def show(r: Maybe<&1,Array<U32>>) -> String:
  match r:
    case None{}: "invalid"
    case Some{a}: H.hex(a)

def one(+n: Nat, +seed: U32, +depth: Nat) -> IO(Unit):
  a = fill(Nat.pow(2n,depth),0,seed,Array.new(U32,depth,0))
  IO.print(show(K.keccak256(a,n)))

def cases(n: Nat, +i: Nat) -> IO(Unit):
  match n:
    case 0n: IO.pure(Unit,Unit{})
    case 1n+p:
      do IO<Unit>:
        one(i,U32.from_nat(Nat.add(i,42n)),7n)
        cases(p,1n+i)

def main() -> IO(Unit):
  do IO<Unit>:
    cases(274n,0n)
    one(4096n,17,10n)
    one(65536n,33,14n)
    one(5n,1,0n)
    one(513n,1,7n)
