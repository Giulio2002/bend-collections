import Base
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../src/crypto/curve25519/x25519.bend as X
import ../curve25519/limbs.bend as LM
import ../../lib/u32.bend as U
import ../curve25519/prime.bend as PRM

# Helpers of the Ed25519 proof roots: p - 1, byte bounds, L, the facade's
# optional results.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def pp1(+one: Nat) -> Nat:
  PRM.pp_of(one)

def ok(+n: Nat, +a: List<&2, U32>, +h: {FS.bytes_ok(n, a) == True{} : Bool}) -> {LM.okb(n, a, 255n) == True{} : Bool}:
  LM.bytes_okb(n, a, h)

def valid_eq(+n: Nat, +xs: List<&2, U32>) -> {X.valid_bytes(n, xs) == FS.bytes_ok(n, xs) : Bool}:
  match n xs:
    case 0n Nil{}:
      {==}
    case 0n Con{y, yt}:
      {==}
    case 1n+m Nil{}:
      {==}
    case 1n+ +m Con{+y, +yt}:
      +e1 = U.is_lt_nat(y, 256)
      +e2 = valid_eq(m, yt)
      Equal.trans(Bool, Bool.and(U32.is_lt(y, 256), X.valid_bytes(m, yt)), Bool.and(Nat.is_lt(v(y), 256n), X.valid_bytes(m, yt)), Bool.and(Nat.is_lt(v(y), 256n), FS.bytes_ok(m, yt)), Equal.cong(Bool, Bool, z => Bool.and(z, X.valid_bytes(m, yt)), U32.is_lt(y, 256), Nat.is_lt(v(y), 256n), e1), Equal.cong(Bool, Bool, z => Bool.and(Nat.is_lt(v(y), 256n), z), X.valid_bytes(m, yt), FS.bytes_ok(m, yt), e2))

def valid_ok(+n: Nat, +xs: List<&2, U32>, +h: {FS.bytes_ok(n, xs) == True{} : Bool}) -> {X.valid_bytes(n, xs) == True{} : Bool}:
  Equal.trans(Bool, X.valid_bytes(n, xs), FS.bytes_ok(n, xs), True{}, valid_eq(n, xs), h)
