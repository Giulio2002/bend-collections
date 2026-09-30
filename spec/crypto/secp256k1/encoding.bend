import Base
import ./field.bend as FS
import ./curve.bend as CS
import ./group.bend as GS

# What a decoded public key is (for the clauses of
# proofs/crypto/secp256k1/laws_encoding.bend): CS.decode answers None or a
# point of the group in normal form, (x : y : 1) with x and y below p.
# Nothing here is used by the implementation.

def normal(+p: Nat, a: CS.SPoint) -> Bool:
  match a:
    case CS.SPoint{x, y, z}:
      Bool.and(Nat.is_lt(x, p), Bool.and(Nat.is_lt(y, p), Nat.is_eq(z, 1n)))

def decoded_ok(+p: Nat, m: Maybe<&2, CS.SPoint>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+a}:
      Bool.and(GS.valid(p, a), normal(p, a))
