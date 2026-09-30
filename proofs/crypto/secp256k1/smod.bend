import Base
import ../../../src/crypto/secp256k1/limbs.bend as L
import ./fmod.bend as M

# The list models of the scalar records of src/crypto/secp256k1/se.bend:
# limbs.bend's reduction (fold, rounds, canon) with 32-bit limb products
# (fmod.convu) and an arithmetic selection of 32-bit products (fmod.selu).
# sval.bend shows they are limbs.bend's functions on 16-bit limbs.

# lo + c hi for the first 16 limbs lo and the rest hi (L.fold)
def foldu(+c: List<&2, Nat>, +xs: List<&2, Nat>) -> List<&2, Nat>:
  L.add(L.take(16n, xs), M.convu(L.drop(16n, xs), c))

# (L.rounds)
def roundsu(k: Nat, +c: List<&2, Nat>, xs: List<&2, Nat>) -> List<&2, Nat>:
  match k:
    case 0n: xs
    case 1n+j: roundsu(j, c, L.carry(32n, foldu(c, xs), 0n))

# (L.canon)
def canonu(+c: List<&2, Nat>, +t: List<&2, Nat>) -> List<&2, Nat>:
  +u = L.carry(32n, L.add(t, c), 0n)
  M.selu(L.horner(L.drop(16n, u)), L.take(16n, u), t)

# (L.reduce)
def redu(+c: List<&2, Nat>, k: Nat, +xs: List<&2, Nat>) -> List<&2, Nat>:
  canonu(c, L.take(16n, roundsu(k, c, L.carry(32n, xs, 0n))))
