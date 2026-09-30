import Base
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/ed25519/scalar.bend as ESC
import ../../../src/crypto/ed25519/step.bend as ST

# The straight-line Horner step is the list form on the limbs: one
# evaluation on symbolic limbs (written by tools/gen_scalar.py together
# with src/crypto/ed25519/step.bend).

def step_b(+R: Nat, +l: FE.Fe, +a: FE.Fe, +d: Nat) -> {FE.to_list(ST.step15(R, l, a, d)) == ESC.step(R, FE.to_list(l), FE.to_list(a), d) : List<&2, Nat>}:
  match l a:
    case FE.Fe{l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14} FE.Fe{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14}:
      {==}
