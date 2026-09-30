import Base
import ../../../../spec/crypto/secp256k1/field.bend as FS
import ../../../../spec/crypto/secp256k1/curve.bend as CS

# The GLV endomorphism of secp256k1 on projective points:
# phi(X : Y : Z) = (beta X : Y : Z), for beta a cube root of 1 in GF(p).

def phi(+p: Nat, +beta: Nat, a: CS.SPoint) -> CS.SPoint:
  match a:
    case CS.SPoint{x, y, z}:
      CS.SPoint{FS.mmul(p, beta, x), y, z}

