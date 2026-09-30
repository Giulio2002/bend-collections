import Base
import ./field.bend as FS
import ./curve.bend as CS

# The GLV endomorphism of secp256k1 (Gallant, Lambert, Vanstone; the
# constants of libsecp256k1 and SEC 2 curve parameters), as the statements
# of proofs/crypto/secp256k1/laws_glv.bend need it. Nothing here is used by
# the implementation or by the other specifications.
#
# beta is a cube root of 1 in GF(p) and lambda a cube root of 1 modulo the
# group order n; phi(X : Y : Z) = (beta X : Y : Z) maps the curve to itself
# and phi(P) = [lambda] P on the multiples of G. The constants are written
# as the other constants of the specification: little-endian 16-bit digits.

# 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
def beta(+one: Nat) -> Nat:
  FS.digits(one, [494n, 29077n, 27688n, 49465n, 35221n, 4853n, 18805n, 40176n, 13545n, 44084n, 18334n, 28260n, 1808n, 25980n, 27179n, 31465n])

# 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72
def lambda(+one: Nat) -> Nat:
  FS.digits(one, [48498n, 6947n, 38524n, 57090n, 26232n, 8321n, 8938n, 4654n, 25690n, 34834n, 7170n, 42278n, 12512n, 49244n, 44364n, 21347n])

def phi(+p: Nat, +beta: Nat, a: CS.SPoint) -> CS.SPoint:
  match a:
    case CS.SPoint{x, y, z}:
      CS.SPoint{FS.mmul(p, beta, x), y, z}
