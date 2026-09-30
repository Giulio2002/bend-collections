import Base
import ../../../src/crypto/secp256k1/limbs.bend as L
import ../../../src/crypto/secp256k1/fe.bend as FE

# The list models of the record field src/crypto/secp256k1/fe.bend: each
# stage of fe.bend is, term for term, one of these functions on its fields
# (febr.bend), and the values are proved here, on lists, by induction
# (fval.bend). The limb lists are those of src/crypto/secp256k1/limbs.bend.

# every limb times a, as 32-bit products (FE.nmul)
def scalu(+a: Nat, ys: List<&2, Nat>) -> List<&2, Nat>:
  match ys:
    case Nil{}: Nil{}
    case y <> yt: FE.nmul(y, a) <> scalu(a, yt)

# the schoolbook product without carries
def convu(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}: Nil{}
    case x <> xt: L.add(scalu(x, ys), 0n <> convu(xt, ys))

# every limb times 2 a
def dscal(+a: Nat, ys: List<&2, Nat>) -> List<&2, Nat>:
  match ys:
    case Nil{}: Nil{}
    case y <> yt: Nat.mul(FE.nmul(y, a), 2n) <> dscal(a, yt)

# the square without carries: (x + B X)^2 = x^2 + B 2 x X + B^2 X^2
def sqru(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}: Nil{}
    case +x <> Nil{}: [FE.nmul(x, x)]
    case +x <> +y <> +t: L.add(FE.nmul(x, x) <> dscal(x, y <> t), 0n <> 0n <> sqru(y <> t))

# n carried limbs, the carry out added to the next limb and the rest kept
def carryp(n: Nat, xs: List<&2, Nat>, u: Nat) -> List<&2, Nat>:
  match n xs:
    case 0n Nil{}: [u]
    case 0n x <> t: Nat.add(u, x) <> t
    case 1n+k Nil{}:
      +s = Nat.add(u, 0n)
      L.lo16(s) <> carryp(k, Nil{}, L.hi16(s))
    case 1n+k x <> t:
      +s = Nat.add(u, x)
      L.lo16(s) <> carryp(k, t, L.hi16(s))

# lo + (2^32 + 977) hi, for lo the first 16 limbs and hi the rest
def fold1(+xs: List<&2, Nat>) -> List<&2, Nat>:
  L.add(L.add(L.take(16n, xs), L.scal(977n, L.drop(16n, xs))), 0n <> 0n <> L.drop(16n, xs))

# lo + (2^32 + 977) t, for lo the first 16 limbs and t the 17th
def foldt(+xs: List<&2, Nat>) -> List<&2, Nat>:
  L.add(L.take(16n, xs), [Nat.mul(L.hd0(L.drop(16n, xs)), 977n), 0n, L.hd0(L.drop(16n, xs))])

# b x + (1 - b) y, limb-wise, as 32-bit products
def selu(+b: Nat, xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs ys:
    case x <> xt y <> yt: Nat.add(FE.nmul(x, b), FE.nmul(y, Nat.sub(1n, b))) <> selu(b, xt, yt)
    case _ _: Nil{}

# x mod m for x = lo + 2^256 t below 2 m (lo 16 limbs, t the 17th), m =
# 2^256 - c: x - m = lo + c - 2^256 when x >= m, that is when t = 1 or lo + c
# reaches 2^256
def finc(+c: List<&2, Nat>, +u: List<&2, Nat>) -> List<&2, Nat>:
  +v = L.carry(16n, L.add(L.take(16n, u), c), 0n)
  selu(Nat.add(L.hd0(L.drop(16n, u)), L.hd0(L.drop(16n, v))), L.take(16n, v), L.take(16n, u))

# for p: c = 2^32 + 977
def fin(+u: List<&2, Nat>) -> List<&2, Nat>:
  finc([977n, 0n, 1n], u)
