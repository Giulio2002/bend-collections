import Base

# Octet strings and 16-bit limbs. Bytes are U32 values; only the low 8 bits
# of a byte are read (the library's byte convention keeps them below 256).

def byte(+b: U32) -> Nat:
  U32.to_nat(U32.and(b, 255))

# little-endian limbs of little-endian bytes (two bytes per limb)
def limbs_le(bs: List<&2, U32>) -> List<&2, Nat>:
  match bs:
    case Nil{}: Nil{}
    case b0 <> Nil{}: [byte(b0)]
    case b0 <> b1 <> t: Nat.add(Nat.mul(byte(b1), 256n), byte(b0)) <> limbs_le(t)

# the 16 limbs of a 32-byte big-endian string (SEC 1 OS2IP)
def of_be(bs: List<&2, U32>) -> List<&2, Nat>:
  limbs_le(List.reverse(&2, U32, bs))

# little-endian bytes of limbs below 2^16
def bytes_le(xs: List<&2, Nat>) -> List<&2, U32>:
  match xs:
    case Nil{}: Nil{}
    case +x <> t: U32.from_nat(Nat.mod(x, 256n)) <> U32.from_nat(Nat.div(x, 256n)) <> bytes_le(t)

# the 32-byte big-endian string of 16 limbs (SEC 1 I2OSP)
def to_be(xs: List<&2, Nat>) -> List<&2, U32>:
  List.reverse(&2, U32, bytes_le(xs))

def has_len(n: Nat, bs: List<&2, U32>) -> Bool:
  match n bs:
    case 0n Nil{}: True{}
    case 0n b <> t: False{}
    case 1n+k Nil{}: False{}
    case 1n+k b <> t: has_len(k, t)

def prefix(n: Nat, bs: List<&2, U32>) -> List<&2, U32>:
  match n bs:
    case 0n _: Nil{}
    case 1n+k Nil{}: Nil{}
    case 1n+k b <> t: b <> prefix(k, t)

def suffix(n: Nat, bs: List<&2, U32>) -> List<&2, U32>:
  match n bs:
    case 0n _: bs
    case 1n+k Nil{}: Nil{}
    case 1n+k b <> t: suffix(k, t)

def head(bs: List<&2, U32>) -> U32:
  match bs:
    case Nil{}: 0
    case b <> t: b

def tail(bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}: Nil{}
    case b <> t: t
