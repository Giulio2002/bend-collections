import Base

# Shared benchmark scaffolding: the deterministic value stream and the
# checksum fold. benchmarks/native/common.h defines exactly the same two functions,
# so both sides consume the identical sequence of pseudo-random arguments and
# must produce the identical checksum.

# Numerical Recipes LCG, mod 2^32.
def lcg(s: U32) -> U32:
  U32.add(U32.mul(s, 1664525), 1013904223)

def mix(c: U32, v: U32) -> U32:
  U32.add(U32.mul(c, 31), v)

# A bounded draw; m must be positive.
def below(v: U32, m: U32) -> U32:
  U32.mod(v, m)

def nat_below(v: U32, m: Nat) -> Nat:
  U32.to_nat(U32.mod(v, U32.from_nat(m)))

def arg(s: String) -> U32:
  Maybe.default(&2, U32, U32.read(s), 0)

def field(parts: List<&2, String>, i: Nat) -> String:
  match parts i:
    case Nil{} _:
      ""
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+p:
      field(t, p)

def shared(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{h, shared(t)}

def times(ta: Nat, tb: Nat, tc: Nat) -> String:
  String.append("TA=", String.append(Nat.show(ta),
    String.append(" TB=", String.append(Nat.show(tb),
      String.append(" TC=", Nat.show(tc))))))
