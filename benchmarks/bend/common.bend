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

def times(ta: Nat, tb: Nat, tc: Nat) -> String:
  String.append("TA=", String.append(Nat.show(ta),
    String.append(" TB=", String.append(Nat.show(tb),
      String.append(" TC=", Nat.show(tc))))))

# The command line, parsed ONCE into scalars: argv = [op, size, count, reps,
# seed, order]. Drivers used to pass the argument List around as a shared
# (`+`) value and index it per use; the runtime seals (reference-counts) EVERY
# node of a type that is shared anywhere in the program, so that one shared
# List made every cons cell a structure builds (to_list, range, ...) pay a
# reference-count cell. The record below carries no List at all.
type Args is Data:
  AG{op: U32, size: U32, count: U32, reps: U32, seed: U32, order: U32}

def parse6(a0: String, a1: String, a2: String, a3: String, a4: String, a5: String) -> Args:
  AG{arg(a0), arg(a1), arg(a2), arg(a3), arg(a4), arg(a5)}

def parse(xs: List<&1, String>) -> Args:
  match xs:
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, r}}}}}}:
      parse6(a0, a1, a2, a3, a4, a5)
    case _:
      AG{99, 0, 0, 0, 0, 0}

def a_op(+g: Args) -> U32:
  match g:
    case AG{+op, size, count, reps, seed, order}:
      op

def a_size(+g: Args) -> U32:
  match g:
    case AG{op, +size, count, reps, seed, order}:
      size

def a_count(+g: Args) -> U32:
  match g:
    case AG{op, size, +count, reps, seed, order}:
      count

def a_reps(+g: Args) -> U32:
  match g:
    case AG{op, size, count, +reps, seed, order}:
      reps

def a_seed(+g: Args) -> U32:
  match g:
    case AG{op, size, count, reps, +seed, order}:
      seed

def a_order(+g: Args) -> U32:
  match g:
    case AG{op, size, count, reps, seed, +order}:
      order
