import Base
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../support/text.bend as T
import ./hex.bend as H

# Test driver: every argv token prints one line.
#   x:<k>:<u>   X25519(k, u)             (hex)
#   iter:<n>    RFC 7748 5.2 iterations, k = u = 9

def opt(m: Maybe<&2, List<&2, U32>>) -> String:
  match m:
    case None{}:
      "None"
    case Some{x}:
      H.show(x)

def iterate(n: Nat, +k: List<&2, U32>, u: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      k
    case 1n+m:
      iterate(m, X.x25519_raw(k, u), k)

def run_if(isx: Bool, +parts: List<&2, String>) -> String:
  match isx:
    case True{}:
      opt(X.x25519(H.bytes(T.field(parts, 1n)), H.bytes(T.field(parts, 2n))))
    case False{}:
      H.show(iterate(T.nat_field(parts, 1n), X.base(), X.base()))

def line(s: String) -> String:
  +parts = T.fields(s)
  run_if(String.eq(T.field(parts, 0n), "x"), parts)

def all(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{line(h), all(t)}

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    T.print_lines(all(T.program_args(args)))
