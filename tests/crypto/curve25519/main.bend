import Base
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../../src/crypto/kex.bend as KX
import ../../../src/crypto/sign.bend as SG
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

def bool(b: Bool) -> String:
  match b:
    case True{}:
      "true"
    case False{}:
      "false"

def pub(m: Maybe<&2, SG.Keypair>) -> String:
  match m:
    case None{}:
      "None"
    case Some{SG.Keypair{s, p}}:
      H.show(p)

def kpub(m: Maybe<&2, KX.Keypair>) -> String:
  match m:
    case None{}:
      "None"
    case Some{KX.Keypair{s, p}}:
      H.show(p)

def f(+parts: List<&2, String>, i: Nat) -> List<&2, U32>:
  H.bytes(T.field(parts, i))

# ops: x (X25519), iter, kpk (kex public), ss (shared secret), epk (Ed25519
# public), esig (sign), ever (verify)
def run(op: Nat, +parts: List<&2, String>) -> String:
  match op:
    case 0n:
      opt(X.x25519(f(parts, 1n), f(parts, 2n)))
    case 1n:
      H.show(iterate(T.nat_field(parts, 1n), X.base(), X.base()))
    case 2n:
      kpub(KX.generate_keypair(f(parts, 1n)))
    case 3n:
      opt(KX.shared_secret(f(parts, 1n), f(parts, 2n)))
    case 4n:
      pub(SG.generate_keypair(f(parts, 1n)))
    case 5n:
      opt(SG.sign(f(parts, 1n), f(parts, 2n)))
    case _:
      bool(SG.verify(f(parts, 1n), f(parts, 2n), f(parts, 3n)))

def op_of(+s: String) -> Nat:
  op_pick(String.eq(s, "x"), String.eq(s, "iter"), String.eq(s, "kpk"), String.eq(s, "ss"), String.eq(s, "epk"), String.eq(s, "esig"))

def op_pick(a: Bool, b: Bool, c: Bool, d: Bool, e: Bool, g: Bool) -> Nat:
  match a:
    case True{}:
      0n
    case False{}:
      match b:
        case True{}:
          1n
        case False{}:
          match c:
            case True{}:
              2n
            case False{}:
              match d:
                case True{}:
                  3n
                case False{}:
                  match e:
                    case True{}:
                      4n
                    case False{}:
                      match g:
                        case True{}:
                          5n
                        case False{}:
                          6n

def line(s: String) -> String:
  +parts = T.fields(s)
  run(op_of(T.field(parts, 0n)), parts)

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
