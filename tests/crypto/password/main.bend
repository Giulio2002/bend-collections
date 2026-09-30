import Base
import ../../../src/crypto/password.bend as PW
import ../../support/text.bend as X

# Password-hashing driver (src/crypto/password.bend). Tokens:
#   hash:<pw hex>:<salt hex>:<m>:<t>:<p>:<tag>   the PHC string, or "invalid"
#   verify:<pw hex>:<PHC string>                 "true" or "false"
#   rehash:<PHC string>:<m>:<t>:<p>:<tag>:<salt> "true" or "false"
#   os:<pw hex>:<m>:<t>:<p>:<tag>:<salt>         a PHC string with a random salt
# tools/check_argon2.py drives it against argon2-cffi's PasswordHasher. Hex
# "-" is the empty byte string.

def nib_of(+x: U32, digit: Bool) -> U32:
  match digit:
    case True{}:
      (x - 48 : U32)
    case False{}:
      (x - 87 : U32)

def nib(c: Char) -> U32:
  match c:
    case Chr{+x}:
      nib_of(x, U32.is_le(x, 57))

def bytes_of(cs: List<&2, Char>) -> List<&2, U32>:
  match cs:
    case a <> b <> rest:
      U32.or(U32.shln(nib(a), 4n), nib(b)) <> bytes_of(rest)
    case _:
      Nil{}

def unhex_if(s: String, empty: Bool) -> List<&2, U32>:
  match empty:
    case True{}:
      Nil{}
    case False{}:
      bytes_of(String.to_list(s))

def unhex(+s: String) -> List<&2, U32>:
  unhex_if(s, String.eq(s, "-"))

def show_maybe(r: Maybe<&2, String>) -> String:
  match r:
    case None{}:
      "invalid"
    case Some{s}:
      s

def show_bool(b: Bool) -> String:
  match b:
    case True{}:
      "true"
    case False{}:
      "false"

def params(+f: List<&2, String>, +i: Nat) -> PW.Params:
  PW.Params{X.nat_field(f, i), X.nat_field(f, Nat.add(i, 1n)), X.nat_field(f, Nat.add(i, 2n)), X.nat_field(f, Nat.add(i, 3n)), X.nat_field(f, Nat.add(i, 4n))}

def os(+pw: List<&2, U32>, +ps: PW.Params) -> IO(String):
  do IO<String>:
    r : Maybe<&2, String> <- PW.hash_password_os(pw, ps)
    return show_maybe(r)

def one_op(+f: List<&2, String>, hash: Bool, verify: Bool, rehash: Bool) -> IO(String):
  match hash verify rehash:
    case True{} _ _:
      IO.pure(String, show_maybe(PW.hash_password(unhex(X.field(f, 1n)), unhex(X.field(f, 2n)), PW.Params{X.nat_field(f, 3n), X.nat_field(f, 4n), X.nat_field(f, 5n), X.nat_field(f, 6n), 16n})))
    case False{} True{} _:
      IO.pure(String, show_bool(PW.verify_password(unhex(X.field(f, 1n)), X.field(f, 2n))))
    case False{} False{} True{}:
      IO.pure(String, show_bool(PW.needs_rehash(X.field(f, 1n), params(f, 2n))))
    case False{} False{} False{}:
      os(unhex(X.field(f, 1n)), params(f, 2n))

def one(+tok: String) -> IO(String):
  +f = X.fields(tok)
  +op = X.field(f, 0n)
  one_op(f, String.eq(op, "hash"), String.eq(op, "verify"), String.eq(op, "rehash"))

def all(ts: List<&2, String>) -> IO(Unit):
  match ts:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case t <> rest:
      do IO<Unit>:
        line : String <- one(t)
        IO.print(line)
        all(rest)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    all(X.program_args(args))
