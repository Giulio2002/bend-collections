import Base
import ../../../src/crypto/argon2/argon2.bend as A2
import ../../support/text.bend as X

# Argon2id driver.
#
# With no arguments: the RFC 9106 section 5.3 Argon2id test vector (with a
# secret K and associated data X) and its H0, printing "ok"/"FAIL" per line and
# the failure count last.
#
# With arguments: each token "pw:salt:key:ad:t:m:p:T" (byte strings in hex,
# "-" for empty) prints the hex tag, or "invalid"; tools/check_argon2.py
# compares the lines with argon2-cffi.

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

def unhex(s: String) -> List<&2, U32>:
  bytes_of(String.to_list(s))

def unhex_if(s: String, empty: Bool) -> List<&2, U32>:
  match empty:
    case True{}:
      Nil{}
    case False{}:
      unhex(s)

def arg_bytes(+s: String) -> List<&2, U32>:
  unhex_if(s, String.eq(s, "-"))

def hex_digit_if(x: U32, small: Bool) -> Char:
  match small:
    case True{}:
      Chr{(48 + x : U32)}
    case False{}:
      Chr{(87 + x : U32)}

def hex_digit(+x: U32) -> Char:
  hex_digit_if(x, U32.is_lt(x, 10))

def hex(bs: List<&2, U32>) -> String:
  match bs:
    case Nil{}:
      ""
    case +b <> rest:
      SCon{hex_digit(U32.shrn(b, 4n)), SCon{hex_digit(U32.and(b, 15)), hex(rest)}}

def show(r: Maybe<&2, List<&2, U32>>) -> String:
  match r:
    case None{}:
      "invalid"
    case Some{t}:
      hex(t)

def one(tok: String) -> String:
  +f = X.fields(tok)
  show(A2.argon2id(arg_bytes(X.field(f, 0n)), arg_bytes(X.field(f, 1n)), arg_bytes(X.field(f, 2n)), arg_bytes(X.field(f, 3n)), X.nat_field(f, 4n), X.nat_field(f, 5n), X.nat_field(f, 6n), X.nat_field(f, 7n)))

def all(ts: List<&2, String>) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> rest:
      one(t) <> all(rest)

def rep(+n: Nat, +b: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      b <> rep(p, b)

def check_if(name: String, got: String, want: String, same: Bool) -> String:
  match same:
    case True{}:
      "ok   " ++ name
    case False{}:
      "FAIL " ++ name ++ " got " ++ got ++ " want " ++ want

def check(name: String, +got: String, +want: String) -> String:
  check_if(name, got, want, String.eq(got, want))

def fail_of(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def failures(ls: List<&2, String>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case l <> rest:
      Nat.add(fail_of(String.starts_with(l, "FAIL")), failures(rest))

def vectors() -> List<&2, String>:
  +pw = rep(32n, 1)
  +salt = rep(16n, 2)
  +key = rep(8n, 3)
  +ad = rep(12n, 4)
  [check("rfc9106 5.3 H0", hex(A2.h0(4n, 32n, 32n, 3n, pw, salt, key, ad)), "2889de487eb42ae500c0007ed9252f1069eadec40d5765b485de6dc2437a67b8546a2f0acc1a0882db8fcf74714b472e94df421a5da1112ffa11434370a1e997"),
   check("rfc9106 5.3 tag", show(A2.argon2id(pw, salt, key, ad, 3n, 32n, 4n, 32n)), "0d640df58d78766c08c037a34a8b53c9d01ef0452d75b65eb52520e96b01e659"),
   check("rejects p = 0", show(A2.argon2id(pw, salt, key, ad, 3n, 32n, 0n, 32n)), "invalid"),
   check("rejects m < 8p", show(A2.argon2id(pw, salt, key, ad, 3n, 31n, 4n, 32n)), "invalid"),
   check("rejects t = 0", show(A2.argon2id(pw, salt, key, ad, 0n, 32n, 4n, 32n)), "invalid"),
   check("rejects T < 4", show(A2.argon2id(pw, salt, key, ad, 3n, 32n, 4n, 3n)), "invalid"),
   check("rejects short salt", show(A2.argon2id(pw, rep(7n, 2), key, ad, 3n, 32n, 4n, 32n)), "invalid")]

def report(+ls: List<&2, String>) -> List<&2, String>:
  List.append(&2, String, ls, [Nat.show(failures(ls)) ++ " failures"])

def pick(ts: List<&2, String>) -> List<&2, String>:
  match ts:
    case Nil{}:
      report(vectors())
    case t <> rest:
      all(t <> rest)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(pick(X.program_args(args)))

