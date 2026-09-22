import Base
import ../../src/containers/bitset.bend as B
import ../../src/containers/types/bitset.bend as E
import ../support/text.bend as X

# Test driver: argv = [size, op tokens...].
# Tokens: len | get:i | set:i | clear:i | count | list |
#         or:BITS | and:BITS | diff:BITS | xor:BITS   (BITS = 0/1 chars, bit 0 first)
# Output, one line per op: "N n" | "OK 0/1" | "OK" | "ERR Name" | "LIST a,b".

def bools(s: String) -> List<&2, Bool>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      Con{Char.is_eq(c, '1'), bools(t)}

def try_list(hit: Bool) -> E.Op:
  match hit:
    case True{}:
      E.ToList{}
    case False{}:
      E.Length{}

def try_xor(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.Xor{bools(X.field(p, 1n))}
    case False{}:
      try_list(String.eq(n, "list"))

def try_diff(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.Difference{bools(X.field(p, 1n))}
    case False{}:
      try_xor(String.eq(n, "xor"), n, p)

def try_and(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.Intersection{bools(X.field(p, 1n))}
    case False{}:
      try_diff(String.eq(n, "diff"), n, p)

def try_or(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.Union{bools(X.field(p, 1n))}
    case False{}:
      try_and(String.eq(n, "and"), n, p)

def try_count(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.Count{}
    case False{}:
      try_or(String.eq(n, "or"), n, p)

def try_clear(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.Clear{X.nat_field(p, 1n)}
    case False{}:
      try_count(String.eq(n, "count"), n, p)

def try_set(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.Set{X.nat_field(p, 1n)}
    case False{}:
      try_clear(String.eq(n, "clear"), n, p)

def try_get(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.Get{X.nat_field(p, 1n)}
    case False{}:
      try_set(String.eq(n, "set"), n, p)

def parse(s: String) -> E.Op:
  +p = X.fields(s)
  +n = X.field(p, 0n)
  try_get(String.eq(n, "get"), n, p)

def all(xs: List<&2, String>) -> List<&2, E.Op>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{parse(h), all(t)}

def err(e: E.Error) -> String:
  match e:
    case E.IndexOutOfRange{}:
      "ERR IndexOutOfRange"
    case E.LengthMismatch{}:
      "ERR LengthMismatch"

def bit(b: Bool) -> String:
  match b:
    case True{}:
      "OK 1"
    case False{}:
      "OK 0"

def show(o: E.Obs) -> String:
  match o:
    case E.ONat{n}:
      "N " ++ Nat.show(n)
    case E.OBit{Fail{e}}:
      err(e)
    case E.OBit{Done{b}}:
      bit(b)
    case E.OUnit{Fail{e}}:
      err(e)
    case E.OUnit{Done{u}}:
      "OK"
    case E.OList{xs}:
      "LIST " ++ X.join_nat(xs)

def lines(xs: List<&2, E.Obs>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{show(h), lines(t)}

def out_done(u: Unit, os: List<&2, E.Obs>) -> List<&2, String>:
  match u:
    case Unit{}:
      lines(os)

def out(r: B.Bitset & List<&2, E.Obs>) -> List<&2, String>:
  (s, os) = r
  out_done(B.dispose(s), os)

def start(args: List<&2, String>) -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case Con{size, ops}:
      out(B.run(all(ops), B.new(X.nat_of(size))))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(start(X.shared(args)))
