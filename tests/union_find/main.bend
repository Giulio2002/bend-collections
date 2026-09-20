import Base
import ../../src/union_find.bend as U
import ../../types/union_find.bend as E
import ../support/text.bend as X

# Test driver: argv = [n, op tokens...].
# Tokens: find:x | union:a:b | conn:a:b | size:x | count
# Output, one line per op: "N n" | "OK v" | "OK true/false" | "ERR OutOfRange".

def try_size(hit: Bool, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.ComponentSize{X.nat_field(p, 1n)}
    case False{}:
      E.ComponentCount{}

def try_conn(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.Connected{X.nat_field(p, 1n), X.nat_field(p, 2n)}
    case False{}:
      try_size(String.eq(n, "size"), p)

def try_union(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.Union{X.nat_field(p, 1n), X.nat_field(p, 2n)}
    case False{}:
      try_conn(String.eq(n, "conn"), n, p)

def try_find(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.Find{X.nat_field(p, 1n)}
    case False{}:
      try_union(String.eq(n, "union"), n, p)

def parse(s: String) -> E.Op:
  +p = X.fields(s)
  +n = X.field(p, 0n)
  try_find(String.eq(n, "find"), n, p)

def all(xs: List<&2, String>) -> List<&2, E.Op>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{parse(h), all(t)}

def show_bool(b: Bool) -> String:
  match b:
    case True{}:
      "OK true"
    case False{}:
      "OK false"

def show(o: E.Obs) -> String:
  match o:
    case E.ONat{n}:
      "N " ++ Nat.show(n)
    case E.OItem{Fail{e}}:
      "ERR OutOfRange"
    case E.OItem{Done{v}}:
      "OK " ++ Nat.show(v)
    case E.OBool{Fail{e}}:
      "ERR OutOfRange"
    case E.OBool{Done{b}}:
      show_bool(b)

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

def out(r: U.UnionFind & List<&2, E.Obs>) -> List<&2, String>:
  (s, os) = r
  out_done(U.dispose(s), os)

def start(args: List<&2, String>) -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case Con{size, ops}:
      out(U.run(all(ops), U.new(X.nat_of(size))))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(start(X.shared(args)))
