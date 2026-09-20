import Base
import ../../src/fenwick_tree.bend as F
import ../../types/fenwick_tree.bend as E
import ../support/text.bend as X

# Test driver: argv = [init, op tokens...]; init is "new:N" or "list:v1,v2,..".
# Tokens: len | add:i:v | prefix:e | range:l:r
# Output, one line per op: "N n" | "OK v" | "OK" | "ERR Name".

def u32s(xs: List<&2, String>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{X.u32_of(h), u32s(t)}

def try_range(hit: Bool, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.RangeSum{X.nat_field(p, 1n), X.nat_field(p, 2n)}
    case False{}:
      E.Length{}

def try_prefix(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.PrefixSum{X.nat_field(p, 1n)}
    case False{}:
      try_range(String.eq(n, "range"), p)

def try_add(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.Add{X.nat_field(p, 1n), X.u32_field(p, 2n)}
    case False{}:
      try_prefix(String.eq(n, "prefix"), n, p)

def parse(s: String) -> E.Op:
  +p = X.fields(s)
  +n = X.field(p, 0n)
  try_add(String.eq(n, "add"), n, p)

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
    case E.InvalidRange{}:
      "ERR InvalidRange"

def show(o: E.Obs) -> String:
  match o:
    case E.ONat{n}:
      "N " ++ Nat.show(n)
    case E.OSum{Fail{e}}:
      err(e)
    case E.OSum{Done{v}}:
      "OK " ++ U32.show(v)
    case E.OUnit{Fail{e}}:
      err(e)
    case E.OUnit{Done{u}}:
      "OK"

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

# The cell array is linear: the driver has to release the tree it built.
def out(r: F.Fenwick & List<&2, E.Obs>) -> List<&2, String>:
  (f, os) = r
  out_done(F.dispose(f), os)

def init_of(is_list: Bool, +p: List<&2, String>) -> F.Fenwick:
  match is_list:
    case True{}:
      F.from_list(u32s(String.split(X.field(p, 1n), ',')))
    case False{}:
      F.new(X.nat_field(p, 1n))

def start(args: List<&2, String>) -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case Con{init, ops}:
      +p = X.fields(init)
      out(F.run(all(ops), init_of(String.eq(X.field(p, 0n), "list"), p)))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(start(X.shared(args)))
