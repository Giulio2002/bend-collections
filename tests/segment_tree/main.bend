import Base
import ../../src/segment_tree.bend as T
import ../../types/segment_tree.bend as E
import ../support/text.bend as X

# Test driver: argv = [init, op tokens...]; init is "new:N" or "list:v1,v2,..".
# Tokens: len | get:i | set:i:v | query:l:r | add:l:r:v
# Output, one line per op: "N n" | "OK v" | "OK" | "ERR Name".

def u32s(xs: List<&2, String>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{X.u32_of(h), u32s(t)}

def try_add(hit: Bool, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.RangeAdd{X.nat_field(p, 1n), X.nat_field(p, 2n), X.u32_field(p, 3n)}
    case False{}:
      E.Length{}

def try_query(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.RangeQuery{X.nat_field(p, 1n), X.nat_field(p, 2n)}
    case False{}:
      try_add(String.eq(n, "add"), p)

def try_set(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.Set{X.nat_field(p, 1n), X.u32_field(p, 2n)}
    case False{}:
      try_query(String.eq(n, "query"), n, p)

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
    case E.InvalidRange{}:
      "ERR InvalidRange"

def show(o: E.Obs) -> String:
  match o:
    case E.ONat{n}:
      "N " ++ Nat.show(n)
    case E.OItem{Fail{e}}:
      err(e)
    case E.OItem{Done{v}}:
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

# The cell arrays are linear: the driver has to release the tree it built.
def out(r: T.SegTree & List<&2, E.Obs>) -> List<&2, String>:
  (s, os) = r
  out_done(T.dispose(s), os)

def init_of(is_list: Bool, +p: List<&2, String>) -> T.SegTree:
  match is_list:
    case True{}:
      T.from_list(u32s(String.split(X.field(p, 1n), ',')))
    case False{}:
      T.new(X.nat_field(p, 1n))

def start(args: List<&2, String>) -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case Con{init, ops}:
      +p = X.fields(init)
      out(T.run(all(ops), init_of(String.eq(X.field(p, 0n), "list"), p)))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(start(X.shared(args)))
