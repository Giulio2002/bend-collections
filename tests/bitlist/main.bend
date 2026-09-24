import Base
import ../../src/containers/bitlist.bend as BL
import ../../src/containers/types/bitlist.bend as E
import ../support/text.bend as X

# Test driver: argv = [limit, op tokens...], limit = none | n.
# Tokens: len | limit | get:i | set:i:b | push:b | pop | clear | count | list
#         (b = 0 or 1).
# Output, one line per op: "N n" | "LIMIT none/n" | "OK 0/1" | "OK" |
# "ERR Name" | "BITS 0101" (bit 0 first).

def bit_of(s: String) -> Bool:
  String.eq(s, "1")

def try_list(hit: Bool) -> E.Op:
  match hit:
    case True{}:
      E.ToList{}
    case False{}:
      E.Length{}

def try_count(hit: Bool, +n: String) -> E.Op:
  match hit:
    case True{}:
      E.Count{}
    case False{}:
      try_list(String.eq(n, "list"))

def try_clear(hit: Bool, +n: String) -> E.Op:
  match hit:
    case True{}:
      E.Clear{}
    case False{}:
      try_count(String.eq(n, "count"), n)

def try_pop(hit: Bool, +n: String) -> E.Op:
  match hit:
    case True{}:
      E.Pop{}
    case False{}:
      try_clear(String.eq(n, "clear"), n)

def try_push(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.Push{bit_of(X.field(p, 1n))}
    case False{}:
      try_pop(String.eq(n, "pop"), n)

def try_set(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.Assign{X.nat_field(p, 1n), bit_of(X.field(p, 2n))}
    case False{}:
      try_push(String.eq(n, "push"), n, p)

def try_get(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.Get{X.nat_field(p, 1n)}
    case False{}:
      try_set(String.eq(n, "set"), n, p)

def try_limit(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.Limit{}
    case False{}:
      try_get(String.eq(n, "get"), n, p)

def parse(s: String) -> E.Op:
  +p = X.fields(s)
  +n = X.field(p, 0n)
  try_limit(String.eq(n, "limit"), n, p)

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
    case E.Full{}:
      "ERR Full"
    case E.Empty{}:
      "ERR Empty"

def bit(b: Bool) -> String:
  match b:
    case True{}:
      "OK 1"
    case False{}:
      "OK 0"

def bstr(bs: List<&2, Bool>) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{True{}, t}:
      "1" ++ bstr(t)
    case Con{False{}, t}:
      "0" ++ bstr(t)

def lim(l: Maybe<&2, Nat>) -> String:
  match l:
    case None{}:
      "LIMIT none"
    case Some{k}:
      "LIMIT " ++ Nat.show(k)

def show(o: E.Obs) -> String:
  match o:
    case E.ONat{n}:
      "N " ++ Nat.show(n)
    case E.OLimit{l}:
      lim(l)
    case E.OBit{Fail{e}}:
      err(e)
    case E.OBit{Done{b}}:
      bit(b)
    case E.OUnit{Fail{e}}:
      err(e)
    case E.OUnit{Done{u}}:
      "OK"
    case E.OBits{bs}:
      "BITS " ++ bstr(bs)

def lines(xs: List<&2, E.Obs>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{show(h), lines(t)}

def out(r: BL.Bitlist & List<&2, E.Obs>) -> List<&2, String>:
  (s, os) = r
  lines(os)

def make(unbounded: Bool, +size: String) -> BL.Bitlist:
  match unbounded:
    case True{}:
      BL.new()
    case False{}:
      BL.with_limit(X.nat_of(size))

def start(args: List<&2, String>) -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case Con{+size, ops}:
      out(BL.run(all(ops), make(String.eq(size, "none"), size)))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(start(X.shared(args)))
