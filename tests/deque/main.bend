import Base
import ../../src/deque.bend as Q
import ../../types/deque.bend as E
import ../support/text.bend as X

# Test driver: argv = op tokens; values are Nat.
# Tokens: len | pf:x | pb:x | popf | popb | peekf | peekb | list
# Output, one line per op: "N n" | "OK" | "OK v" | "ERR EmptyDeque" | "LIST a,b".

def show(o: E.Obs<Nat>) -> String:
  match o:
    case E.ONat{n}:
      "N " ++ Nat.show(n)
    case E.OItem{Fail{e}}:
      "ERR EmptyDeque"
    case E.OItem{Done{v}}:
      "OK " ++ Nat.show(v)
    case E.OUnit{}:
      "OK"
    case E.OList{xs}:
      "LIST " ++ X.join_nat(xs)

def try_peekb(hit: Bool) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.PeekBack{}
    case False{}:
      E.ToList{}

def try_peekf(hit: Bool, +n: String) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.PeekFront{}
    case False{}:
      try_peekb(String.eq(n, "peekb"))

def try_popb(hit: Bool, +n: String) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.PopBack{}
    case False{}:
      try_peekf(String.eq(n, "peekf"), n)

def try_popf(hit: Bool, +n: String) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.PopFront{}
    case False{}:
      try_popb(String.eq(n, "popb"), n)

def try_pb(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.PushBack{X.nat_field(p, 1n)}
    case False{}:
      try_popf(String.eq(n, "popf"), n)

def try_pf(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.PushFront{X.nat_field(p, 1n)}
    case False{}:
      try_pb(String.eq(n, "pb"), n, p)

def try_len(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.Length{}
    case False{}:
      try_pf(String.eq(n, "pf"), n, p)

def parse(t: String) -> E.Op<Nat>:
  +p = X.fields(t)
  +n = X.field(p, 0n)
  try_len(String.eq(n, "len"), n, p)

def parse_all(xs: List<&2, String>) -> List<&2, E.Op<Nat>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{parse(h), parse_all(t)}

def lines(xs: List<&2, E.Obs<Nat>>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{show(h), lines(t)}

def out(r: Q.Deque<Nat> & List<&2, E.Obs<Nat>>) -> List<&2, String>:
  (d, os) = r
  lines(os)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(out(Q.run(~Nat, parse_all(X.shared(args)), Q.new(~Nat))))
