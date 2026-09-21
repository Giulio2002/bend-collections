import Base
import ../../src/queue.bend as Q
import ../../types/queue.bend as E
import ../support/text.bend as X

# Test driver: argv = op tokens; values are Nat.
# Tokens: len | enq:x | deq | peek | list
# Output, one line per op: "N n" | "OK" | "OK v" | "ERR EmptyQueue" | "LIST a,b".

def show(o: E.Obs<Nat>) -> String:
  match o:
    case E.ONat{n}:
      "N " ++ Nat.show(n)
    case E.OItem{Fail{e}}:
      "ERR EmptyQueue"
    case E.OItem{Done{v}}:
      "OK " ++ Nat.show(v)
    case E.OUnit{}:
      "OK"
    case E.OList{xs}:
      "LIST " ++ X.join_nat(xs)

def try_peek(hit: Bool) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.Peek{}
    case False{}:
      E.ToList{}

def try_deq(hit: Bool, +n: String) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.Dequeue{}
    case False{}:
      try_peek(String.eq(n, "peek"))

def try_enq(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.Enqueue{X.nat_field(p, 1n)}
    case False{}:
      try_deq(String.eq(n, "deq"), n)

def try_len(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.Length{}
    case False{}:
      try_enq(String.eq(n, "enq"), n, p)

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

def out(r: Q.Queue<Nat> & List<&2, E.Obs<Nat>>) -> List<&2, String>:
  (d, os) = r
  lines(os)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(out(Q.run(~Nat, parse_all(X.shared(args)), Q.new(~Nat))))
