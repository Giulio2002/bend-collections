import Base
import ../../src/containers/simple_queue.bend as Q
import ../../src/containers/queue.bend as K
import ../../src/containers/types/queue.bend as E
import ../support/text.bend as X

def obs_nat(~T: Data, r: K.Queue<T> & Nat) -> K.Queue<T> & E.Obs<T>:
  (q, n) = r
  (q, E.ONat{n})

def obs_item(~T: Data, r: K.Queue<T> & Result<&2, &2, E.Error, T>) -> K.Queue<T> & E.Obs<T>:
  (q, x) = r
  (q, E.OItem{x})

def obs_list(~T: Data, r: K.Queue<T> & List<&2, T>) -> K.Queue<T> & E.Obs<T>:
  (q, xs) = r
  (q, E.OList{xs})

def step(~T: Data, q: K.Queue<T>, op: E.Op<T>) -> K.Queue<T> & E.Obs<T>:
  match op:
    case E.Length{}:
      obs_nat(~T, Q.qsize(~T, q))
    case E.Enqueue{+x}:
      (Q.put(~T, q, x), E.OUnit{})
    case E.Dequeue{}:
      obs_item(~T, Q.get(~T, q))
    case E.Peek{}:
      obs_item(~T, Q.peek(~T, q))
    case E.ToList{}:
      obs_list(~T, Q.to_list(~T, q))

def record(~T: Data, acc: List<&2, E.Obs<T>>, r: K.Queue<T> & E.Obs<T>) -> K.Queue<T> & List<&2, E.Obs<T>>:
  (q, o) = r
  (q, Con{o, acc})

def step_acc(~T: Data, op: E.Op<T>, st: K.Queue<T> & List<&2, E.Obs<T>>) -> K.Queue<T> & List<&2, E.Obs<T>>:
  (q, acc) = st
  record(~T, acc, step(~T, q, op))

def run_acc(~T: Data, ops: List<&2, E.Op<T>>, st: K.Queue<T> & List<&2, E.Obs<T>>) -> K.Queue<T> & List<&2, E.Obs<T>>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      run_acc(~T, rest, step_acc(~T, op, st))

def finish(~T: Data, st: K.Queue<T> & List<&2, E.Obs<T>>) -> K.Queue<T> & List<&2, E.Obs<T>>:
  (q, acc) = st
  (q, List.reverse(&2, E.Obs<T>, acc))

def run(~T: Data, ops: List<&2, E.Op<T>>, q: K.Queue<T>) -> K.Queue<T> & List<&2, E.Obs<T>>:
  finish(~T, run_acc(~T, ops, (q, Nil{})))

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

def out(r: K.Queue<Nat> & List<&2, E.Obs<Nat>>) -> List<&2, String>:
  (d, os) = r
  lines(os)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(out(run(~Nat, parse_all(X.shared(args)), Q.new(~Nat))))
