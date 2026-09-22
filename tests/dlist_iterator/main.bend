import Base
import ../../src/dlist_iterator.bend as I
import ../../src/doubly_linked_list.bend as D
import ../../types/doubly_linked_list.bend as E
import ../support/text.bend as X

type Op is Data:
  First{}
  Last{}
  Next{}
  Previous{}
  Add{x: U32}
  Set{x: U32}
  Remove{}
  HasNext{}
  HasPrevious{}
  Position{}
  Listing{}

def error(e: I.Error) -> String:
  match e:
    case I.Exhausted{}:
      "ERR end"
    case I.NoCurrent{}:
      "ERR state"
    case I.Storage{x}:
      "ERR storage"

def show_value(r: Result<&2, &2, I.Error, U32>) -> String:
  match r:
    case Fail{e}:
      error(e)
    case Done{x}:
      "V " ++ U32.show(x)

def show_unit(r: Result<&2, &2, I.Error, Unit>) -> String:
  match r:
    case Fail{e}:
      error(e)
    case Done{x}:
      "OK"

def show_bool(b: Bool) -> String:
  match b:
    case False{}:
      "B 0"
    case True{}:
      "B 1"

def out_value(r: I.Iterator<U32> & Result<&2, &2, I.Error, U32>) -> I.Iterator<U32> & String:
  (it, x) = r
  (it, show_value(x))

def out_unit(r: I.Iterator<U32> & Result<&2, &2, I.Error, Unit>) -> I.Iterator<U32> & String:
  (it, x) = r
  (it, show_unit(x))

def out_bool(r: I.Iterator<U32> & Bool) -> I.Iterator<U32> & String:
  (it, x) = r
  (it, show_bool(x))

def out_nat(r: I.Iterator<U32> & Nat) -> I.Iterator<U32> & String:
  (it, x) = r
  (it, "N " ++ Nat.show(x))

def listed(n: U32, last: U32, f: Bool, i: Nat, r: D.DList<U32> & List<&2, U32>) -> I.Iterator<U32> & String:
  (s, xs) = r
  (I.IT{s, n, last, f, i}, "LIST " ++ X.join_u32(xs))

def listing(it: I.Iterator<U32>) -> I.Iterator<U32> & String:
  I.IT{s, n, last, f, i} = it
  listed(n, last, f, i, D.to_list(~U32, s))

def apply(it: I.Iterator<U32>, op: Op) -> I.Iterator<U32> & String:
  match op:
    case First{}:
      (I.iter_first(~U32, I.finish(~U32, it)), "OK")
    case Last{}:
      (I.iter_last(~U32, I.finish(~U32, it)), "OK")
    case Next{}:
      out_value(I.next(~U32, it))
    case Previous{}:
      out_value(I.previous(~U32, it))
    case Add{x}:
      out_unit(I.add(~U32, it, x))
    case Set{x}:
      out_unit(I.set(~U32, it, x))
    case Remove{}:
      out_unit(I.remove(~U32, it))
    case HasNext{}:
      out_bool(I.has_next(~U32, it))
    case HasPrevious{}:
      out_bool(I.has_previous(~U32, it))
    case Position{}:
      out_nat(I.position(~U32, it))
    case Listing{}:
      listing(it)

def try_pos(+n: String, +v: U32, hit: Bool) -> Op:
  match hit:
    case True{}:
      Position{}
    case False{}:
      Listing{}

def try_hp(+n: String, +v: U32, hit: Bool) -> Op:
  match hit:
    case True{}:
      HasPrevious{}
    case False{}:
      try_pos(n, v, String.eq(n, "pos"))

def try_hn(+n: String, +v: U32, hit: Bool) -> Op:
  match hit:
    case True{}:
      HasNext{}
    case False{}:
      try_hp(n, v, String.eq(n, "hp"))

def try_remove(+n: String, +v: U32, hit: Bool) -> Op:
  match hit:
    case True{}:
      Remove{}
    case False{}:
      try_hn(n, v, String.eq(n, "hn"))

def try_set(+n: String, +v: U32, hit: Bool) -> Op:
  match hit:
    case True{}:
      Set{v}
    case False{}:
      try_remove(n, v, String.eq(n, "remove"))

def try_add(+n: String, +v: U32, hit: Bool) -> Op:
  match hit:
    case True{}:
      Add{v}
    case False{}:
      try_set(n, v, String.eq(n, "set"))

def try_prev(+n: String, +v: U32, hit: Bool) -> Op:
  match hit:
    case True{}:
      Previous{}
    case False{}:
      try_add(n, v, String.eq(n, "add"))

def try_next(+n: String, +v: U32, hit: Bool) -> Op:
  match hit:
    case True{}:
      Next{}
    case False{}:
      try_prev(n, v, String.eq(n, "prev"))

def try_last(+n: String, +v: U32, hit: Bool) -> Op:
  match hit:
    case True{}:
      Last{}
    case False{}:
      try_next(n, v, String.eq(n, "next"))

def try_first(+n: String, +v: U32, hit: Bool) -> Op:
  match hit:
    case True{}:
      First{}
    case False{}:
      try_last(n, v, String.eq(n, "last"))

def parse(t: String) -> Op:
  +p = X.fields(t)
  +n = X.field(p, 0n)
  +v = X.u32_field(p, 1n)
  try_first(n, v, String.eq(n, "first"))

def record(acc: List<&2, String>, r: I.Iterator<U32> & String) -> I.Iterator<U32> & List<&2, String>:
  (it, line) = r
  (it, Con{line, acc})

def step(token: String, st: I.Iterator<U32> & List<&2, String>) -> I.Iterator<U32> & List<&2, String>:
  (it, acc) = st
  record(acc, apply(it, parse(token)))

def run(tokens: List<&2, String>, st: I.Iterator<U32> & List<&2, String>) -> List<&2, String>:
  match tokens:
    case Nil{}:
      (it, acc) = st
      List.reverse(&2, String, acc)
    case Con{h, tail}:
      run(tail, step(h, st))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(run(X.shared(args), (I.iter_first(~U32, D.new(~U32, 1)), Nil{})))
