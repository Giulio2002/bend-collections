import Base
import ../../src/dynamic_array.bend as A
import ../../types/dynamic_array.bend as E
import ./main.bend as D
import ../support/text.bend as X

# A genuinely non-copyable payload: another dynamic array.
type Box is Type:
  Box{inner: A.DynArray<&2, U32>}

def box_done(r: A.DynArray<&2, U32> & Result<&2, &2, E.Error, Unit>) -> Box:
  (a, status) = r
  Box{a}

def value(r: Result<&2, &2, E.Error, U32>) -> U32:
  match r:
    case Done{x}:
      x
    case Fail{e}:
      999999

def item(r: Result<&2, &1, E.Error, U32>) -> String:
  match r:
    case Fail{e}:
      D.err(e)
    case Done{v}:
      "OK " ++ U32.show(v)

def num(r: A.DynArray<Box> & Nat) -> A.DynArray<Box> & String:
  (a, n) = r
  (a, "N " ++ Nat.show(n))

def unit(r: A.DynArray<Box> & Result<&2, &2, E.Error, Unit>) -> A.DynArray<Box> & String:
  match r:
    case Tuple{a, Done{x}}:
      (a, "OK")
    case Tuple{a, Fail{e}}:
      (a, D.err(e))

def list_done(r: A.DynArray<Box> & List<&2, U32>) -> A.DynArray<Box> & String:
  (a, xs) = r
  (a, "LIST " ++ X.join_u32(xs))

def run_item(acc: List<&2, String>, r: A.DynArray<Box> & String) -> A.DynArray<Box> & List<&2, String>:
  (a, text) = r
  (a, Con{text, acc})

def box(x: U32) -> Box:
  box_done(A.push_at(~U32, A.new_at(~U32), x))

def peek_done(r: A.DynArray<&2, U32> & Result<&2, &2, E.Error, U32>) -> Box & U32:
  (a, x) = r
  (Box{a}, value(x))

def got(r: A.DynArray<Box> & Result<&2, &1, E.Error, U32>) -> A.DynArray<Box> & String:
  (a, result) = r
  (a, item(result))

def owned_value(r: Result<&2, &1, E.Error, U32>) -> U32:
  match r:
    case Done{x}:
      x
    case Fail{e}:
      999999

def scan_item(acc: List<&2, U32>, r: A.DynArray<Box> & Result<&2, &1, E.Error, U32>) -> A.DynArray<Box> & List<&2, U32>:
  (a, x) = r
  (a, Con{owned_value(x), acc})

def peek(x: Box) -> Box & U32:
  Box{a} = x
  peek_done(A.get_at(~U32, a, 0n))

def scan(k: Nat, +i: Nat, st: A.DynArray<Box> & List<&2, U32>) -> A.DynArray<Box> & List<&2, U32>:
  match k st:
    case 0n Tuple{a, acc}:
      (a, List.reverse(&2, U32, acc))
    case 1n+p Tuple{a, acc}:
      scan(p, 1n+i, scan_item(acc, A.update_owned(~Box, ~U32, a, i, peek)))

def consume(x: Box) -> U32:
  Pair.snd(Box, U32, peek(x))

def list_len(r: A.DynArray<Box> & Nat) -> A.DynArray<Box> & String:
  (a, n) = r
  list_done(scan(n, 0n, (a, Nil{})))

def pushed(r: A.DynArray<Box> & Result<&1, &2, E.Rejected<Box>, Unit>) -> A.DynArray<Box> & String:
  match r:
    case Tuple{a, Done{u}}:
      (a, "OK")
    case Tuple{a, Fail{E.Rejected{e, x}}}:
      (a, D.err(e) ++ " RETURN " ++ U32.show(consume(x)))

def swapped(r: A.DynArray<Box> & Result<&1, &1, E.Rejected<Box>, Maybe<Box>>) -> A.DynArray<Box> & String:
  match r:
    case Tuple{a, Done{Some{x}}}:
      (a, "OLD " ++ U32.show(consume(x)))
    case Tuple{a, Done{None{}}}:
      (a, "INVALID HOLE")
    case Tuple{a, Fail{E.Rejected{e, x}}}:
      (a, D.err(e) ++ " RETURN " ++ U32.show(consume(x)))

def popped(r: A.DynArray<Box> & Result<&2, &1, E.Error, Box>) -> A.DynArray<Box> & String:
  match r:
    case Tuple{a, Done{x}}:
      (a, "OK " ++ U32.show(consume(x)))
    case Tuple{a, Fail{e}}:
      (a, D.err(e))

def list(a: A.DynArray<Box>) -> A.DynArray<Box> & String:
  list_len(A.length_owned(~Box, a))

def drained(xs: List<Box>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      Con{consume(x), drained(rest)}

def step(a: A.DynArray<Box>, op: E.Op<U32>) -> A.DynArray<Box> & String:
  match op:
    case E.Length{}:
      num(A.length_owned(~Box, a))
    case E.Capacity{}:
      num(A.capacity_owned(~Box, a))
    case E.Push{x}:
      pushed(A.push_owned(~Box, a, box(x)))
    case E.Pop{}:
      popped(A.pop_owned(~Box, a))
    case E.Get{i}:
      got(A.update_owned(~Box, ~U32, a, i, peek))
    case E.Set{i, x}:
      swapped(A.swap_owned(~Box, a, i, box(x)))
    case E.Reserve{n}:
      unit(A.reserve_owned(~Box, a, n))
    case E.Clear{}:
      (A.clear_owned(~Box, a), "OK")
    case E.ToList{}:
      list(a)

def run(ops: List<&2, E.Op<U32>>, st: A.DynArray<Box> & List<&2, String>) -> List<&2, String>:
  match ops st:
    case Nil{} Tuple{a, acc}:
      List.reverse(&2, String, Con{"DRAIN " ++ X.join_u32(drained(A.into_list_owned(~Box, a))), acc})
    case Con{op, rest} Tuple{a, acc}:
      run(rest, run_item(acc, step(a, op)))

def start(args: List<&2, String>) -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case Con{limit, ops}:
      run(D.parse_all_u(ops), (A.with_limit_owned(~Box, X.nat_of(limit)), Nil{}))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(start(X.shared(args)))
