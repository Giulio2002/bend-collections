import Base
import ../../src/priority_queue.bend as Q
import ../../src/binary_heap.bend as K
import ../../types/binary_heap.bend as E
import ../support/text.bend as X

def obs_nat(~A: Data, r: K.Heap<A> & Nat) -> K.Heap<A> & E.Obs<A>:
  (h, n) = r
  (h, E.ONat{n})

def obs_item(~A: Data, r: K.Heap<A> & Result<&2, &2, E.Error, A>) -> K.Heap<A> & E.Obs<A>:
  (h, x) = r
  (h, E.OItem{x})

def obs_list(~A: Data, r: K.Heap<A> & List<&2, A>) -> K.Heap<A> & E.Obs<A>:
  (h, xs) = r
  (h, E.OList{xs})

def drop_heap(~A: Data, h: K.Heap<A>, v: K.Heap<A> & E.Obs<A>) -> K.Heap<A> & E.Obs<A>:
  v

# FromList replaces the heap: the old block is dropped (O(1) erasure).
def replace(~A: Data, ~cmp: A -> A -> Cmp, h: K.Heap<A>, xs: List<&2, A>) -> K.Heap<A> & E.Obs<A>:
  K.BH{size, n, depth, cap, arr} = h
  (Q.from_list(~A, ~cmp, xs), E.OUnit{})

def step(~A: Data, ~cmp: A -> A -> Cmp, h: K.Heap<A>, op: E.Op<A>) -> K.Heap<A> & E.Obs<A>:
  match op:
    case E.Length{}:
      obs_nat(~A, Q.qsize(~A, h))
    case E.Push{x}:
      (Q.put(~A, ~cmp, h, x), E.OUnit{})
    case E.Peek{}:
      obs_item(~A, Q.peek(~A, h))
    case E.Pop{}:
      obs_item(~A, Q.get(~A, ~cmp, h))
    case E.FromList{xs}:
      replace(~A, ~cmp, h, xs)
    case E.ToSortedList{}:
      obs_list(~A, Q.to_sorted_list(~A, ~cmp, h))

def record(~A: Data, acc: List<&2, E.Obs<A>>, r: K.Heap<A> & E.Obs<A>) -> K.Heap<A> & List<&2, E.Obs<A>>:
  (h, o) = r
  (h, Con{o, acc})

def step_acc(~A: Data, ~cmp: A -> A -> Cmp, op: E.Op<A>, st: K.Heap<A> & List<&2, E.Obs<A>>) -> K.Heap<A> & List<&2, E.Obs<A>>:
  (h, acc) = st
  record(~A, acc, step(~A, ~cmp, h, op))

def run_acc(~A: Data, ~cmp: A -> A -> Cmp, ops: List<&2, E.Op<A>>, st: K.Heap<A> & List<&2, E.Obs<A>>) -> K.Heap<A> & List<&2, E.Obs<A>>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      run_acc(~A, ~cmp, rest, step_acc(~A, ~cmp, op, st))

def finish(~A: Data, st: K.Heap<A> & List<&2, E.Obs<A>>) -> K.Heap<A> & List<&2, E.Obs<A>>:
  (h, acc) = st
  (h, List.reverse(&2, E.Obs<A>, acc))

def run(~A: Data, ~cmp: A -> A -> Cmp, ops: List<&2, E.Op<A>>, h: K.Heap<A>) -> K.Heap<A> & List<&2, E.Obs<A>>:
  finish(~A, run_acc(~A, ~cmp, ops, (h, Nil{})))

# ---- checked instances (proofs/binary_heap.bend) ----

def run_u32(ops: List<&2, E.Op<U32>>, h: K.Heap<U32>) -> K.Heap<U32> & List<&2, E.Obs<U32>>:
  run(~U32, ~U32.cmp, ops, h)

def run_string(ops: List<&2, E.Op<String>>, h: K.Heap<String>) -> K.Heap<String> & List<&2, E.Obs<String>>:
  run(~String, ~String.order, ops, h)

# Test driver: argv = [kind, op tokens...], kind "u32" or "str".
# Tokens: len | push:v | peek | pop | from:v1,v2,.. | sorted.

def u32s_go(xs: List<&2, String>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{X.u32_of(h), u32s_go(t)}

def u32s(s: String) -> List<&2, U32>:
  u32s_go(String.split(s, ','))

def strs(s: String) -> List<&2, String>:
  String.split(s, ',')

def try_sorted_u(hit: Bool) -> E.Op<U32>:
  match hit:
    case True{}:
      E.ToSortedList{}
    case False{}:
      E.Length{}

def try_from_u(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<U32>:
  match hit:
    case True{}:
      E.FromList{u32s(X.field(p, 1n))}
    case False{}:
      try_sorted_u(String.eq(n, "sorted"))

def try_pop_u(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<U32>:
  match hit:
    case True{}:
      E.Pop{}
    case False{}:
      try_from_u(String.eq(n, "from"), n, p)

def try_peek_u(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<U32>:
  match hit:
    case True{}:
      E.Peek{}
    case False{}:
      try_pop_u(String.eq(n, "pop"), n, p)

def try_push_u(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<U32>:
  match hit:
    case True{}:
      E.Push{X.u32_field(p, 1n)}
    case False{}:
      try_peek_u(String.eq(n, "peek"), n, p)

def parse_u(s: String) -> E.Op<U32>:
  +p = X.fields(s)
  +n = X.field(p, 0n)
  try_push_u(String.eq(n, "push"), n, p)

def try_sorted_s(hit: Bool) -> E.Op<String>:
  match hit:
    case True{}:
      E.ToSortedList{}
    case False{}:
      E.Length{}

def try_from_s(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<String>:
  match hit:
    case True{}:
      E.FromList{strs(X.field(p, 1n))}
    case False{}:
      try_sorted_s(String.eq(n, "sorted"))

def try_pop_s(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<String>:
  match hit:
    case True{}:
      E.Pop{}
    case False{}:
      try_from_s(String.eq(n, "from"), n, p)

def try_peek_s(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<String>:
  match hit:
    case True{}:
      E.Peek{}
    case False{}:
      try_pop_s(String.eq(n, "pop"), n, p)

def try_push_s(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<String>:
  match hit:
    case True{}:
      E.Push{X.field(p, 1n)}
    case False{}:
      try_peek_s(String.eq(n, "peek"), n, p)

def parse_s(s: String) -> E.Op<String>:
  +p = X.fields(s)
  +n = X.field(p, 0n)
  try_push_s(String.eq(n, "push"), n, p)

def all_u(xs: List<&2, String>) -> List<&2, E.Op<U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{parse_u(h), all_u(t)}

def all_s(xs: List<&2, String>) -> List<&2, E.Op<String>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{parse_s(h), all_s(t)}

def show_u(o: E.Obs<U32>) -> String:
  match o:
    case E.ONat{n}:
      "N " ++ Nat.show(n)
    case E.OItem{Fail{e}}:
      "ERR EmptyHeap"
    case E.OItem{Done{x}}:
      "OK " ++ U32.show(x)
    case E.OUnit{}:
      "OK"
    case E.OList{xs}:
      "LIST " ++ X.join_u32(xs)

def show_s(o: E.Obs<String>) -> String:
  match o:
    case E.ONat{n}:
      "N " ++ Nat.show(n)
    case E.OItem{Fail{e}}:
      "ERR EmptyHeap"
    case E.OItem{Done{x}}:
      "OK " ++ x
    case E.OUnit{}:
      "OK"
    case E.OList{xs}:
      "LIST " ++ String.join(xs, ",")

def lines_u(xs: List<&2, E.Obs<U32>>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{show_u(h), lines_u(t)}

def lines_s(xs: List<&2, E.Obs<String>>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{show_s(h), lines_s(t)}

def out_u(r: K.Heap<U32> & List<&2, E.Obs<U32>>) -> List<&2, String>:
  (h, os) = r
  lines_u(os)

def out_s(r: K.Heap<String> & List<&2, E.Obs<String>>) -> List<&2, String>:
  (h, os) = r
  lines_s(os)

def dispatch(is_u: Bool, ops: List<&2, String>) -> List<&2, String>:
  match is_u:
    case True{}:
      out_u(run_u32(all_u(ops), Q.new(~U32)))
    case False{}:
      out_s(run_string(all_s(ops), Q.new(~String)))

def start(args: List<&2, String>) -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case Con{kind, ops}:
      dispatch(String.eq(kind, "u32"), ops)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(start(X.shared(args)))
