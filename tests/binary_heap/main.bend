import Base
import ../../src/containers/binary_heap.bend as H
import ../../src/containers/types/binary_heap.bend as E
import ../support/text.bend as X

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

def out_u(r: H.Heap<U32> & List<&2, E.Obs<U32>>) -> List<&2, String>:
  (h, os) = r
  lines_u(os)

def out_s(r: H.Heap<String> & List<&2, E.Obs<String>>) -> List<&2, String>:
  (h, os) = r
  lines_s(os)

def dispatch(is_u: Bool, ops: List<&2, String>) -> List<&2, String>:
  match is_u:
    case True{}:
      out_u(H.run_u32(all_u(ops), H.new(~U32)))
    case False{}:
      out_s(H.run_string(all_s(ops), H.new(~String)))

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
