import Base
import ../../src/dynamic_array.bend as DA
import ../../types/dynamic_array.bend as E
import ../support/text.bend as X

# Test driver: argv = [kind, limit, op tokens...], kind "nat" or "u32".
# It runs the real executable public API (DA.run_at, the closed-element-type
# specialization proved equal to DA.run in proofs/dynamic_array/closed.bend)
# and prints one line per observation. Expected answers never enter here.
# Tokens: len | cap | get:i | set:i:v | push:v | pop | reserve:n | clear |
#         to_list (any other token)

# ---- Nat elements ----

def try_clear(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.Clear{}
    case False{}:
      E.ToList{}

def try_reserve(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.Reserve{X.nat_field(p, 1n)}
    case False{}:
      try_clear(String.eq(n, "clear"), n, p)

def try_pop(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.Pop{}
    case False{}:
      try_reserve(String.eq(n, "reserve"), n, p)

def try_push(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.Push{X.nat_field(p, 1n)}
    case False{}:
      try_pop(String.eq(n, "pop"), n, p)

def try_set(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.Set{X.nat_field(p, 1n), X.nat_field(p, 2n)}
    case False{}:
      try_push(String.eq(n, "push"), n, p)

def try_get(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.Get{X.nat_field(p, 1n)}
    case False{}:
      try_set(String.eq(n, "set"), n, p)

def try_cap(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.Capacity{}
    case False{}:
      try_get(String.eq(n, "get"), n, p)

def try_len(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.Length{}
    case False{}:
      try_cap(String.eq(n, "cap"), n, p)

def parse_op(+n: String, +p: List<&2, String>) -> E.Op<Nat>:
  try_len(String.eq(n, "len"), n, p)

def parse(s: String) -> E.Op<Nat>:
  +p = X.fields(s)
  parse_op(X.field(p, 0n), p)

def parse_all(xs: List<&2, String>) -> List<&2, E.Op<Nat>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{parse(h), parse_all(t)}

# ---- U32 elements ----

def try_clear_u(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<U32>:
  match hit:
    case True{}:
      E.Clear{}
    case False{}:
      E.ToList{}

def try_reserve_u(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<U32>:
  match hit:
    case True{}:
      E.Reserve{X.nat_field(p, 1n)}
    case False{}:
      try_clear_u(String.eq(n, "clear"), n, p)

def try_pop_u(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<U32>:
  match hit:
    case True{}:
      E.Pop{}
    case False{}:
      try_reserve_u(String.eq(n, "reserve"), n, p)

def try_push_u(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<U32>:
  match hit:
    case True{}:
      E.Push{X.u32_field(p, 1n)}
    case False{}:
      try_pop_u(String.eq(n, "pop"), n, p)

def try_set_u(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<U32>:
  match hit:
    case True{}:
      E.Set{X.nat_field(p, 1n), X.u32_field(p, 2n)}
    case False{}:
      try_push_u(String.eq(n, "push"), n, p)

def try_get_u(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<U32>:
  match hit:
    case True{}:
      E.Get{X.nat_field(p, 1n)}
    case False{}:
      try_set_u(String.eq(n, "set"), n, p)

def try_cap_u(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<U32>:
  match hit:
    case True{}:
      E.Capacity{}
    case False{}:
      try_get_u(String.eq(n, "get"), n, p)

def try_len_u(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<U32>:
  match hit:
    case True{}:
      E.Length{}
    case False{}:
      try_cap_u(String.eq(n, "cap"), n, p)

def parse_u(s: String) -> E.Op<U32>:
  +p = X.fields(s)
  try_len_u(String.eq(X.field(p, 0n), "len"), X.field(p, 0n), p)

def parse_all_u(xs: List<&2, String>) -> List<&2, E.Op<U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{parse_u(h), parse_all_u(t)}

# ---- rendering ----

def err(e: E.Error) -> String:
  match e:
    case E.IndexOutOfRange{}:
      "ERR IndexOutOfRange"
    case E.EmptyArray{}:
      "ERR EmptyArray"
    case E.CapacityExceeded{}:
      "ERR CapacityExceeded"

def show(o: E.Obs<Nat>) -> String:
  match o:
    case E.ONat{n}:
      "N " ++ Nat.show(n)
    case E.OItem{Fail{e}}:
      err(e)
    case E.OItem{Done{x}}:
      "OK " ++ Nat.show(x)
    case E.OUnit{Fail{e}}:
      err(e)
    case E.OUnit{Done{u}}:
      "OK"
    case E.OList{xs}:
      "LIST " ++ X.join_nat(xs)

def show_u(o: E.Obs<U32>) -> String:
  match o:
    case E.ONat{n}:
      "N " ++ Nat.show(n)
    case E.OItem{Fail{e}}:
      err(e)
    case E.OItem{Done{x}}:
      "OK " ++ U32.show(x)
    case E.OUnit{Fail{e}}:
      err(e)
    case E.OUnit{Done{u}}:
      "OK"
    case E.OList{xs}:
      "LIST " ++ X.join_u32(xs)

def show_all(xs: List<&2, E.Obs<Nat>>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{show(h), show_all(t)}

def show_all_u(xs: List<&2, E.Obs<U32>>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{show_u(h), show_all_u(t)}

def result_lines(r: DA.DynArray<Nat> & List<&2, E.Obs<Nat>>) -> List<&2, String>:
  (d, outs) = r
  show_all(outs)

def result_lines_u(r: DA.DynArray<U32> & List<&2, E.Obs<U32>>) -> List<&2, String>:
  (d, outs) = r
  show_all_u(outs)

def dispatch(is_u: Bool, +lim: String, ops: List<&2, String>) -> List<&2, String>:
  match is_u:
    case True{}:
      result_lines_u(DA.run_at(~U32, parse_all_u(ops), DA.with_limit_at(~U32, X.nat_of(lim))))
    case False{}:
      result_lines(DA.run_at(~Nat, parse_all(ops), DA.with_limit_at(~Nat, X.nat_of(lim))))

def start(args: List<&2, String>) -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case Con{kind, rest}:
      match rest:
        case Nil{}:
          Nil{}
        case Con{lim, ops}:
          dispatch(String.eq(kind, "u32"), lim, ops)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(start(X.shared(args)))
