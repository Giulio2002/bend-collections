import Base
import ../../src/doubly_linked_list.bend as D
import ../../types/doubly_linked_list.bend as E
import ../support/text.bend as X

# Test driver: argv = [tag, op tokens...]; values are Nat, handles "list:id".
# Tokens: len | pf:x | pb:x | ib:l:i:x | ia:l:i:x | rm:l:i | get:l:i |
#         set:l:i:x | nx:l:i | pv:l:i | list
# Output, one line per op: "N n" | "H l:i" | "OK H l:i" | "OK none" | "OK v" |
# "OK" | "ERR ForeignHandle" | "ERR StaleHandle" | "LIST a,b".

def err(e: E.Error) -> String:
  match e:
    case E.ForeignHandle{}:
      "ERR ForeignHandle"
    case E.StaleHandle{}:
      "ERR StaleHandle"

def htext(h: E.Handle) -> String:
  match h:
    case E.H{l, i, g}:
      "H " ++ U32.show(l) ++ ":" ++ U32.show(i) ++ ":" ++ U32.show(g)

def show(o: E.Obs<Nat>) -> String:
  match o:
    case E.ONat{n}:
      "N " ++ Nat.show(n)
    case E.OHandle{h}:
      htext(h)
    case E.OInsert{Done{h}}:
      "OK " ++ htext(h)
    case E.OInsert{Fail{e}}:
      err(e)
    case E.OVal{Done{v}}:
      "OK " ++ Nat.show(v)
    case E.OVal{Fail{e}}:
      err(e)
    case E.OUnit{Done{u}}:
      "OK"
    case E.OUnit{Fail{e}}:
      err(e)
    case E.ONbr{Done{None{}}}:
      "OK none"
    case E.ONbr{Done{Some{h}}}:
      "OK " ++ htext(h)
    case E.ONbr{Fail{e}}:
      err(e)
    case E.OList{xs}:
      "LIST " ++ X.join_nat(xs)

def hd(+p: List<&2, String>) -> E.Handle:
  E.H{X.u32_field(p, 1n), X.u32_field(p, 2n), X.u32_field(p, 3n)}

def try_pv(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.Prev{hd(p)}
    case False{}:
      E.ToList{}

def try_nx(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.Next{hd(p)}
    case False{}:
      try_pv(String.eq(n, "pv"), n, p)

def try_set(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.Set{hd(p), X.nat_field(p, 4n)}
    case False{}:
      try_nx(String.eq(n, "nx"), n, p)

def try_get(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.Get{hd(p)}
    case False{}:
      try_set(String.eq(n, "set"), n, p)

def try_rm(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.Remove{hd(p)}
    case False{}:
      try_get(String.eq(n, "get"), n, p)

def try_ia(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.InsertAfter{hd(p), X.nat_field(p, 4n)}
    case False{}:
      try_rm(String.eq(n, "rm"), n, p)

def try_ib(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.InsertBefore{hd(p), X.nat_field(p, 4n)}
    case False{}:
      try_ia(String.eq(n, "ia"), n, p)

def try_pb(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.PushBack{X.nat_field(p, 1n)}
    case False{}:
      try_ib(String.eq(n, "ib"), n, p)

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

def out(r: D.DList<Nat> & List<&2, E.Obs<Nat>>) -> List<&2, String>:
  (s, os) = r
  lines(os)

def start(args: List<&2, String>) -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case Con{tag, ops}:
      out(D.run(~Nat, parse_all(ops), D.new(~Nat, X.u32_of(tag))))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(start(X.shared(args)))
