import Base
import ../../src/containers/doubly_linked_list.bend as D
import ../../src/containers/types/doubly_linked_list.bend as E
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

def val_obs(r: D.DList<Nat> & Result<&2, &2, E.Error, Nat>) -> D.DList<Nat> & E.Obs<Nat>:
  (s, x) = r
  (s, E.OVal{x})

def unit_obs(r: D.DList<Nat> & Result<&2, &2, E.Error, Unit>) -> D.DList<Nat> & E.Obs<Nat>:
  (s, x) = r
  (s, E.OUnit{x})

def insert_obs(r: D.DList<Nat> & Result<&2, &2, E.Error, E.Handle>) -> D.DList<Nat> & E.Obs<Nat>:
  (s, x) = r
  (s, E.OInsert{x})

def neighbour_obs(r: D.DList<Nat> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>) -> D.DList<Nat> & E.Obs<Nat>:
  (s, x) = r
  (s, E.ONbr{x})

def len_obs(r: D.DList<Nat> & Nat) -> D.DList<Nat> & E.Obs<Nat>:
  (s, x) = r
  (s, E.ONat{x})

def list_obs(r: D.DList<Nat> & List<&2, Nat>) -> D.DList<Nat> & E.Obs<Nat>:
  (s, x) = r
  (s, E.OList{x})

def handle_obs(r: D.DList<Nat> & E.Handle) -> D.DList<Nat> & E.Obs<Nat>:
  (s, x) = r
  (s, E.OHandle{x})

def public_step(s: D.DList<Nat>, op: E.Op<Nat>) -> D.DList<Nat> & E.Obs<Nat>:
  match op:
    case E.Get{h}:
      val_obs(D.get(~Nat, s, h))
    case E.Set{h, x}:
      unit_obs(D.set(~Nat, s, h, x))
    case E.Remove{h}:
      val_obs(D.remove(~Nat, s, h))
    case E.Next{h}:
      neighbour_obs(D.next(~Nat, s, h))
    case E.Prev{h}:
      neighbour_obs(D.prev(~Nat, s, h))
    case E.InsertBefore{h, x}:
      insert_obs(D.insert_before(~Nat, s, h, x))
    case E.InsertAfter{h, x}:
      insert_obs(D.insert_after(~Nat, s, h, x))
    case E.PushFront{x}:
      handle_obs(D.push_front(~Nat, s, x))
    case E.PushBack{x}:
      handle_obs(D.push_back(~Nat, s, x))
    case E.Length{}:
      len_obs(D.length(~Nat, s))
    case E.ToList{}:
      list_obs(D.to_list(~Nat, s))

def public_record(acc: List<&2, E.Obs<Nat>>, r: D.DList<Nat> & E.Obs<Nat>) -> D.DList<Nat> & List<&2, E.Obs<Nat>>:
  (s, o) = r
  (s, Con{o, acc})

def public_step_acc(op: E.Op<Nat>, r: D.DList<Nat> & List<&2, E.Obs<Nat>>) -> D.DList<Nat> & List<&2, E.Obs<Nat>>:
  (s, acc) = r
  public_record(acc, public_step(s, op))

def public_run(ops: List<&2, E.Op<Nat>>, r: D.DList<Nat> & List<&2, E.Obs<Nat>>) -> D.DList<Nat> & List<&2, E.Obs<Nat>>:
  match ops:
    case Nil{}:
      D.finish(~Nat, r)
    case Con{op, tail}:
      public_run(tail, public_step_acc(op, r))

def start(args: List<&2, String>) -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case Con{tag, ops}:
      out(public_run(parse_all(ops), (D.new(~Nat, X.u32_of(tag)), Nil{})))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(start(X.shared(args)))
