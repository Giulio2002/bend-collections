import Base
import ../../src/balanced_search_tree.bend as B
import ../../types/balanced_search_tree.bend as E
import ../support/text.bend as X

# Test driver: argv = [kind, op tokens...]; values are Nat.
# kind "u32" / "str"  -> one observation line per operation (see below);
# kind "rb32" / "rbstr" -> one RED-BLACK STRUCTURE line per operation, which
# re-derives the structural invariants from the tree that src/ actually
# built: black root, no red-red parent/child edge anywhere, the same number
# of black nodes on every root-to-leaf path, strictly increasing in-order
# keys, and cached size = entry count.
# Tokens: len | ins:k:v | rm:k | get:k | has:k | min | max | lb:k | range:lo:hi | list
# Output, one line per op: "N n" | "OK" | "OK v" | "OK true/false" | "OK k=v" |
# "ERR KeyNotFound" | "ERR EmptyTree" | "LIST k=v,k=v".

def err(e: E.Error) -> String:
  match e:
    case E.KeyNotFound{}:
      "ERR KeyNotFound"
    case E.EmptyTree{}:
      "ERR EmptyTree"

def show_bool(b: Bool) -> String:
  match b:
    case True{}:
      "OK true"
    case False{}:
      "OK false"

def key_u(p: List<&2, String>, i: Nat) -> U32:
  X.u32_of(X.field(p, i))

def try_list_u(hit: Bool) -> E.Op<U32, Nat>:
  match hit:
    case True{}:
      E.ToList{}
    case False{}:
      E.Length{}

def try_range_u(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<U32, Nat>:
  match hit:
    case True{}:
      E.Range{key_u(p, 1n), key_u(p, 2n)}
    case False{}:
      try_list_u(String.eq(n, "list"))

def try_lb_u(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<U32, Nat>:
  match hit:
    case True{}:
      E.LowerBound{key_u(p, 1n)}
    case False{}:
      try_range_u(String.eq(n, "range"), n, p)

def try_max_u(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<U32, Nat>:
  match hit:
    case True{}:
      E.Max{}
    case False{}:
      try_lb_u(String.eq(n, "lb"), n, p)

def try_min_u(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<U32, Nat>:
  match hit:
    case True{}:
      E.Min{}
    case False{}:
      try_max_u(String.eq(n, "max"), n, p)

def try_has_u(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<U32, Nat>:
  match hit:
    case True{}:
      E.Contains{key_u(p, 1n)}
    case False{}:
      try_min_u(String.eq(n, "min"), n, p)

def try_get_u(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<U32, Nat>:
  match hit:
    case True{}:
      E.Lookup{key_u(p, 1n)}
    case False{}:
      try_has_u(String.eq(n, "has"), n, p)

def try_rm_u(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<U32, Nat>:
  match hit:
    case True{}:
      E.Remove{key_u(p, 1n)}
    case False{}:
      try_get_u(String.eq(n, "get"), n, p)

def try_ins_u(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<U32, Nat>:
  match hit:
    case True{}:
      E.Insert{key_u(p, 1n), X.nat_field(p, 2n)}
    case False{}:
      try_rm_u(String.eq(n, "rm"), n, p)

def parse_u(t: String) -> E.Op<U32, Nat>:
  +p = X.fields(t)
  +n = X.field(p, 0n)
  try_ins_u(String.eq(n, "ins"), n, p)

def all_u(xs: List<&2, String>) -> List<&2, E.Op<U32, Nat>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{parse_u(h), all_u(t)}

def entry_u(e: E.Entry<U32, Nat>) -> String:
  match e:
    case E.Entry{k, v}:
      U32.show(k) ++ "=" ++ Nat.show(v)

def entries_u(xs: List<&2, E.Entry<U32, Nat>>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      match t:
        case Nil{}:
          entry_u(h)
        case Con{h2, t2}:
          entry_u(h) ++ "," ++ entries_u(Con{h2, t2})

def show_u(o: E.Obs<U32, Nat>) -> String:
  match o:
    case E.ONat{n}:
      "N " ++ Nat.show(n)
    case E.OUnit{}:
      "OK"
    case E.OBool{b}:
      show_bool(b)
    case E.OVal{Fail{e}}:
      err(e)
    case E.OVal{Done{v}}:
      "OK " ++ Nat.show(v)
    case E.OEntry{Fail{e}}:
      err(e)
    case E.OEntry{Done{e}}:
      "OK " ++ entry_u(e)
    case E.OList{xs}:
      "LIST " ++ entries_u(xs)

def lines_u(xs: List<&2, E.Obs<U32, Nat>>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{show_u(h), lines_u(t)}

def out_u(r: B.OrdMap<U32, Nat> & List<&2, E.Obs<U32, Nat>>) -> List<&2, String>:
  (m, os) = r
  lines_u(os)

def key_s(p: List<&2, String>, i: Nat) -> String:
  X.field(p, i)

def try_list_s(hit: Bool) -> E.Op<String, Nat>:
  match hit:
    case True{}:
      E.ToList{}
    case False{}:
      E.Length{}

def try_range_s(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<String, Nat>:
  match hit:
    case True{}:
      E.Range{key_s(p, 1n), key_s(p, 2n)}
    case False{}:
      try_list_s(String.eq(n, "list"))

def try_lb_s(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<String, Nat>:
  match hit:
    case True{}:
      E.LowerBound{key_s(p, 1n)}
    case False{}:
      try_range_s(String.eq(n, "range"), n, p)

def try_max_s(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<String, Nat>:
  match hit:
    case True{}:
      E.Max{}
    case False{}:
      try_lb_s(String.eq(n, "lb"), n, p)

def try_min_s(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<String, Nat>:
  match hit:
    case True{}:
      E.Min{}
    case False{}:
      try_max_s(String.eq(n, "max"), n, p)

def try_has_s(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<String, Nat>:
  match hit:
    case True{}:
      E.Contains{key_s(p, 1n)}
    case False{}:
      try_min_s(String.eq(n, "min"), n, p)

def try_get_s(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<String, Nat>:
  match hit:
    case True{}:
      E.Lookup{key_s(p, 1n)}
    case False{}:
      try_has_s(String.eq(n, "has"), n, p)

def try_rm_s(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<String, Nat>:
  match hit:
    case True{}:
      E.Remove{key_s(p, 1n)}
    case False{}:
      try_get_s(String.eq(n, "get"), n, p)

def try_ins_s(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<String, Nat>:
  match hit:
    case True{}:
      E.Insert{key_s(p, 1n), X.nat_field(p, 2n)}
    case False{}:
      try_rm_s(String.eq(n, "rm"), n, p)

def parse_s(t: String) -> E.Op<String, Nat>:
  +p = X.fields(t)
  +n = X.field(p, 0n)
  try_ins_s(String.eq(n, "ins"), n, p)

def all_s(xs: List<&2, String>) -> List<&2, E.Op<String, Nat>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{parse_s(h), all_s(t)}

def entry_s(e: E.Entry<String, Nat>) -> String:
  match e:
    case E.Entry{k, v}:
      k ++ "=" ++ Nat.show(v)

def entries_s(xs: List<&2, E.Entry<String, Nat>>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      match t:
        case Nil{}:
          entry_s(h)
        case Con{h2, t2}:
          entry_s(h) ++ "," ++ entries_s(Con{h2, t2})

def show_s(o: E.Obs<String, Nat>) -> String:
  match o:
    case E.ONat{n}:
      "N " ++ Nat.show(n)
    case E.OUnit{}:
      "OK"
    case E.OBool{b}:
      show_bool(b)
    case E.OVal{Fail{e}}:
      err(e)
    case E.OVal{Done{v}}:
      "OK " ++ Nat.show(v)
    case E.OEntry{Fail{e}}:
      err(e)
    case E.OEntry{Done{e}}:
      "OK " ++ entry_s(e)
    case E.OList{xs}:
      "LIST " ++ entries_s(xs)

def lines_s(xs: List<&2, E.Obs<String, Nat>>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{show_s(h), lines_s(t)}

def out_s(r: B.OrdMap<String, Nat> & List<&2, E.Obs<String, Nat>>) -> List<&2, String>:
  (m, os) = r
  lines_s(os)


# ---- red-black structural checks, recomputed from the built tree ----

def bit(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def bh_add(c: B.Color, +n: Nat) -> Nat:
  match c:
    case B.R{}:
      n
    case B.B{}:
      1n+n

def bh_pick(hit: Bool, c: B.Color, +x: Nat) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{bh_add(c, x)}
    case False{}:
      None{}

def bh_comb(c: B.Color, a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match a b:
    case None{} _:
      None{}
    case Some{x} None{}:
      None{}
    case Some{+x} Some{+y}:
      bh_pick(Nat.is_eq(x, y), c, x)

# Some h when every root-to-leaf path holds exactly h black nodes.
def bhs(-K: Data, -V: Data, t: B.Tree<K, V>) -> Maybe<&2, Nat>:
  match t:
    case B.Leaf{}:
      Some{0n}
    case B.Node{c, l, e, r}:
      bh_comb(c, bhs(K, V, l), bhs(K, V, r))

def some_b(-A: Data, m: Maybe<&2, A>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

def rr_c(-K: Data, -V: Data, c: B.Color, +l: B.Tree<K, V>, +r: B.Tree<K, V>) -> Bool:
  match c:
    case B.R{}:
      Bool.and(Bool.not(B.is_red(K, V, l)), Bool.not(B.is_red(K, V, r)))
    case B.B{}:
      True{}

def nrr(-K: Data, -V: Data, t: B.Tree<K, V>) -> Bool:
  match t:
    case B.Leaf{}:
      True{}
    case B.Node{c, +l, e, +r}:
      Bool.and(Bool.and(nrr(K, V, l), nrr(K, V, r)), rr_c(K, V, c, l, r))

def lt_flag(c: Cmp) -> Bool:
  match c:
    case LT{}:
      True{}
    case EQ{}:
      False{}
    case GT{}:
      False{}

def inc2(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, E.Entry<K, V>>, a: E.Entry<K, V>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+b, +t}:
      Bool.and(lt_flag(cmp(E.key(K, V, a), E.key(K, V, b))), inc2(~K, ~cmp, V, t, b))

def inc(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, E.Entry<K, V>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+a, t}:
      inc2(~K, ~cmp, V, t, a)

def llen(-K: Data, -V: Data, xs: List<&2, E.Entry<K, V>>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+llen(K, V, t)

def rb_line(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +n: Nat, +t: B.Tree<K, V>) -> String:
  "RB root=" ++ bit(Bool.not(B.is_red(K, V, t))) ++ " nrr=" ++ bit(nrr(K, V, t)) ++ " bh=" ++ bit(some_b(Nat, bhs(K, V, t))) ++ " ord=" ++ bit(inc(~K, ~cmp, V, B.entries(K, V, t, Nil{}))) ++ " sz=" ++ bit(Nat.is_eq(n, llen(K, V, B.entries(K, V, t, Nil{})))) ++ " n=" ++ Nat.show(n)

def rb_of(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, m: B.OrdMap<K, V>) -> String:
  match m:
    case B.BST{+n, +t}:
      rb_line(~K, ~cmp, V, n, t)

def rb_run(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, ops: List<&2, E.Op<K, V>>, m: B.OrdMap<K, V>) -> List<&2, String>:
  match ops:
    case Nil{}:
      Nil{}
    case Con{o, t}:
      +m2 = Pair.fst(B.OrdMap<K, V>, E.Obs<K, V>, B.step(~K, ~cmp, V, m, o))
      Con{rb_of(~K, ~cmp, V, m2), rb_run(~K, ~cmp, V, t, m2)}

def d_rbs(hit: Bool, ops: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      rb_run(~String, ~String.order, Nat, all_s(ops), B.new(String, Nat))
    case False{}:
      out_s(B.run_string(Nat, all_s(ops), B.new(String, Nat)))

def d_rbu(hit: Bool, +kind: String, ops: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      rb_run(~U32, ~U32.cmp, Nat, all_u(ops), B.new(U32, Nat))
    case False{}:
      d_rbs(String.eq(kind, "rbstr"), ops)

def dispatch(is_u: Bool, +kind: String, ops: List<&2, String>) -> List<&2, String>:
  match is_u:
    case True{}:
      out_u(B.run_u32(Nat, all_u(ops), B.new(U32, Nat)))
    case False{}:
      d_rbu(String.eq(kind, "rb32"), kind, ops)

def start(args: List<&2, String>) -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case Con{+kind, ops}:
      dispatch(String.eq(kind, "u32"), kind, ops)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(start(X.shared(args)))
