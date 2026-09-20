import Base
import ../../src/prefix_trie.bend as P
import ../../types/prefix_trie.bend as E
import ../../types/balanced_search_tree.bend as BE
import ../support/text.bend as X

# Test driver: argv = op tokens; keys are Strings (possibly empty), values Nat.
# Tokens: ins:k:v | get:k | rm:k | has:k | pre:p | lp:text
# Output, one line per op: "OK" | "OK v" | "ERR KeyNotFound" |
# "OK true/false" | "LIST k=v,k=v" | "OK k=v".

def show_bool(b: Bool) -> String:
  match b:
    case True{}:
      "OK true"
    case False{}:
      "OK false"

def entry_text(e: BE.Entry<String, Nat>) -> String:
  match e:
    case BE.Entry{k, v}:
      k ++ "=" ++ Nat.show(v)

def entries_text(xs: List<&2, BE.Entry<String, Nat>>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      match t:
        case Nil{}:
          entry_text(h)
        case Con{h2, t2}:
          entry_text(h) ++ "," ++ entries_text(Con{h2, t2})

def show(o: E.Obs<Nat>) -> String:
  match o:
    case E.OUnit{}:
      "OK"
    case E.OVal{Fail{e}}:
      "ERR KeyNotFound"
    case E.OVal{Done{v}}:
      "OK " ++ Nat.show(v)
    case E.OBool{b}:
      show_bool(b)
    case E.OList{xs}:
      "LIST " ++ entries_text(xs)
    case E.OEntry{Fail{e}}:
      "ERR KeyNotFound"
    case E.OEntry{Done{e}}:
      "OK " ++ entry_text(e)

def try_lp(hit: Bool, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.LongestPrefix{X.field(p, 1n)}
    case False{}:
      E.Contains{X.field(p, 1n)}

def try_pre(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.PrefixEntries{X.field(p, 1n)}
    case False{}:
      try_lp(String.eq(n, "lp"), p)

def try_rm(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.Remove{X.field(p, 1n)}
    case False{}:
      try_pre(String.eq(n, "pre"), n, p)

def try_get(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.Lookup{X.field(p, 1n)}
    case False{}:
      try_rm(String.eq(n, "rm"), n, p)

def try_ins(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op<Nat>:
  match hit:
    case True{}:
      E.Insert{X.field(p, 1n), X.nat_field(p, 2n)}
    case False{}:
      try_get(String.eq(n, "get"), n, p)

def parse(t: String) -> E.Op<Nat>:
  +p = X.fields(t)
  +n = X.field(p, 0n)
  try_ins(String.eq(n, "ins"), n, p)

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

def out(r: P.PrefixTrie<Nat> & List<&2, E.Obs<Nat>>) -> List<&2, String>:
  (s, os) = r
  lines(os)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(out(P.run(Nat, parse_all(X.shared(args)), P.new(Nat))))
