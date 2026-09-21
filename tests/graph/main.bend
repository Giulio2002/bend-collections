import Base
import ../../src/graph.bend as G
import ../../types/graph.bend as E
import ../support/text.bend as X

# Test driver: argv = [mode, op tokens...], mode "dir" or "undir".
# Tokens: av:v | rv:v | ae:u:v | re:u:v | hv:v | he:u:v | nb:v | vs | vb | es
#
# `vs` observes the vertices through the LIST form `G.vertices` (the trace
# runner's `E.Vertices` step); `vb` observes exactly the same sequence
# through the public BLOCK form `G.vertices_block` and prints the identical
# "LIST ..." line, so the oracle answers both the same way and a mutation of
# either enumeration is rejected. The driver folds `G.step` over the tokens
# (`G.run` is the same fold, and is exercised by the trace proof).
# Output, one line per op: "OK" | "ERR <Error>" | "BOOL true/false" |
# "OK true/false" | "LIST a,b" | "EDGES u-v,u-v".

def err(e: E.Error) -> String:
  match e:
    case E.VertexExists{}:
      "ERR VertexExists"
    case E.VertexNotFound{}:
      "ERR VertexNotFound"
    case E.SelfLoop{}:
      "ERR SelfLoop"
    case E.EdgeNotFound{}:
      "ERR EdgeNotFound"

def bool_text(b: Bool) -> String:
  match b:
    case True{}:
      "true"
    case False{}:
      "false"

def edge_text(e: E.Edge) -> String:
  match e:
    case E.Edge{u, v}:
      U32.show(u) ++ "-" ++ U32.show(v)

def edges_text(xs: List<&2, E.Edge>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      match t:
        case Nil{}:
          edge_text(h)
        case Con{h2, t2}:
          edge_text(h) ++ "," ++ edges_text(Con{h2, t2})

def show(o: E.Obs) -> String:
  match o:
    case E.OUnit{Done{u}}:
      "OK"
    case E.OUnit{Fail{e}}:
      err(e)
    case E.OBool{b}:
      "BOOL " ++ bool_text(b)
    case E.OFlag{Done{b}}:
      "OK " ++ bool_text(b)
    case E.OFlag{Fail{e}}:
      err(e)
    case E.ONeighbors{Done{xs}}:
      "LIST " ++ X.join_u32(xs)
    case E.ONeighbors{Fail{e}}:
      err(e)
    case E.OVertices{xs}:
      "LIST " ++ X.join_u32(xs)
    case E.OEdges{xs}:
      "EDGES " ++ edges_text(xs)

def u(p: List<&2, String>, i: Nat) -> U32:
  X.u32_field(p, i)

def try_vs(hit: Bool) -> E.Op:
  match hit:
    case True{}:
      E.Vertices{}
    case False{}:
      E.Edges{}

def try_nb(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.Neighbors{u(p, 1n)}
    case False{}:
      try_vs(String.eq(n, "vs"))

def try_he(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.HasEdge{u(p, 1n), u(p, 2n)}
    case False{}:
      try_nb(String.eq(n, "nb"), n, p)

def try_hv(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.HasVertex{u(p, 1n)}
    case False{}:
      try_he(String.eq(n, "he"), n, p)

def try_re(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.RemoveEdge{u(p, 1n), u(p, 2n)}
    case False{}:
      try_hv(String.eq(n, "hv"), n, p)

def try_ae(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.AddEdge{u(p, 1n), u(p, 2n)}
    case False{}:
      try_re(String.eq(n, "re"), n, p)

def try_rv(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.RemoveVertex{u(p, 1n)}
    case False{}:
      try_ae(String.eq(n, "ae"), n, p)

def try_av(hit: Bool, +n: String, +p: List<&2, String>) -> E.Op:
  match hit:
    case True{}:
      E.AddVertex{u(p, 1n)}
    case False{}:
      try_rv(String.eq(n, "rv"), n, p)

def parse(t: String) -> E.Op:
  +p = X.fields(t)
  +n = X.field(p, 0n)
  try_av(String.eq(n, "av"), n, p)

def parse_all(xs: List<&2, String>) -> List<&2, E.Op>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{parse(h), parse_all(t)}

def lines(xs: List<&2, E.Obs>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{show(h), lines(t)}

# ---- the block enumeration, read by index ----

def blk_go(k: Nat, acc: List<&2, U32>, +j: U32, r: Array<U32> & U32) -> Array<U32> & List<&2, U32>:
  match k r:
    case 0n Tuple{a, x}:
      (a, acc)
    case 1n+m Tuple{a, +x}:
      blk_go(m, Con{x, acc}, U32.sub(j, 1), Array.get(U32, a, U32.sub(j, 1)))

def blk_fin(g: G.Graph, r: Array<U32> & List<&2, U32>) -> G.Graph & String:
  (a, xs) = r
  (g, "LIST " ++ X.join_u32(xs))

def blk_line(v: G.VBlk) -> G.Graph & String:
  G.VB{g, blk, +n} = v
  blk_fin(g, blk_go(U32.to_nat(n), Nil{}, U32.sub(n, 1), Array.get(U32, blk, U32.sub(n, 1))))

# ---- one token ----

type Acc is Type:
  A{g: G.Graph, out: List<&2, String>}

def acc_line(acc: List<&2, String>, r: G.Graph & String) -> Acc:
  (g, l) = r
  A{g, Con{l, acc}}

def acc_step(acc: List<&2, String>, r: G.Graph & E.Obs) -> Acc:
  (g, o) = r
  A{g, Con{show(o), acc}}

def do_tok(is_vb: Bool, g: G.Graph, acc: List<&2, String>, +t: String) -> Acc:
  match is_vb:
    case True{}:
      acc_line(acc, blk_line(G.vertices_block(g)))
    case False{}:
      acc_step(acc, G.step(g, parse(t)))

def tok_at(+t: String, a: Acc) -> Acc:
  A{g, acc} = a
  do_tok(String.eq(X.field(X.fields(t), 0n), "vb"), g, acc, t)

def fold_toks(xs: List<&2, String>, a: Acc) -> Acc:
  match xs:
    case Nil{}:
      a
    case Con{+t, rest}:
      fold_toks(rest, tok_at(t, a))

def out(a: Acc) -> List<&2, String>:
  A{g, acc} = a
  List.reverse(&2, String, acc)

def out_run(r: G.Graph & List<&2, E.Obs>) -> List<&2, String>:
  (g, os) = r
  lines(os)

def has_vb(xs: List<&2, String>, acc: Bool) -> Bool:
  match xs:
    case Nil{}:
      acc
    case Con{+t, rest}:
      has_vb(rest, Bool.or(acc, String.eq(X.field(X.fields(t), 0n), "vb")))

# Without a `vb` token every scenario goes through the public trace runner
# `G.run` exactly as before; a scenario that observes the block enumeration
# folds `G.step` itself (`G.run` IS that fold followed by a reverse).
def pick_run(vb: Bool, +dir: Bool, ops: List<&2, String>) -> List<&2, String>:
  match vb:
    case True{}:
      out(fold_toks(ops, A{G.new(dir), Nil{}}))
    case False{}:
      out_run(G.run(parse_all(ops), G.new(dir)))

def start(args: List<&2, String>) -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case Con{+mode, +ops}:
      pick_run(has_vb(ops, False{}), String.eq(mode, "dir"), ops)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(start(X.shared(args)))
