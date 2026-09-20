import Base
import ../../src/graph.bend as G
import ../../types/graph.bend as E
import ../support/text.bend as X

# Test driver: argv = [mode, op tokens...], mode "dir" or "undir".
# Tokens: av:v | rv:v | ae:u:v | re:u:v | hv:v | he:u:v | nb:v | vs | es
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

def out(r: G.Graph & List<&2, E.Obs>) -> List<&2, String>:
  (g, os) = r
  lines(os)

def start(args: List<&2, String>) -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case Con{+mode, ops}:
      out(G.run(parse_all(ops), G.new(String.eq(mode, "dir"))))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(start(X.shared(args)))
