import Base
import ../../src/containers/hash_table.bend as H
import ../support/text.bend as X

# Test driver: argv = op tokens; keys are Strings, values U32.
# Tokens: set:k:v | get:k | has:k | pop:k | del:k | size | keys
# Output, one line per op:
#   set, del -> "OK"        get  -> "V v" (4294967295 when absent)
#   has      -> "B 0|1"     pop  -> "M v" | "M -"
#   size     -> "N n"       keys -> "K k1,k2,..." (bucket order)

def bit(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def join(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      match t:
        case Nil{}:
          h
        case Con{h2, t2}:
          h ++ "," ++ join(Con{h2, t2})

type Res is Type:
  R{m: H.HashMap<&2, U32>, line: String}

def r_get(r: H.HashMap<&2, U32> & U32) -> Res:
  (m, v) = r
  R{m, "V " ++ U32.show(v)}

def r_has(r: H.HashMap<&2, U32> & Bool) -> Res:
  (m, b) = r
  R{m, "B " ++ bit(b)}

def r_pop(r: H.HashMap<&2, U32> & Maybe<&2, U32>) -> Res:
  (m, v) = r
  match v:
    case None{}:
      R{m, "M -"}
    case Some{x}:
      R{m, "M " ++ U32.show(x)}

def r_size(r: H.HashMap<&2, U32> & U32) -> Res:
  (m, n) = r
  R{m, "N " ++ U32.show(n)}

def r_keys(r: H.HashMap<&2, U32> & List<&2, String>) -> Res:
  (m, ks) = r
  R{m, "K " ++ join(ks)}

def op_keys(m: H.HashMap<&2, U32>, hit: Bool) -> Res:
  match hit:
    case True{}:
      r_keys(H.keys(&2, U32, m))
    case False{}:
      R{m, "ERR"}

def op_size(m: H.HashMap<&2, U32>, hit: Bool, +n: String) -> Res:
  match hit:
    case True{}:
      r_size(H.size(&2, U32, m))
    case False{}:
      op_keys(m, String.eq(n, "keys"))

def op_del(m: H.HashMap<&2, U32>, hit: Bool, +n: String, +p: List<&2, String>) -> Res:
  match hit:
    case True{}:
      R{H.del(&2, U32, m, X.field(p, 1n)), "OK"}
    case False{}:
      op_size(m, String.eq(n, "size"), n)

def op_pop(m: H.HashMap<&2, U32>, hit: Bool, +n: String, +p: List<&2, String>) -> Res:
  match hit:
    case True{}:
      r_pop(H.pop(&2, U32, m, X.field(p, 1n)))
    case False{}:
      op_del(m, String.eq(n, "del"), n, p)

def op_has(m: H.HashMap<&2, U32>, hit: Bool, +n: String, +p: List<&2, String>) -> Res:
  match hit:
    case True{}:
      r_has(H.has(&2, U32, m, X.field(p, 1n)))
    case False{}:
      op_pop(m, String.eq(n, "pop"), n, p)

def op_get(m: H.HashMap<&2, U32>, hit: Bool, +n: String, +p: List<&2, String>) -> Res:
  match hit:
    case True{}:
      r_get(H.get(U32, 4294967295, m, X.field(p, 1n)))
    case False{}:
      op_has(m, String.eq(n, "has"), n, p)

def op_set(m: H.HashMap<&2, U32>, hit: Bool, +n: String, +p: List<&2, String>) -> Res:
  match hit:
    case True{}:
      R{H.set(&2, U32, m, X.field(p, 1n), X.u32_field(p, 2n)), "OK"}
    case False{}:
      op_get(m, String.eq(n, "get"), n, p)

def step(m: H.HashMap<&2, U32>, t: String) -> Res:
  +p = X.fields(t)
  +n = X.field(p, 0n)
  op_set(m, String.eq(n, "set"), n, p)

def drop_first(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

# r carries the table and the line of the previous op.
def run(xs: List<&2, String>, r: Res, acc: List<&2, String>) -> List<&2, String>:
  match xs r:
    case Nil{} R{m, line}:
      drop_first(List.reverse(&2, String, Con{line, acc}))
    case Con{t, rest} R{m, line}:
      run(rest, step(m, t), Con{line, acc})

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(run(X.shared(args), R{H.new(&2, U32), ""}, Nil{}))
