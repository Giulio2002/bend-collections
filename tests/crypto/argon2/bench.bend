import Base
import ../../../src/crypto/argon2/types.bend as A
import ../../../src/crypto/argon2/blamka.bend as G
import ../../../src/crypto/argon2/memory.bend as M
import ../../../src/crypto/argon2/argon2.bend as A2
import ../../support/text.bend as X

# Micro-benchmarks: "compress n", "memory n k", "full t m p".

def comp_go(n: Nat, x: A.Block, +y: A.Block) -> A.Block:
  match n:
    case 0n:
      x
    case 1n+p:
      comp_go(p, G.compress(x, y), y)

def mem_fin(n: Nat, +k: Nat, +mask: Nat, pair: Array<U32> & A.Block) -> Array<U32>:
  match n pair:
    case 0n Tuple{a, b}:
      a
    case 1n+ +p Tuple{a, b}:
      mem_fin(p, k, mask, M.get(Nat.mod(Nat.mul(p, 7n), mask), M.set(Nat.mod(p, mask), b, a)))

def lane0(b: A.Block) -> String:
  U32.show(G.lo(A2.lane(b, 0n)))

def done(a: Array<U32>) -> String:
  "done"

def run_pick(c: Bool, +n: Nat, +k: Nat) -> String:
  match c:
    case True{}:
      lane0(comp_go(n, A2.input_block(1n, 2n, 3n, 4n, 5n, 6n), A2.input_block(6n, 5n, 4n, 3n, 2n, 1n)))
    case False{}:
      done(mem_fin(n, k, M.pw(k), M.get(0n, M.new(k))))

def run_op(+op: String, +n: Nat, +k: Nat) -> String:
  run_pick(String.eq(op, "compress"), n, k)

def run(ts: List<&2, String>) -> String:
  match ts:
    case Nil{}:
      "usage"
    case t <> rest:
      +f = X.fields(t)
      run_op(X.field(f, 0n), X.nat_field(f, 1n), X.nat_field(f, 2n))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    IO.print(run(X.program_args(args)))
