import Base
import ./common.bend as B
import ./intrusive_support.bend as A

# One transfer, not a move-out-and-back pair: the two roots retain different
# changing orders. Payloads and stable entity IDs survive every transfer.
def move_owner(+n: U32, r: Array<U32> & U32) -> Array<U32>:
  (s, +owner) = r
  Array.set(U32, A.prepend(A.remove(s, owner, n), (1 - owner : U32), n), (8 * n + 5 : U32), (1 - owner : U32))

def move(s: Array<U32>, +n: U32) -> Array<U32>:
  move_owner(n, Array.get(U32, s, (8 * n + 5 : U32)))

# The emitted-C runner brackets this function only. Inputs are runtime argv.
def churn(churn_iterations: Nat, +size: U32, s: Array<U32>, +rng: U32) -> Array<U32>:
  match churn_iterations:
    case 0n: s
    case 1n+ +p: churn(p, size, move(s, (1 + rng / 256 % size : U32)), A.lcg(rng))

def setup(n: Nat, s: Array<U32>) -> Array<U32>:
  match n:
    case 0n: s
    case 1n+ +p:
      setup(p, A.prepend(Array.set(U32, s, (8 * U32.from_nat(1n+p) + 2 : U32), A.mix(U32.from_nat(1n+p), 17)), 0, U32.from_nat(1n+p)))

def observe_step(fuel: Nat, r: Array<U32> & U32) -> Array<U32>:
  match fuel r:
    case _ Tuple{s, 0}: s
    case 0n Tuple{s, n}: A.error(s)
    case 1n+ +p Tuple{s, +n}:
      observe_step(p, Array.get(U32, A.note(s, n), (8 * n : U32)))

def observe(s: Array<U32>, root: U32, size: U32) -> Array<U32>:
  observe_step(U32.to_nat(size), Array.get(U32, A.note(s, 4294967295), root))

def go(+g: B.Args) -> String:
  +size : U32 = B.a_size(g)
  s : Array<U32> = churn(U32.to_nat(B.a_count(g)), size, setup(U32.to_nat(size), A.fresh(size)), B.a_seed(g))
  A.output(observe(observe(s, 0, size), 1, size), size)

def main() -> IO(Unit):
  do IO<Unit>:
    raw : List<String> <- IO.args()
    IO.print(go(B.parse(raw)))
