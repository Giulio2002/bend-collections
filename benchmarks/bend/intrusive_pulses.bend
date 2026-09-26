import Base
import ./common.bend as B
import ./intrusive_support.bend as A
import ../../src/containers/types/intrusive_doubly_linked_list.bend as E

# The whole lifecycle is measured: take -> reset payload -> attach -> process
# by saved identity -> detach -> recycle. Both drivers use the same entity
# pool. The DList variant differs only in its membership representation.
def attach(s: Array<U32>, pool: E.Pool<U32>, serial: U32, value: U32, +n: U32) -> Array<U32> & E.Pool<U32>:
  (A.prepend(Array.set(U32, Array.set(U32, s, (8 * n + 2 : U32), value), (8 * serial + 6 : U32), n), 0, n), pool)

def spawned(serial: U32, value: U32, r: Array<U32> & (E.Pool<U32> & U32)) -> Array<U32> & E.Pool<U32>:
  match r:
    case Tuple{s, Tuple{pool, n}}: attach(s, pool, serial, value, n)

def spawn(k: Nat, +seed: U32, r: Array<U32> & E.Pool<U32>) -> Array<U32> & E.Pool<U32>:
  match k:
    case 0n: r
    case 1n+ +p: spawn(p, A.lcg(seed), spawned(U32.from_nat(1n+p), seed, A.take(r)))

def recycle(pool: E.Pool<U32>, r: Array<U32> & U32) -> Array<U32> & E.Pool<U32>:
  (s, +n) = r
  A.release(A.remove(A.consume(s, n), 0, n), pool, n)

def drain(k: Nat, r: Array<U32> & E.Pool<U32>) -> Array<U32> & E.Pool<U32>:
  match k r:
    case 0n Tuple{s, pool}: (s, pool)
    case 1n+ +p Tuple{s, pool}:
      drain(p, recycle(pool, Array.get(U32, s, (8 * U32.from_nat(1n+p) + 6 : U32))))

def pulse(+size: Nat, seed: U32, r: Array<U32> & E.Pool<U32>) -> Array<U32> & E.Pool<U32>:
  drain(size, spawn(size, seed, r))

def churn(churn_iterations: Nat, +size: Nat, r: Array<U32> & E.Pool<U32>, +rng: U32) -> Array<U32> & E.Pool<U32>:
  match churn_iterations:
    case 0n: r
    case 1n+ +p: churn(p, size, pulse(size, rng, r), A.lcg(rng))

def reset(r: Array<U32> & E.Pool<U32>) -> Array<U32> & E.Pool<U32>:
  (s, pool) = r
  (Array.set(U32, s, 3, 0), pool)

def empty_output(size: U32, r: Array<U32> & U32) -> String:
  (s, root) = r
  A.output(A.note(s, root), size)

def output(+size: U32, r: Array<U32> & E.Pool<U32>) -> String:
  (s, E.Pool{head, count}) = r
  empty_output(size, Array.get(U32, A.observe_pool(U32.to_nat(size), (A.note(s, U32.from_nat(count)), head)), 0))

def go(+g: B.Args) -> String:
  +size : U32 = B.a_size(g)
  output(size, churn(U32.to_nat(B.a_count(g)), U32.to_nat(size), reset(pulse(U32.to_nat(size), 0, A.new_pool(size))), B.a_seed(g)))

def main() -> IO(Unit):
  do IO<Unit>:
    raw : List<String> <- IO.args()
    IO.print(go(B.parse(raw)))
