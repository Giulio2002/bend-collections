import Base
import ../../src/containers/intrusive_doubly_linked_list.bend as L
import ../../src/containers/types/intrusive_doubly_linked_list.bend as E
import ./churn.bend as C

# The pool starts populated. Its factory is never reached in the timed loop.
def make(s: Array<U32>, c: Unit) -> Array<U32> & U32:
  (s, 31)

def take(r: Array<U32> & E.Pool<U32>) -> Array<U32> & (E.Pool<U32> & U32):
  (s, pool) = r
  L.pool_next(~Array<U32>, ~U32, ~Unit, ~C.next, ~C.set_next, ~make, s, pool, Unit{})

def step(+rng: U32, r: Array<U32> & (E.Pool<U32> & U32)) -> Array<U32> & (E.Pool<U32> & U32):
  Tuple{s, Tuple{pool, old}} = r
  take(L.pool_free(~Array<U32>, ~U32, ~C.set_next, s, pool, (2 + rng % 30 : U32)))

def churn(churn_iterations: Nat, r: Array<U32> & (E.Pool<U32> & U32), +rng: U32) -> Array<U32> & (E.Pool<U32> & U32):
  match churn_iterations:
    case 0n: r
    case 1n+p: churn(p, step(rng, r), (rng * 1664525 + 1013904223 : U32))

def result(r: Array<U32> & (E.Pool<U32> & U32)) -> U32:
  Tuple{s, Tuple{pool, node}} = r
  node

def main() -> U32:
  result(churn(100000n, (Array.new(U32, 7n, 0), (E.Pool{Some{1}, 1n}, 0)), 1))
