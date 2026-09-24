import Base
import ../../src/containers/intrusive_doubly_linked_list.bend as L

# A fixed-capacity application's fields, with 0 reserved for null.
# Slots 0/1 are roots, 32+n is next, 64+n is prev; nodes are 1..31.
# Only the setup allocates this block. No payload is moved during transfers.
def decode_pick(+n: U32, zero: Bool) -> Maybe<&2, U32>:
  match zero:
    case True{}: None{}
    case False{}: Some{n}

def decode(+n: U32) -> Maybe<&2, U32>:
  decode_pick(n, U32.is_eq(n, 0))

def encode(m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}: 0
    case Some{n}: n

def read_result(r: Array<U32> & U32) -> Array<U32> & Maybe<&2, U32>:
  (s, n) = r
  (s, decode(n))

def next(s: Array<U32>, n: U32) -> Array<U32> & Maybe<&2, U32>:
  read_result(Array.get(U32, s, (32 + n : U32)))

def prev(s: Array<U32>, n: U32) -> Array<U32> & Maybe<&2, U32>:
  read_result(Array.get(U32, s, (64 + n : U32)))

def set_next(s: Array<U32>, n: U32, m: Maybe<&2, U32>) -> Array<U32>:
  Array.set(U32, s, (32 + n : U32), encode(m))

def set_prev(s: Array<U32>, n: U32, m: Maybe<&2, U32>) -> Array<U32>:
  Array.set(U32, s, (64 + n : U32), encode(m))

def get_head(s: Array<U32>, root: U32) -> Array<U32> & Maybe<&2, U32>:
  read_result(Array.get(U32, s, root))

def set_head(s: Array<U32>, root: U32, m: Maybe<&2, U32>) -> Array<U32>:
  Array.set(U32, s, root, encode(m))

def set_full(s: Array<U32>, root: U32, n: U32) -> Array<U32>:
  Array.set(U32, s, root, n)

def prepend(s: Array<U32>, root: U32, n: U32) -> Array<U32>:
  L.prepend(~Array<U32>, ~U32, ~U32, ~get_head, ~set_next, ~set_prev, ~set_full, s, root, n)

def remove(s: Array<U32>, root: U32, n: U32) -> Array<U32>:
  L.remove(~Array<U32>, ~U32, ~U32, ~next, ~prev, ~set_next, ~set_prev, ~set_head, s, root, n)

# Four edits per iteration; a changing node makes each round observable in
# the final order. The measurement brackets only this compiled function.
def round(s: Array<U32>, +node: U32) -> Array<U32>:
  prepend(remove(prepend(remove(s, 0, node), 1, node), 1, node), 0, node)

def churn(churn_iterations: Nat, s: Array<U32>, +rng: U32) -> Array<U32>:
  match churn_iterations:
    case 0n: s
    case 1n+p:
      churn(p, round(s, (1 + rng % 31 : U32)), (rng * 1664525 + 1013904223 : U32))

def setup(+n: Nat, s: Array<U32>) -> Array<U32>:
  match n:
    case 0n: s
    case 1n+p: setup(p, prepend(s, 0, U32.from_nat(1n+p)))

def hash_step(h: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  (s, v) = r
  (s, (h * 33 + v : U32))

def checksum(+n: Nat, r: Array<U32> & U32) -> U32:
  match n r:
    case 0n Tuple{s, h}: h
    case 1n+p Tuple{s, h}: checksum(p, hash_step(h, Array.get(U32, s, U32.from_nat(p))))

def main() -> U32:
  checksum(128n, (churn(100000n, setup(31n, Array.new(U32, 7n, 0)), 1), 0))
