import Base
import ../../src/containers/intrusive_doubly_linked_list.bend as IL
import ../../src/containers/types/intrusive_doubly_linked_list.bend as E

# Shared application state for BOTH representations. Trusted IDs are 1..size.
# Metadata: roots 0/1, factory calls 2, digest 3, errors 4.
# Eight U32 fields per entity: next, prev, payload, handle slot, generation,
# owner, issued-ID scratch, unused. DList owns its own membership arenas;
# both drivers retain the same external entity storage and payload lifetime.
def mix(h: U32, v: U32) -> U32:
  (h * 33 + v : U32)

def lcg(r: U32) -> U32:
  (r * 1664525 + 1013904223 : U32)

def decode_pick(n: U32, zero: Bool) -> Maybe<&2, U32>:
  match zero:
    case True{}: None{}
    case False{}: Some{n}

def decode(+n: U32) -> Maybe<&2, U32>:
  decode_pick(n, U32.is_eq(n, 0))

def encode(m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}: 0
    case Some{n}: n

def read_link(r: Array<U32> & U32) -> Array<U32> & Maybe<&2, U32>:
  (s, n) = r
  (s, decode(n))

def next(s: Array<U32>, n: U32) -> Array<U32> & Maybe<&2, U32>:
  read_link(Array.get(U32, s, (8 * n : U32)))

def prev(s: Array<U32>, n: U32) -> Array<U32> & Maybe<&2, U32>:
  read_link(Array.get(U32, s, (8 * n + 1 : U32)))

def set_next(s: Array<U32>, n: U32, m: Maybe<&2, U32>) -> Array<U32>:
  Array.set(U32, s, (8 * n : U32), encode(m))

def set_prev(s: Array<U32>, n: U32, m: Maybe<&2, U32>) -> Array<U32>:
  Array.set(U32, s, (8 * n + 1 : U32), encode(m))

def get_head(s: Array<U32>, root: U32) -> Array<U32> & Maybe<&2, U32>:
  read_link(Array.get(U32, s, root))

def set_head(s: Array<U32>, root: U32, m: Maybe<&2, U32>) -> Array<U32>:
  Array.set(U32, s, root, encode(m))

def set_full(s: Array<U32>, root: U32, n: U32) -> Array<U32>:
  Array.set(U32, s, root, n)

def prepend(s: Array<U32>, root: U32, n: U32) -> Array<U32>:
  IL.prepend(~Array<U32>, ~U32, ~U32, ~get_head, ~set_next, ~set_prev, ~set_full, s, root, n)

def remove(s: Array<U32>, root: U32, n: U32) -> Array<U32>:
  IL.remove(~Array<U32>, ~U32, ~U32, ~next, ~prev, ~set_next, ~set_prev, ~set_head, s, root, n)

def made(r: Array<U32> & U32) -> Array<U32> & U32:
  (s, +old) = r
  (Array.set(U32, s, 2, (old + 1 : U32)), (old + 1 : U32))

# Storage is reserved before the benchmark. The runner bounds size and never
# exceeds it. The counter exposes any accidental factory call after prewarm.
def make(s: Array<U32>, c: Unit) -> Array<U32> & U32:
  made(Array.get(U32, s, 2))

def take(r: Array<U32> & E.Pool<U32>) -> Array<U32> & (E.Pool<U32> & U32):
  (s, pool) = r
  IL.pool_next(~Array<U32>, ~U32, ~Unit, ~next, ~set_next, ~make, s, pool, Unit{})

def release(s: Array<U32>, pool: E.Pool<U32>, n: U32) -> Array<U32> & E.Pool<U32>:
  IL.pool_free(~Array<U32>, ~U32, ~set_next, s, pool, n)

def depth(fuel: Nat, remaining: Nat) -> Nat:
  match fuel remaining:
    case _ 0n: 0n
    case 0n _: 0n
    case 1n+f 1n+p: 1n+depth(f, Nat.div(1n+p, 2n))

def fresh(+size: U32) -> Array<U32>:
  Array.new(U32, depth(32n, U32.to_nat((8 * (size + 1) - 1 : U32))), 0)

def new_pool(+size: U32) -> Array<U32> & E.Pool<U32>:
  IL.pool_new(~Array<U32>, ~U32, ~Unit, ~set_next, ~make, U32.to_nat(size), fresh(size), Unit{})

def note_result(n: U32, r: Array<U32> & U32) -> Array<U32>:
  (s, h) = r
  Array.set(U32, s, 3, mix(h, n))

def note(s: Array<U32>, n: U32) -> Array<U32>:
  note_result(n, Array.get(U32, s, 3))

def consume_value(n: U32, r: Array<U32> & U32) -> Array<U32>:
  (s, value) = r
  note(note(s, n), value)

def consume(s: Array<U32>, +n: U32) -> Array<U32>:
  consume_value(n, Array.get(U32, s, (8 * n + 2 : U32)))

def error_result(r: Array<U32> & U32) -> Array<U32>:
  (s, old) = r
  Array.set(U32, s, 4, (old + 1 : U32))

def error(s: Array<U32>) -> Array<U32>:
  error_result(Array.get(U32, s, 4))

def observe_pool(fuel: Nat, r: Array<U32> & Maybe<&2, U32>) -> Array<U32>:
  match fuel r:
    case _ Tuple{s, None{}}: s
    case 0n Tuple{s, Some{n}}: error(s)
    case 1n+p Tuple{s, Some{+n}}: observe_pool(p, next(note(s, n), n))

def finish_fields(n: Nat, s: Array<U32>) -> Array<U32>:
  match n:
    case 0n: s
    case 1n+ +p: finish_fields(p, consume(s, U32.from_nat(1n+p)))

def output3(h: U32, made: U32, r: Array<U32> & U32) -> String:
  (s, errors) = r
  U32.show(h) ++ " " ++ U32.show(made) ++ " " ++ U32.show(errors)

def output2(h: U32, r: Array<U32> & U32) -> String:
  (s, made) = r
  output3(h, made, Array.get(U32, s, 4))

def output1(r: Array<U32> & U32) -> String:
  (s, h) = r
  output2(h, Array.get(U32, s, 2))

def output(s: Array<U32>, size: U32) -> String:
  output1(Array.get(U32, finish_fields(U32.to_nat(size), s), 3))
