import Base
import ./example.bend as A
import ../../src/containers/intrusive_doubly_linked_list.bend as IL
import ../../src/containers/types/intrusive_doubly_linked_list.bend as E

# Reuse four application-owned entities over three pulses. The factory issues
# identities in the already reserved Array; it is only needed during prewarm.
# Each use explicitly resets the payload. Recycling alone never clears it.
# Storage from example.bend: roots 0/1, links 32+n and 64+n.
# Added fields: created count at 2, digest at 3, issued IDs at 8+serial,
# payload at 96+n. Four trusted IDs fit within the example's 31-node capacity.
def made(r: Array<U32> & U32) -> Array<U32> & A.Entity:
  (s, +old) = r
  (Array.set(U32, s, 2, (old + 1 : U32)), A.Entity{(old + 1 : U32)})

def make(s: Array<U32>, c: Unit) -> Array<U32> & A.Entity:
  made(Array.get(U32, s, 2))

def take(r: Array<U32> & E.Pool<A.Entity>) -> Array<U32> & (E.Pool<A.Entity> & A.Entity):
  (s, pool) = r
  IL.pool_next(~Array<U32>, ~A.Entity, ~Unit, ~A.next, ~A.set_next, ~make, s, pool, Unit{})

def attach(s: Array<U32>, pool: E.Pool<A.Entity>, serial: U32, value: U32, +id: U32) -> Array<U32> & E.Pool<A.Entity>:
  (A.prepend(Array.set(U32, Array.set(U32, s, (96 + id : U32), value), (8 + serial : U32), id), A.Group{0}, A.Writer{0}, A.Entity{id}), pool)

def spawned(serial: U32, value: U32, r: Array<U32> & (E.Pool<A.Entity> & A.Entity)) -> Array<U32> & E.Pool<A.Entity>:
  Tuple{s, Tuple{pool, A.Entity{id}}} = r
  attach(s, pool, serial, value, id)

def spawn(k: Nat, +pulse: U32, r: Array<U32> & E.Pool<A.Entity>) -> Array<U32> & E.Pool<A.Entity>:
  match k:
    case 0n: r
    case 1n+ +p: spawn(p, pulse, spawned(U32.from_nat(1n+p), (100 * pulse + U32.from_nat(1n+p) : U32), take(r)))

def counted(value: U32, r: Array<U32> & U32) -> Array<U32>:
  (s, digest) = r
  Array.set(U32, s, 3, (digest + value : U32))

def consumed(r: Array<U32> & U32) -> Array<U32>:
  (s, value) = r
  counted(value, Array.get(U32, s, 3))

# Process by the saved identity, then remove before reusing its next field as
# a pool link. No payload is copied or destroyed by either membership edit.
def recycle(pool: E.Pool<A.Entity>, r: Array<U32> & U32) -> Array<U32> & E.Pool<A.Entity>:
  (s, +id) = r
  IL.pool_free(~Array<U32>, ~A.Entity, ~A.set_next,
    A.remove(consumed(Array.get(U32, s, (96 + id : U32))), A.Writer{0}, A.Entity{id}), pool, A.Entity{id})

def drain(k: Nat, r: Array<U32> & E.Pool<A.Entity>) -> Array<U32> & E.Pool<A.Entity>:
  match k r:
    case 0n Tuple{s, pool}: (s, pool)
    case 1n+ +p Tuple{s, pool}: drain(p, recycle(pool, Array.get(U32, s, (8 + U32.from_nat(1n+p) : U32))))

def pulse(index: U32, r: Array<U32> & E.Pool<A.Entity>) -> Array<U32> & E.Pool<A.Entity>:
  drain(4n, spawn(4n, index, r))

def finish_count(available: Nat, digest: U32, r: Array<U32> & U32) -> String:
  (s, created) = r
  "3 pulses, 12 uses\nNodes created: " ++ U32.show(created) ++ " (all during prewarm)\nNodes available: " ++ Nat.show(available) ++ "\nPayload sum: " ++ U32.show(digest)

def finish_digest(available: Nat, r: Array<U32> & U32) -> String:
  (s, digest) = r
  finish_count(available, digest, Array.get(U32, s, 2))

def finish(r: Array<U32> & E.Pool<A.Entity>) -> String:
  (s, E.Pool{head, count}) = r
  finish_digest(count, Array.get(U32, s, 3))

def demo() -> String:
  finish(pulse(3, pulse(2, pulse(1,
    IL.pool_new(~Array<U32>, ~A.Entity, ~Unit, ~A.set_next, ~make, 4n, Array.new(U32, 7n, 0), Unit{})))))

def main() -> IO(Unit):
  IO.print(demo())
