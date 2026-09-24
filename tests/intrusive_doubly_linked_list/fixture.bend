import Base
import ../../src/containers/compat/intrusive_doubly_linked_list.bend as L
import ../../src/containers/types/intrusive_doubly_linked_list.bend as E
import ./churn.bend as C
import ../support/text.bend as X

# Two independent associations, four roots, distinct read/write contexts.
# Fixed identities 1..31. The fixture logs root hooks and user callbacks.
type Reader is Data:
  Room{id: U32}
type Writer is Data:
  Commander{id: U32}
type World is Type:
  W{cells: Array<U32>, log: List<&2, U32>, fresh: U32, pool: E.Pool<U32>}

def record(s: World, event: U32) -> World:
  W{a, log, fresh, pool} = s
  W{a, Con{event, log}, fresh, pool}

def read_done(log: List<&2, U32>, fresh: U32, pool: E.Pool<U32>, r: Array<U32> & U32) -> World & U32:
  (a, v) = r
  (W{a, log, fresh, pool}, v)

def read(s: World, index: U32) -> World & U32:
  W{a, log, fresh, pool} = s
  read_done(log, fresh, pool, Array.get(U32, a, index))

def write(s: World, index: U32, v: U32) -> World:
  W{a, log, fresh, pool} = s
  W{Array.set(U32, a, index, v), log, fresh, pool}

def link_result(r: World & U32) -> World & Maybe<&2, U32>:
  (s, v) = r
  (s, C.decode(v))

def next(s: World, n: U32) -> World & Maybe<&2, U32>:
  link_result(read(s, (32 + n : U32)))

def set_next(s: World, n: U32, m: Maybe<&2, U32>) -> World:
  write(s, (32 + n : U32), C.encode(m))

def prev(s: World, n: U32) -> World & Maybe<&2, U32>:
  link_result(read(s, (64 + n : U32)))

def set_prev(s: World, n: U32, m: Maybe<&2, U32>) -> World:
  write(s, (64 + n : U32), C.encode(m))

def next2(s: World, n: U32) -> World & Maybe<&2, U32>:
  link_result(read(s, (96 + n : U32)))

def set_next2(s: World, n: U32, m: Maybe<&2, U32>) -> World:
  write(s, (96 + n : U32), C.encode(m))

def prev2(s: World, n: U32) -> World & Maybe<&2, U32>:
  link_result(read(s, (128 + n : U32)))

def set_prev2(s: World, n: U32, m: Maybe<&2, U32>) -> World:
  write(s, (128 + n : U32), C.encode(m))

def value(s: World, n: U32) -> World & U32:
  read(s, (160 + n : U32))

def get_head(s: World, h: Reader) -> World & Maybe<&2, U32>:
  Room{id} = h
  link_result(read(s, id))

def set_maybe(s: World, +id: U32, +n: U32) -> World:
  record(write(s, id, n), (1000 + id * 100 + n : U32))

def set_head(s: World, i: Writer, m: Maybe<&2, U32>) -> World:
  Commander{+id} = i
  set_maybe(s, id, C.encode(m))

def set_full(s: World, i: Writer, +n: U32) -> World:
  Commander{+id} = i
  record(write(s, id, n), (2000 + id * 100 + n : U32))

def set_same(s: World, h: Reader, m: Maybe<&2, U32>) -> World:
  Room{id} = h
  set_head(s, Commander{id}, m)

def full_same(s: World, h: Reader, n: U32) -> World:
  Room{id} = h
  set_full(s, Commander{id}, n)

def prepend(s: World, +root: U32, n: U32) -> World:
  L.prepend_as(~World, ~U32, ~Reader, ~Writer, ~get_head, ~set_next, ~set_prev, ~(s => i => n => set_full(s, i, n)), s, Room{root}, Commander{root}, n)

def remove(s: World, root: U32, n: U32) -> World:
  L.remove(~World, ~U32, ~Writer, ~next, ~prev, ~set_next, ~set_prev, ~set_head, s, Commander{root}, n)

def prepend2(s: World, +root: U32, n: U32) -> World:
  L.prepend_as(~World, ~U32, ~Reader, ~Writer, ~get_head, ~set_next2, ~set_prev2, ~(s => i => n => set_full(s, i, n)), s, Room{root}, Commander{root}, n)

def remove2(s: World, root: U32, n: U32) -> World:
  L.remove(~World, ~U32, ~Writer, ~next2, ~prev2, ~set_next2, ~set_prev2, ~set_head, s, Commander{root}, n)

def visit(s: World, c: U32, +v: U32) -> World:
  record(s, (3000 + v : U32))

def visit_remove(s: World, root: U32, +v: U32) -> World:
  remove(record(s, (3000 + v : U32)), root, v)

def after_remove(s: World, c: U32, +n: U32) -> World:
  record(s, (7000 + n : U32))

def predicate_pick(s: World, +c: U32, +v: U32, change: Bool) -> World & Bool:
  match change:
    case True{}: (remove(s, 0, v), False{})
    case False{}: (s, Bool.or(U32.is_eq(c, 1), Bool.or(U32.is_eq(c, 3), Bool.and(U32.is_eq(c, 0), U32.is_eq((v % 2 : U32), 0)))))

def predicate(s: World, +c: U32, +v: U32) -> World & Bool:
  predicate_pick(record(s, (4000 + v : U32)), c, v, Bool.and(U32.is_eq(c, 3), U32.is_eq(v, 1)))

def convert_pick(s: World, v: U32, even: Bool) -> World & Maybe<&2, U32>:
  match even:
    case True{}: (s, Some{(v * 10 : U32)})
    case False{}: (s, None{})

def convert(s: World, +v: U32) -> World & Maybe<&2, U32>:
  convert_pick(record(s, (5000 + v : U32)), v, U32.is_eq((v % 2 : U32), 0))

def sum(s: World, c: U32, acc: U32, +v: U32) -> World & U32:
  (record(s, (3000 + v : U32)), (acc + v : U32))

def mapped(s: World, c: U32, +v: U32) -> World & U32:
  (record(s, (3000 + v : U32)), (v * 10 : U32))

def flat_pick(s: World, v: U32, even: Bool) -> World & Maybe<U32>:
  match even:
    case True{}: (s, Some{(v * 10 : U32)})
    case False{}: (s, None{})

def flat(s: World, c: U32, +v: U32) -> World & Maybe<U32>:
  flat_pick(record(s, (3000 + v : U32)), v, U32.is_eq((v % 2 : U32), 0))

def make(s: World, c: U32, +v: U32) -> World & U32:
  W{a, log, +fresh, pool} = s
  (W{Array.set(U32, a, (160 + fresh : U32), v), Con{(6000 + v : U32), log}, (fresh + 1 : U32), pool}, fresh)

def make_empty(s: World, c: U32) -> World & U32:
  make(s, c, 0)

def free_done(r: World & E.Pool<U32>) -> World:
  (s, pool) = r
  W{a, log, fresh, old} = s
  W{a, log, fresh, pool}

def free(s: World, c: U32, +n: U32) -> World:
  W{a, log, fresh, pool} = s
  free_done(L.pool_free(~World, ~U32, ~set_next, record(W{a, log, fresh, E.Pool{None{}, 0n}}, (7000 + n : U32)), pool, n))

def take_done(r: World & (E.Pool<U32> & U32)) -> World & U32:
  Tuple{W{a, log, fresh, old}, Tuple{pool, n}} = r
  (W{a, log, fresh, pool}, n)

def take(s: World) -> World & U32:
  W{a, log, fresh, pool} = s
  take_done(L.pool_next(~World, ~U32, ~U32, ~next, ~set_next, ~make_empty, W{a, log, fresh, E.Pool{None{}, 0n}}, pool, 0))

def pool_new(s: World, size: Nat) -> World:
  free_done(L.pool_new(~World, ~U32, ~U32, ~set_next, ~make_empty, size, s, 0))

def init_nodes(+n: Nat, s: World) -> World:
  match n:
    case 0n: s
    case 1n+p: init_nodes(p, write(s, (160 + U32.from_nat(1n+p) : U32), U32.from_nat(1n+p)))

def new() -> World:
  init_nodes(16n, W{Array.new(U32, 8n, 0), Nil{}, 17, E.Pool{None{}, 0n}})

# Include every root/link/payload field and callback event in observations.
def scan_step(xs: List<&2, U32>, r: Array<U32> & U32) -> Array<U32> & List<&2, U32>:
  (a, v) = r
  (a, Con{v, xs})

def scan(+n: Nat, r: Array<U32> & List<&2, U32>) -> Array<U32> & List<&2, U32>:
  match n r:
    case 0n Tuple{a, xs}: (a, xs)
    case 1n+p Tuple{a, xs}: scan(p, scan_step(xs, Array.get(U32, a, U32.from_nat(p))))

def snap_done(log: List<&2, U32>, +fresh: U32, pool: E.Pool<U32>, +out: String, r: Array<U32> & List<&2, U32>) -> World & String:
  match pool r:
    case E.Pool{+head, +count} Tuple{a, xs}:
      (W{a, Nil{}, fresh, E.Pool{head, count}}, out ++ "|" ++ X.join_u32(xs) ++ "|" ++ X.join_u32(List.reverse(&2, U32, log)) ++ "|" ++ U32.show(fresh) ++ "," ++ Nat.show(count) ++ "," ++ U32.show(C.encode(head)))

def snapshot(r: World & String) -> World & String:
  (s, out) = r
  W{a, log, fresh, pool} = s
  snap_done(log, fresh, pool, out, scan(192n, (a, Nil{})))
