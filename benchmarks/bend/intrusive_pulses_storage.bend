# Diagnostic counterpart; see intrusive_storage_support.bend.
import Base
import ./common.bend as B
import ./intrusive_support.bend as A
import ./intrusive_storage_support.bend as D
import ../../src/containers/internal/dlist_storage.bend as DL
import ../../src/containers/types/intrusive_doubly_linked_list.bend as E

type State is Type:
  S{cells: Array<U32>, pool: E.Pool<U32>, list: DL.DList<U32>}

def pushed(pool: E.Pool<U32>, r: Array<U32> & DL.DList<U32>) -> State:
  (s, list) = r
  S{s, pool, list}

def attach(list: DL.DList<U32>, s: Array<U32>, pool: E.Pool<U32>, serial: U32, value: U32, +n: U32) -> State:
  pushed(pool, D.push(Array.set(U32, Array.set(U32, s, (8 * n + 2 : U32), value), (8 * serial + 6 : U32), n), list, n))

def spawned(list: DL.DList<U32>, serial: U32, value: U32, r: Array<U32> & (E.Pool<U32> & U32)) -> State:
  Tuple{s, Tuple{pool, n}} = r
  attach(list, s, pool, serial, value, n)

def spawn(k: Nat, +seed: U32, st: State) -> State:
  match k st:
    case 0n s: s
    case 1n+ +p S{s, pool, list}: spawn(p, A.lcg(seed), spawned(list, U32.from_nat(1n+p), seed, A.take((s, pool))))

def released(list: DL.DList<U32>, r: Array<U32> & E.Pool<U32>) -> State:
  (s, pool) = r
  S{s, pool, list}

def removed(pool: E.Pool<U32>, r: Array<U32> & (DL.DList<U32> & U32)) -> State:
  Tuple{s, Tuple{list, n}} = r
  released(list, A.release(s, pool, n))

def recycle(list: DL.DList<U32>, pool: E.Pool<U32>, r: Array<U32> & U32) -> State:
  (s, +n) = r
  removed(pool, D.remove(A.consume(s, n), list, n, 0))

def drain(k: Nat, st: State) -> State:
  match k st:
    case 0n s: s
    case 1n+ +p S{s, pool, list}: drain(p, recycle(list, pool, Array.get(U32, s, (8 * U32.from_nat(1n+p) + 6 : U32))))

def pulse(+size: Nat, seed: U32, st: State) -> State:
  drain(size, spawn(size, seed, st))

def churn(churn_iterations: Nat, +size: Nat, st: State, +rng: U32) -> State:
  match churn_iterations:
    case 0n: st
    case 1n+p: churn(p, size, pulse(size, rng, st), A.lcg(rng))

def initial(r: Array<U32> & E.Pool<U32>) -> State:
  (s, pool) = r
  S{s, pool, DL.new(~U32, 0)}

def reset(st: State) -> State:
  S{s, pool, list} = st
  S{Array.set(U32, s, 3, 0), pool, list}

def empty_output(size: U32, s: Array<U32>, r: DL.DList<U32> & Nat) -> String:
  (list, count) = r
  A.output(A.note(s, U32.from_nat(count)), size)

def output(+size: U32, st: State) -> String:
  S{s, E.Pool{head, count}, list} = st
  empty_output(size, A.observe_pool(U32.to_nat(size), (A.note(s, U32.from_nat(count)), head)), DL.length(~U32, list))

def go(+g: B.Args) -> String:
  +size : U32 = B.a_size(g)
  output(size, churn(U32.to_nat(B.a_count(g)), U32.to_nat(size), reset(pulse(U32.to_nat(size), 0, initial(A.new_pool(size)))), B.a_seed(g)))

def main() -> IO(Unit):
  do IO<Unit>:
    raw : List<String> <- IO.args()
    IO.print(go(B.parse(raw)))
