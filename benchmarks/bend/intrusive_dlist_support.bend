import Base
import ./intrusive_support.bend as A
import ../../src/containers/doubly_linked_list.bend as DL
import ../../src/containers/types/doubly_linked_list.bend as E

# Use the direct PUBLIC checked API, never dispatch/step or private storage.
# The external ID survives a transfer; its list-local handle is replaced.
def remember(s: Array<U32>, +n: U32, h: E.Handle) -> Array<U32>:
  E.H{owner, slot, generation} = h
  Array.set(U32, Array.set(U32, s, (8 * n + 3 : U32), slot), (8 * n + 4 : U32), generation)

def inserted(s: Array<U32>, n: U32, r: DL.DList<U32> & E.Handle) -> Array<U32> & DL.DList<U32>:
  (list, h) = r
  (remember(s, n, h), list)

def push(s: Array<U32>, list: DL.DList<U32>, +n: U32) -> Array<U32> & DL.DList<U32>:
  inserted(s, n, DL.push_front(~U32, list, n))

def handle_gen(owner: U32, slot: U32, r: Array<U32> & U32) -> Array<U32> & E.Handle:
  (s, generation) = r
  (s, E.H{owner, slot, generation})

def handle_slot(n: U32, owner: U32, r: Array<U32> & U32) -> Array<U32> & E.Handle:
  (s, slot) = r
  handle_gen(owner, slot, Array.get(U32, s, (8 * n + 4 : U32)))

def handle(s: Array<U32>, +n: U32, owner: U32) -> Array<U32> & E.Handle:
  handle_slot(n, owner, Array.get(U32, s, (8 * n + 3 : U32)))

def removed(s: Array<U32>, r: DL.DList<U32> & Result<&2, &2, E.Error, U32>) -> Array<U32> & (DL.DList<U32> & U32):
  match r:
    case Tuple{list, Done{n}}: (s, (list, n))
    case Tuple{list, Fail{e}}: (A.error(s), (list, 0))

def remove_handle(list: DL.DList<U32>, r: Array<U32> & E.Handle) -> Array<U32> & (DL.DList<U32> & U32):
  (s, h) = r
  removed(s, DL.remove(~U32, list, h))

def remove(s: Array<U32>, list: DL.DList<U32>, n: U32, owner: U32) -> Array<U32> & (DL.DList<U32> & U32):
  remove_handle(list, handle(s, n, owner))

def forget(r: Array<U32> & (DL.DList<U32> & U32)) -> Array<U32> & DL.DList<U32>:
  Tuple{s, Tuple{list, n}} = r
  (s, list)

def fill(k: Nat, r: Array<U32> & DL.DList<U32>) -> Array<U32> & DL.DList<U32>:
  match k r:
    case 0n Tuple{s, list}: (s, list)
    case 1n+ +p Tuple{s, list}:
      fill(p, push(Array.set(U32, s, (8 * U32.from_nat(1n+p) + 2 : U32), A.mix(U32.from_nat(1n+p), 17)), list, U32.from_nat(1n+p)))

def empty(k: Nat, +owner: U32, r: Array<U32> & DL.DList<U32>) -> Array<U32> & DL.DList<U32>:
  match k r:
    case 0n Tuple{s, list}: (s, list)
    case 1n+ +p Tuple{s, list}: empty(p, owner, forget(remove(s, list, U32.from_nat(1n+p), owner)))

def observe_ids(ids: List<&2, U32>, s: Array<U32>) -> Array<U32>:
  match ids:
    case Nil{}: s
    case Con{n, rest}: observe_ids(rest, A.note(s, n))

def observed(s: Array<U32>, r: DL.DList<U32> & List<&2, U32>) -> Array<U32>:
  (list, ids) = r
  observe_ids(ids, A.note(s, 4294967295))

def observe(s: Array<U32>, list: DL.DList<U32>) -> Array<U32>:
  observed(s, DL.to_list(~U32, list))
