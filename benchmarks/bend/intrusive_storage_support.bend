import Base
import ./intrusive_support.bend as A
import ../../src/containers/internal/dlist_storage.bend as DL
import ../../src/containers/types/internal_dlist.bend as E

# Diagnostic only: shared DList storage without the generation facade.
# Bounds, owner and live-slot checks, tail/count, arenas and handle mapping
# remain. Handles are used once, immediately discarded, and never escape;
# recycling here deliberately does not provide stale-after-reuse protection.
def remember(s: Array<U32>, +n: U32, h: E.Handle) -> Array<U32>:
  E.H{owner, slot} = h
  Array.set(U32, s, (8 * n + 3 : U32), slot)

def inserted(s: Array<U32>, n: U32, r: DL.DList<U32> & E.Handle) -> Array<U32> & DL.DList<U32>:
  (list, h) = r
  (remember(s, n, h), list)

def push(s: Array<U32>, list: DL.DList<U32>, +n: U32) -> Array<U32> & DL.DList<U32>:
  inserted(s, n, DL.push_front_free(~U32, list, n))

def handle_slot(n: U32, owner: U32, r: Array<U32> & U32) -> Array<U32> & E.Handle:
  (s, slot) = r
  (s, E.H{owner, slot})

def handle(s: Array<U32>, +n: U32, owner: U32) -> Array<U32> & E.Handle:
  handle_slot(n, owner, Array.get(U32, s, (8 * n + 3 : U32)))

def removed(s: Array<U32>, slot: U32, r: DL.DList<U32> & Result<&2, &2, E.Error, U32>) -> Array<U32> & (DL.DList<U32> & U32):
  match r:
    case Tuple{list, Done{n}}: (s, (DL.recycle_slot(~U32, list, slot), n))
    case Tuple{list, Fail{e}}: (A.error(s), (list, 0))

def remove_handle(list: DL.DList<U32>, r: Array<U32> & E.Handle) -> Array<U32> & (DL.DList<U32> & U32):
  (s, E.H{owner, +slot}) = r
  removed(s, slot, DL.remove(~U32, list, E.H{owner, slot}))

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
