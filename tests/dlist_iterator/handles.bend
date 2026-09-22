import Base
import ../../src/dlist_iterator.bend as I
import ../../src/doubly_linked_list.bend as D
import ../../src/internal/dlist_storage.bend as R
import ../../types/doubly_linked_list.bend as E

# Retained public handles must survive cursor compaction correctly: the
# removed slot's handle is stale even after recycling; a survivor stays live.
def survivor(r: D.DList<U32> & Result<&2, &2, E.Error, U32>) -> U32:
  match r:
    case Tuple{s, Done{x}}:
      x
    case Tuple{s, Fail{e}}:
      999

def stale(keep: E.Handle, r: D.DList<U32> & Result<&2, &2, E.Error, U32>) -> U32:
  match r:
    case Tuple{s, Fail{E.StaleHandle{}}}:
      survivor(D.get(~U32, s, keep))
    case Tuple{s, Fail{E.ForeignHandle{}}}:
      998
    case Tuple{s, Done{x}}:
      997

def after_add(old: E.Handle, keep: E.Handle, r: I.Iterator<U32> & Result<&2, &2, I.Error, Unit>) -> U32:
  (it, result) = r
  stale(keep, D.get(~U32, I.finish(~U32, it), old))

def after_remove(old: E.Handle, keep: E.Handle, r: I.Iterator<U32> & Result<&2, &2, I.Error, Unit>) -> U32:
  (it, result) = r
  after_add(old, keep, I.add(~U32, it, 42))

def after_next(old: E.Handle, keep: E.Handle, r: I.Iterator<U32> & Result<&2, &2, I.Error, U32>) -> U32:
  (it, result) = r
  after_remove(old, keep, I.remove(~U32, it))

def after_second(old: E.Handle, r: D.DList<U32> & E.Handle) -> U32:
  (s, keep) = r
  after_next(old, keep, I.next(~U32, I.iter_first(~U32, s)))

def after_first(r: D.DList<U32> & E.Handle) -> U32:
  (s, old) = r
  after_second(old, D.push_back(~U32, s, 23))

# UINT32_MAX generations must retire, not wrap and recycle. Construct this
# boundary directly because reaching it via 2^32 removals is not a useful test.
def retired_added(r: D.DList<U32> & E.Handle) -> U32:
  (s, E.H{tag, id, gen}) = r
  id

def retired_removed(r: I.Iterator<U32> & Result<&2, &2, I.Error, Unit>) -> U32:
  (it, result) = r
  retired_added(D.push_back(~U32, I.finish(~U32, it), 42))

def retired_next(r: I.Iterator<U32> & Result<&2, &2, I.Error, U32>) -> U32:
  (it, result) = r
  retired_removed(I.remove(~U32, it))

def retire_first(r: D.DList<U32> & E.Handle) -> U32:
  (D.DL{tag, depth, cap, raw, gens}, h) = r
  retired_next(I.next(~U32, I.iter_first(~U32, D.DL{tag, depth, cap, raw, Array.set(U32, gens, 0, 4294967295)})))

def main() -> IO(Unit):
  do IO<Unit>:
    a : Unit <- IO.print(U32.show(after_first(D.push_back(~U32, D.new(~U32, 7), 11))))
    IO.print(U32.show(retire_first(D.push_back(~U32, D.new(~U32, 7), 11))))
