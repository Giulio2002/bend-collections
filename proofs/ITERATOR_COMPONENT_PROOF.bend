import Base
import ../src/containers/dlist_iterator.bend as I
import ../src/containers/doubly_linked_list.bend as D
import ../src/containers/types/doubly_linked_list.bend as E
import ../src/containers/internal/dlist_storage.bend as R

# Component laws over the actual cursor implementation. These are not a full
# sequence-refinement proof for all edits/traces or the underlying arena.
def finish_owns(s: D.DList<U32>, n: U32, last: U32, f: Bool, i: Nat) -> {I.finish(~U32, I.IT{s, n, last, f, i}) == s : D.DList<U32>}:
  {==}

def next_exhausted(s: D.DList<U32>, +last: U32, +f: Bool, +i: Nat) -> {I.next(~U32, I.IT{s, 0, last, f, i}) == (I.IT{s, 0, last, f, i}, Fail{I.Exhausted{}}) : I.Iterator<U32> & Result<&2, &2, I.Error, U32>}:
  match s:
    case D.DL{tag, depth, cap, R.DL{owner, fresh, free, count, head, tail, rd, rc, vals, prevs, nexts}, gens}:
      {==}

def set_requires_current(s: D.DList<U32>, +n: U32, +f: Bool, +i: Nat, x: U32) -> {I.set(~U32, I.IT{s, n, 0, f, i}, x) == (I.IT{s, n, 0, f, i}, Fail{I.NoCurrent{}}) : I.Iterator<U32> & Result<&2, &2, I.Error, Unit>}:
  {==}

def remove_requires_current(s: D.DList<U32>, +n: U32, +f: Bool, +i: Nat) -> {I.remove(~U32, I.IT{s, n, 0, f, i}) == (I.IT{s, n, 0, f, i}, Fail{I.NoCurrent{}}) : I.Iterator<U32> & Result<&2, &2, I.Error, Unit>}:
  match s:
    case D.DL{tag, depth, cap, R.DL{owner, fresh, free, count, head, tail, rd, rc, vals, prevs, nexts}, gens}:
      {==}

def has_next_state(s: D.DList<U32>, +n: U32, +last: U32, +f: Bool, +i: Nat) -> {I.has_next(~U32, I.IT{s, n, last, f, i}) == (I.IT{s, n, last, f, i}, I.present(n)) : I.Iterator<U32> & Bool}:
  {==}

def has_previous_state(s: D.DList<U32>, +n: U32, +last: U32, +f: Bool, +i: Nat) -> {I.has_previous(~U32, I.IT{s, n, last, f, i}) == (I.IT{s, n, last, f, i}, Nat.is_lt(0n, i)) : I.Iterator<U32> & Bool}:
  {==}

def added_clears_current(s: D.DList<U32>, +n: U32, last: U32, +f: Bool, +i: Nat, h: E.Handle) -> {I.added(~U32, n, last, f, i, (s, Done{h})) == (I.IT{s, n, 0, f, 1n+i}, Done{Unit{}}) : I.Iterator<U32> & Result<&2, &2, I.Error, Unit>}:
  {==}

def removed_forward(s: D.DList<U32>, n: U32, last: U32, +i: Nat, +after: U32, x: U32) -> {I.removed(~U32, n, last, True{}, i, after, (s, Done{x})) == (I.IT{s, after, 0, True{}, Nat.sub(i, 1n)}, Done{Unit{}}) : I.Iterator<U32> & Result<&2, &2, I.Error, Unit>}:
  {==}

def removed_backward(s: D.DList<U32>, n: U32, last: U32, +i: Nat, +after: U32, x: U32) -> {I.removed(~U32, n, last, False{}, i, after, (s, Done{x})) == (I.IT{s, after, 0, False{}, i}, Done{Unit{}}) : I.Iterator<U32> & Result<&2, &2, I.Error, Unit>}:
  {==}

def finish_owns_string(s: D.DList<String>, n: U32, last: U32, f: Bool, i: Nat) -> {I.finish(~String, I.IT{s, n, last, f, i}) == s : D.DList<String>}:
  {==}

def next_exhausted_string(s: D.DList<String>, +last: U32, +f: Bool, +i: Nat) -> {I.next(~String, I.IT{s, 0, last, f, i}) == (I.IT{s, 0, last, f, i}, Fail{I.Exhausted{}}) : I.Iterator<String> & Result<&2, &2, I.Error, String>}:
  match s:
    case D.DL{tag, depth, cap, R.DL{owner, fresh, free, count, head, tail, rd, rc, vals, prevs, nexts}, gens}:
      {==}

def set_requires_current_string(s: D.DList<String>, +n: U32, +f: Bool, +i: Nat, x: String) -> {I.set(~String, I.IT{s, n, 0, f, i}, x) == (I.IT{s, n, 0, f, i}, Fail{I.NoCurrent{}}) : I.Iterator<String> & Result<&2, &2, I.Error, Unit>}:
  {==}

def remove_requires_current_string(s: D.DList<String>, +n: U32, +f: Bool, +i: Nat) -> {I.remove(~String, I.IT{s, n, 0, f, i}) == (I.IT{s, n, 0, f, i}, Fail{I.NoCurrent{}}) : I.Iterator<String> & Result<&2, &2, I.Error, Unit>}:
  match s:
    case D.DL{tag, depth, cap, R.DL{owner, fresh, free, count, head, tail, rd, rc, vals, prevs, nexts}, gens}:
      {==}

def has_next_state_string(s: D.DList<String>, +n: U32, +last: U32, +f: Bool, +i: Nat) -> {I.has_next(~String, I.IT{s, n, last, f, i}) == (I.IT{s, n, last, f, i}, I.present(n)) : I.Iterator<String> & Bool}:
  {==}

def has_previous_state_string(s: D.DList<String>, +n: U32, +last: U32, +f: Bool, +i: Nat) -> {I.has_previous(~String, I.IT{s, n, last, f, i}) == (I.IT{s, n, last, f, i}, Nat.is_lt(0n, i)) : I.Iterator<String> & Bool}:
  {==}

def added_clears_current_string(s: D.DList<String>, +n: U32, last: U32, +f: Bool, +i: Nat, h: E.Handle) -> {I.added(~String, n, last, f, i, (s, Done{h})) == (I.IT{s, n, 0, f, 1n+i}, Done{Unit{}}) : I.Iterator<String> & Result<&2, &2, I.Error, Unit>}:
  {==}

def removed_forward_string(s: D.DList<String>, n: U32, last: U32, +i: Nat, +after: U32, x: String) -> {I.removed(~String, n, last, True{}, i, after, (s, Done{x})) == (I.IT{s, after, 0, True{}, Nat.sub(i, 1n)}, Done{Unit{}}) : I.Iterator<String> & Result<&2, &2, I.Error, Unit>}:
  {==}

def removed_backward_string(s: D.DList<String>, n: U32, last: U32, +i: Nat, +after: U32, x: String) -> {I.removed(~String, n, last, False{}, i, after, (s, Done{x})) == (I.IT{s, after, 0, False{}, i}, Done{Unit{}}) : I.Iterator<String> & Result<&2, &2, I.Error, Unit>}:
  {==}

# The end-gap insertion is exactly the public DLL append, including capacity
# growth, free-slot reuse, and generation bookkeeping. This is an algorithm
# bridge, not merely an equality with a model that invokes the iterator.
def end_gap_is_append(s: D.DList<U32>, x: U32) -> {I.cursor_insert_gap(~U32, s, 0, x) == I.insert_gap_result(~U32, D.push_back(~U32, s, x)) : D.DList<U32> & Result<&2, &2, E.Error, E.Handle>}:
  match s:
    case D.DL{tag, depth, cap, R.DL{owner, fresh, free, count, head, tail, rd, rc, vals, prevs, nexts}, gens}:
      {==}

def end_gap_is_append_string(s: D.DList<String>, x: String) -> {I.cursor_insert_gap(~String, s, 0, x) == I.insert_gap_result(~String, D.push_back(~String, s, x)) : D.DList<String> & Result<&2, &2, E.Error, E.Handle>}:
  match s:
    case D.DL{tag, depth, cap, R.DL{owner, fresh, free, count, head, tail, rd, rc, vals, prevs, nexts}, gens}:
      {==}

def move_forward_cursor(n: U32, last: U32, f: Bool, +i: Nat, +h: U32, +after: U32, +x: U32) -> {I.move_meta(~U32, n, last, f, i, h, after, True{}, Done{x}) == I.M{after, h, True{}, 1n+i, Done{x}} : I.Move<U32>}:
  {==}

def move_backward_cursor(n: U32, last: U32, f: Bool, +i: Nat, +h: U32, +x: U32) -> {I.move_meta(~U32, n, last, f, i, h, h, False{}, Done{x}) == I.M{h, h, False{}, Nat.sub(i, 1n), Done{x}} : I.Move<U32>}:
  {==}

def failed_move_preserves_cursor(+n: U32, +last: U32, +f: Bool, +i: Nat, h: U32, after: U32, forward: Bool, +e: I.Error) -> {I.move_meta(~U32, n, last, f, i, h, after, forward, Fail{e}) == I.M{n, last, f, i, Fail{e}} : I.Move<U32>}:
  {==}
