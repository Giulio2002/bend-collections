import Base
import ./dlist/state.bend as ST
import ./dlist/reuse_insert.bend as RI
import ../src/deque.bend as Q
import ../src/doubly_linked_list.bend as D
import ../types/deque.bend as E
import ../types/doubly_linked_list.bend as H

# Actual public adapter laws. These establish routing, empty behavior and
# indefinitely reusable singleton storage. They are NOT the general sequence
# refinement/invariant theorem in proofs/deque.bend, whose migration is pending.

def new_uses_dll(~T: Data) -> {Q.new(~T) == Q.DQ{D.new(~T, 0)} : Q.Deque<T>}:
  {==}

def push_front_uses_dll(~T: Data, +sh: ST.Shadow<T>, +free: U32, +x: T) -> {Q.push_front(~T, Q.DQ{RI.real_with_free(~T, sh, free)}, x) == Q.pushed(~T, D.push_front_free(~T, RI.real_with_free(~T, sh, free), x)) : Q.Deque<T>}:
  {==}

def push_back_uses_dll(~T: Data, +sh: ST.Shadow<T>, +free: U32, +x: T) -> {Q.push_back(~T, Q.DQ{RI.real_with_free(~T, sh, free)}, x) == Q.pushed(~T, D.push_back_free(~T, RI.real_with_free(~T, sh, free), x)) : Q.Deque<T>}:
  {==}

def pop_front_uses_dll(~T: Data, +sh: ST.Shadow<T>, +free: U32) -> {Q.pop_front(~T, Q.DQ{RI.real_with_free(~T, sh, free)}) == Q.lift(~T, D.pop_front_free(~T, RI.real_with_free(~T, sh, free))) : Q.Deque<T> & Result<&2, &2, E.Error, T>}:
  {==}

def pop_back_uses_dll(~T: Data, +sh: ST.Shadow<T>, +free: U32) -> {Q.pop_back(~T, Q.DQ{RI.real_with_free(~T, sh, free)}) == Q.lift(~T, D.pop_back_free(~T, RI.real_with_free(~T, sh, free))) : Q.Deque<T> & Result<&2, &2, E.Error, T>}:
  {==}

def peek_front_uses_dll(~T: Data, +sh: ST.Shadow<T>, +free: U32) -> {Q.peek_front(~T, Q.DQ{RI.real_with_free(~T, sh, free)}) == Q.lift(~T, D.peek_front(~T, RI.real_with_free(~T, sh, free))) : Q.Deque<T> & Result<&2, &2, E.Error, T>}:
  {==}

def peek_back_uses_dll(~T: Data, +sh: ST.Shadow<T>, +free: U32) -> {Q.peek_back(~T, Q.DQ{RI.real_with_free(~T, sh, free)}) == Q.lift(~T, D.peek_back(~T, RI.real_with_free(~T, sh, free))) : Q.Deque<T> & Result<&2, &2, E.Error, T>}:
  {==}

def length_uses_dll(~T: Data, +sh: ST.Shadow<T>, +free: U32) -> {Q.length(~T, Q.DQ{RI.real_with_free(~T, sh, free)}) == Q.lift_nat(~T, D.length(~T, RI.real_with_free(~T, sh, free))) : Q.Deque<T> & Nat}:
  {==}

def list_uses_dll(~T: Data, +sh: ST.Shadow<T>, +free: U32) -> {Q.to_list(~T, Q.DQ{RI.real_with_free(~T, sh, free)}) == Q.lift_list(~T, D.to_list(~T, RI.real_with_free(~T, sh, free))) : Q.Deque<T> & List<&2, T>}:
  {==}

# Initial versus recycled empty states are distinct: recycled storage must
# remain available without retaining an element value.
def recycled(~T: Data) -> Q.Deque<T>:
  Q.DQ{D.DL{0, 1, 1, 0n, 0, 0, 0n, 1, ALeaf{None{}}, ALeaf{0}, ALeaf{0}}}

def singleton(~T: Data, x: T) -> Q.Deque<T>:
  Q.DQ{D.DL{0, 1, 0, 1n, 1, 1, 0n, 1, ALeaf{Some{x}}, ALeaf{0}, ALeaf{0}}}

def first_front(~T: Data, +x: T) -> {Q.push_front(~T, Q.new(~T), x) == singleton(~T, x) : Q.Deque<T>}:
  {==}

def first_back(~T: Data, +x: T) -> {Q.push_back(~T, Q.new(~T), x) == singleton(~T, x) : Q.Deque<T>}:
  {==}

def reuse_front(~T: Data, +x: T) -> {Q.push_front(~T, recycled(~T), x) == singleton(~T, x) : Q.Deque<T>}:
  {==}

def reuse_back(~T: Data, +x: T) -> {Q.push_back(~T, recycled(~T), x) == singleton(~T, x) : Q.Deque<T>}:
  {==}

def retire_front(~T: Data, +x: T) -> {Q.pop_front(~T, singleton(~T, x)) == (recycled(~T), Done{x}) : Q.Deque<T> & Result<&2, &2, E.Error, T>}:
  {==}

def retire_back(~T: Data, +x: T) -> {Q.pop_back(~T, singleton(~T, x)) == (recycled(~T), Done{x}) : Q.Deque<T> & Result<&2, &2, E.Error, T>}:
  {==}

def recycled_empty_front(~T: Data) -> {Q.pop_front(~T, recycled(~T)) == (recycled(~T), Fail{E.EmptyDeque{}}) : Q.Deque<T> & Result<&2, &2, E.Error, T>}:
  {==}

def recycled_empty_back(~T: Data) -> {Q.pop_back(~T, recycled(~T)) == (recycled(~T), Fail{E.EmptyDeque{}}) : Q.Deque<T> & Result<&2, &2, E.Error, T>}:
  {==}

def initial_empty_front(~T: Data) -> {Q.pop_front(~T, Q.new(~T)) == (Q.new(~T), Fail{E.EmptyDeque{}}) : Q.Deque<T> & Result<&2, &2, E.Error, T>}:
  {==}

def initial_empty_back(~T: Data) -> {Q.pop_back(~T, Q.new(~T)) == (Q.new(~T), Fail{E.EmptyDeque{}}) : Q.Deque<T> & Result<&2, &2, E.Error, T>}:
  {==}

# A concrete family of arbitrary-length traces: push_back(x), pop_front for
# every input value. All values are observed; capacity and allocation count
# remain one regardless of trace length. This is not the all-operation trace.
def append_result(~T: Data, acc: List<&2, T>, r: Q.Deque<T> & Result<&2, &2, E.Error, T>) -> Q.Deque<T> & List<&2, T>:
  match r:
    case Tuple{d, Done{x}}:
      (d, Con{x, acc})
    case Tuple{d, Fail{e}}:
      (d, acc)

def round(~T: Data, x: T, st: Q.Deque<T> & List<&2, T>) -> Q.Deque<T> & List<&2, T>:
  (d, acc) = st
  append_result(~T, acc, Q.pop_front(~T, Q.push_back(~T, d, x)))

def cycles(~T: Data, xs: List<&2, T>, st: Q.Deque<T> & List<&2, T>) -> Q.Deque<T> & List<&2, T>:
  match xs:
    case Nil{}:
      st
    case Con{x, rest}:
      cycles(~T, rest, round(~T, x, st))

def unlimited_reuse(~T: Data, +xs: List<&2, T>, +acc: List<&2, T>) -> {cycles(~T, xs, (recycled(~T), acc)) == (recycled(~T), List.reverse.go(&2, T, xs, acc)) : Q.Deque<T> & List<&2, T>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      unlimited_reuse(~T, rest, Con{x, acc})

law unlimited_reuse_u32:
  for +xs: List<&2, U32>
  for +acc: List<&2, U32>
  {cycles(~U32, xs, (recycled(~U32), acc)) == (recycled(~U32), List.reverse.go(&2, U32, xs, acc)) : Q.Deque<U32> & List<&2, U32>}
def unlimited_reuse_u32(xs, acc):
  unlimited_reuse(~U32, xs, acc)

law unlimited_reuse_string:
  for +xs: List<&2, String>
  for +acc: List<&2, String>
  {cycles(~String, xs, (recycled(~String), acc)) == (recycled(~String), List.reverse.go(&2, String, xs, acc)) : Q.Deque<String> & List<&2, String>}
def unlimited_reuse_string(xs, acc):
  unlimited_reuse(~String, xs, acc)
