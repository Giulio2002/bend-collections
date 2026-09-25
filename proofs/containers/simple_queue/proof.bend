import Base
import ../../../src/containers/simple_queue.bend as P1
import ../../../src/containers/queue.bend as K1
import ../../../src/containers/types/queue.bend as E1
import ../../../spec/containers/simple_queue.bend as S
import ../queue/proof.bend as UP

# src/containers/simple_queue.bend: a FIFO queue behind the queue interface (put = enqueue, get = dequeue, qsize = length).

def simple_queue_put(q: K1.Queue<U32>, +v: U32) -> {P1.put(~U32, q, v) == K1.enqueue(~U32, q, v) : K1.Queue<U32>}:
  {==}

def simple_queue_get(q: K1.Queue<U32>) -> {P1.get(~U32, q) == K1.dequeue(~U32, q) : K1.Queue<U32> & Result<&2, &2, E1.Error, U32>}:
  {==}

def simple_queue_qsize(q: K1.Queue<U32>) -> {P1.qsize(~U32, q) == K1.length(~U32, q) : K1.Queue<U32> & Nat}:
  {==}

# ==== the contract of simple_queue (stated in spec/containers/simple_queue.bend) ====================

def new_is(~T: Data) -> {P1.new(~T) == K1.new(~T) : K1.Queue<T>}:
  {==}

def qsize_is(~T: Data, q: K1.Queue<T>) -> {P1.qsize(~T, q) == K1.length(~T, q) : K1.Queue<T> & Nat}:
  {==}

def put_is(~T: Data, q: K1.Queue<T>, x: T) -> {P1.put(~T, q, x) == K1.enqueue(~T, q, x) : K1.Queue<T>}:
  {==}

def get_is(~T: Data, q: K1.Queue<T>) -> {P1.get(~T, q) == K1.dequeue(~T, q) : K1.Queue<T> & Result<&2, &2, E1.Error, T>}:
  {==}

def peek_is(~T: Data, q: K1.Queue<T>) -> {P1.peek(~T, q) == K1.peek(~T, q) : K1.Queue<T> & Result<&2, &2, E1.Error, T>}:
  {==}

def to_list_is(~T: Data, q: K1.Queue<T>) -> {P1.to_list(~T, q) == K1.to_list(~T, q) : K1.Queue<T> & List<&2, T>}:
  {==}

# ---- the queue's contract, carried: every clause is proved by the queue ----

def length_result(-T: Data, +xs: List<&2, T>) -> S.Length.length_result(T, xs):
  UP.length_result(T, xs)

def length_frame(-T: Data, +xs: List<&2, T>) -> S.Length.length_frame(T, xs):
  UP.length_frame(T, xs)

def to_list_model(-T: Data, +xs: List<&2, T>) -> S.Iteration.to_list_model(T, xs):
  UP.to_list_model(T, xs)

def to_list_frame(-T: Data, +xs: List<&2, T>) -> S.Iteration.to_list_frame(T, xs):
  UP.to_list_frame(T, xs)

def enqueue_length(-T: Data, +xs: List<&2, T>, +v: T) -> S.Append.enqueue_length(T, xs, v):
  UP.enqueue_length(T, xs, v)

def enqueue_prefix(-T: Data, +xs: List<&2, T>, +v: T) -> S.Append.enqueue_prefix(T, xs, v):
  UP.enqueue_prefix(T, xs, v)

def enqueue_element(-T: Data, +xs: List<&2, T>, +v: T) -> S.Append.enqueue_element(T, xs, v):
  UP.enqueue_element(T, xs, v)

def dequeue_length(-T: Data, +h: T, +t: List<&2, T>) -> S.Delete_First.dequeue_length(T, h, t):
  UP.dequeue_length(T, h, t)

def dequeue_shifted(-T: Data, +h: T, +t: List<&2, T>) -> S.Delete_First.dequeue_shifted(T, h, t):
  UP.dequeue_shifted(T, h, t)

def dequeue_result(-T: Data, +h: T, +t: List<&2, T>) -> S.Delete_First.dequeue_result(T, h, t):
  UP.dequeue_result(T, h, t)

def dequeue_empty(-T: Data) -> S.Delete_First.dequeue_empty(T):
  UP.dequeue_empty(T)

def peek_first(-T: Data, +h: T, +t: List<&2, T>) -> S.First_Element.peek_first(T, h, t):
  UP.peek_first(T, h, t)

def peek_frame(-T: Data, +xs: List<&2, T>) -> S.First_Element.peek_frame(T, xs):
  UP.peek_frame(T, xs)

def peek_empty(-T: Data) -> S.First_Element.peek_empty(T):
  UP.peek_empty(T)

