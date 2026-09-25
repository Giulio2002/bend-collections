import Base
import ./queue.bend as QS

# ---- contract (SPARK formal containers) ----
# Each `<Subprogram>.<clause>` definition below states one Post clause of
# that SPARK subprogram, as a proposition on this model; the table names the
# clauses. proofs/containers/simple_queue/ proves every clause under its clause name,
# and its `impl` lemma carries them to the implementation.
#
# The simple queue is the FIFO queue behind another interface; every one of
# its operations is the queue's (for every element type), so it has the
# queue's SPARK formal-vector contracts, spec/containers/queue.bend (restated below):
#
#   SPARK subprogram      simple_queue   queue     contract lemmas (QC.)
#   Empty_Vector          new            new       new_empty, new_impl
#   Length                qsize          length    length_result, length_frame
#   Append                put            enqueue   enqueue_length, enqueue_prefix, enqueue_element
#   Delete_First          get            dequeue   dequeue_length, dequeue_shifted,
#                                                  dequeue_result, dequeue_empty
#   First_Element         peek           peek      peek_first, peek_frame, peek_empty
#   iteration             to_list        to_list   to_list_model, to_list_frame
#   implementation                                 QC.impl

# The model is the queue's (QS.step) and so is every clause:

def Length.length_result(-T: Data, +xs: List<&2, T>) -> Type:
  QS.Length.length_result(T, xs)

def Length.length_frame(-T: Data, +xs: List<&2, T>) -> Type:
  QS.Length.length_frame(T, xs)

def Iteration.to_list_model(-T: Data, +xs: List<&2, T>) -> Type:
  QS.Iteration.to_list_model(T, xs)

def Iteration.to_list_frame(-T: Data, +xs: List<&2, T>) -> Type:
  QS.Iteration.to_list_frame(T, xs)

def Append.enqueue_length(-T: Data, +xs: List<&2, T>, +v: T) -> Type:
  QS.Append.enqueue_length(T, xs, v)

def Append.enqueue_prefix(-T: Data, +xs: List<&2, T>, +v: T) -> Type:
  QS.Append.enqueue_prefix(T, xs, v)

def Append.enqueue_element(-T: Data, +xs: List<&2, T>, +v: T) -> Type:
  QS.Append.enqueue_element(T, xs, v)

def Delete_First.dequeue_length(-T: Data, +h: T, +t: List<&2, T>) -> Type:
  QS.Delete_First.dequeue_length(T, h, t)

def Delete_First.dequeue_shifted(-T: Data, +h: T, +t: List<&2, T>) -> Type:
  QS.Delete_First.dequeue_shifted(T, h, t)

def Delete_First.dequeue_result(-T: Data, +h: T, +t: List<&2, T>) -> Type:
  QS.Delete_First.dequeue_result(T, h, t)

def Delete_First.dequeue_empty(-T: Data) -> Type:
  QS.Delete_First.dequeue_empty(T)

def First_Element.peek_first(-T: Data, +h: T, +t: List<&2, T>) -> Type:
  QS.First_Element.peek_first(T, h, t)

def First_Element.peek_frame(-T: Data, +xs: List<&2, T>) -> Type:
  QS.First_Element.peek_frame(T, xs)

def First_Element.peek_empty(-T: Data) -> Type:
  QS.First_Element.peek_empty(T)

